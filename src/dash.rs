//! Live terminal dashboard (ANSI, no dependencies). Redraws in place a few times per second on a TTY; on a pipe it
//! prints one plain progress line every few seconds instead.

use crate::glue::{Mode, Route, Shared};
use crate::sys;
use std::io::Write;
use std::sync::atomic::Ordering::Relaxed;
use std::time::{Duration, Instant};

pub const RESET: &str = "\x1b[0m";
pub const BOLD: &str = "\x1b[1m";
pub const DIM: &str = "\x1b[2m";
pub const RED: &str = "\x1b[31m";
pub const GREEN: &str = "\x1b[32m";
pub const YELLOW: &str = "\x1b[33m";
pub const BLUE: &str = "\x1b[34m";
pub const MAGENTA: &str = "\x1b[35m";
pub const CYAN: &str = "\x1b[36m";

pub fn is_tty() -> bool {
    extern "C" {
        fn isatty(fd: i32) -> i32;
    }
    unsafe { isatty(1) == 1 }
}

pub fn term_width() -> usize {
    #[repr(C)]
    struct Winsize {
        row: u16,
        col: u16,
        x: u16,
        y: u16,
    }
    extern "C" {
        fn ioctl(fd: i32, req: u64, ...) -> i32;
    }
    let mut ws = Winsize { row: 0, col: 0, x: 0, y: 0 };
    let r = unsafe { ioctl(1, 0x5413, &mut ws as *mut Winsize) };
    if r == 0 && ws.col >= 40 {
        ws.col as usize
    } else {
        110
    }
}

pub fn commas(x: u64) -> String {
    let s = x.to_string();
    let mut out = String::new();
    for (i, ch) in s.chars().enumerate() {
        if i > 0 && (s.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(ch);
    }
    out
}

pub fn si(x: f64) -> String {
    let a = x.abs();
    if a >= 1e9 {
        format!("{:.2}G", x / 1e9)
    } else if a >= 1e6 {
        format!("{:.2}M", x / 1e6)
    } else if a >= 1e4 {
        format!("{:.1}k", x / 1e3)
    } else if a >= 100.0 {
        format!("{:.0}", x)
    } else {
        format!("{:.1}", x)
    }
}

pub fn dur(secs: f64) -> String {
    if !secs.is_finite() || secs < 0.0 {
        return "--".into();
    }
    let s = secs as u64;
    if s >= 86400 * 2 {
        format!("{:.1}d", secs / 86400.0)
    } else if s >= 3600 {
        format!("{}h{:02}m", s / 3600, s % 3600 / 60)
    } else if s >= 60 {
        format!("{}m{:02}s", s / 60, s % 60)
    } else {
        format!("{:.1}s", secs)
    }
}

fn gib(kb: u64) -> String {
    format!("{:.1} GiB", kb as f64 / 1048576.0)
}

pub fn bar(frac: f64, width: usize) -> String {
    let frac = frac.clamp(0.0, 1.0);
    let cells = frac * width as f64;
    let full = cells.floor() as usize;
    let parts = [" ", "▏", "▎", "▍", "▌", "▋", "▊", "▉"];
    let mut s = "█".repeat(full);
    if full < width {
        s.push_str(parts[((cells - full as f64) * 8.0) as usize]);
        s.push_str(&"·".repeat(width - full - 1));
    }
    s
}

fn spark(v: &[f64]) -> String {
    let ticks = ['▁', '▂', '▃', '▄', '▅', '▆', '▇', '█'];
    let max = v.iter().cloned().fold(0.0f64, f64::max);
    v.iter()
        .map(|&x| if max <= 0.0 { ticks[0] } else { ticks[((x / max) * 7.0).round() as usize] })
        .collect()
}

/// visible width of a string with ANSI escapes
fn vis(s: &str) -> usize {
    let mut n = 0;
    let mut esc = false;
    for ch in s.chars() {
        if esc {
            if ch == 'm' {
                esc = false;
            }
        } else if ch == '\x1b' {
            esc = true;
        } else {
            n += 1;
        }
    }
    n
}

fn pad(s: &str, w: usize) -> String {
    let v = vis(s);
    if v >= w {
        s.to_string()
    } else {
        format!("{s}{}", " ".repeat(w - v))
    }
}

pub struct Dash {
    last: Instant,
    last_pairs: u64,
    last_conf: u64,
    last_cpu: f64,
    hist: Vec<f64>,
    rate_ema: f64,
    conf_rate: f64,
    cpu_pct: f64,
    tty: bool,
    machine: sys::Machine,
    lines_drawn: usize,
}

impl Dash {
    pub fn new(machine: sys::Machine) -> Dash {
        Dash {
            last: Instant::now(),
            last_pairs: 0,
            last_conf: 0,
            last_cpu: sys::cpu_seconds(),
            hist: Vec::new(),
            rate_ema: 0.0,
            conf_rate: 0.0,
            cpu_pct: 0.0,
            tty: is_tty(),
            machine,
            lines_drawn: 0,
        }
    }

    pub fn start(&self) {
        if self.tty {
            print!("\x1b[?25l\x1b[2J\x1b[H");
            let _ = std::io::stdout().flush();
        }
    }

    pub fn finish(&self) {
        if self.tty {
            print!("\x1b[?25h");
            let _ = std::io::stdout().flush();
        }
    }

    fn sample(&mut self, sh: &Shared) -> (u64, u64) {
        let pairs: u64 = sh.workers.iter().map(|w| w.pairs.load(Relaxed)).sum();
        let conf: u64 = sh.workers.iter().map(|w| w.live.load(Relaxed)).sum();
        let now = Instant::now();
        let dt = now.duration_since(self.last).as_secs_f64();
        if dt >= 0.2 {
            let r = (pairs - self.last_pairs) as f64 / dt;
            let c = (conf.saturating_sub(self.last_conf)) as f64 / dt;
            let cpu = sys::cpu_seconds();
            self.cpu_pct = (cpu - self.last_cpu) / dt * 100.0;
            self.last_cpu = cpu;
            self.rate_ema = if self.hist.is_empty() { r } else { 0.85 * self.rate_ema + 0.15 * r };
            self.conf_rate = if self.hist.is_empty() { c } else { 0.7 * self.conf_rate + 0.3 * c };
            self.hist.push(r);
            if self.hist.len() > 60 {
                self.hist.remove(0);
            }
            self.last = now;
            self.last_pairs = pairs;
            self.last_conf = conf;
        }
        (pairs, conf)
    }

    pub fn tick(&mut self, sh: &Shared, final_frame: bool) {
        let (pairs, _conf) = self.sample(sh);
        if !self.tty {
            let target: u64 = sh.stage_target.iter().sum();
            let done: u64 = sh.stage_done.iter().map(|x| x.load(Relaxed)).sum();
            let el = sh.started.elapsed().as_secs_f64();
            let avg = pairs as f64 / el.max(1e-9);
            println!(
                "[{}] {}/{} pairs ({:.2}%)  {:.0} pairs/s  {} conflicts/s  ETA {}  SAT {}  errors {}",
                dur(el),
                commas(done),
                commas(target),
                100.0 * done as f64 / target.max(1) as f64,
                avg,
                si(self.conf_rate),
                dur((target - done.min(target)) as f64 / avg.max(1e-9)),
                sh.sats.lock().unwrap().len(),
                sh.errors.lock().unwrap().len()
            );
            return;
        }
        let w = term_width().min(140);
        let mut out: Vec<String> = Vec::new();
        let cfg = &sh.cfg;
        let el = sh.started.elapsed().as_secs_f64();
        let title = format!(
            "{BOLD}{MAGENTA} ▓▓ MONSTER ▓▓ {RESET}{BOLD} R({},{}) on K{} {RESET}{DIM}·{RESET} route {} {DIM}·{RESET} mode {} {DIM}·{RESET} {} workers",
            cfg.s,
            cfg.t,
            cfg.n,
            match cfg.route {
                Route::Parity => "parity (even d)",
                Route::All => "all degrees",
            },
            match cfg.mode {
                Mode::Stream => "stream+core-memory",
                Mode::Pair => "pair (baseline)",
                Mode::Unit => "gray-edge units",
                Mode::Hybrid => "hybrid: pattern CDCL + catalogue cubes",
                Mode::Cone => "feasible cones (uncertified prototype)",
            },
            cfg.workers
        );
        let right = format!("elapsed {BOLD}{}{RESET}", dur(el));
        out.push(format!("{}{}", pad(&title, w.saturating_sub(vis(&right) + 1)), right));
        let (rss, hwm) = sys::rss_kb();
        out.push(format!(
            "{DIM} box  {RESET}{} ×{} {DIM}·{RESET} {} {DIM}·{RESET} {} RAM {DIM}·{RESET} load {}",
            self.machine.model,
            self.machine.threads,
            self.machine.flags.join(" "),
            gib(self.machine.mem_total_kb),
            sys::loadavg()
        ));
        out.push(format!(
            "{DIM} proc {RESET}CPU {BOLD}{:.0}%{RESET} {DIM}·{RESET} RSS {} {DIM}(peak {}){RESET} {DIM}·{RESET} {BOLD}{}{RESET} conflicts/s",
            self.cpu_pct,
            gib(rss),
            gib(hwm),
            si(self.conf_rate)
        ));
        out.push(format!("{CYAN}─ stages {}{RESET}", "─".repeat(w.saturating_sub(10))));
        out.push(format!(
            "{DIM}  {:>3}  {:<14} {:<16} {:>14}  {:<26} {:>14} {:>6} {:>12}{RESET}",
            "d", "A (red nbhd)", "B (blue nbhd)", "pairs", "progress", "UNSAT", "SAT", "certified"
        ));
        let mut total_target = 0u64;
        let mut total_done = 0u64;
        for (i, st) in sh.stages.iter().enumerate() {
            let target = sh.stage_target[i];
            let done = sh.stage_done[i].load(Relaxed);
            let unsat = sh.stage_unsat[i].load(Relaxed);
            let sat = sh.stage_sat[i].load(Relaxed);
            let chk = sh.stage_checked[i].load(Relaxed);
            total_target += target;
            total_done += done;
            let frac = done as f64 / target.max(1) as f64;
            let prog = if done == target && target > 0 {
                format!("{GREEN}{}{RESET} {GREEN}done{RESET}", bar(1.0, 18))
            } else if done == 0 {
                format!("{DIM}{} wait{RESET}", bar(0.0, 18))
            } else {
                format!("{YELLOW}{}{RESET} {:>5.1}%", bar(frac, 18), frac * 100.0)
            };
            let la = format!("r{}{}/n{} ({})", cfg.s - 1, cfg.t, st.d, commas(st.a.graphs.len() as u64));
            let lb = format!("r{}{}/n{} ({})", cfg.s, cfg.t - 1, st.m, commas(st.b.graphs.len() as u64));
            let stream_mark = |side: crate::encode::Side| if st.side == side { "⇶" } else { " " };
            out.push(format!(
                "  {BOLD}{:>3}{RESET}  {}{:<13} {}{:<15} {:>14}  {} {}{:>14}{RESET} {}{:>6}{RESET} {YELLOW}{:>12}{RESET}",
                st.d,
                stream_mark(crate::encode::Side::A),
                la,
                stream_mark(crate::encode::Side::B),
                lb,
                commas(target),
                pad(&prog, 26),
                GREEN,
                commas(unsat),
                if sat > 0 { RED } else { DIM },
                commas(sat),
                commas(chk)
            ));
        }
        let left = total_target.saturating_sub(total_done);
        let avg = pairs as f64 / el.max(1e-9);
        let eta_rate = if self.rate_ema > 0.0 { 0.5 * self.rate_ema + 0.5 * avg } else { avg };
        out.push(format!("{CYAN}─ throughput {}{RESET}", "─".repeat(w.saturating_sub(14))));
        let hits: u64 = sh.workers.iter().map(|w| w.hits.load(Relaxed)).sum();
        let solves: u64 = sh.workers.iter().map(|w| w.solves.load(Relaxed)).sum();
        let roots: u64 = sh.workers.iter().map(|w| w.roots.load(Relaxed)).sum();
        let cores: u64 = sh.workers.iter().map(|w| w.cores.load(Relaxed)).sum();
        let core_lits: u64 = sh.workers.iter().map(|w| w.core_lits.load(Relaxed)).sum();
        out.push(format!(
            "  total {BOLD}{}{RESET} / {} pairs  {}  ETA {BOLD}{}{RESET}",
            commas(total_done),
            commas(total_target),
            bar(total_done as f64 / total_target.max(1) as f64, 30),
            if left == 0 { "done".into() } else { dur(left as f64 / eta_rate.max(1e-9)) }
        ));
        out.push(format!(
            "  pairs/s {BOLD}{}{RESET} now {DIM}·{RESET} {} avg   {}",
            si(self.rate_ema),
            si(avg),
            spark(&self.hist)
        ));
        if cfg.mode != Mode::Pair {
            let refuted = hits + solves + roots;
            out.push(format!(
                "  memory: {BOLD}{}{RESET} pairs refuted by cached cores ({:.1}%) {DIM}·{RESET} {} solver calls {DIM}·{RESET} {} cores, avg {:.1} of {} edge lits{}",
                commas(hits),
                100.0 * hits as f64 / refuted.max(1) as f64,
                commas(solves),
                commas(cores),
                core_lits as f64 / cores.max(1) as f64,
                sh.stages.first().map(|s| s.streamed().n * (s.streamed().n - 1) / 2).unwrap_or(0),
                if roots > 0 { format!(" {DIM}·{RESET} {GREEN}{} by root refutations{RESET}", commas(roots)) } else { String::new() }
            ));
        }
        out.push(format!(
            "  tasks {} done / {} {DIM}·{RESET} certified tasks {YELLOW}{}{RESET} (1 in {}) {DIM}·{RESET} errors {}",
            commas(sh.tasks_done.load(Relaxed) as u64),
            commas(sh.tasks.len() as u64),
            sh.tasks_checked.load(Relaxed),
            if cfg.check_every == 0 { "∞".to_string() } else { cfg.check_every.to_string() },
            {
                let e = sh.errors.lock().unwrap().len();
                if e > 0 { format!("{RED}{BOLD}{e}{RESET}") } else { format!("{GREEN}0{RESET}") }
            }
        ));
        out.push(format!("{CYAN}─ workers {}{RESET}", "─".repeat(w.saturating_sub(11))));
        let colw = 68usize;
        let cols = (w / colw).max(1);
        let mut row = String::new();
        for (i, ws) in sh.workers.iter().enumerate() {
            let busy = ws.busy.load(Relaxed);
            let chk = ws.checking.load(Relaxed);
            let p = ws.pairs.load(Relaxed);
            let h = ws.hits.load(Relaxed);
            let sv = ws.solves.load(Relaxed);
            let state = if chk {
                format!("{YELLOW}✔ certifying{RESET}")
            } else if busy {
                let pos = ws.pos.load(Relaxed);
                let hi = ws.hi.load(Relaxed);
                format!(
                    "d{} f#{:<5} #{:>8}/{:<8}",
                    ws.stage_d.load(Relaxed),
                    ws.fixed.load(Relaxed),
                    commas(pos),
                    commas(hi)
                )
            } else {
                format!("{DIM}idle{RESET}")
            };
            let cell = format!(
                "{DIM}w{:02}{RESET} {} {DIM}pairs{RESET} {:>7} {DIM}mem{RESET} {:>3.0}%",
                i,
                pad(&state, 32),
                si(p as f64),
                100.0 * h as f64 / (h + sv).max(1) as f64
            );
            row.push_str(&pad(&cell, colw));
            if (i + 1) % cols == 0 {
                out.push(std::mem::take(&mut row));
            }
        }
        if !row.is_empty() {
            out.push(row);
        }
        out.push(format!("{CYAN}─ events {}{RESET}", "─".repeat(w.saturating_sub(10))));
        {
            let ev = sh.events.lock().unwrap();
            let n = ev.len();
            for e in ev.iter().skip(n.saturating_sub(6)) {
                let color = if e.starts_with("ERROR") {
                    RED
                } else if e.starts_with("SAT") {
                    MAGENTA
                } else if e.starts_with("ROOT") {
                    GREEN
                } else {
                    DIM
                };
                let mut line = e.clone();
                if line.chars().count() > w - 4 {
                    line = line.chars().take(w - 5).collect::<String>() + "…";
                }
                out.push(format!("  {color}{line}{RESET}"));
            }
            for _ in n.min(6)..6 {
                out.push(String::new());
            }
        }
        if !final_frame {
            out.push(format!("{DIM}  Ctrl-C stops cleanly (finished tasks are logged; rerun with --resume){RESET}"));
        }
        let mut buf = String::from("\x1b[H");
        for l in &out {
            buf.push_str(l);
            buf.push_str("\x1b[K\n");
        }
        buf.push_str("\x1b[J");
        self.lines_drawn = out.len();
        print!("{buf}");
        let _ = std::io::stdout().flush();
    }

    pub fn interval(&self) -> Duration {
        if self.tty {
            Duration::from_millis(250)
        } else {
            Duration::from_secs(10)
        }
    }
}
