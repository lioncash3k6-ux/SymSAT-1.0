//! monster — exact Ramsey gluing solver.
//!
//!   monster glue   --s 4 --t 5 --n 25 [--route parity|all] [--d 8,10,12] [--mode stream|pair] [--workers N]
//!                  [--chunk K] [--check-every K] [--minimize C] [--sample K] [--seed S] [--out DIR] [--resume]
//!                  [--stop-on-sat] [--catalogs DIR]
//!   monster ladder [--workers N]          regression ladder: both sides of R(3,3) .. R(3,7), R(4,4), R(4,5) d=8
//!   monster cnf    s t A.g6 B.g6 p out    write one pair CNF exactly like the repo's encode.py (for byte-diffing)
//!   monster info                          machine report

mod ab;
mod assemble;
mod canon;
mod catalog;
mod cone;
mod count;
mod cover;
mod dash;
mod encode;
mod flag;
mod full;
mod pattern;
mod glue;
mod interval;
mod graph;
mod leanstage;
mod leanunit;
mod srgen;
mod lift;
mod mrcover;
mod sat;
mod sha256;
mod sys;

use dash::*;
use glue::{Config, Mode, Route};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::sync::Arc;
use std::time::Instant;

static SIGINT: AtomicBool = AtomicBool::new(false);

extern "C" fn on_sigint(_: i32) {
    SIGINT.store(true, Relaxed);
}

fn install_sigint() {
    extern "C" {
        fn signal(sig: i32, handler: extern "C" fn(i32)) -> usize;
    }
    unsafe {
        signal(2, on_sigint);
    }
}

struct Args {
    kv: HashMap<String, String>,
    flags: Vec<String>,
    pos: Vec<String>,
}

fn parse(args: &[String]) -> Args {
    let bool_flags = ["resume", "stop-on-sat", "quiet", "help", "degree-axioms", "vivify", "stable", "patterns", "proof", "lemmas", "books", "no-adaptive", "one-sided", "no-flip", "cube-lemmas", "flip", "sub-flip", "no-books", "verify", "record", "parity", "book-axioms", "reuse-sol", "no-check", "bounds", "keep", "fake", "biclique"];
    let mut kv = HashMap::new();
    let mut flags = Vec::new();
    let mut pos = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if let Some(k) = a.strip_prefix("--") {
            if let Some((k, v)) = k.split_once('=') {
                kv.insert(k.to_string(), v.to_string());
            } else if bool_flags.contains(&k) || i + 1 >= args.len() {
                flags.push(k.to_string());
            } else {
                kv.insert(k.to_string(), args[i + 1].clone());
                i += 1;
            }
        } else {
            pos.push(a.clone());
        }
        i += 1;
    }
    Args { kv, flags, pos }
}

impl Args {
    fn get<T: std::str::FromStr>(&self, k: &str, def: T) -> T {
        match self.kv.get(k) {
            Some(v) => v.parse().unwrap_or_else(|_| die(&format!("bad value for --{k}: {v}"))),
            None => def,
        }
    }
    fn has(&self, k: &str) -> bool {
        self.flags.iter().any(|f| f == k)
    }
}

fn die(msg: &str) -> ! {
    eprintln!("{RED}{BOLD}error:{RESET} {msg}");
    std::process::exit(2)
}

fn config_from(a: &Args) -> Config {
    let m = sys::machine();
    let s = a.get("s", 4usize);
    let t = a.get("t", 5usize);
    let n = a.get("n", 25usize);
    let route = match a.kv.get("route").map(|s| s.as_str()) {
        Some("parity") => Route::Parity,
        Some("all") => Route::All,
        None => {
            if n % 2 == 1 {
                Route::Parity
            } else {
                Route::All
            }
        }
        Some(x) => die(&format!("unknown route {x}")),
    };
    let degrees = a.kv.get("d").map(|v| {
        v.split(',')
            .map(|x| x.trim().parse().unwrap_or_else(|_| die(&format!("bad degree list {v}"))))
            .collect()
    });
    let mode = match a.kv.get("mode").map(|s| s.as_str()) {
        Some("pair") => Mode::Pair,
        Some("stream") | None => Mode::Stream,
        Some("unit") => Mode::Unit,
        Some("hybrid") => Mode::Hybrid,
        Some("cone") => Mode::Cone,
        Some(x) => die(&format!("unknown mode {x}")),
    };
    Config {
        s,
        t,
        n,
        route,
        degrees,
        workers: a.get("workers", m.threads),
        chunk: a.get("chunk", 2048usize),
        mode,
        minimize: a.get("minimize", 0u64),
        check_every: a.get("check-every", 64usize),
        sample: a.kv.get("sample").map(|v| v.parse().unwrap_or_else(|_| die("bad --sample"))),
        shard: a.kv.get("shard").map(|v| {
            let (i, n) = v.split_once('/').unwrap_or_else(|| die("bad --shard: use I/N"));
            let (i, n): (usize, usize) = (i.parse().unwrap_or_else(|_| die("bad --shard")), n.parse().unwrap_or_else(|_| die("bad --shard")));
            if n == 0 || i >= n {
                die("bad --shard: need 0 <= I < N");
            }
            (i, n)
        }),
        seed: a.get("seed", 20261025u64),
        catalogs: a.kv.get("catalogs").map(PathBuf::from).unwrap_or_else(catalog::default_dir),
        out: a.kv.get("out").map(PathBuf::from),
        resume: a.has("resume"),
        cache_cap: a.get("cache", 50_000usize),
        stop_on_sat: a.has("stop-on-sat"),
        quiet: a.has("quiet"),
        max_pairs_per_task: a.kv.get("task-pairs").map(|v| v.parse().unwrap_or_else(|_| die("bad --task-pairs"))),
        covers: a.kv.get("covers").map(PathBuf::from),
        gray_a: a.get("gray-a", 6usize),
        gray_b: a.get("gray-b", 6usize),
        // unit mode: cube-and-conquer inside one solver by default (A/B 2026-10-27: secs 0.27, CI 0.20-0.43 vs whole unit)
        unit_budget: a.get("unit-budget", if mode == Mode::Unit { 5_000u64 } else { 20_000u64 }),
        degree_axioms: a.has("degree-axioms"),
        biclique: a.has("biclique"),
        book_axioms: a.has("book-axioms"),
        vivify: a.has("vivify"),
        cube_budget: a.get("cube-budget", if mode == Mode::Unit { 5_000u64 } else { 0u64 }),
        stable: a.has("stable"),
        pat_lbd: a.get("max-lbd", 12u32),
        books: !a.has("no-books"), // rooted lemmas beyond stars: on by default (`--books` is accepted and redundant)
        one_sided: a.has("one-sided"),
        sched_static: match a.kv.get("sched").map(|s| s.as_str()) {
            None | Some("dynamic") => false,
            Some("static") => true,
            Some(x) => die(&format!("--sched {x}: use static or dynamic")),
        },
        units: a.kv.get("units").map(|f| {
            std::fs::read_to_string(f)
                .unwrap_or_else(|e| die(&format!("{f}: {e}")))
                .lines()
                .filter_map(|l| {
                    let v: Vec<usize> = l.split_whitespace().filter_map(|x| x.parse().ok()).collect();
                    (v.len() == 2).then(|| (v[0], v[1]))
                })
                .collect()
        }),
    }
}

/// Outcome of one glue run, for the ladder and the summary.
struct Outcome {
    pairs_target: u64,
    pairs_done: u64,
    unsat: u64,
    sat: u64,
    checked: u64,
    complete: bool,
    /// the stages run cover every admissible degree of the route (needed for a claim about R(s,t))
    full_route: bool,
    errors: Vec<String>,
    secs: f64,
    first_sat: Option<String>,
}

fn run_glue(cfg: Config, show: bool) -> Result<Outcome, String> {
    let machine = sys::machine();
    let t0 = Instant::now();
    let (sh, notes) = glue::build(cfg.clone())?;
    if let Some(dir) = &cfg.out {
        write_meta(dir, &sh, &machine, &notes);
    }
    let mut dash = Dash::new(machine);
    if show {
        dash.start();
        for n in &notes {
            sh.event(format!("note: {n}"));
        }
        sh.event(format!(
            "planned {} stage(s), {} tasks, {} pairs{}",
            sh.stages.len(),
            commas(sh.tasks.len() as u64),
            commas(sh.stage_target.iter().sum()),
            if cfg.sample.is_some() { " (SAMPLE: cost estimate only, not a proof)" } else { "" }
        ));
    }
    let handles = glue::spawn_workers(&sh);
    let ui_every = dash.interval();
    let mut last_ui = Instant::now() - ui_every;
    loop {
        if SIGINT.load(Relaxed) && !sh.stop.load(Relaxed) {
            sh.stop.store(true, Relaxed);
            sh.event("interrupt: finishing current pairs, unfinished tasks will rerun on --resume".into());
        }
        if handles.iter().all(|h| h.is_finished()) {
            break;
        }
        if show && last_ui.elapsed() >= ui_every {
            dash.tick(&sh, false);
            last_ui = Instant::now();
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
    for h in handles {
        let _ = h.join();
    }
    if show {
        dash.tick(&sh, true);
        dash.finish();
    }
    let target: u64 = sh.stage_target.iter().sum::<u64>() + sh.skipped_pairs.iter().sum::<u64>();
    let done: u64 = sh.stage_done.iter().map(|x| x.load(Relaxed)).sum();
    let unsat: u64 = sh.stage_unsat.iter().map(|x| x.load(Relaxed)).sum();
    let sat: u64 = sh.stage_sat.iter().map(|x| x.load(Relaxed)).sum();
    let checked: u64 = sh.stage_checked.iter().map(|x| x.load(Relaxed)).sum();
    let errors = sh.errors.lock().unwrap().clone();
    let sats = sh.sats.lock().unwrap();
    let out = Outcome {
        pairs_target: target,
        pairs_done: done,
        unsat,
        sat,
        checked,
        complete: done == target && cfg.sample.is_none() && cfg.shard.is_none(),
        full_route: match &cfg.degrees {
            None => true,
            Some(ds) => glue::admissible_degrees(&cfg).iter().all(|d| ds.contains(d)),
        },
        errors,
        secs: t0.elapsed().as_secs_f64(),
        first_sat: sats.first().map(|r| r.g6.clone()),
    };
    if let Some(dir) = &cfg.out {
        let mut s = String::new();
        for r in sats.iter() {
            s.push_str(&format!("{} d={} fixed={} streamed={}\n", r.g6, r.d, r.fixed_idx, r.streamed_idx));
        }
        if !s.is_empty() {
            let _ = std::fs::write(dir.join("sat_witnesses.g6"), s);
        }
    }
    drop(sats);
    if show {
        summary(&cfg, &sh, &out);
    }
    if let Some(dir) = &cfg.out {
        let _ = std::fs::write(
            dir.join("summary.json"),
            format!(
                "{{\"s\":{},\"t\":{},\"n\":{},\"pairs_target\":{},\"pairs_done\":{},\"unsat\":{},\"sat\":{},\"certified_pairs\":{},\"complete\":{},\"errors\":{},\"secs\":{:.1},\"plan_tasks\":{},\"plan_pairs\":{}}}\n",
                cfg.s, cfg.t, cfg.n, out.pairs_target, out.pairs_done, out.unsat, out.sat, out.checked, out.complete,
                out.errors.len(), out.secs, sh.plan_tasks, sh.plan_pairs
            ),
        );
    }
    Ok(out)
}

fn write_meta(dir: &std::path::Path, sh: &glue::Shared, m: &sys::Machine, notes: &[String]) {
    let mut s = String::new();
    s.push_str("{\n");
    s.push_str(&format!("  \"cmdline\": {:?},\n", std::env::args().collect::<Vec<_>>().join(" ")));
    s.push_str(&format!("  \"machine\": {:?},\n", format!("{} x{} {:?} {} kB", m.model, m.threads, m.flags, m.mem_total_kb)));
    s.push_str(&format!("  \"config\": {:?},\n", format!("{:?}", sh.cfg)));
    s.push_str("  \"catalogues\": [\n");
    let mut first = true;
    for st in &sh.stages {
        for lv in [&st.a, &st.b] {
            let bytes = std::fs::read(&lv.path).unwrap_or_default();
            if !first {
                s.push_str(",\n");
            }
            first = false;
            s.push_str(&format!(
                "    {{\"file\": {:?}, \"graphs\": {}, \"mckay\": {:?}, \"sha256\": \"{}\"}}",
                lv.path.display().to_string(),
                lv.graphs.len(),
                lv.mckay,
                sha256::sha256(&bytes)
            ));
        }
    }
    s.push_str("\n  ],\n");
    s.push_str(&format!("  \"notes\": {:?}\n}}\n", notes));
    let _ = std::fs::write(dir.join("meta.json"), s);
}

fn summary(cfg: &Config, sh: &glue::Shared, o: &Outcome) {
    println!();
    println!("{BOLD}{CYAN}═══ result ═══{RESET}");
    for (i, st) in sh.stages.iter().enumerate() {
        println!(
            "  d={:<3} pairs {:>14}  done {:>14}  UNSAT {:>14}  SAT {:>6}  certified {:>12}",
            st.d,
            commas(sh.stage_target[i] + sh.skipped_pairs[i]),
            commas(sh.stage_done[i].load(Relaxed)),
            commas(sh.stage_unsat[i].load(Relaxed)),
            commas(sh.stage_sat[i].load(Relaxed)),
            commas(sh.stage_checked[i].load(Relaxed))
        );
    }
    println!("  wall {}  ·  {:.0} pairs/s", dur(o.secs), o.pairs_done as f64 / o.secs.max(1e-9));
    if !o.errors.is_empty() {
        println!("{RED}{BOLD}  {} ERROR(S) — no claim is made:{RESET}", o.errors.len());
        for e in o.errors.iter().take(5) {
            println!("    {e}");
        }
        return;
    }
    if o.sat > 0 {
        println!(
            "{MAGENTA}{BOLD}  SAT: found {} verified ({},{})-good colouring(s) of K{}  ⇒  R({},{}) > {}{RESET}",
            o.sat, cfg.s, cfg.t, cfg.n, cfg.s, cfg.t, cfg.n
        );
        if let Some(g) = &o.first_sat {
            println!("  first witness (graph6, red = edge): {g}");
        }
        println!("  {DIM}(each witness was rebuilt as a full colouring and brute-force checked for red K{} / blue K{}){RESET}", cfg.s, cfg.t);
    } else if o.complete && !o.full_route {
        let ds: Vec<String> = sh.stages.iter().map(|s| s.d.to_string()).collect();
        let missing: Vec<String> = glue::admissible_degrees(cfg)
            .into_iter()
            .filter(|d| !sh.stages.iter().any(|s| s.d == *d))
            .map(|d| d.to_string())
            .collect();
        println!(
            "{GREEN}{BOLD}  stage result: every pair with red degree d ∈ {{{}}} is refuted{RESET}",
            ds.join(",")
        );
        println!(
            "  {DIM}NOT a claim about R({},{}): the route also needs d ∈ {{{}}}{RESET}",
            cfg.s,
            cfg.t,
            missing.join(",")
        );
        println!(
            "  {DIM}pairs certified by the independent checker: {} of {}{RESET}",
            commas(o.checked),
            commas(o.unsat)
        );
    } else if o.complete {
        println!(
            "{GREEN}{BOLD}  UNSAT: every pair of every stage is refuted  ⇒  R({},{}) ≤ {}{RESET}",
            cfg.s, cfg.t, cfg.n
        );
        println!("  {DIM}conditional on: the degree argument ({}), catalogue completeness (counts = McKay's table),", match cfg.route {
            Route::Parity => "some vertex has even red degree, N odd",
            Route::All => "the red degree of one fixed vertex",
        });
        println!(
            "  the pair encoder, and the solver for the {} pairs not independently certified (certified: {}){RESET}",
            commas(o.unsat - o.checked.min(o.unsat)),
            commas(o.checked)
        );
    } else {
        println!(
            "{YELLOW}  partial: {} of {} pairs refuted, no SAT pair so far — no claim{}{RESET}",
            commas(o.pairs_done),
            commas(o.pairs_target),
            if cfg.sample.is_some() { " (sample run)" } else { "" }
        );
    }
}

fn cmd_info() {
    let m = sys::machine();
    println!("{BOLD}machine{RESET}");
    println!("  cpu      {} ({} threads{})", m.model, m.threads, if m.hypervisor { ", virtualised" } else { "" });
    println!("  features {}", m.flags.join(" "));
    println!("  memory   {:.1} GiB", m.mem_total_kb as f64 / 1048576.0);
    println!("  catalogs {}", catalog::default_dir().display());
    println!("  build    target-cpu=native, popcnt {}", if cfg!(target_feature = "popcnt") { "on" } else { "off" });
}

fn cmd_cnf(a: &Args) {
    if a.pos.len() < 7 {
        die("usage: monster cnf s t A.g6 B.g6 p out.cnf");
    }
    let s: usize = a.pos[1].parse().unwrap_or_else(|_| die("bad s"));
    let t: usize = a.pos[2].parse().unwrap_or_else(|_| die("bad t"));
    let la: Vec<String> = std::fs::read_to_string(&a.pos[3])
        .unwrap_or_else(|e| die(&e.to_string()))
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.trim().to_string())
        .collect();
    let lb: Vec<String> = std::fs::read_to_string(&a.pos[4])
        .unwrap_or_else(|e| die(&e.to_string()))
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.trim().to_string())
        .collect();
    let p: usize = a.pos[5].parse().unwrap_or_else(|_| die("bad p"));
    let (ia, ib) = (p % la.len(), p / la.len());
    if ib >= lb.len() {
        die("pair out of range");
    }
    let ga = graph::Graph::from_g6(&la[ia]).unwrap_or_else(|e| die(&e));
    let gb = graph::Graph::from_g6(&lb[ib]).unwrap_or_else(|e| die(&e));
    let cl = encode::pair_clauses(s, t, &ga, &gb);
    let txt = encode::to_dimacs(ga.n * gb.n, &cl);
    std::fs::write(&a.pos[6], &txt).unwrap_or_else(|e| die(&e.to_string()));
    println!(
        "{{\"ia\": {ia}, \"ib\": {ib}, \"d\": {}, \"m\": {}, \"nclauses\": {}, \"sha256\": \"{}\"}}",
        ga.n,
        gb.n,
        cl.len(),
        sha256::sha256(txt.as_bytes())
    );
}

/// monster gamma --covers DIR --d 10 --ga 10 --gb 3190 [--gray-a 6 --gray-b 6] out.cnf
fn cmd_gamma(a: &Args) {
    let mut cfg = config_from(a);
    cfg.mode = Mode::Unit;
    let d: usize = a.get("d", 10usize);
    cfg.degrees = Some(vec![d]);
    cfg.route = Route::All;
    let (stages, _) = glue::plan(&cfg).unwrap_or_else(|e| die(&e));
    let st = &stages[0];
    let (ga, gb) = (a.get("ga", 0usize), a.get("gb", 0usize));
    let gm = cover::build_gamma(cfg.s, cfg.t, &st.cov_a.as_ref().unwrap().gens[ga], &st.cov_b.as_ref().unwrap().gens[gb]);
    let txt = encode::to_dimacs(gm.nvars, &gm.clauses);
    let out = a.pos.get(1).cloned().unwrap_or_else(|| die("output file?"));
    std::fs::write(&out, &txt).unwrap_or_else(|e| die(&e.to_string()));
    let np = st.cov_a.as_ref().unwrap().members[ga].len() * st.cov_b.as_ref().unwrap().members[gb].len();
    println!("GAMMA d={d} unit ({ga},{gb}): {} vars, {} clauses, {np} pairs, sha256 {}", gm.nvars, gm.clauses.len(), sha256::sha256(txt.as_bytes()));
}

/// monster cover --s 4 --t 4 --n 14 --gray 6 out.txt   (catalogue r<s><t>/n<n>)
fn cmd_cover(a: &Args) {
    let (s, t, n) = (a.get("s", 4usize), a.get("t", 4usize), a.get("n", 14usize));
    let gray = a.get("gray", 6usize);
    let threads = a.get("workers", sys::machine().threads);
    let dir = a.kv.get("catalogs").map(PathBuf::from).unwrap_or_else(catalog::default_dir);
    let lv = catalog::load(&dir, s, t, n).unwrap_or_else(|e| die(&e));
    let out = a.pos.get(1).cloned().unwrap_or_else(|| die("output file?"));
    let t0 = Instant::now();
    let text = if a.kv.get("method").map(|m| m.as_str()) == Some("greedy") {
        cover::build_cover(&lv.graphs, gray, threads)
    } else {
        cover::build_cover_setcover(&lv.graphs, gray, threads, a.get("stride", 1usize))
    };
    std::fs::write(&out, &text).unwrap_or_else(|e| die(&e.to_string()));
    let c = cover::Cover::load(std::path::Path::new(&out), &lv.graphs).unwrap_or_else(|e| die(&format!("built cover fails its own check: {e}")));
    let sizes: Vec<usize> = c.members.iter().map(|m| m.len()).collect();
    println!(
        "cover r{s}{t}/n{n} gray<={gray}: {} graphs -> {} generalisations (avg {:.1} members, max {}), {} in {}",
        lv.graphs.len(),
        c.gens.len(),
        lv.graphs.len() as f64 / c.gens.len().max(1) as f64,
        sizes.iter().max().unwrap_or(&0),
        out,
        dur(t0.elapsed().as_secs_f64())
    );
}

/// What [`build_solver`] sets up besides the formula and the pattern store.
struct SolverSetup {
    use_lrat: bool,
    proof: bool,
    phase: Option<bool>,
}

/// A solver for F(s,t,n) with its vertices renamed by `perm` (and colours swapped when `flip`, s = t only), with the
/// proof mode and initial phase of `setup` and the pattern store of the command line. Also returns the map from its
/// ids of the original clauses to their canonical positions 1..m in `full_clauses` order, for the SLRAT writer.
fn build_solver(a: &Args, setup: &SolverSetup, s: usize, t: usize, n: usize, perm: &[usize], flip: bool, seed: u64) -> (sat::solver::Solver, HashMap<u64, u64>) {
    let cls = full::full_clauses(s, t, n);
    let identity = !flip && perm.iter().enumerate().all(|(i, &p)| i == p);
    let canon: HashMap<Vec<i32>, u64> = if setup.use_lrat && !identity {
        cls.iter()
            .enumerate()
            .map(|(i, c)| {
                let mut k = c.clone();
                k.sort_unstable();
                (k, i as u64 + 1)
            })
            .collect()
    } else {
        HashMap::new()
    };
    let edges = full::edge_table(n);
    let mut sv = sat::solver::Solver::new(n * n.saturating_sub(1) / 2);
    if setup.use_lrat {
        sv.lrat_enable();
    } else if setup.proof {
        sv.enable_proof();
    }
    let mut ids = HashMap::new();
    for (i, c) in cls.iter().enumerate() {
        let mut pc = if identity { c.clone() } else { full::permute_clause(c, perm, &edges) };
        if flip {
            for l in pc.iter_mut() {
                *l = -*l;
            }
        }
        let id = sv.next_clause_id();
        sv.add_clause_dimacs(&pc);
        if setup.use_lrat {
            let pos = if identity {
                i as u64 + 1
            } else {
                let mut k = pc;
                k.sort_unstable();
                canon[&k]
            };
            ids.insert(id, pos);
        }
    }
    sv.set_initial_phase(setup.phase, seed);
    if a.has("patterns") {
        let mut pp = pattern::PatternProp::new(n);
        pp.max_k = a.get("max-k", 12usize);
        pp.max_lbd = a.get("max-lbd", 12u32);
        pp.max_pats = a.get("max-pats", 4000usize);
        pp.max_edges = a.get("max-edges", 24usize);
        pp.node_budget = a.get("node-budget", 20000u64);
        pp.slack_mode = a.get("slack", 2u8);
        pp.adaptive = !a.has("no-adaptive");
        pp.flip_ok = s == t && !a.has("no-flip");
        sv.patterns = Some(Box::new(pp));
    }
    sv.vivify_enabled = a.has("vivify");
    (sv, ids)
}

/// A star lemma lifted from its own sub-instance (`--lib lift`).
struct StarLift {
    /// the sub-instance F(s,t,m) and its refutation (LRAT), with its original ids mapped to canonical positions
    s: usize,
    t: usize,
    m: usize,
    log: Vec<sat::solver::LratLine>,
    ids: HashMap<u64, u64>,
    /// sub-solver id of the empty clause
    empty: u64,
    /// apex, its colour and the leaves (the lift's embedding)
    v: usize,
    red: bool,
    emb: Vec<usize>,
    /// the lifted clause: some edge from the apex to a leaf is not of the apex colour
    clause: Vec<i32>,
    conflicts: u64,
}

/// Where an imported library clause is proved: in the library solver (its id there) or by a lifted star.
enum Origin {
    Lib(u64),
    Star(usize),
}

/// `--lib lift`: each star lemma comes from its own sub-instance. A red star with k = R(s-1,t) leaves forces an
/// (s-1,t)-good colouring on the leaves, which F(s-1,t,k) refutes; that refutation lifted with the star's centre as
/// apex (the Lean-verified lift rule) is exactly the star lemma. The sub-instance is far smaller than F(s,t,n), so
/// this replaces the library's most expensive and most order-sensitive proofs. When s = t only one star is lifted
/// (its colour-swapped twin arrives as a flip image), as in the in-formula library.
#[allow(clippy::too_many_arguments)]
fn lift_stars(a: &Args, setup: &SolverSetup, s: usize, t: usize, n: usize, perm: &[usize], flip: bool, seed: u64, books: bool, relabel: u64) -> Vec<StarLift> {
    let swap = s == t && a.has("patterns") && !a.has("no-flip") && std::env::var_os("MONSTER_NO_ORBIT").is_none();
    let red_rep = std::env::var("MONSTER_ORBIT_REP").is_ok_and(|v| v == "red");
    let mut out = Vec::new();
    for (sa, sb) in [(1usize, 0usize), (0, 1)] {
        if swap && (if red_rep { sa < sb } else { sa > sb }) {
            continue;
        }
        let red = (sa == 1) != flip; // the apex colour after the relabelling's colour swap
        let (s2, t2) = if red { (s - 1, t) } else { (s, t - 1) };
        let Some(k) = full::known_ramsey(s2, t2) else { continue };
        if k < 2 || k + 1 > n {
            continue;
        }
        let pk = full::relabel_perm(k, relabel);
        let sub_setup = SolverSetup { use_lrat: setup.use_lrat, proof: false, phase: setup.phase };
        let (mut ss, ids) = build_solver(a, &sub_setup, s2, t2, k, &pk, false, seed);
        let t1 = Instant::now();
        let sub_lemmas = full::add_lemma_library(&mut ss, s2, t2, k, &full::LibOpts { books, perm: &pk, flip: false, skip_stars: false });
        let r = ss.solve(&[]);
        if r != sat::solver::SolveResult::Unsat {
            die(&format!("sub-instance R({s2},{t2})/K{k} was not refuted ({r:?})"));
        }
        let log = ss.lrat.take().unwrap_or_default();
        let empty = log
            .iter()
            .rev()
            .find_map(|l| match l {
                sat::solver::LratLine::Lemma { id, lits, .. } if lits.is_empty() => Some(*id),
                _ => None,
            })
            .unwrap_or(0);
        let v = perm[0];
        let emb: Vec<usize> = (1..=k).map(|x| perm[x]).collect();
        let clause: Vec<i32> = emb.iter().map(|&x| if red { -full::evar(v, x) } else { full::evar(v, x) }).collect();
        println!(
            "  lemma: {} star with {k} leaves, lifted from R({s2},{t2})/K{k}: {} conflicts, {} ({} sub-lemmas)",
            if red { "red" } else { "blue" },
            commas(ss.stats.conflicts),
            dur(t1.elapsed().as_secs_f64()),
            sub_lemmas.len()
        );
        out.push(StarLift { s: s2, t: t2, m: k, log, ids, empty, v, red, emb, clause, conflicts: ss.stats.conflicts });
    }
    out
}

/// monster full --s 4 --t 4 --n 18 [--patterns] [--lemmas [--no-books] [--lib inline|separate|lift]] [--relabel SEED]
///              [--phase blue|red|random] [--proof | --slrat FILE | --lrat FILE] [--max-k 12] [--max-lbd 12] [--budget N]
fn cmd_full(a: &Args) {
    let (s, t, n) = (a.get("s", 4usize), a.get("t", 4usize), a.get("n", 18usize));
    // general rooted lemmas (books, mixed books, ...) are the default; `--no-books` keeps stars only
    let books = !a.has("no-books");
    let cls = full::full_clauses(s, t, n);
    let nv = n * (n - 1) / 2;
    let lrat_path = a.kv.get("lrat").cloned();
    // default lift: no heavy tail over relabellings (RESULTS.md 2026-10-26, library modes); inline for --lrat
    let lib_mode = a.kv.get("lib").cloned().unwrap_or_else(|| if lrat_path.is_some() { "inline" } else { "lift" }.into());
    // inline: lemmas proved in the main solver; separate: in their own solver, imported in canonical order;
    // lift: like separate, with the stars lifted from sub-instances; lift-inline: stars lifted, other lemmas inline
    let (separate, lift) = match lib_mode.as_str() {
        "inline" => (false, false),
        "separate" => (true, false),
        "lift" => (true, true),
        "lift-inline" => (false, true),
        x => die(&format!("--lib {x}: use inline, separate, lift or lift-inline")),
    };
    // --proof on the lift path: the proof spans several solvers and lift lines, which only SLRAT carries, so it is
    // written to a temporary SLRAT file and checked by the reference checker instead of the in-memory one
    let proof_flag = a.kv.contains_key("proof") || a.has("proof");
    let tmp_slrat = (proof_flag && lift && lrat_path.is_none() && !a.kv.contains_key("slrat"))
        .then(|| std::env::temp_dir().join(format!("monster-proof-{}.slrat", std::process::id())).display().to_string());
    let proof = proof_flag && tmp_slrat.is_none();
    let slrat_path = a.kv.get("slrat").cloned().or_else(|| tmp_slrat.clone());
    let use_lrat = lrat_path.is_some() || slrat_path.is_some();
    // --relabel SEED: the same formula with its vertices renamed (other clause order and lemma roots; 0 = identity);
    // when s = t, odd seeds also swap the colours, so both colourings of the search get sampled
    let relabel = a.get("relabel", 0u64);
    let perm = full::relabel_perm(n, relabel);
    let flip = s == t && relabel % 2 == 1;
    let seed = a.get("seed", relabel);
    let phase_name = a.kv.get("phase").cloned().unwrap_or_else(|| "blue".into());
    let phase = match phase_name.as_str() {
        "blue" => Some(true),
        "red" => Some(false),
        "random" => None,
        x => die(&format!("--phase {x}: use blue, red or random")),
    };
    if lrat_path.is_some() && (relabel != 0 || separate) {
        die("--lrat (expanded LRAT for cake_lpr) needs --relabel 0 and --lib inline; use --slrat instead");
    }
    if a.kv.contains_key("library") && use_lrat {
        die("--library FILE carries a symmetric proof only; for SLRAT use --lemmas --lib separate");
    }
    let mut slrat_verdict: Option<&str> = None;
    let setup = SolverSetup { use_lrat, proof, phase };
    let (mut sv, mut ids) = build_solver(a, &setup, s, t, n, &perm, flip, seed);
    sv.conflict_budget = a.get("budget", u64::MAX);
    // library-only (MONSTER_LIBONLY=1) applies to this main solver only, never to the solvers that prove the library
    if std::env::var_os("MONSTER_LIBONLY").is_some() {
        if let Some(pp) = sv.patterns.as_mut() {
            pp.lib_only = true;
        }
    }
    let t0 = Instant::now();
    let (mut lib_conflicts, mut lib_secs) = (0u64, 0.0f64);
    let mut inline_lib = 0u64; // library conflicts spent inside the main solver
    let mut lib_log: Option<(Vec<sat::solver::LratLine>, HashMap<u64, u64>)> = None;
    let mut stars: Vec<StarLift> = Vec::new();
    let mut lib_star_ids: Vec<(u64, usize)> = Vec::new(); // (id in the library solver, star index)
    let mut imported: Vec<(u64, Origin)> = Vec::new(); // (id in the main solver, where that clause is proved)
    if let Some(path) = a.kv.get("library") {
        let t1 = Instant::now();
        let lib = full::Library::get(s, t, n, books, Some(std::path::Path::new(path)), false).unwrap_or_else(|e| die(&e));
        lib.import(&mut sv);
        println!("  library: {} lemmas imported, proof re-verified ({})", lib.lemmas.len(), dur(t1.elapsed().as_secs_f64()));
    } else if a.has("lemmas") && separate {
        // prove the library in its own solver and import the lemmas into this fresh one in a canonical order: the main
        // search then depends on the lemma set only, not on the proof order or on the learned state the proofs leave.
        // With --lib lift the stars come from their own small sub-instances first (see lift_stars).
        if lift {
            stars = lift_stars(a, &setup, s, t, n, &perm, flip, seed, books, relabel);
            lib_conflicts += stars.iter().map(|x| x.conflicts).sum::<u64>();
        }
        let (mut ls, lib_ids) = build_solver(a, &setup, s, t, n, &perm, flip, seed);
        for (j, st) in stars.iter().enumerate() {
            let lid = ls.next_clause_id();
            ls.add_clause_dimacs(&st.clause);
            let lits: Vec<u32> = st.clause.iter().map(|&l| sat::solver::lit_from_dimacs(l)).collect();
            if let Some(pp) = ls.patterns.as_mut() {
                pp.learn_forced(&lits, lid);
            }
            lib_star_ids.push((lid, j));
        }
        let mut lemmas = Vec::new();
        let opts = full::LibOpts { books, perm: &perm, flip, skip_stars: lift };
        for line in full::add_lemma_library_collect(&mut ls, s, t, n, &opts, &mut lemmas) {
            println!("  {line}");
        }
        lib_conflicts += ls.stats.conflicts;
        lib_secs = t0.elapsed().as_secs_f64();
        let key = |c: &Vec<i32>| {
            let mut k = c.clone();
            k.sort_unstable();
            (c.len(), k)
        };
        let mut all: Vec<(Vec<i32>, Origin)> = stars.iter().enumerate().map(|(j, st)| (st.clause.clone(), Origin::Star(j))).collect();
        all.extend(lemmas.iter().map(|(c, lid)| (c.clone(), Origin::Lib(*lid))));
        all.sort_by(|x, y| key(&x.0).cmp(&key(&y.0)));
        if proof && !use_lrat {
            sv.proof = ls.proof.clone();
            sv.proof_lemmas = ls.proof_lemmas;
        }
        for (c, origin) in all {
            let mid = sv.next_clause_id();
            sv.add_clause_dimacs(&c);
            let lits: Vec<u32> = c.iter().map(|&l| sat::solver::lit_from_dimacs(l)).collect();
            let pid = match origin {
                _ if use_lrat => mid,
                Origin::Lib(lid) => lid,
                Origin::Star(_) => 0,
            };
            if let Some(pp) = sv.patterns.as_mut() {
                pp.learn_forced(&lits, pid);
            }
            imported.push((mid, origin));
        }
        if use_lrat {
            lib_log = Some((ls.lrat.take().unwrap_or_default(), lib_ids));
        }
        println!(
            "  library: {} lemmas ({} lifted stars) proved outside the main solver ({} conflicts, {}), imported in canonical order",
            lemmas.len() + stars.len(),
            stars.len(),
            commas(lib_conflicts),
            dur(lib_secs)
        );
    } else if a.has("lemmas") {
        if lift {
            stars = lift_stars(a, &setup, s, t, n, &perm, flip, seed, books, relabel);
            lib_conflicts += stars.iter().map(|x| x.conflicts).sum::<u64>();
            for (j, st) in stars.iter().enumerate() {
                let mid = sv.next_clause_id();
                sv.add_clause_dimacs(&st.clause);
                let lits: Vec<u32> = st.clause.iter().map(|&l| sat::solver::lit_from_dimacs(l)).collect();
                if let Some(pp) = sv.patterns.as_mut() {
                    pp.learn_forced(&lits, mid);
                }
                imported.push((mid, Origin::Star(j)));
            }
        }
        let opts = full::LibOpts { books, perm: &perm, flip, skip_stars: lift };
        let c0 = sv.stats.conflicts;
        for line in full::add_lemma_library(&mut sv, s, t, n, &opts) {
            println!("  {line}");
        }
        inline_lib = sv.stats.conflicts - c0;
        lib_conflicts += inline_lib;
        lib_secs = t0.elapsed().as_secs_f64();
    }
    if a.has("cube-lemmas") {
        let dir = a.kv.get("catalogs").map(PathBuf::from).unwrap_or_else(catalog::default_dir);
        for line in full::add_cube_lemmas(&mut sv, s, t, n, &dir) {
            println!("  {line}");
        }
    }
    // MONSTER_MINE=k,budget,tries,every: after every `every` main-search conflicts, mine up to `tries` small lemmas
    // (sub-clauses of recent learned clauses on their k densest vertices, refuted by bounded assumption solves of
    // `budget` conflicts; see full::mine_lemmas). Main-search conflicts count against --budget, mining ones do not.
    let r = match std::env::var("MONSTER_MINE").ok().map(|v| v.split(',').filter_map(|x| x.parse::<u64>().ok()).collect::<Vec<u64>>()) {
        Some(m) if m.len() == 4 => {
            let (k, budget, tries, every) = (m[0] as usize, m[1], m[2] as usize, m[3].max(1));
            let total = sv.conflict_budget;
            let mut seen = std::collections::HashSet::new();
            let (mut spent, mut tried, mut mined, mut mining) = (0u64, 0usize, 0usize, 0u64);
            loop {
                sv.conflict_budget = every.min(total.saturating_sub(spent));
                let c0 = sv.stats.conflicts;
                let r = sv.solve(&[]);
                spent += sv.stats.conflicts - c0;
                if r != sat::solver::SolveResult::Unknown || spent >= total {
                    println!("  mining: {tried} sub-clauses tried, {mined} lemmas mined, {} mining conflicts", commas(mining));
                    break r;
                }
                let (t, mm, c) = full::mine_lemmas(&mut sv, k, budget, tries, &mut seen);
                (tried, mined, mining) = (tried + t, mined + mm, mining + c);
            }
        }
        _ => sv.solve(&[]),
    };
    let secs = t0.elapsed().as_secs_f64();
    let main_conflicts = sv.stats.conflicts - inline_lib;
    let total_conflicts = lib_conflicts + main_conflicts;
    let st = &sv.stats;
    println!(
        "R({s},{t})/K{n}: {:?} in {} | conflicts {} (library {}, main {}) decisions {} props {}",
        r,
        dur(secs),
        commas(total_conflicts),
        commas(lib_conflicts),
        commas(main_conflicts),
        commas(st.decisions),
        commas(st.propagations)
    );
    if let Some(pp) = &sv.patterns {
        let p = &pp.stats;
        println!(
            "  patterns: learned {} stored {} dup {} rejected {} | images used {} (as conflicts {}) | search nodes {} budget cuts {}",
            commas(p.learned), commas(p.stored), commas(p.duplicates), commas(p.rejected), commas(p.images),
            commas(p.conflicts), commas(p.nodes), commas(p.budget_cut)
        );
        if std::env::var_os("MONSTER_DEPTH").is_some() {
            pattern::DEPTH_NODES.with(|d| {
                let d = d.borrow();
                let tot: u64 = d.iter().sum();
                for (i, &x) in d.iter().enumerate() {
                    if x > 0 {
                        println!("    depth {i:>2}: {:>12} nodes ({:.1}%)", x, 100.0 * x as f64 / tot.max(1) as f64);
                    }
                }
            });
        }
        if std::env::var_os("MONSTER_YIELD").is_some() {
            for (k, e, c, h, nd) in pp.yield_table().iter().take(25) {
                println!("    pattern k={k:<2} e={e:<2} calls {c:>9} hits {h:>7} nodes {nd:>11} yield {:.2e}", *h as f64 / (*c).max(1) as f64);
            }
        }
        let st = p.stored.max(1) as f64;
        println!(
            "  pattern shape: avg {:.1} vertices, {:.1} edges, {:.1} leaves (degree-1 vertices)",
            p.sum_k as f64 / st, p.sum_edges as f64 / st, p.sum_leaves as f64 / st
        );
        println!(
            "  pattern time: {:.1}s propagation, {:.1}s canonical forms, of {:.1}s total, {} embed calls ({:.0} nodes/call)",
            p.prop_ns as f64 / 1e9, p.canon_ns as f64 / 1e9, secs, commas(p.embed_calls), p.nodes as f64 / p.embed_calls.max(1) as f64
        );
        if std::env::var_os("MONSTER_ADMIT").is_some() {
            println!(
                "  admission: rejected {} = edges {} + lbd {} + store full {} + vertices {} + disconnected {}",
                commas(p.rejected), commas(p.rej_edges), commas(p.rej_lbd), commas(p.rej_full), commas(p.rej_k), commas(p.rej_disc)
            );
            let h: Vec<String> = p.vhist.iter().enumerate().filter(|(_, &c)| c > 0).map(|(k, c)| format!("{k}:{c}")).collect();
            println!("  learned clauses by vertex count: {}", h.join(" "));
            let [l, c] = pp.source_split();
            println!(
                "  pattern sources: library {} patterns, {} images, {} nodes | learned {} patterns, {} images, {} nodes (rejected as library-only: {})",
                l.0, commas(l.2), commas(l.3), c.0, commas(c.2), commas(c.3), commas(p.rej_lib)
            );
        }
        if sv.pv_shrunk > 0 || std::env::var_os("MONSTER_PATVIV").is_some() {
            println!("  vertex vivification: {} runs, {} pattern tries, {} patterns shrunk, {} vertices removed", sv.pv_runs, sv.pv_tried, sv.pv_shrunk, sv.pv_vertices);
        }
    }
    if r == sat::solver::SolveResult::Sat {
        let mut g = graph::BigGraph::new(n);
        for j in 1..n {
            for i in 0..j {
                g.set(i, j, sv.model_value(full::evar(i, j) as usize));
            }
        }
        let ok = g.find_mono(s, true).is_none() && g.find_mono(t, false).is_none();
        println!("  witness {} independently {}", g.to_g6(), if ok { "VERIFIED" } else { "FAILED" });
    }
    if let (Some(path), sat::solver::SolveResult::Unsat) = (&slrat_path, r) {
        let f = std::fs::File::create(path).unwrap_or_else(|e| die(&e.to_string()));
        let mut w = full::SlratWriter::new(s, t, n, std::io::BufWriter::new(f)).unwrap_or_else(|e| die(&e.to_string()));
        // lifted stars: each sub-instance's refutation, then one lift line into the main database
        let mut star_ids: Vec<u64> = Vec::new();
        for st in stars.iter_mut() {
            let k = w.open_sub(st.s, st.t, st.m).unwrap_or_else(|e| die(&e.to_string()));
            w.emit_sub(k, &st.log, &mut st.ids).unwrap_or_else(|e| die(&e));
            let src = *st.ids.get(&st.empty).unwrap_or_else(|| die("sub-instance refutation has no empty clause"));
            star_ids.push(w.lift(k, src, st.v, st.red, &st.emb).unwrap_or_else(|e| die(&e.to_string())));
        }
        // the library's own proof next (separate modes), then the main proof citing imported clauses by proof id
        let mut lib_map: HashMap<u64, u64> = HashMap::new();
        if let Some((log, mut lmap)) = lib_log.take() {
            for &(lid, j) in &lib_star_ids {
                lmap.insert(lid, star_ids[j]);
            }
            w.emit(&log, &mut lmap).unwrap_or_else(|e| die(&e));
            lib_map = lmap;
        }
        for (mid, origin) in &imported {
            let pid = match origin {
                Origin::Lib(lid) => *lib_map.get(lid).unwrap_or_else(|| die("an imported lemma is missing from the library proof")),
                Origin::Star(j) => star_ids[*j],
            };
            ids.insert(*mid, pid);
        }
        w.emit(sv.lrat.as_ref().unwrap(), &mut ids).unwrap_or_else(|e| die(&e));
        let k = w.finish().unwrap_or_else(|e| die(&e.to_string()));
        let t1 = Instant::now();
        let text = std::fs::read_to_string(path).unwrap();
        let shown = if tmp_slrat.is_some() { "a temporary file" } else { path.as_str() };
        match full::check_slrat(&text) {
            Ok(true) => {
                slrat_verdict = Some("verified");
                println!("  SLRAT: {} lines -> {shown}; reference checker: s VERIFIED UNSAT ({})", commas(k), dur(t1.elapsed().as_secs_f64()))
            }
            Ok(false) => {
                slrat_verdict = Some("no-empty-clause");
                println!("  SLRAT: {} lines; reference checker: no empty clause", commas(k))
            }
            Err(e) => {
                slrat_verdict = Some("REJECTED");
                println!("  SLRAT REJECTED by reference checker: {e}")
            }
        }
        if tmp_slrat.is_some() {
            let _ = std::fs::remove_file(path);
        }
    }
    if let (Some(path), sat::solver::SolveResult::Unsat) = (&lrat_path, r) {
        let cnf_path = format!("{path}.cnf");
        std::fs::write(&cnf_path, encode::to_dimacs(nv, &cls)).unwrap_or_else(|e| die(&e.to_string()));
        let t1 = Instant::now();
        let f = std::fs::File::create(path).unwrap_or_else(|e| die(&e.to_string()));
        let mut w = std::io::BufWriter::with_capacity(1 << 22, f);
        match full::write_lrat_expanded(n, &cls, sv.lrat.as_ref().unwrap(), &mut w) {
            Ok((lines, exp)) => {
                use std::io::Write;
                w.flush().unwrap();
                println!(
                    "  LRAT: {} lines ({} from expanding symmetric images) -> {} + {} ({})",
                    commas(lines),
                    commas(exp),
                    cnf_path,
                    path,
                    dur(t1.elapsed().as_secs_f64())
                );
            }
            Err(e) => println!("  LRAT expansion FAILED: {e}"),
        }
    }
    let mut verdict = slrat_verdict.unwrap_or("unchecked").to_string();
    if r == sat::solver::SolveResult::Sat {
        verdict = "witness".into();
    }
    if proof && r == sat::solver::SolveResult::Unsat && sv.proof.is_some() {
        let log = sv.proof.as_ref().unwrap();
        let t1 = Instant::now();
        let res = full::check_symmetric(s, t, n, log);
        verdict = match &res {
            Ok((_, _, true)) => "verified".into(),
            Ok(_) => "no-empty-clause".into(),
            Err(_) => "REJECTED".into(),
        };
        match res {
            Ok((rup, img, unsat)) => println!(
                "  symmetric proof: {} RUP lemmas + {} image lines, empty clause {} -> {} ({})",
                commas(rup),
                commas(img),
                if unsat { "derived" } else { "MISSING" },
                if unsat { "s VERIFIED UNSAT" } else { "NOT VERIFIED" },
                dur(t1.elapsed().as_secs_f64())
            ),
            Err(e) => println!("  symmetric proof REJECTED: {e}"),
        }
    }
    println!(
        "RESULT {{\"instance\":\"R({s},{t})/K{n}\",\"result\":\"{:?}\",\"secs\":{:.3},\"conflicts\":{},\"lib_conflicts\":{},\"main_conflicts\":{},\"lib_secs\":{:.3},\"relabel\":{},\"lib\":\"{}\",\"phase\":\"{}\",\"proof\":\"{}\"}}",
        r, secs, total_conflicts, lib_conflicts, main_conflicts, lib_secs, relabel, lib_mode, phase_name, verdict
    );
}

/// value of `"key":` in a one-line JSON record (numbers and strings; enough for RESULT lines)
fn json_field(line: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\":");
    let i = line.find(&pat)? + pat.len();
    let rest = &line[i..];
    if let Some(r) = rest.strip_prefix('"') {
        return r.find('"').map(|j| r[..j].to_string());
    }
    let j = rest.find([',', '}']).unwrap_or(rest.len());
    Some(rest[..j].trim().to_string())
}

/// (min, median, p90, max, mean) of a sample
fn distribution(v: &mut [f64]) -> (f64, f64, f64, f64, f64) {
    if v.is_empty() {
        return (0.0, 0.0, 0.0, 0.0, 0.0);
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let k = v.len();
    let median = if k % 2 == 1 { v[k / 2] } else { (v[k / 2 - 1] + v[k / 2]) / 2.0 };
    let p90 = v[((0.9 * k as f64).ceil() as usize).clamp(1, k) - 1];
    (v[0], median, p90, v[k - 1], v.iter().sum::<f64>() / k as f64)
}

/// monster bench --s 4 --t 4 --n 18 [--samples 16] [--seed0 1] [--jobs N] [--verify] [--record] [any `full` flags]
/// Runs `monster full` on --samples vertex relabellings of the same formula (seeds seed0, seed0+1, ...) and reports
/// the distribution (min, median, p90, max, mean) of conflicts (library, main, total) and seconds. Each seed is
/// deterministic, so medians and worst cases compare across commits; one lucky run cannot pass for typical behaviour.
/// --verify writes every SLRAT proof and checks it (reference checker, and the Lean checker when it is built).
/// --record appends the summary to bench/consistency.jsonl. Prints one `BENCH {json}` line for scripts and tests.
fn cmd_bench(a: &Args, argv: &[String]) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let samples = a.get("samples", 16usize).max(1);
    let seed0 = a.get("seed0", 1u64);
    let cores = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    let jobs = a.get("jobs", cores.min(samples)).max(1);
    let verify = a.has("verify");
    let (s, t, n) = (a.get("s", 4usize), a.get("t", 4usize), a.get("n", 18usize));
    // everything except bench's own options goes to `monster full`
    let mut pass: Vec<String> = Vec::new();
    let mut i = 1;
    while i < argv.len() {
        match argv[i].as_str() {
            "--samples" | "--seed0" | "--jobs" | "--relabel" | "--slrat" | "--lrat" => i += 2,
            "--verify" | "--record" => i += 1,
            x => {
                pass.push(x.to_string());
                i += 1;
            }
        }
    }
    let exe = std::env::current_exe().unwrap_or_else(|e| die(&e.to_string()));
    let tmp = std::env::temp_dir().join(format!("monster-bench-{}", std::process::id()));
    if verify {
        std::fs::create_dir_all(&tmp).unwrap_or_else(|e| die(&e.to_string()));
    }
    let lean = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("verified/.lake/build/bin/checker");
    let use_lean = verify && lean.exists();
    // (seed, result, secs, conflicts, library conflicts, main conflicts, verified)
    type Run = (u64, String, f64, f64, f64, f64, bool);
    let runs: std::sync::Mutex<Vec<Run>> = std::sync::Mutex::new(Vec::new());
    let next = AtomicUsize::new(0);
    let t0 = Instant::now();
    std::thread::scope(|sc| {
        for _ in 0..jobs {
            sc.spawn(|| loop {
                let k = next.fetch_add(1, Ordering::SeqCst);
                if k >= samples {
                    break;
                }
                let seed = seed0 + k as u64;
                let mut args: Vec<String> = vec!["full".into()];
                args.extend(pass.iter().cloned());
                args.extend(["--relabel".to_string(), seed.to_string()]);
                let proof_file = tmp.join(format!("seed{seed}.slrat"));
                if verify {
                    args.extend(["--slrat".to_string(), proof_file.display().to_string()]);
                }
                let out = std::process::Command::new(&exe).args(&args).output();
                let text = out.map(|o| String::from_utf8_lossy(&o.stdout).into_owned()).unwrap_or_default();
                let line = text.lines().find(|l| l.starts_with("RESULT ")).unwrap_or("").to_string();
                let num = |key: &str| json_field(&line, key).and_then(|v| v.parse::<f64>().ok()).unwrap_or(f64::NAN);
                let result = json_field(&line, "result").unwrap_or_else(|| "error".into());
                let verified = match result.as_str() {
                    "Unsat" if verify => {
                        text.contains("reference checker: s VERIFIED UNSAT")
                            && (!use_lean
                                || std::process::Command::new(&lean)
                                    .arg(&proof_file)
                                    .output()
                                    .map(|o| String::from_utf8_lossy(&o.stdout).contains("VERIFIED UNSAT"))
                                    .unwrap_or(false))
                    }
                    "Sat" => text.contains("independently VERIFIED"),
                    "Unsat" => true,
                    _ => false,
                };
                if verify {
                    let _ = std::fs::remove_file(&proof_file);
                }
                let run = (seed, result, num("secs"), num("conflicts"), num("lib_conflicts"), num("main_conflicts"), verified);
                runs.lock().unwrap().push(run);
            });
        }
    });
    let _ = std::fs::remove_dir(&tmp);
    let mut runs = runs.into_inner().unwrap();
    runs.sort_by_key(|r| r.0);
    let wall = t0.elapsed().as_secs_f64();
    let col = |f: &dyn Fn(&Run) -> f64| -> Vec<f64> { runs.iter().map(f).collect() };
    let metrics: [(&str, Vec<f64>); 4] = [
        ("conflicts", col(&|r| r.3)),
        ("lib_conflicts", col(&|r| r.4)),
        ("main_conflicts", col(&|r| r.5)),
        ("secs", col(&|r| r.2)),
    ];
    let mut results: Vec<(String, usize)> = Vec::new();
    for r in &runs {
        match results.iter_mut().find(|(k, _)| *k == r.1) {
            Some(e) => e.1 += 1,
            None => results.push((r.1.clone(), 1)),
        }
    }
    let verified = runs.iter().filter(|r| r.6).count();
    println!(
        "R({s},{t})/K{n}: {samples} relabellings (seeds {seed0}..{}), {jobs} at a time, {} | monster full {}",
        seed0 + samples as u64 - 1,
        dur(wall),
        pass.join(" ")
    );
    println!("  {:<15} {:>10} {:>10} {:>10} {:>10} {:>10}", "", "min", "median", "p90", "max", "mean");
    let mut json = format!(
        "{{\"instance\":\"R({s},{t})/K{n}\",\"flags\":\"{}\",\"samples\":{samples},\"seed0\":{seed0},\"results\":{{{}}},\"verified\":{verified}",
        pass.join(" "),
        results.iter().map(|(k, c)| format!("\"{k}\":{c}")).collect::<Vec<_>>().join(",")
    );
    for (name, v) in metrics {
        let mut v = v;
        let (mn, md, p9, mx, me) = distribution(&mut v);
        if name == "secs" {
            println!("  {name:<15} {mn:>10.3} {md:>10.3} {p9:>10.3} {mx:>10.3} {me:>10.3}");
        } else {
            println!("  {name:<15} {mn:>10.0} {md:>10.0} {p9:>10.0} {mx:>10.0} {me:>10.0}");
        }
        json.push_str(&format!(",\"{name}\":{{\"min\":{mn},\"median\":{md},\"p90\":{p9},\"max\":{mx},\"mean\":{me:.1}}}"));
    }
    json.push('}');
    println!(
        "  results: {}; {} {verified}/{samples}{}",
        results.iter().map(|(k, c)| format!("{c} {k}")).collect::<Vec<_>>().join(", "),
        if verify { "proofs verified" } else { "checked" },
        if use_lean { " (reference checker + Lean checker)" } else if verify { " (reference checker)" } else { " (witnesses only; --verify checks proofs)" }
    );
    println!("BENCH {json}");
    if a.has("record") {
        let commit = std::process::Command::new("git")
            .args(["rev-parse", "--short", "HEAD"])
            .output()
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .unwrap_or_default();
        let row = format!("{{\"commit\":\"{commit}\",{}\n", &json[1..]);
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open("bench/consistency.jsonl") {
            let _ = f.write_all(row.as_bytes());
        }
    }
    let consistent = results.len() == 1 && results[0].0 != "error";
    if !consistent || verified < samples {
        std::process::exit(1);
    }
}

fn cmd_ladder(a: &Args) {
    let m = sys::machine();
    let workers = a.get("workers", m.threads);
    let catalogs = a.kv.get("catalogs").map(PathBuf::from).unwrap_or_else(catalog::default_dir);
    println!("{BOLD}{MAGENTA} ▓▓ MONSTER ladder ▓▓{RESET}  {} ×{} · catalogues {}", m.model, m.threads, catalogs.display());
    println!("{DIM}  every rung runs the full gluing with certification of EVERY task (independent RUP checker + glue check){RESET}");
    println!(
        "  {:<10} {:>4}  {:<6} {:>10} {:>10} {:>8} {:>10} {:>9}  {}",
        "R(s,t)", "N", "expect", "pairs", "UNSAT", "SAT", "certified", "time", "verdict"
    );
    // (s, t, N, expect_sat, degrees)
    let rungs: Vec<(usize, usize, usize, bool, Option<Vec<usize>>)> = vec![
        (3, 3, 5, true, None),
        (3, 3, 6, false, None),
        (3, 4, 8, true, None),
        (3, 4, 9, false, None),
        (3, 5, 13, true, None),
        (3, 5, 14, false, None),
        (4, 4, 17, true, None),
        (4, 4, 18, false, None),
        (3, 6, 17, true, None),
        (3, 6, 18, false, None),
        (3, 7, 22, true, None),
        (3, 7, 23, false, None),
        (4, 5, 25, false, Some(vec![8])),
    ];
    let mut all_ok = true;
    for (s, t, n, expect_sat, degs) in rungs {
        let cfg = Config {
            s,
            t,
            n,
            route: Route::All,
            degrees: degs.clone(),
            workers,
            chunk: 256,
            mode: Mode::Stream,
            minimize: 0,
            check_every: 1,
            sample: None,
            shard: None,
            seed: 1,
            catalogs: catalogs.clone(),
            out: None,
            resume: false,
            cache_cap: 50_000,
            stop_on_sat: false,
            quiet: true,
            max_pairs_per_task: None,
            covers: None,
            gray_a: 0,
            gray_b: 0,
            unit_budget: 0,
            units: None,
            degree_axioms: false,
            biclique: false,
            book_axioms: false,
            vivify: false,
            cube_budget: 0,
            stable: false,
            pat_lbd: 12,
            books: false,
            one_sided: false,
            sched_static: false,
        };
        let label = match &degs {
            Some(d) => format!("R({s},{t}) d={}", d.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")),
            None => format!("R({s},{t})"),
        };
        match run_glue(cfg, false) {
            Ok(o) => {
                let got_sat = o.sat > 0;
                let ok = o.errors.is_empty() && o.complete && got_sat == expect_sat && o.checked == o.unsat;
                all_ok &= ok;
                let verdict = if !o.errors.is_empty() {
                    format!("{RED}ERROR {}{RESET}", o.errors[0])
                } else if got_sat {
                    format!("{}R({s},{t}) > {n}{RESET}", if ok { GREEN } else { RED })
                } else if o.pairs_target == 0 {
                    format!("{}R({s},{t}) ≤ {n} (no admissible degree){RESET}", if ok { GREEN } else { RED })
                } else {
                    format!("{}{} ≤ {n} for these degrees{RESET}", if ok { GREEN } else { RED }, if degs.is_some() { "stage" } else { "R" })
                };
                println!(
                    "  {:<10} {:>4}  {:<6} {:>10} {:>10} {:>8} {:>10} {:>9}  {} {}",
                    label,
                    n,
                    if expect_sat { "SAT" } else { "UNSAT" },
                    commas(o.pairs_target),
                    commas(o.unsat),
                    commas(o.sat),
                    commas(o.checked),
                    dur(o.secs),
                    if ok { format!("{GREEN}✔{RESET}") } else { format!("{RED}✘{RESET}") },
                    verdict
                );
            }
            Err(e) => {
                all_ok = false;
                println!("  {:<10} {:>4}  {RED}could not run: {e}{RESET}", label, n);
            }
        }
    }
    println!();
    if all_ok {
        println!("{GREEN}{BOLD}  ladder: all rungs behave as the known Ramsey values require{RESET}");
    } else {
        println!("{RED}{BOLD}  ladder: FAILURES above{RESET}");
        std::process::exit(1);
    }
}

/// monster lift-demo --s 4 --t 4 --n 18 --red 9 --blue 9 [--flip] [--sub-flip] [--patterns] --slrat out.slrat
fn cmd_lift_demo(a: &Args) {
    let (s, t) = (a.get("s", 3usize), a.get("t", 3usize));
    let d = lift::LiftDemo {
        s,
        t,
        n: a.get("n", 6usize),
        m_red: a.get("red", full::known_ramsey(s - 1, t).unwrap_or(0)),
        m_blue: a.get("blue", full::known_ramsey(s, t - 1).unwrap_or(0)),
        flip: a.has("flip"),
        sub_flip: a.has("sub-flip"),
        patterns: a.has("patterns"),
    };
    let path = a.kv.get("slrat").cloned().unwrap_or_else(|| die("--slrat FILE is required"));
    let t0 = Instant::now();
    let text = lift::lift_demo(&d).unwrap_or_else(|e| die(&e));
    std::fs::write(&path, &text).unwrap_or_else(|e| die(&e.to_string()));
    let verdict = match full::check_slrat(&text) {
        Ok(true) => "s VERIFIED UNSAT".to_string(),
        Ok(false) => "no empty clause".to_string(),
        Err(e) => format!("REJECTED: {e}"),
    };
    println!(
        "lift proof R({s},{t}) <= {}: {} lines -> {path} ({}); reference checker: {verdict}",
        d.n,
        commas(text.lines().count() as u64),
        dur(t0.elapsed().as_secs_f64())
    );
}

fn usage() {
    println!("{BOLD}monster{RESET} — exact Ramsey gluing solver (streamed CDCL + core memory + independent RUP checking)");
    println!();
    println!("  monster glue   --s 4 --t 5 --n 25 [--route parity|all] [--d 8,10,12] [--mode stream|pair]");
    println!("                 [--workers N] [--chunk K] [--check-every K] [--minimize C] [--cache K]");
    println!("                 [--sample K --seed S [--task-pairs P]] [--shard I/N] [--out DIR [--resume]] [--stop-on-sat] [--sched static]");
    println!("                 --mode unit|hybrid|cone with --covers DIR: gray-edge units; cone = feasible-cone search,");
    println!("                 uncertified prototype (needs --check-every 0)");
    println!("  monster ab     --base BIN|REV [--cand BIN] [--base-env K=V] -- glue ... --sample K");
    println!("                 paired A/B of two binaries on the same task sample, extrapolated to the full run");
    println!("  monster bench  --s S --t T --n N --samples K [full flags]   relabelled-run distribution");
    println!("  monster ladder [--workers N]    regression ladder, every task certified");
    println!("  monster cnf    s t A.g6 B.g6 p out.cnf   pair CNF byte-identical to v6/scripts/encode.py");
    println!("  monster info");
}

fn main() {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let a = parse(&argv);
    match a.pos.first().map(|s| s.as_str()) {
        Some("glue") => {
            install_sigint();
            let cfg = config_from(&a);
            let show = !cfg.quiet;
            match run_glue(cfg, show) {
                Ok(o) => {
                    if !o.errors.is_empty() {
                        std::process::exit(1);
                    }
                }
                Err(e) => die(&e),
            }
        }
        Some("ladder") => cmd_ladder(&a),
        Some("cnf") => cmd_cnf(&a),
        Some("info") => cmd_info(),
        Some("gamma") => cmd_gamma(&a),
        Some("cover-aut") => cmd_cover_aut(&a),
        Some("cover") => cmd_cover(&a),
        Some("full") => cmd_full(&a),
        Some("check-slrat") => {
            let path = a.pos.get(1).cloned().unwrap_or_else(|| die("usage: monster check-slrat proof.slrat"));
            let text = std::fs::read_to_string(&path).unwrap_or_else(|e| die(&e.to_string()));
            match full::check_slrat(&text) {
                Ok(true) => println!("s VERIFIED UNSAT"),
                Ok(false) => { println!("s NOT VERIFIED (no empty clause)"); std::process::exit(1) }
                Err(e) => { println!("s REJECTED: {e}"); std::process::exit(1) }
            }
        }
        Some("bench") => cmd_bench(&a, &argv),
        Some("ab") => ab::cmd_ab(&argv),
        Some("flag") => flag::cmd_flag(&a),
        Some("cone") => cone::cmd_cone(&a),
        Some("lift-demo") => cmd_lift_demo(&a),
        Some("lift-test") => {
            let lean = a.kv.get("lean").map(PathBuf::from);
            let (rep, fails) = lift::battery(lean.as_deref()).unwrap_or_else(|e| die(&e));
            for l in &rep {
                println!("{l}");
            }
            println!("{fails} failure(s){}", if lean.is_none() { " (reference checker only; pass --lean verified/.lake/build/bin/checker)" } else { "" });
            if fails > 0 {
                std::process::exit(1);
            }
        }
        Some("unit-lean") => cmd_unit_lean(&a),
        Some("unit-lean-stage") => cmd_unit_lean_stage(&a),
        Some("assemble-spec") => cmd_assemble_spec(&a),
        Some("mr-glue") => {
            // interval gluing measurement on sampled (G', H) pairs of the vertex-deletion covers (src/interval.rs)
            let cfg = config_from(&a);
            let d: usize = a.get("d", 10usize);
            let m = cfg.n - 1 - d;
            let la = catalog::load(&cfg.catalogs, cfg.s - 1, cfg.t, d).unwrap_or_else(|e| die(&e));
            let lb = catalog::load(&cfg.catalogs, cfg.s, cfg.t - 1, m).unwrap_or_else(|e| die(&e));
            let dir = a.kv.get("covers").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("results/covers_mr"));
            let ca = cover::Cover::load(&dir.join(format!("c{}{}_{d}_g{}.txt", cfg.s - 1, cfg.t, d - 1)), &la.graphs).unwrap_or_else(|e| die(&e));
            let k: usize = a.get("sample", 8usize);
            let seed: u64 = a.get("seed", 1u64);
            let mut rng = seed;
            let mut tot = 0f64;
            for _ in 0..k {
                rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let ga = (rng >> 33) as usize % ca.gens.len();
                rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let hb = (rng >> 33) as usize % lb.graphs.len();
                // G' = the base without its last (gray) vertex
                let base = &ca.gens[ga].base;
                let mut gp = graph::Graph::empty(base.n - 1);
                for u in 0..base.n - 1 { for v in u + 1..base.n - 1 { if base.has_edge(u, v) { gp.add_edge(u, v); } } }
                // vertex order of G' (MONSTER_MR_ORDER = canon | dense | sparse): the order the DFS adds vertices in
                let order = std::env::var("MONSTER_MR_ORDER").unwrap_or_default();
                if order == "dense" || order == "sparse" {
                    let mut vs: Vec<usize> = (0..gp.n).collect();
                    let deg = |v: usize| (gp.adj[v] & ((1u32 << gp.n) - 1)).count_ones();
                    // greedy: next vertex = the one with most (dense) / fewest (sparse) edges to the already placed ones, ties by degree
                    let mut placed: Vec<usize> = Vec::new();
                    while placed.len() < gp.n {
                        let best = vs.iter().copied().filter(|v| !placed.contains(v)).max_by_key(|&v| {
                            let to_placed = placed.iter().filter(|&&p| gp.has_edge(p, v)).count() as i64;
                            let key = to_placed * 100 + deg(v) as i64;
                            if order == "dense" { key } else { -key }
                        }).unwrap();
                        placed.push(best);
                    }
                    vs = placed;
                    let lab: Vec<u8> = vs.iter().map(|&v| v as u8).collect();
                    gp = canon::relabel(&gp, &lab);
                }
                let t0 = std::time::Instant::now();
                let st = interval::glue(&gp, &lb.graphs[hb], true);
                let secs = t0.elapsed().as_secs_f64();
                tot += secs;
                println!("mr-glue (G' gen {ga}, H {hb}): {} nodes{}, {} (4,5,24)-solutions, {} extensions, {:.3} s; intervals {}; tried/alive per level {:?}", st.nodes, if st.capped { " (CAPPED)" } else { "" }, st.solutions, st.extensions, secs, interval::h_tables(&lb.graphs[hb]).intervals.len(), (0..=gp.n).map(|l| format!("{}/{}", st.tried[l], st.alive[l])).collect::<Vec<_>>());
            }
            println!("mean {:.3} s per (G', H) pair; x {} gens x {} H = {:.0} CPU-h for d={d}", tot / k as f64, ca.gens.len(), lb.graphs.len(), tot / k as f64 * (ca.gens.len() * lb.graphs.len()) as f64 / 3600.0);
        }
        Some("cover-mr") => {
            // McKay-Radziszowski-style covers (src/mrcover.rs): A = (s-1,t,d-1)-graph + free vertex, B = itself
            let cfg = config_from(&a);
            let d: usize = a.get("d", 10usize);
            let m = cfg.n - 1 - d;
            let la = catalog::load(&cfg.catalogs, cfg.s - 1, cfg.t, d).unwrap_or_else(|e| die(&e));
            let lb = catalog::load(&cfg.catalogs, cfg.s, cfg.t - 1, m).unwrap_or_else(|e| die(&e));
            let out = a.kv.get("out").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("results/covers_mr"));
            mrcover::write(&la, &lb, cfg.s, cfg.t, d, &out).unwrap_or_else(|e| die(&e));
        }
        Some("count-kill") => {
            // counting-only refutation census of a stage (src/count.rs); no proofs, a measurement
            let cfg = config_from(&a);
            let d: usize = a.get("d", 10usize);
            let m = cfg.n - 1 - d;
            let la = catalog::load(&cfg.catalogs, cfg.s - 1, cfg.t, d).unwrap_or_else(|e| die(&e));
            let lb = catalog::load(&cfg.catalogs, cfg.s, cfg.t - 1, m).unwrap_or_else(|e| die(&e));
            count::run(cfg.s, cfg.t, cfg.n, d, &la, &lb, a.get("threads", 8usize));
        }
        Some("merge-shards") => {
            let out = a.kv.get("out").map(PathBuf::from).unwrap_or_else(|| die("usage: monster merge-shards --out DIR SHARD_DIR..."));
            let shards: Vec<PathBuf> = a.pos.iter().skip(1).map(PathBuf::from).collect();
            if shards.is_empty() {
                die("usage: monster merge-shards --out DIR SHARD_DIR...");
            }
            assemble::merge_shards(&out, &shards).unwrap_or_else(|e| die(&e));
        }
        Some("bootstrap") => {
            // the embedded scripts/bootstrap.sh: installs Rust + Lean, clones, builds, starts a Lean shard
            let p = std::env::temp_dir().join(format!("symsat-bootstrap-{}.sh", std::process::id()));
            std::fs::write(&p, include_str!("../scripts/bootstrap.sh")).unwrap_or_else(|e| die(&format!("{}: {e}", p.display())));
            let st = std::process::Command::new("bash").arg(&p).args(a.pos.iter().skip(1)).args(a.kv.iter().flat_map(|(k, v)| vec![format!("--{k}"), v.clone()])).args(a.flags.iter().map(|f| format!("--{f}"))).status().unwrap_or_else(|e| die(&format!("bash: {e}")));
            let _ = std::fs::remove_file(&p);
            std::process::exit(st.code().unwrap_or(1));
        }
        Some("sr-check") => cmd_sr_check(&a),
        Some("slrat-hints") => {
            // monster slrat-hints IN.slrat OUT.slrat: add LRAT hints to the `p` and unhinted `r` lines (e.g. `sr-gen` output)
            let (Some(inp), Some(out)) = (a.pos.get(1), a.pos.get(2)) else { die("usage: monster slrat-hints IN.slrat OUT.slrat") };
            let text = std::fs::read_to_string(inp).unwrap_or_else(|e| die(&format!("{inp}: {e}")));
            let t0 = std::time::Instant::now();
            let (hinted, empty) = full::slrat_add_hints(&text).unwrap_or_else(|e| die(&e));
            std::fs::write(out, &hinted).unwrap_or_else(|e| die(&format!("{out}: {e}")));
            let t1 = std::time::Instant::now();
            let (empty2, _, pure) = full::check_slrat_last(&hinted).unwrap_or_else(|e| die(&format!("hinted form REJECTED: {e}")));
            println!("{out}: {} lines, {:.1} MB, hinted in {:.2} s, re-checked in {:.2} s: {}", hinted.lines().count() - 1, hinted.len() as f64 / 1e6, (t1 - t0).as_secs_f64(), t1.elapsed().as_secs_f64(), if empty && empty2 { "empty clause derived" } else if pure { "last clause pure" } else { "last clause SR-tier" });
        }
        Some("sr-gen") => cmd_sr_gen(&a),
        Some("slrat2lean") => {
            let (Some(path), Some(name)) = (a.pos.get(1), a.pos.get(2)) else { die("usage: monster slrat2lean proof.slrat Name > Name.lean") };
            let text = std::fs::read_to_string(path).unwrap_or_else(|e| die(&e.to_string()));
            print!("{}", lift::slrat_to_lean(&text, name).unwrap_or_else(|e| die(&e)));
        }
        _ => usage(),
    }
    let _ = Arc::new(0);
}

/// monster cover-aut --s 4 --t 5 --n 25 --d 10 --covers DIR --gray-a 6 --gray-b 6 [--tasks tasks.jsonl]
/// Symmetry groups of the unit sides: |Stab(gen)| = vertex permutations preserving base edges and the gray set.
/// With --tasks, one line per task of that run: fixed lo conflicts secs |Stab A| |Stab B| product.
fn cmd_cover_aut(a: &Args) {
    let mut cfg = config_from(a);
    cfg.mode = Mode::Unit;
    let d: usize = a.get("d", 10usize);
    cfg.degrees = Some(vec![d]);
    cfg.route = Route::All;
    let (stages, _) = glue::plan(&cfg).unwrap_or_else(|e| die(&e));
    let st = &stages[0];
    let cap = a.get("cap", 1usize << 20);
    let orders = |cov: &cover::Cover| -> Vec<usize> { cov.gens.iter().map(|g| g.stabiliser(cap).len()).collect() };
    let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
    let oa = orders(ca);
    let ob = orders(cb);
    let hist = |o: &[usize]| -> String {
        let mut m: std::collections::BTreeMap<usize, usize> = Default::default();
        for &x in o {
            *m.entry(x).or_default() += 1;
        }
        m.iter().map(|(k, v)| format!("{k}:{v}")).collect::<Vec<_>>().join(" ")
    };
    println!("A side d={d}: {} gens, |Stab| histogram (order:count) {}", oa.len(), hist(&oa));
    println!("B side m={}: {} gens, |Stab| histogram (order:count) {}", cfg.n - 1 - d, ob.len(), hist(&ob));
    if let Some(p) = a.kv.get("tasks") {
        let text = std::fs::read_to_string(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
        println!("fixed lo conflicts secs stabA stabB product");
        for line in text.lines() {
            let get = |k: &str| -> Option<f64> {
                let i = line.find(&format!("\"{k}\":"))? + k.len() + 3;
                let rest = &line[i..];
                let end = rest.find(|c: char| !(c.is_ascii_digit() || c == '.')).unwrap_or(rest.len());
                rest[..end].parse().ok()
            };
            if let (Some(f), Some(lo), Some(c), Some(s)) = (get("fixed"), get("lo"), get("conflicts"), get("secs")) {
                let (f, lo) = (f as usize, lo as usize);
                println!("{f} {lo} {c:.0} {s:.1} {} {} {}", oa[f], ob[lo], oa[f] * ob[lo]);
            }
        }
    }
}

/// monster unit-lean --s 4 --t 5 --n 25 --d D --covers DIR --gray-a GA --gray-b GB --ga I --gb J OUT.slrat
///                   [--budget CONFLICTS] [--no-check] [--lean verified/.lake/build/bin/checker]
/// One unit's refutation as an SLRAT proof over the full K_n formula (see src/leanunit.rs for the embedding), checked
/// by the reference checker and, with --lean, by the verified checker.
fn cmd_unit_lean(a: &Args) {
    let mut cfg = config_from(a);
    cfg.mode = Mode::Unit;
    cfg.route = Route::All;
    let d: usize = a.get("d", 7usize);
    cfg.degrees = Some(vec![d]);
    let out = a.pos.get(1).cloned().unwrap_or_else(|| die("usage: monster unit-lean --s S --t T --n N --d D --covers DIR --gray-a GA --gray-b GB --ga I --gb J OUT.slrat [--budget C] [--no-check] [--lean BIN]"));
    let (stages, _) = glue::plan(&cfg).unwrap_or_else(|e| die(&e));
    let st = stages.first().unwrap_or_else(|| die(&format!("d={d} is not an admissible degree")));
    let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
    let (ga, gb) = (a.get("ga", 0usize), a.get("gb", 0usize));
    let (Some(ga), Some(gb)) = (ca.gens.get(ga), cb.gens.get(gb)) else { die(&format!("unit ({ga},{gb}) out of range: {} x {} generalisations", ca.gens.len(), cb.gens.len())) };
    let opts = leanunit::Options { budget: a.get("budget", u64::MAX), cube_budget: a.get("cube-budget", 5_000u64) };
    let lean = a.kv.get("lean").map(PathBuf::from);
    leanunit::run(cfg.s, cfg.t, cfg.n, ga, gb, &out, &opts, !a.has("no-check"), lean.as_deref()).unwrap_or_else(|e| die(&e));
}

/// monster sr-check --s S --t T --n N PROOF.sr [--slrat OUT]: check a DSR/PPR proof (Heule's `sr2drat` / `dsr-trim`
/// line format) of "no good colouring of K_N" with the reference checker's SR rule; optionally write the SLRAT form.
fn cmd_sr_check(a: &Args) {
    let (s, t, n) = (a.get("s", 4usize), a.get("t", 4usize), a.get("n", 18usize));
    let path = a.pos.get(1).cloned().unwrap_or_else(|| die("usage: monster sr-check --s S --t T --n N PROOF.sr [--slrat OUT]"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| die(&format!("{path}: {e}")));
    let t0 = std::time::Instant::now();
    let slrat = full::sr_to_slrat(s, t, n, &text).unwrap_or_else(|e| die(&e));
    if let Some(out) = a.kv.get("slrat") {
        // the hinted form (α hints and one hint group per clause whose image needs propagation): what the Lean
        // checker takes; checked while converting, then re-checked from the text by the hinted reference path
        let t1 = std::time::Instant::now();
        let (hinted, _) = full::sr_to_slrat_hinted(s, t, n, &text).unwrap_or_else(|e| die(&format!("hinted conversion: {e}")));
        std::fs::write(out, &hinted).unwrap_or_else(|e| die(&format!("{out}: {e}")));
        let t2 = std::time::Instant::now();
        match full::check_slrat_last(&hinted) {
            Ok((true, _, _)) => println!(
                "hinted SLRAT written to {out}: {} lines, {:.1} MB, converted in {:.2} s, re-checked with hints in {:.2} s (Lean: verified/.lake/build/bin/checker {out})",
                hinted.lines().count() - 1,
                hinted.len() as f64 / 1e6,
                (t2 - t1).as_secs_f64(),
                t2.elapsed().as_secs_f64()
            ),
            Ok((false, _, _)) => die("hinted form: every line checks but the empty clause was not derived"),
            Err(e) => die(&format!("hinted form REJECTED by the reference checker: {e}")),
        }
    }
    let lines = slrat.lines().count() - 1;
    match full::check_slrat_last(&slrat) {
        Ok((true, _, _)) => println!(
            "s VERIFIED: R({s},{t}) <= {n}: the {lines}-line SR proof derives the empty clause from F({s},{t},{n}) ({} clauses) in {:.2} s",
            full::full_clauses(s, t, n).len(),
            t0.elapsed().as_secs_f64()
        ),
        Ok((false, _, _)) => {
            println!("s NOT VERIFIED: every line checks but the empty clause was not derived");
            std::process::exit(1);
        }
        Err(e) => {
            println!("s NOT VERIFIED: {e}");
            std::process::exit(1);
        }
    }
}

/// monster sr-gen --s S --t T --n N OUT.slrat [--bounds]: write the SR degree-argument proof (`srgen`): a refutation
/// of F(S,T,N) when N >= R(S,T), or with `--bounds` the two degree-bound clauses for vertex 0; then check it.
fn cmd_sr_gen(a: &Args) {
    let (s, t, n) = (a.get("s", 4usize), a.get("t", 4usize), a.get("n", 18usize));
    let out = a.pos.get(1).cloned().unwrap_or_else(|| die("usage: monster sr-gen --s S --t T --n N OUT.slrat [--bounds]"));
    let mut g = srgen::Gen::new(s, t, n);
    if a.has("bounds") {
        g.degree_bounds(s, t);
    } else {
        let all: Vec<usize> = (0..n).collect();
        g.prove(s, t, &all, &[]);
    }
    let text = g.text();
    std::fs::write(&out, &text).unwrap_or_else(|e| die(&format!("{out}: {e}")));
    let t0 = std::time::Instant::now();
    match full::check_slrat_last(&text) {
        Ok((empty, last, pure)) => println!(
            "{} SR lines, {} propagation lines, {} bytes; reference checker: {} in {:.2} s (last clause {:?}, pure {pure})",
            g.sr_lines,
            g.prop_lines,
            text.len(),
            if empty { "empty clause derived" } else { "every line checks, no empty clause" },
            t0.elapsed().as_secs_f64(),
            last.map(|c| c.len())
        ),
        Err(e) => {
            println!("s NOT VERIFIED: {e}");
            std::process::exit(1);
        }
    }
}

/// monster unit-lean-stage --s 4 --t 5 --n 25 --d D --covers DIR --gray-a GA --gray-b GB --out DIR [--workers W]
///                         [--batch K] [--keep] [--resume] [--lean BIN] [--budget C] [--quiet]
/// Lean-verify a whole gluing stage: every unit exported by the unit-lean machinery, checked in Lean batches
/// (`checker --lemmas`), results in DIR/verified.jsonl and DIR/summary.json (src/leanstage.rs).
fn cmd_unit_lean_stage(a: &Args) {
    let mut cfg = config_from(a);
    cfg.mode = Mode::Unit;
    cfg.route = Route::All;
    let d: usize = a.get("d", 7usize);
    cfg.degrees = Some(vec![d]);
    let out = a.kv.get("out").map(PathBuf::from).unwrap_or_else(|| die("usage: monster unit-lean-stage --s S --t T --n N --d D --covers DIR --gray-a GA --gray-b GB --out DIR [--workers W] [--lean-jobs J] [--batch K] [--cube-budget C] [--shard I/N] [--keep] [--resume] [--lean BIN]"));
    let (stages, _) = glue::plan(&cfg).unwrap_or_else(|e| die(&e));
    let st = stages.first().unwrap_or_else(|| die(&format!("d={d} is not an admissible degree")));
    let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
    let workers: usize = a.get("workers", 3usize);
    let opts = leanstage::StageOpts {
        out,
        workers,
        batch: a.get("batch", 8usize),
        keep: a.has("keep"),
        lean: a.kv.get("lean").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("verified/.lake/build/bin/checker")),
        resume: a.has("resume"),
        budget: a.get("budget", u64::MAX),
        lean_jobs: a.get("lean-jobs", workers),
        cube_budget: a.get("cube-budget", 5_000u64),
        shard: a.kv.get("shard").map(|s| {
            let (i, n) = s.split_once('/').unwrap_or_else(|| die("--shard I/N"));
            let (i, n): (usize, usize) = (i.parse().unwrap_or_else(|_| die("--shard I/N")), n.parse().unwrap_or_else(|_| die("--shard I/N")));
            if n == 0 || i >= n {
                die("--shard I/N needs 0 <= I < N");
            }
            (i, n)
        }),
    };
    if !opts.lean.exists() {
        die(&format!("Lean checker {} not found (lake build in verified/)", opts.lean.display()));
    }
    let tt = leanstage::run_stage(cfg.s, cfg.t, cfg.n, d, &ca.gens, &cb.gens, &opts, a.has("quiet")).unwrap_or_else(|e| die(&e));
    if tt.failed > 0 {
        std::process::exit(1);
    }
}

/// `monster assemble-spec --s S --t T --n N --d D --covers DIR --gray-a GA --gray-b GB --out DIR
/// [--from-record FILE | --proofs LIST | --fake] [--spec FILE] [--threads K]`: hints + spec block for `checker --assemble`.
fn cmd_assemble_spec(a: &Args) {
    let mut cfg = config_from(a);
    cfg.mode = Mode::Unit;
    cfg.route = Route::All;
    let d: usize = a.get("d", 8usize);
    cfg.degrees = Some(vec![d]);
    let out = a.kv.get("out").map(PathBuf::from).unwrap_or_else(|| die("usage: monster assemble-spec --s S --t T --n N --d D --covers DIR --gray-a GA --gray-b GB --out DIR [--from-record FILE | --proofs LIST | --fake] [--spec FILE] [--threads K]"));
    let (stages, _) = glue::plan(&cfg).unwrap_or_else(|e| die(&e));
    let st = stages.first().unwrap_or_else(|| die(&format!("d={d} is not an admissible degree")));
    let source = if let Some(p) = a.kv.get("from-record") {
        assemble::Source::Record(PathBuf::from(p))
    } else if let Some(p) = a.kv.get("proofs") {
        assemble::Source::Proofs(PathBuf::from(p))
    } else if a.has("fake") {
        assemble::Source::Fake
    } else {
        die("one of --from-record FILE, --proofs LIST, --fake is required")
    };
    let spec = a.kv.get("spec").map(PathBuf::from).unwrap_or_else(|| out.join("assemble.spec"));
    assemble::write_spec(st, d, &out, &spec, source, a.get("threads", 16usize)).unwrap_or_else(|e| die(&e));
}
