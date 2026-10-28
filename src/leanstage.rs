//! Stage driver for Lean-verified gluing stages (`monster unit-lean-stage`): every unit (ga, gb) of a stage, in the
//! order `glue --mode unit` uses (all pairs of the two covers' generalisations, ga-major), is exported with the
//! `unit-lean` machinery (whole-unit solve, assumption rule, deletion lines) by W worker threads; finished files are
//! handed in batches of K to ONE Lean process each (`checker --lemmas LIST [--delete]`, Stream.lean `batch_sound`),
//! run from a collector thread while the workers keep solving. Results: `DIR/verified.jsonl` (one line per unit:
//! ga, gb, the clause LEAN printed, lean true/false, solve_secs, lean_secs, bytes, ...) and `DIR/summary.json`.
//! Per-unit Lean seconds are the batch's wall time apportioned by file size (one process checks the whole batch).

use crate::cover::Gen;
use crate::leanunit::{assumption_lits, export_unit, is_negated_assumption, Options};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::{mpsc, Arc, Mutex};

pub struct StageOpts {
    pub out: PathBuf,
    pub workers: usize,
    pub batch: usize,
    pub keep: bool,
    pub lean: PathBuf,
    pub resume: bool,
    pub budget: u64,
    /// concurrent Lean batch processes
    pub lean_jobs: usize,
    /// cube-and-conquer budget per cube (0 = whole-unit solves)
    pub cube_budget: u64,
    /// `Some((i, n))`: only the units with index = i (mod n); a shard never claims `complete`
    pub shard: Option<(usize, usize)>,
}

/// one exported unit, waiting for or back from Lean
struct Exported {
    ga: usize,
    gb: usize,
    path: PathBuf,
    bytes: u64,
    solve_secs: f64,
    export_secs: f64,
    conflicts: u64,
    lemmas: u64,
    assum: Vec<i32>,
    error: Option<String>,
}

#[derive(Default)]
pub struct Totals {
    pub units: usize,
    pub verified: usize,
    pub failed: usize,
    pub skipped: usize,
    pub solve_secs: f64,
    pub export_secs: f64,
    pub lean_secs: f64,
    pub lean_batches: usize,
    pub lean_peak_rss_kb: u64,
    pub bytes: u64,
    pub conflicts: u64,
    pub wall_secs: f64,
}

fn json_lits(c: &[i32]) -> String {
    format!("[{}]", c.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}

/// Parse `s VERIFIED LEMMA <path>: [lits]` / `s NOT VERIFIED <path>` lines of one batch; returns path -> clause (None
/// = not verified).
fn parse_batch_output(out: &str) -> Vec<(String, Option<Vec<i32>>)> {
    let mut v = Vec::new();
    for line in out.lines() {
        if let Some(rest) = line.strip_prefix("s VERIFIED LEMMA ") {
            if let Some((path, cl)) = rest.split_once(": [") {
                let lits: Vec<i32> = cl.trim_end_matches(']').split(',').filter_map(|x| x.trim().parse().ok()).collect();
                v.push((path.trim().to_string(), Some(lits)));
            }
        } else if let Some(path) = line.strip_prefix("s NOT VERIFIED ") {
            v.push((path.trim().to_string(), None));
        }
    }
    v
}

/// Run one Lean batch (`/usr/bin/time` wrapper for the peak RSS when available); returns (results, wall secs, rss kb).
fn run_lean_batch(lean: &Path, list: &Path, delete: bool, record: &Path) -> Result<(Vec<(String, Option<Vec<i32>>)>, f64, u64), String> {
    let t0 = std::time::Instant::now();
    let timer = Path::new("/usr/bin/time").exists();
    let mut cmd = if timer {
        let mut c = std::process::Command::new("/usr/bin/time");
        c.arg("-f").arg("MAXRSS_KB %M").arg(lean);
        c
    } else {
        std::process::Command::new(lean)
    };
    cmd.arg("--lemmas").arg(list);
    if delete {
        cmd.arg("--delete");
    }
    cmd.arg("--record").arg(record);
    let out = cmd.output().map_err(|e| format!("{}: {e}", lean.display()))?;
    let secs = t0.elapsed().as_secs_f64();
    let so = String::from_utf8_lossy(&out.stdout);
    let se = String::from_utf8_lossy(&out.stderr);
    let rss = se.lines().rev().find_map(|l| l.strip_prefix("MAXRSS_KB ").and_then(|x| x.trim().parse::<u64>().ok())).unwrap_or(0);
    let res = parse_batch_output(&so);
    if res.is_empty() {
        return Err(format!("Lean batch produced no verdicts: {} {}", so.trim(), se.trim()));
    }
    Ok((res, secs, rss))
}

/// Read `verified.jsonl` for `--resume`: the (ga, gb) already verified.
fn read_verified(path: &Path) -> std::collections::HashSet<(usize, usize)> {
    let mut done = std::collections::HashSet::new();
    if let Ok(text) = std::fs::read_to_string(path) {
        for line in text.lines() {
            let get = |k: &str| -> Option<usize> {
                let i = line.find(&format!("\"{k}\":"))? + k.len() + 3;
                let rest = &line[i..];
                let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
                rest[..end].parse().ok()
            };
            if line.contains("\"lean\":true") {
                if let (Some(ga), Some(gb)) = (get("ga"), get("gb")) {
                    done.insert((ga, gb));
                }
            }
        }
    }
    done
}

/// The driver. `gens_a`, `gens_b`: the two covers' generalisations (units = all pairs, ga-major).
pub fn run_stage(s: usize, t: usize, n: usize, d: usize, gens_a: &[Gen], gens_b: &[Gen], opts: &StageOpts, quiet: bool) -> Result<Totals, String> {
    let t_start = std::time::Instant::now();
    let units_dir = opts.out.join("units");
    std::fs::create_dir_all(&units_dir).map_err(|e| format!("{}: {e}", units_dir.display()))?;
    let jsonl_path = opts.out.join("verified.jsonl");
    let done = if opts.resume { read_verified(&jsonl_path) } else { Default::default() };
    let mut todo: Vec<(usize, usize)> = Vec::new();
    let (shard_i, shard_n) = opts.shard.unwrap_or((0, 1));
    for ga in 0..gens_a.len() {
        for gb in 0..gens_b.len() {
            // `--shard I/N`: this machine takes the units with index = I (mod N) (ga-major index, like the plan)
            if (ga * gens_b.len() + gb) % shard_n == shard_i && !done.contains(&(ga, gb)) {
                todo.push((ga, gb));
            }
        }
    }
    let total_units = gens_a.len() * gens_b.len();
    if !quiet {
        println!(
            "unit-lean-stage d={d}: {} x {} generalisations = {total_units} units, {} to do ({} already verified), {} workers, Lean batches of {}, {}",
            gens_a.len(),
            gens_b.len(),
            todo.len(),
            done.len(),
            opts.workers,
            opts.batch,
            if opts.keep { "files kept" } else { "verified files deleted" }
        );
    }
    let jsonl = Arc::new(Mutex::new(
        std::fs::OpenOptions::new().create(true).append(true).open(&jsonl_path).map_err(|e| format!("{}: {e}", jsonl_path.display()))?,
    ));
    let totals = Arc::new(Mutex::new(Totals { units: total_units, skipped: done.len(), ..Default::default() }));
    let todo = Arc::new(todo);
    let next = Arc::new(AtomicUsize::new(0));
    let (tx, rx) = mpsc::channel::<Exported>();
    let gens_a: Arc<Vec<Gen>> = Arc::new(gens_a.to_vec());
    let gens_b: Arc<Vec<Gen>> = Arc::new(gens_b.to_vec());
    // workers: export units
    let mut handles = Vec::new();
    for _ in 0..opts.workers.max(1) {
        let (todo, next, tx, gens_a, gens_b, units_dir, totals) = (todo.clone(), next.clone(), tx.clone(), gens_a.clone(), gens_b.clone(), units_dir.clone(), totals.clone());
        let (budget, cube_budget) = (opts.budget, opts.cube_budget);
        handles.push(std::thread::spawn(move || loop {
            let i = next.fetch_add(1, Relaxed);
            if i >= todo.len() {
                break;
            }
            let (ga, gb) = todo[i];
            let path = units_dir.join(format!("u{ga}_{gb}.slrat"));
            let t0 = std::time::Instant::now();
            let assum = assumption_lits(&gens_a[ga], &gens_b[gb]);
            let r = std::fs::File::create(&path)
                .map_err(|e| e.to_string())
                .and_then(|f| export_unit(s, t, n, &gens_a[ga], &gens_b[gb], &Options { budget, cube_budget }, std::io::BufWriter::with_capacity(1 << 20, f)));
            let export_secs = t0.elapsed().as_secs_f64();
            let mut ex = Exported { ga, gb, path, bytes: 0, solve_secs: 0.0, export_secs, conflicts: 0, lemmas: 0, assum, error: None };
            match r {
                Ok(rep) => {
                    ex.bytes = rep.bytes;
                    ex.solve_secs = rep.solve_secs;
                    ex.conflicts = rep.conflicts;
                    ex.lemmas = rep.lemmas;
                    let mut tt = totals.lock().unwrap();
                    tt.solve_secs += rep.solve_secs;
                    tt.export_secs += export_secs;
                    tt.bytes += rep.bytes;
                    tt.conflicts += rep.conflicts;
                }
                Err(e) => ex.error = Some(e),
            }
            let _ = tx.send(ex);
        }));
    }
    drop(tx);
    // collector: batches to Lean, up to `lean_jobs` Lean processes at a time (Lean costs ~0.9x the solve CPU, so one
    // sequential process would make a 12-worker stage Lean-bound by ~10x: measured on d=8, 3 workers, 2026-10-28)
    struct Ctx {
        lean: PathBuf,
        out: PathBuf,
        keep: bool,
        d: usize,
        quiet: bool,
        jsonl: Arc<Mutex<std::fs::File>>,
        totals: Arc<Mutex<Totals>>,
    }
    let ctx = Arc::new(Ctx { lean: opts.lean.clone(), out: opts.out.clone(), keep: opts.keep, d, quiet, jsonl: jsonl.clone(), totals: totals.clone() });
    fn process_batch(ctx: &Ctx, mut batch: Vec<Exported>, batch_no: usize) -> Result<(), String> {
        let list = ctx.out.join(format!("batch_{batch_no}.txt"));
        let mut body = String::new();
        for ex in batch.iter() {
            body.push_str(&format!("{}\n", ex.path.display()));
        }
        std::fs::write(&list, &body).map_err(|e| format!("{}: {e}", list.display()))?;
        // one record file per batch (several Lean processes run at once; O_APPEND interleaving of one shared file is avoided)
        let rec_dir = ctx.out.join("rec");
        std::fs::create_dir_all(&rec_dir).map_err(|e| format!("{}: {e}", rec_dir.display()))?;
        let (res, secs, rss) = run_lean_batch(&ctx.lean, &list, !ctx.keep, &rec_dir.join(format!("batch_{batch_no}.rec")))?;
        let _ = std::fs::remove_file(&list);
        let bytes_batch: u64 = batch.iter().map(|e| e.bytes).sum::<u64>().max(1);
        let d = ctx.d;
        let mut out = ctx.jsonl.lock().unwrap();
        let mut tt = ctx.totals.lock().unwrap();
        tt.lean_secs += secs;
        tt.lean_batches += 1;
        tt.lean_peak_rss_kb = tt.lean_peak_rss_kb.max(rss);
        for ex in batch.drain(..) {
            let verdict = res.iter().find(|(p, _)| Path::new(p) == ex.path).map(|(_, c)| c.clone());
            // the clause recorded is the one Lean printed; it must be the unit's ¬A
            let (lean_ok, clause) = match &verdict {
                Some(Some(c)) if is_negated_assumption(c, &ex.assum).is_ok() => (true, c.clone()),
                Some(Some(c)) => (false, c.clone()),
                _ => (false, Vec::new()),
            };
            let lean_secs = secs * ex.bytes as f64 / bytes_batch as f64;
            if lean_ok {
                tt.verified += 1;
            } else {
                tt.failed += 1;
            }
            let err = match (&ex.error, &verdict) {
                (Some(e), _) => format!(",\"error\":{:?}", e),
                (None, Some(Some(_))) if !lean_ok => ",\"error\":\"Lean's clause is not the unit's negated assumption\"".to_string(),
                (None, Some(None)) => ",\"error\":\"NOT VERIFIED\"".to_string(),
                (None, None) => ",\"error\":\"no Lean verdict for this file\"".to_string(),
                _ => String::new(),
            };
            let _ = writeln!(
                out,
                "{{\"d\":{d},\"ga\":{},\"gb\":{},\"clause\":{},\"lean\":{},\"solve_secs\":{:.3},\"export_secs\":{:.3},\"lean_secs\":{:.3},\"bytes\":{},\"conflicts\":{},\"lemmas\":{},\"batch\":{}{err}}}",
                ex.ga,
                ex.gb,
                json_lits(&clause),
                lean_ok,
                ex.solve_secs,
                ex.export_secs,
                lean_secs,
                ex.bytes,
                ex.conflicts,
                ex.lemmas,
                batch_no
            );
            if !ctx.quiet {
                println!(
                    "unit ({},{}): {} conflicts, solve {:.1} s, {:.1} MB, Lean batch {} ({:.1} s): {}",
                    ex.ga,
                    ex.gb,
                    ex.conflicts,
                    ex.solve_secs,
                    ex.bytes as f64 / 1e6,
                    batch_no,
                    secs,
                    if lean_ok { "VERIFIED LEMMA" } else { "NOT VERIFIED" }
                );
            }
        }
        out.flush().map_err(|e| e.to_string())?;
        Ok(())
    }
    let lean_jobs = opts.lean_jobs.max(1);
    let slots = Arc::new((Mutex::new(0usize), std::sync::Condvar::new()));
    let first_err: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
    let mut lean_threads: Vec<std::thread::JoinHandle<()>> = Vec::new();
    let mut batch: Vec<Exported> = Vec::new();
    let mut batch_no = 0usize;
    let spawn_batch = |batch: Vec<Exported>, batch_no: usize, lean_threads: &mut Vec<std::thread::JoinHandle<()>>| {
        // wait for a free Lean slot (backpressure also bounds the proof files waiting on disk)
        {
            let (m, cv) = &*slots;
            let mut running = m.lock().unwrap();
            while *running >= lean_jobs {
                running = cv.wait(running).unwrap();
            }
            *running += 1;
        }
        let (ctx, slots, first_err) = (ctx.clone(), slots.clone(), first_err.clone());
        lean_threads.push(std::thread::spawn(move || {
            if let Err(e) = process_batch(&ctx, batch, batch_no) {
                first_err.lock().unwrap().get_or_insert(e);
            }
            let (m, cv) = &*slots;
            *m.lock().unwrap() -= 1;
            cv.notify_one();
        }));
    };
    for ex in rx {
        if first_err.lock().unwrap().is_some() {
            break;
        }
        if ex.error.is_some() {
            // nothing to check; record the failure directly
            let mut out = jsonl.lock().unwrap();
            let mut tt = totals.lock().unwrap();
            tt.failed += 1;
            let _ = writeln!(out, "{{\"d\":{d},\"ga\":{},\"gb\":{},\"clause\":[],\"lean\":false,\"solve_secs\":{:.3},\"export_secs\":{:.3},\"lean_secs\":0,\"bytes\":0,\"conflicts\":0,\"lemmas\":0,\"batch\":0,\"error\":{:?}}}", ex.ga, ex.gb, ex.solve_secs, ex.export_secs, ex.error.as_deref().unwrap_or(""));
            continue;
        }
        batch.push(ex);
        if batch.len() >= opts.batch.max(1) {
            batch_no += 1;
            spawn_batch(std::mem::take(&mut batch), batch_no, &mut lean_threads);
        }
    }
    if !batch.is_empty() && first_err.lock().unwrap().is_none() {
        batch_no += 1;
        spawn_batch(std::mem::take(&mut batch), batch_no, &mut lean_threads);
    }
    for h in lean_threads {
        let _ = h.join();
    }
    for h in handles {
        let _ = h.join();
    }
    let first_err = first_err.lock().unwrap().take();
    drop(spawn_batch);
    drop(ctx);
    if let Some(e) = first_err {
        return Err(e);
    }
    let mut tt = Arc::try_unwrap(totals).map_err(|_| "totals still shared".to_string())?.into_inner().unwrap();
    tt.wall_secs = t_start.elapsed().as_secs_f64();
    let summary = format!(
        "{{\"d\":{d},\"s\":{s},\"t\":{t},\"n\":{n},\"units\":{},\"verified\":{},\"failed\":{},\"skipped_already_verified\":{},\"complete\":{},\"solve_cpu_secs\":{:.1},\"export_cpu_secs\":{:.1},\"lean_cpu_secs\":{:.1},\"lean_batches\":{},\"lean_peak_rss_kb\":{},\"bytes_exported\":{},\"conflicts\":{},\"wall_secs\":{:.1},\"workers\":{},\"batch\":{}}}\n",
        tt.units,
        tt.verified,
        tt.failed,
        tt.skipped,
        tt.verified + tt.skipped == tt.units && tt.failed == 0,
        tt.solve_secs,
        tt.export_secs,
        tt.lean_secs,
        tt.lean_batches,
        tt.lean_peak_rss_kb,
        tt.bytes,
        tt.conflicts,
        tt.wall_secs,
        opts.workers,
        opts.batch
    );
    std::fs::write(opts.out.join("summary.json"), &summary).map_err(|e| e.to_string())?;
    if !quiet {
        print!("{summary}");
    }
    Ok(tt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::Graph;

    fn gen(n: usize, edges: &[(usize, usize)], gray: &[(usize, usize)]) -> Gen {
        let mut base = Graph::empty(n);
        for &(a, b) in edges {
            base.add_edge(a, b);
        }
        Gen { base, gray: gray.to_vec() }
    }

    /// the R(3,4) K_9 toy stage: 2 A-generalisations x 2 B-generalisations = 4 units through the whole driver
    /// (export, two Lean batches, verified.jsonl, summary.json); runs when the built checker has batch mode
    #[test]
    fn unit_lean_stage_toy() {
        let lean = std::path::Path::new("verified/.lake/build/bin/checker");
        if !lean.exists() {
            return;
        }
        let probe = std::process::Command::new(lean).arg("--lemmas").arg("/nonexistent-list").output().unwrap();
        if String::from_utf8_lossy(&probe.stdout).contains("usage") {
            return; // a checker without batch mode
        }
        let dir = std::env::temp_dir().join(format!("monster-stage-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let gens_a = [gen(3, &[], &[(0, 1)]), gen(3, &[], &[(1, 2)])];
        let gens_b = [gen(5, &[(1, 2), (2, 3), (3, 4), (4, 0)], &[(0, 1)]), gen(5, &[(0, 1), (2, 3), (3, 4), (4, 0)], &[(1, 2)])];
        let opts = StageOpts { out: dir.clone(), workers: 2, batch: 3, keep: false, lean: lean.to_path_buf(), resume: false, budget: u64::MAX, lean_jobs: 2, cube_budget: 5_000, shard: None };
        let tt = run_stage(3, 4, 9, 3, &gens_a, &gens_b, &opts, true).unwrap();
        assert_eq!((tt.units, tt.verified, tt.failed, tt.lean_batches), (4, 4, 0, 2));
        let jsonl = std::fs::read_to_string(dir.join("verified.jsonl")).unwrap();
        assert_eq!(jsonl.lines().count(), 4);
        assert!(jsonl.lines().all(|l| l.contains("\"lean\":true")));
        assert!(std::fs::read_to_string(dir.join("summary.json")).unwrap().contains("\"complete\":true"));
        assert_eq!(std::fs::read_dir(dir.join("units")).unwrap().count(), 0, "verified files are deleted");
        // resume: nothing left to do
        let tt2 = run_stage(3, 4, 9, 3, &gens_a, &gens_b, &StageOpts { resume: true, ..opts }, true).unwrap();
        assert_eq!((tt2.verified, tt2.skipped, tt2.failed), (0, 4, 0));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
