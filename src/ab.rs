//! `monster ab`: paired A/B comparison of two monster binaries on the same seeded sample of a full run's tasks.
//!
//! Both binaries run `glue <args>` with the same `--sample K --seed S`, so they solve exactly the same tasks, and with
//! `--sched static`, so every per-task count is reproducible (hybrid workers keep their solver across tasks; a
//! first-come schedule would make counts depend on thread timing). For each metric the report gives the ratio of
//! totals, which is what the full run's cost changes by, with a bootstrap 95% interval over tasks; the geometric mean
//! of per-task ratios (the typical task); and the full run's cost extrapolated from the sample (pairs-weighted ratio
//! estimator over the unsampled plan, `plan_pairs` in summary.json). Every task's verdict must agree between the two
//! binaries: a disagreement is a correctness alarm and fails the command. One JSON row per comparison is appended to
//! `bench/ab.jsonl`, so every change is judged against its predecessor on the same tasks.
//!
//! `--base` is a binary path or a git revision (built once from `git archive` into ~/.cache/symsat/base/<sha>/);
//! `--cand` defaults to this binary. Seconds come from both sides running at the same time on the same box, so they
//! share its load; conflicts, search nodes and embed calls are deterministic.

use crate::{die, json_field, parse};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

#[derive(Clone, Copy)]
struct Rec {
    pairs: f64,
    unsat: u64,
    sat: u64,
    secs: f64,
    conflicts: f64,
    nodes: f64,
    embed: f64,
}

type Key = (u64, u64, u64, u64); // (d, fixed, lo, hi)

fn read_tasks(path: &Path) -> Result<HashMap<Key, Rec>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut m = HashMap::new();
    for line in text.lines().filter(|l| l.starts_with('{')) {
        let int = |k: &str| json_field(line, k).and_then(|v| v.parse::<u64>().ok());
        let num = |k: &str| json_field(line, k).and_then(|v| v.parse::<f64>().ok()).unwrap_or(f64::NAN);
        let (Some(d), Some(f), Some(lo), Some(hi)) = (int("d"), int("fixed"), int("lo"), int("hi")) else { continue };
        let (unsat, sat) = (int("unsat").unwrap_or(0), int("sat").unwrap_or(0));
        let rec = Rec { pairs: (unsat + sat) as f64, unsat, sat, secs: num("secs"), conflicts: num("conflicts"), nodes: num("nodes"), embed: num("embed") };
        m.insert((d, f, lo, hi), rec);
    }
    Ok(m)
}

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

fn quantiles(mut v: Vec<f64>) -> (f64, f64) {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let at = |q: f64| v[((v.len() - 1) as f64 * q).round() as usize];
    (at(0.025), at(0.975))
}

/// (ratio of totals Σc/Σb, its bootstrap 95% interval, geometric mean of per-task c/b, its interval); tasks where
/// either side is 0 or missing are left out of the geometric mean. Deterministic (fixed resampling seed).
pub fn paired(b: &[f64], c: &[f64]) -> Option<(f64, (f64, f64), f64, (f64, f64))> {
    let idx: Vec<usize> = (0..b.len()).filter(|&i| b[i].is_finite() && c[i].is_finite()).collect();
    if idx.is_empty() {
        return None;
    }
    let tot = |ix: &mut dyn Iterator<Item = usize>| -> f64 {
        let (mut sb, mut sc) = (0.0, 0.0);
        for i in ix {
            sb += b[i];
            sc += c[i];
        }
        if sb > 0.0 { sc / sb } else { f64::NAN }
    };
    let logs: Vec<f64> = idx.iter().filter(|&&i| b[i] > 0.0 && c[i] > 0.0).map(|&i| (c[i] / b[i]).ln()).collect();
    let gm = |v: &mut dyn Iterator<Item = f64>| -> f64 {
        let (mut s, mut k) = (0.0, 0usize);
        for x in v {
            s += x;
            k += 1;
        }
        if k > 0 { (s / k as f64).exp() } else { f64::NAN }
    };
    let point = tot(&mut idx.iter().copied());
    let gpoint = gm(&mut logs.iter().copied());
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let (mut rs, mut gs) = (Vec::new(), Vec::new());
    for _ in 0..2000 {
        rs.push(tot(&mut (0..idx.len()).map(|_| idx[rng.below(idx.len())])));
        if !logs.is_empty() {
            gs.push(gm(&mut (0..logs.len()).map(|_| logs[rng.below(logs.len())])));
        }
    }
    rs.retain(|x| x.is_finite());
    let ci = if rs.is_empty() { (f64::NAN, f64::NAN) } else { quantiles(rs) };
    let gci = if gs.is_empty() { (f64::NAN, f64::NAN) } else { quantiles(gs) };
    Some((point, ci, gpoint, gci))
}

/// Civil UTC time from Unix seconds (Howard Hinnant's days-to-civil).
fn utc(secs: u64) -> String {
    let (days, rem) = ((secs / 86_400) as i64, secs % 86_400);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + (m <= 2) as i64;
    format!("{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z", rem / 3600, rem / 60 % 60, rem % 60)
}

fn run(cmd: &mut Command, what: &str) -> Result<String, String> {
    let o = cmd.output().map_err(|e| format!("{what}: {e}"))?;
    if !o.status.success() {
        return Err(format!("{what} failed: {}", String::from_utf8_lossy(&o.stderr).trim()));
    }
    Ok(String::from_utf8_lossy(&o.stdout).trim().to_string())
}

/// A binary path as given, or the monster binary built from git revision `spec` (cached by commit).
fn resolve(spec: &str, repo: &Path) -> Result<(PathBuf, String), String> {
    let p = Path::new(spec);
    if p.is_file() {
        return Ok((p.to_path_buf(), spec.to_string()));
    }
    let sha = run(Command::new("git").arg("-C").arg(repo).args(["rev-parse", "--verify", &format!("{spec}^{{commit}}")]), "git rev-parse")?;
    let dir = PathBuf::from(std::env::var("HOME").unwrap_or_default()).join(".cache/symsat/base").join(&sha[..12]);
    let exe = dir.join("target/release/monster");
    let label = format!("{spec} ({})", &sha[..12]);
    if exe.is_file() {
        return Ok((exe, label));
    }
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    eprintln!("ab: building {label} in {} ...", dir.display());
    let archive = Command::new("git").arg("-C").arg(repo).args(["archive", "--format=tar", &sha]).output().map_err(|e| e.to_string())?;
    if !archive.status.success() {
        return Err("git archive failed".into());
    }
    let mut tar = Command::new("tar").arg("-x").arg("-C").arg(&dir).stdin(std::process::Stdio::piped()).spawn().map_err(|e| e.to_string())?;
    std::io::Write::write_all(tar.stdin.as_mut().unwrap(), &archive.stdout).map_err(|e| e.to_string())?;
    drop(tar.stdin.take());
    if !tar.wait().map_err(|e| e.to_string())?.success() {
        return Err("tar failed".into());
    }
    let cargo = std::env::var("HOME").map(|h| PathBuf::from(h).join(".cargo/bin/cargo")).ok().filter(|c| c.is_file()).unwrap_or_else(|| "cargo".into());
    let st = Command::new(cargo).args(["build", "--release", "--quiet"]).current_dir(&dir).status().map_err(|e| e.to_string())?;
    if !st.success() || !exe.is_file() {
        return Err(format!("building {label} failed"));
    }
    Ok((exe, label))
}

fn envs(spec: Option<&String>) -> Vec<(String, String)> {
    spec.map(|s| s.split(',').filter_map(|kv| kv.split_once('=').map(|(k, v)| (k.to_string(), v.to_string()))).collect()).unwrap_or_default()
}

pub fn cmd_ab(argv: &[String]) {
    let split = argv.iter().position(|x| x == "--").unwrap_or_else(|| {
        die("usage: monster ab --base BIN|REV [--cand BIN] [--base-env K=V,..] [--cand-env K=V,..] [--label TEXT] [--out DIR] -- glue ARGS.. --sample K")
    });
    let a = parse(&argv[..split]);
    let mut child: Vec<String> = argv[split + 1..].to_vec();
    if child.first().map(|s| s.as_str()) != Some("glue") || !child.iter().any(|x| x == "--sample") {
        die("ab compares `glue` runs on a task sample: give `-- glue ... --sample K`");
    }
    if child.iter().any(|x| x == "--out") {
        die("ab sets --out for both sides itself (use ab's own --out DIR)");
    }
    let has = |c: &[String], k: &str| c.iter().any(|x| x == k);
    let threads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    for (k, v) in [("--sched", "static".to_string()), ("--check-every", "0".into()), ("--chunk", "1".into()), ("--workers", (threads / 2).max(1).to_string())] {
        if !has(&child, k) {
            child.extend([k.to_string(), v]);
        }
    }
    if !has(&child, "--quiet") {
        child.push("--quiet".into());
    }
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let base_spec = a.kv.get("base").cloned().unwrap_or_else(|| "HEAD".into());
    let (base, base_label) = resolve(&base_spec, &repo).unwrap_or_else(|e| die(&e));
    let (cand, cand_label) = match a.kv.get("cand") {
        Some(c) => resolve(c, &repo).unwrap_or_else(|e| die(&e)),
        None => (std::env::current_exe().unwrap_or_else(|e| die(&e.to_string())), "this binary".into()),
    };
    let (base_env, cand_env) = (envs(a.kv.get("base-env")), envs(a.kv.get("cand-env")));
    // --base-args / --cand-args: options appended to one side only (e.g. "--mode unit" vs "--mode hybrid"); the task
    // sample stays the same as long as both sides plan the same tasks
    let side_args = |k: &str| -> Vec<String> { a.kv.get(k).map(|s| s.split_whitespace().map(String::from).collect()).unwrap_or_default() };
    let (base_args, cand_args) = (side_args("base-args"), side_args("cand-args"));
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
    let out = a.kv.get("out").map(PathBuf::from).unwrap_or_else(|| repo.join("results/ab").join(utc(now).replace(':', "")));
    std::fs::create_dir_all(&out).unwrap_or_else(|e| die(&format!("{}: {e}", out.display())));
    let fmt_env = |e: &[(String, String)]| e.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(",");
    let desc = |label: &String, env: &[(String, String)], extra: &[String]| {
        let mut d = label.clone();
        if !env.is_empty() {
            d.push_str(&format!(" [{}]", fmt_env(env)));
        }
        if !extra.is_empty() {
            d.push_str(&format!(" +[{}]", extra.join(" ")));
        }
        d
    };
    let (base_desc, cand_desc) = (desc(&base_label, &base_env, &base_args), desc(&cand_label, &cand_env, &cand_args));
    println!("ab: base {base_desc} | cand {cand_desc}\nab: monster {} -> {}", child.join(" "), out.display());
    // both sides at once, so their seconds share the box's load
    let t0 = Instant::now();
    let walls: Vec<(bool, f64)> = std::thread::scope(|sc| {
        let hs: Vec<_> = [("base", &base, &base_env, &base_args), ("cand", &cand, &cand_env, &cand_args)]
            .into_iter()
            .map(|(side, exe, env, extra)| {
                let mut args = child.clone();
                args.extend(extra.iter().cloned());
                args.extend(["--out".to_string(), out.join(side).display().to_string()]);
                let log = std::fs::File::create(out.join(format!("{side}.log"))).unwrap_or_else(|e| die(&e.to_string()));
                let mut cmd = Command::new(exe);
                cmd.args(&args).current_dir(&repo).stdout(log.try_clone().unwrap()).stderr(log);
                for (k, v) in env {
                    cmd.env(k, v);
                }
                sc.spawn(move || {
                    let ok = cmd.status().map(|s| s.success()).unwrap_or(false);
                    (ok, t0.elapsed().as_secs_f64())
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for (side, (ok, _)) in ["base", "cand"].iter().zip(&walls) {
        if !ok {
            die(&format!("{side} run failed: see {}", out.join(format!("{side}.log")).display()));
        }
    }
    let tb = read_tasks(&out.join("base/tasks.jsonl")).unwrap_or_else(|e| die(&e));
    let tc = read_tasks(&out.join("cand/tasks.jsonl")).unwrap_or_else(|e| die(&e));
    let mut keys: Vec<Key> = tb.keys().filter(|k| tc.contains_key(k)).copied().collect();
    keys.sort();
    let disagree: Vec<&Key> = keys.iter().filter(|k| (tb[k].unsat, tb[k].sat) != (tc[k].unsat, tc[k].sat)).collect();
    let summary = std::fs::read_to_string(out.join("cand/summary.json")).unwrap_or_default();
    let plan_pairs = json_field(&summary, "plan_pairs").and_then(|v| v.parse::<f64>().ok());
    let plan_tasks = json_field(&summary, "plan_tasks").unwrap_or_else(|| "?".into());
    let sample_pairs: f64 = keys.iter().map(|k| tc[k].pairs).sum();
    println!(
        "ab: {} common tasks ({} base, {} cand), {} pairs, of a plan of {} tasks / {} pairs | wall {:.0}s base, {:.0}s cand",
        keys.len(),
        tb.len(),
        tc.len(),
        sample_pairs,
        plan_tasks,
        plan_pairs.map_or("?".into(), |p| format!("{p}")),
        walls[0].1,
        walls[1].1
    );
    if !disagree.is_empty() {
        println!("ab: VERDICTS DISAGREE on {} task(s) (d, fixed, lo, hi): {:?}", disagree.len(), &disagree[..disagree.len().min(10)]);
    } else {
        println!("ab: verdicts agree on every common task");
    }
    let col = |m: &HashMap<Key, Rec>, f: fn(&Rec) -> f64| -> Vec<f64> { keys.iter().map(|k| f(&m[k])).collect() };
    let metrics: [(&str, fn(&Rec) -> f64); 4] = [("secs", |r| r.secs), ("conflicts", |r| r.conflicts), ("nodes", |r| r.nodes), ("embed", |r| r.embed)];
    println!("{:<10} {:>14} {:>14} {:>26} {:>26}", "metric", "base total", "cand total", "cand/base total (95% CI)", "per-task geomean (95% CI)");
    let mut row = format!(
        "{{\"utc\":\"{}\",\"label\":{:?},\"base\":{:?},\"cand\":{:?},\"args\":{:?},\"tasks\":{},\"pairs\":{},\"plan_pairs\":{},\"disagree\":{},\"wall_base\":{:.1},\"wall_cand\":{:.1}",
        utc(now),
        a.kv.get("label").cloned().unwrap_or_default(),
        base_desc,
        cand_desc,
        child.join(" "),
        keys.len(),
        sample_pairs,
        plan_pairs.unwrap_or(f64::NAN),
        disagree.len(),
        walls[0].1,
        walls[1].1
    );
    let mut secs_tot = (f64::NAN, f64::NAN);
    for (name, f) in metrics {
        let (b, c) = (col(&tb, f), col(&tc, f));
        let (sb, sc): (f64, f64) = (b.iter().filter(|x| x.is_finite()).sum(), c.iter().filter(|x| x.is_finite()).sum());
        if name == "secs" {
            secs_tot = (sb, sc);
        }
        match paired(&b, &c) {
            Some((r, (lo, hi), g, (glo, ghi))) => {
                let show = |x: f64| if name == "secs" { format!("{x:.1}") } else { crate::dash::commas(x as u64) };
                println!("{name:<10} {:>14} {:>14} {:>26} {:>26}", show(sb), show(sc), format!("{r:.3} ({lo:.3}-{hi:.3})"), format!("{g:.3} ({glo:.3}-{ghi:.3})"));
                row.push_str(&format!(",\"{name}\":{{\"base\":{sb},\"cand\":{sc},\"ratio\":{r:.4},\"lo\":{lo:.4},\"hi\":{hi:.4},\"geomean\":{g:.4}}}"));
            }
            None => println!("{name:<10} {:>14} {:>14} {:>26}", "n/a", "n/a", "(not recorded by one side)"),
        }
    }
    if let (Some(pp), true) = (plan_pairs, sample_pairs > 0.0) {
        let scale = pp / sample_pairs;
        let (fb, fc) = (secs_tot.0 * scale / 3600.0, secs_tot.1 * scale / 3600.0);
        let span = |h: f64| if h >= 1.0 { format!("{h:.2} h") } else if h * 60.0 >= 1.0 { format!("{:.1} min", h * 60.0) } else { format!("{:.0} s", h * 3600.0) };
        println!(
            "full run, extrapolated from the sample: base {} CPU, cand {} CPU; at {threads} workers {} vs {}",
            span(fb),
            span(fc),
            span(fb / threads as f64),
            span(fc / threads as f64)
        );
        row.push_str(&format!(",\"full_cpu_h\":{{\"base\":{fb:.3},\"cand\":{fc:.3}}}"));
    }
    row.push_str("}\n");
    let log = repo.join("bench/ab.jsonl");
    let _ = std::fs::OpenOptions::new().create(true).append(true).open(&log).and_then(|mut f| std::io::Write::write_all(&mut f, row.as_bytes()));
    println!("ab: row appended to {}", log.display());
    if !disagree.is_empty() {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn paired_ratio_and_interval() {
        let b = [10.0, 20.0, 30.0, 40.0];
        let c = [5.0, 10.0, 15.0, 20.0];
        let (r, (lo, hi), g, _) = super::paired(&b, &c).unwrap();
        assert!((r - 0.5).abs() < 1e-12 && (g - 0.5).abs() < 1e-12 && (lo - 0.5).abs() < 1e-12 && (hi - 0.5).abs() < 1e-12);
        let c2 = [5.0, 40.0, 15.0, 20.0];
        let (r2, (lo2, hi2), _, _) = super::paired(&b, &c2).unwrap();
        assert!(lo2 <= r2 && r2 <= hi2 && lo2 < hi2);
    }

    #[test]
    fn utc_format() {
        assert_eq!(super::utc(0), "1970-01-01T00:00:00Z");
        assert_eq!(super::utc(1_793_016_000), "2026-10-26T12:00:00Z");
    }
}
