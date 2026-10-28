//! Lift rule (local symmetry) in SLRAT: sub-instances F(s',t',m) refuted in their own databases by monster's CDCL,
//! lifted to an apex of the main formula, plus the mutant battery for the reference and Lean checkers and the
//! SLRAT -> Lean term converter for kernel-only checks.
//!
//! Lines: `o s' t' m` opens a sub-instance, `s k <line>` is a step inside it, `id l k src v r|b e0..e{m-1} 0` lifts
//! clause src of sub-instance k (see `full::check_slrat` and verified/SOUNDNESS.md).

use crate::full::{check_slrat, evar, full_clauses};
use crate::sat::solver::{LratLine, SolveResult, Solver};
use std::collections::HashMap;
use std::fmt::Write as _;

/// all k-subsets of `items`, lexicographic
fn combinations(items: &[usize], k: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut idx: Vec<usize> = (0..k).collect();
    if k > items.len() {
        return out;
    }
    loop {
        out.push(idx.iter().map(|&i| items[i]).collect());
        let mut i = k;
        while i > 0 && idx[i - 1] == items.len() - k + i - 1 {
            i -= 1;
        }
        if i == 0 {
            return out;
        }
        idx[i - 1] += 1;
        for j in i..k {
            idx[j] = idx[j - 1] + 1;
        }
    }
}

/// Refute `clauses` with LRAT logging. `patterns = Some((m, flip))` adds pattern CDCL on K_m (images become SLRAT
/// image lines). Returns the solver id of every input clause and the log.
fn refute(clauses: &[Vec<i32>], nv: usize, patterns: Option<(usize, bool)>) -> Result<(Vec<u64>, Vec<LratLine>), String> {
    let mut sv = Solver::new(nv);
    sv.lrat_enable();
    let mut ids = Vec::with_capacity(clauses.len());
    for c in clauses {
        ids.push(sv.next_clause_id());
        sv.add_clause_dimacs(c);
    }
    if let Some((m, flip)) = patterns {
        let mut pp = crate::pattern::PatternProp::new(m);
        pp.flip_ok = flip;
        sv.patterns = Some(Box::new(pp));
    }
    if sv.solve(&[]) != SolveResult::Unsat {
        return Err("formula not refuted".into());
    }
    Ok((ids, sv.lrat.take().unwrap()))
}

/// Append the log as SLRAT lines with `prefix` ("" for the main database, "s k " for sub-instance k). `map` takes
/// solver ids to proof ids and grows; returns the proof id of the empty clause.
fn emit(out: &mut String, prefix: &str, log: &[LratLine], map: &mut HashMap<u64, u64>, next: &mut u64) -> Result<u64, String> {
    let get = |map: &HashMap<u64, u64>, x: &u64| map.get(x).copied().ok_or_else(|| format!("log cites unknown clause {x}"));
    for l in log {
        let (id, empty) = match l {
            LratLine::Delete { .. } => continue,
            LratLine::Lemma { id, lits, hints } => {
                let _ = write!(out, "{prefix}{next}");
                for x in lits {
                    let _ = write!(out, " {x}");
                }
                out.push_str(" 0");
                for h in hints {
                    let _ = write!(out, " {}", get(map, h)?);
                }
                out.push_str(" 0\n");
                (*id, lits.is_empty())
            }
            LratLine::Image { id, lits, src, perm, flip } => {
                let _ = write!(out, "{prefix}{next} {} {}", if *flip { "f" } else { "i" }, get(map, src)?);
                for p in perm {
                    let _ = write!(out, " {p}");
                }
                out.push_str(" 0\n");
                (*id, lits.is_empty())
            }
        };
        map.insert(id, *next);
        *next += 1;
        if empty {
            return Ok(*next - 1);
        }
    }
    Err("log has no empty clause".into())
}

/// Test proof of R(s,t) <= n through lifts, following R(s,t) <= R(s-1,t) + R(s,t-1).
pub struct LiftDemo {
    pub s: usize,
    pub t: usize,
    pub n: usize,
    /// size of the red-apex sub-instance F(s-1,t,m_red)
    pub m_red: usize,
    /// size of the blue-apex sub-instance F(s,t-1,m_blue)
    pub m_blue: usize,
    /// s = t: no blue sub-instance; lifted red clauses are colour-swapped in the main database
    pub flip: bool,
    /// a symmetric sub-instance also swaps its empty clause and lifts the swapped copy (always emits an `f` line)
    pub sub_flip: bool,
    /// pattern CDCL inside sub-instances (images, and colour swap when s' = t', become sub-instance image lines)
    pub patterns: bool,
}

/// Sub-instances are refuted inside their own databases, their empty clauses lifted to apex 0 over every m-subset
/// of its neighbours, and monster's CDCL derives ⊥ from the lifted clauses (vertex 0 cannot have m_red red or m_blue
/// blue neighbours).
pub fn lift_demo(d: &LiftDemo) -> Result<String, String> {
    let (s, t, n) = (d.s, d.t, d.n);
    if s < 2 || t < 2 {
        return Err("need s, t >= 2".into());
    }
    if d.flip && (s != t || d.m_red != d.m_blue) {
        return Err("--flip needs s = t and equal sub-instance sizes".into());
    }
    let mut out = format!("c slrat {s} {t} {n}\n");
    let mut next = full_clauses(s, t, n).len() as u64 + 1;
    let mut subs = vec![(s - 1, t, d.m_red, true)];
    if !d.flip {
        subs.push((s, t - 1, d.m_blue, false));
    }
    let others: Vec<usize> = (1..n).collect();
    let mut lifted: Vec<(u64, Vec<i32>)> = Vec::new();
    for (k, &(ss, tt, m, red)) in subs.iter().enumerate() {
        let _ = writeln!(out, "o {ss} {tt} {m}");
        let orig = full_clauses(ss, tt, m);
        let (ids, log) = refute(&orig, m * (m - 1) / 2, d.patterns.then_some((m, ss == tt)))?;
        let mut map: HashMap<u64, u64> = ids.iter().enumerate().map(|(i, &x)| (x, i as u64 + 1)).collect();
        let mut snext = orig.len() as u64 + 1;
        let prefix = format!("s {k} ");
        let mut empty = emit(&mut out, &prefix, &log, &mut map, &mut snext)?;
        if d.sub_flip && ss == tt {
            let rev: Vec<String> = (0..m).rev().map(|x| x.to_string()).collect();
            let _ = writeln!(out, "s {k} {snext} f {empty} {} 0", rev.join(" "));
            empty = snext;
        }
        let (col, sign) = if red { ("r", -1) } else { ("b", 1) };
        for emb in combinations(&others, m) {
            let e: Vec<String> = emb.iter().map(|x| x.to_string()).collect();
            let _ = writeln!(out, "{next} l {k} {empty} 0 {col} {} 0", e.join(" "));
            lifted.push((next, emb.iter().map(|&x| sign * evar(0, x)).collect()));
            next += 1;
        }
    }
    if d.flip {
        let ident: Vec<String> = (0..n).map(|x| x.to_string()).collect();
        for i in 0..lifted.len() {
            let _ = writeln!(out, "{next} f {} {} 0", lifted[i].0, ident.join(" "));
            let neg = lifted[i].1.iter().map(|l| -l).collect();
            lifted.push((next, neg));
            next += 1;
        }
    }
    let clauses: Vec<Vec<i32>> = lifted.iter().map(|(_, c)| c.clone()).collect();
    let (ids, log) = refute(&clauses, n * (n - 1) / 2, None)?;
    let mut map: HashMap<u64, u64> = ids.iter().zip(&lifted).map(|(&x, (pid, _))| (x, *pid)).collect();
    emit(&mut out, "", &log, &mut map, &mut next)?;
    Ok(out)
}

/// Convert an SLRAT proof to a Lean term so the kernel checks it (no parser, no compiler trust). Untrusted: the
/// kernel re-checks every step as written.
pub fn slrat_to_lean(text: &str, name: &str) -> Result<String, String> {
    fn local(tk: &[&str]) -> Result<String, String> {
        if tk.len() < 2 {
            return Err("short line".into());
        }
        if tk[1] == "i" || tk[1] == "f" {
            let perm = tk[3..tk.len() - 1].join(", ");
            return Ok(format!(".img {} {} #[{perm}] {}", tk[0], tk[2], tk[1] == "f"));
        }
        let z = tk[1..].iter().position(|&x| x == "0").ok_or("missing 0")? + 1;
        let lits: Vec<String> = tk[1..z].iter().map(|x| format!("({x} : Int)")).collect();
        Ok(format!(".add {} [{}] [{}]", tk[0], lits.join(", "), tk[z + 1..tk.len() - 1].join(", ")))
    }
    let mut lines = text.lines().map(|l| l.split_whitespace().collect::<Vec<_>>()).filter(|l| !l.is_empty());
    let h = lines.next().ok_or("empty proof")?;
    if h.len() != 5 || h[0] != "c" || h[1] != "slrat" {
        return Err("bad header".into());
    }
    let (s, t, n) = (h[2], h[3], h[4]);
    let mut steps = Vec::new();
    for tk in lines {
        steps.push(match tk[0] {
            "c" => continue,
            "o" => format!(".openSub {} {} {}", tk[1], tk[2], tk[3]),
            "s" => format!(".sub {} ({})", tk[1], local(&tk[2..])?),
            _ if tk.get(1) == Some(&"l") => {
                format!(".lift {} {} {} {} {} #[{}]", tk[0], tk[2], tk[3], tk[4], tk[5] == "r", tk[6..tk.len() - 1].join(", "))
            }
            _ => local(&tk)?,
        });
    }
    Ok(format!(
        "import MonsterVerified.Checker\nopen MonsterVerified\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n\
         def {name}_steps : List Step := [\n  {}]\n\n\
         /-- kernel-checked: no compiler trust -/\ntheorem {name} : ∀ c, ¬ Good {s} {t} {n} c :=\n  \
         check_sound (steps := {name}_steps) (by decide +kernel)\n\n#print axioms {name}\n",
        steps.join(",\n  ")
    ))
}

// ---------------------------------------------------------------------------------------------------------------
// Mutant battery: every mutant must be rejected by the reference checker with the named reason, and (when a Lean
// checker binary is given) by the Lean checker; the base proofs must pass both.

type Mutate = fn(&mut Vec<String>);

fn find(lines: &[String], pred: impl Fn(&[&str]) -> bool) -> usize {
    lines
        .iter()
        .position(|l| pred(&l.split_whitespace().collect::<Vec<_>>()))
        .expect("mutant target line not found")
}

fn is_lift(tk: &[&str], k: &str) -> bool {
    tk.get(1) == Some(&"l") && tk.get(2) == Some(&k)
}

/// replace token `i` of `lines[at]`
fn set_tok(lines: &mut [String], at: usize, i: usize, v: &str) {
    let mut tk: Vec<String> = lines[at].split_whitespace().map(String::from).collect();
    tk[i] = v.into();
    lines[at] = tk.join(" ");
}

fn first_lift(l: &[String]) -> usize {
    find(l, |tk| is_lift(tk, "0"))
}

fn last_id(l: &[String]) -> u64 {
    l.iter().rev().find_map(|x| x.split_whitespace().next()?.parse().ok()).unwrap()
}

/// (name, base proof index, mutation, expected substring of the reference checker's error)
const MUTANTS: &[(&str, usize, Mutate, &str)] = &[
    ("embedding not injective", 0, |l| { let a = first_lift(l); let v = l[a].split_whitespace().nth(6).unwrap().to_string(); set_tok(l, a, 7, &v) }, "not injective"),
    ("embedding contains the apex", 0, |l| { let a = first_lift(l); set_tok(l, a, 6, "0") }, "not injective"),
    ("embedding leaves K_n", 0, |l| { let a = first_lift(l); set_tok(l, a, 6, "999") }, "not injective"),
    ("apex leaves K_n", 0, |l| { let a = first_lift(l); set_tok(l, a, 4, "999") }, "apex out of range"),
    ("wrong apex colour (red sub-instance, blue apex)", 0, |l| { let a = first_lift(l); set_tok(l, a, 5, "b") }, "do not match"),
    ("wrong apex colour (blue sub-instance, red apex)", 0, |l| { let a = find(l, |tk| is_lift(tk, "1")); set_tok(l, a, 5, "r") }, "do not match"),
    ("missing context vertex", 0, |l| { let a = first_lift(l); let mut tk: Vec<&str> = l[a].split_whitespace().collect(); tk.remove(6); l[a] = tk.join(" ") }, "exactly m vertices"),
    ("extra context vertex", 0, |l| { let a = first_lift(l); let mut tk: Vec<String> = l[a].split_whitespace().map(String::from).collect(); tk.insert(6, "999".into()); l[a] = tk.join(" ") }, "exactly m vertices"),
    ("lemma from the main database (main-only id as src)", 0, |l| { let a = first_lift(l); set_tok(l, a, 3, "9999") }, "unknown src"),
    ("lemma from the wrong sub-instance", 0, |l| { let a = find(l, |tk| is_lift(tk, "1")); set_tok(l, a, 2, "0") }, "do not match"),
    ("lift from a sub-instance not yet open", 0, |l| { let a = first_lift(l); set_tok(l, a, 2, "1") }, "not open"),
    ("step in a sub-instance not open", 0, |l| { let a = find(l, |tk| tk[0] == "s"); set_tok(l, a, 1, "7") }, "not open"),
    ("sub-instance RUP fails (hints dropped)", 0, |l| {
        let a = find(l, |tk| tk[0] == "s" && tk.get(3) == Some(&"0"));
        let tk: Vec<&str> = l[a].split_whitespace().collect();
        l[a] = format!("{} {} {} 0 0", tk[0], tk[1], tk[2]);
    }, "conflict"),
    ("sub-instance below its Ramsey number", 0, |l| { let a = find(l, |tk| tk[0] == "o"); let m: usize = l[a].split_whitespace().nth(3).unwrap().parse().unwrap(); set_tok(l, a, 3, &(m - 1).to_string()) }, ""),
    ("colour swap in an asymmetric sub-instance", 0, |l| {
        let a = find(l, |tk| tk[0] == "o");
        let m: usize = l[a].split_whitespace().nth(3).unwrap().parse().unwrap();
        let rev: Vec<String> = (0..m).rev().map(|x| x.to_string()).collect();
        l.insert(a + 1, format!("s 0 999 f 1 {} 0", rev.join(" ")));
    }, "only a symmetry"),
    ("colour swap in an asymmetric main instance", 2, |l| {
        let id = last_id(l) + 1;
        let ident: Vec<String> = (0..14).map(|x| x.to_string()).collect();
        l.push(format!("{id} f 1 {} 0", ident.join(" ")));
    }, "only a symmetry"),
    ("sub-instance image with a K_n permutation", 1, |l| {
        let a = find(l, |tk| tk[0] == "s" && tk.get(3) == Some(&"f"));
        let tk: Vec<&str> = l[a].split_whitespace().collect();
        let p: Vec<String> = (0..10).rev().map(|x| x.to_string()).collect();
        l[a] = format!("{} {} {} f {} {} 0", tk[0], tk[1], tk[2], tk[4], p.join(" "));
    }, "wrong length"),
    ("sub-instance image not a permutation", 1, |l| {
        let a = find(l, |tk| tk[0] == "s" && tk.get(3) == Some(&"f"));
        let v = l[a].split_whitespace().nth(5).unwrap().to_string();
        set_tok(l, a, 6, &v);
    }, "not a permutation"),
    ("lift id reused", 0, |l| { let a = first_lift(l); set_tok(l, a, 0, "1") }, "id reused"),
    ("malformed open line", 0, |l| { let a = find(l, |tk| tk[0] == "o"); let mut tk: Vec<&str> = l[a].split_whitespace().collect(); tk.pop(); l[a] = tk.join(" ") }, "open line"),
];

/// base proofs: R(3,3) <= 6 (two sub-instances), R(3,4) <= 10 (swap inside the (3,3) sub-instance),
/// R(3,5) <= 14 (two sub-instances, asymmetric main)
pub fn battery_bases() -> Result<Vec<(String, String)>, String> {
    let mk = |s, t, n, m_red, m_blue, sub_flip| LiftDemo { s, t, n, m_red, m_blue, flip: false, sub_flip, patterns: false };
    Ok(vec![
        ("R(3,3)<=6".into(), lift_demo(&mk(3, 3, 6, 3, 3, false))?),
        ("R(3,4)<=10 sub-flip".into(), lift_demo(&mk(3, 4, 10, 4, 6, true))?),
        ("R(3,5)<=14".into(), lift_demo(&mk(3, 5, 14, 5, 9, false))?),
    ])
}

fn lean_accepts(bin: &std::path::Path, text: &str) -> Result<bool, String> {
    let path = std::env::temp_dir().join(format!("monster-lift-{}.slrat", std::process::id()));
    std::fs::write(&path, text).map_err(|e| e.to_string())?;
    let out = std::process::Command::new(bin).arg(&path).output().map_err(|e| format!("{}: {e}", bin.display()))?;
    let _ = std::fs::remove_file(&path);
    Ok(out.status.success() && String::from_utf8_lossy(&out.stdout).contains("VERIFIED UNSAT"))
}

/// Run the battery; returns one report line per case and the number of failures.
pub fn battery(lean: Option<&std::path::Path>) -> Result<(Vec<String>, usize), String> {
    let bases = battery_bases()?;
    let mut rep = Vec::new();
    let mut fails = 0;
    for (name, text) in &bases {
        let ok = check_slrat(text) == Ok(true) && lean.map_or(Ok(true), |b| lean_accepts(b, text))?;
        rep.push(format!("{} accept {name}", if ok { "ok  " } else { "FAIL" }));
        fails += !ok as usize;
    }
    for &(name, base, mutate, why) in MUTANTS {
        let mut lines: Vec<String> = bases[base].1.lines().map(String::from).collect();
        mutate(&mut lines);
        let text = lines.join("\n") + "\n";
        let rust = check_slrat(&text);
        let rust_ok = match &rust {
            Err(e) => e.contains(why),
            Ok(_) => false,
        };
        let lean_ok = lean.map_or(Ok(true), |b| lean_accepts(b, &text).map(|a| !a))?;
        let ok = rust_ok && lean_ok;
        rep.push(format!("{} reject {name}{}", if ok { "ok  " } else { "FAIL" }, if ok { String::new() } else { format!(" (reference: {rust:?}, lean rejects: {lean_ok})") }));
        fails += !ok as usize;
    }
    Ok((rep, fails))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combinations_lex() {
        assert_eq!(combinations(&[1, 2, 3, 4], 2), vec![vec![1, 2], vec![1, 3], vec![1, 4], vec![2, 3], vec![2, 4], vec![3, 4]]);
        assert_eq!(combinations(&[1, 2], 3), Vec::<Vec<usize>>::new());
    }

    #[test]
    fn lift_battery_reference_checker() {
        // the Lean checker joins in when it is built (lake build in verified/)
        let lean = std::path::Path::new("verified/.lake/build/bin/checker");
        let (rep, fails) = battery(lean.exists().then_some(lean)).unwrap();
        assert_eq!(fails, 0, "{}", rep.join("\n"));
    }

    #[test]
    fn lift_with_sub_instance_patterns() {
        let d = LiftDemo { s: 3, t: 4, n: 10, m_red: 4, m_blue: 6, flip: false, sub_flip: false, patterns: true };
        assert_eq!(check_slrat(&lift_demo(&d).unwrap()), Ok(true));
    }
}
