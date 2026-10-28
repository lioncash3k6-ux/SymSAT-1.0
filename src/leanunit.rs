//! Lean-checkable unit refutations (`monster unit-lean`): solve one gluing unit GAMMA(ga, gb) with LRAT on, and
//! translate the proof into an SLRAT proof over the FULL K_n formula in the Lean checker's numbering
//! (`full::evar`, originals in `full::full_clauses` order), using the checker's assumption rule
//! (verified/MonsterVerified/Assume.lean; reference checker `full::check_slrat`):
//!
//! ```text
//! c slrat s t n
//! a <fixed-edge literals of the unit> 0        open assumption sub-database 0: F(s,t,n) reduced under A
//! u 0 <id> <lits> 0 <hints> 0                  every solver lemma, verbatim (GAMMA literals renamed to K_n edges)
//! <|F|+1> a 0 <id of the empty clause> 0       close: main clause ¬A, "some fixed edge has the other colour"
//! ```
//!
//! Embedding of the n = 1 + d + m vertices: the root v = 0 (red to every A-vertex, blue to every B-vertex),
//! A-vertex u (0 <= u < d) is vertex 1 + u, B-vertex w (0 <= w < m) is vertex 1 + d + w.
//! GAMMA variable -> K_n edge variable (red = true on both sides): cross y(u,w) = 1 + u*m + w -> evar(1+u, 1+d+w);
//! gray-A i = (a,b) -> evar(1+a, 1+b); gray-B i = (a,b) -> evar(1+d+a, 1+d+b).
//!
//! The unit's assumption A = the fixed edges with their fixed colours: the v-edges, and the non-gray pairs inside A
//! (red iff an edge of ga.base) and inside B (red iff an edge of gb.base). Every GAMMA clause is a K_n clique clause
//! with its assumption-false literals removed, i.e. exactly a reduced original of the assumption sub-database
//! (checked here by lookup, nothing about build_gamma is trusted), so the solver's hints are valid verbatim.
//! The final main clause ¬A is the Lean-checkable statement (`checkLemma_sound`) that no good colouring of K_n
//! has these fixed edges, hence none extends the unit.

use crate::cover::{build_gamma, Gamma, Gen};
use crate::full::{binom, check_slrat_last, check_slrat_read, evar, full_clauses};
use crate::sat::checker::IdHasher;
use crate::sat::solver::{LratLine, SolveResult, Solver};
use std::collections::HashMap;
use std::io::Write;

type IdMap<V> = HashMap<u64, V, std::hash::BuildHasherDefault<IdHasher>>;

pub struct Options {
    /// conflict budget for the whole export (u64::MAX = none); every exported line is a solver LRAT line
    pub budget: u64,
    /// cube-and-conquer: conflicts per cube before splitting (0 = solve the unit whole; glue unit mode uses 5,000)
    pub cube_budget: u64,
}

#[derive(Debug, Default, Clone)]
pub struct Report {
    pub nvars: usize,
    pub nclauses: usize,
    pub n_assumption: usize,
    pub conflicts: u64,
    pub lemmas: u64,
    pub deletions: u64,
    pub literals: u64,
    pub hints: u64,
    pub bytes: u64,
    pub solve_secs: f64,
}

/// Translates one solver's LRAT lines (over GAMMA) into steps of assumption sub-database 0, streaming to `out`.
struct Translator<W: Write> {
    vmap: Vec<i32>,
    /// solver clause id -> id in the assumption sub-database
    ids: IdMap<u64>,
    next: u64,
    n_orig: u64,
    out: W,
    line: String,
    empty_id: Option<u64>,
    rep: Report,
}

fn vertex_pairs(gen: &Gen) -> std::collections::HashSet<(usize, usize)> {
    gen.gray.iter().map(|&(a, b)| (a.min(b), a.max(b))).collect()
}

/// The unit's assumption as K_n literals (true under the unit), in a fixed order: v-edges to A (red), v-edges to B
/// (blue), non-gray pairs inside A, non-gray pairs inside B (red iff an edge of the base graph).
pub fn assumption_lits(ga: &Gen, gb: &Gen) -> Vec<i32> {
    let (d, m) = (ga.base.n, gb.base.n);
    let mut assum: Vec<i32> = Vec::new();
    for u in 0..d {
        assum.push(evar(0, 1 + u));
    }
    for w in 0..m {
        assum.push(-evar(0, 1 + d + w));
    }
    let (gray_a, gray_b) = (vertex_pairs(ga), vertex_pairs(gb));
    for a in 0..d {
        for b in a + 1..d {
            if !gray_a.contains(&(a, b)) {
                assum.push(if ga.base.has_edge(a, b) { evar(1 + a, 1 + b) } else { -evar(1 + a, 1 + b) });
            }
        }
    }
    for a in 0..m {
        for b in a + 1..m {
            if !gray_b.contains(&(a, b)) {
                assum.push(if gb.base.has_edge(a, b) { evar(1 + d + a, 1 + d + b) } else { -evar(1 + d + a, 1 + d + b) });
            }
        }
    }
    assum
}

/// Independent check of what a checked proof states: its last main clause must be exactly ¬A as a set.
pub fn is_negated_assumption(clause: &[i32], assum: &[i32]) -> Result<(), String> {
    let mut a: Vec<i32> = assum.iter().map(|&l| -l).collect();
    let mut c = clause.to_vec();
    a.sort_unstable();
    a.dedup();
    c.sort_unstable();
    c.dedup();
    if a != c {
        return Err(format!("final clause has {} literals and is not ¬A (|A| = {})", clause.len(), assum.len()));
    }
    Ok(())
}

impl<W: Write> Translator<W> {
    fn new(s: usize, t: usize, n: usize, ga: &Gen, gb: &Gen, gm: &Gamma, assum: &[i32], mut out: W) -> Result<Self, String> {
        let (d, m) = (gm.d, gm.m);
        if n != 1 + d + m {
            return Err(format!("n = {n} but the unit has 1 + {d} + {m} vertices"));
        }
        let nv = n * (n - 1) / 2;
        // 1. GAMMA variable -> K_n variable
        let mut vmap = vec![0i32; gm.nvars + 1];
        for u in 0..d {
            for w in 0..m {
                vmap[1 + u * m + w] = evar(1 + u, 1 + d + w);
            }
        }
        for (i, &(a, b)) in ga.gray.iter().enumerate() {
            vmap[gm.gray_a(i) as usize] = evar(1 + a, 1 + b);
        }
        for (i, &(a, b)) in gb.gray.iter().enumerate() {
            vmap[gm.gray_b(i) as usize] = evar(1 + d + a, 1 + d + b);
        }
        // 2. the assumption as a value table
        let mut fixed = vec![0i8; nv + 1]; // +1 red, -1 blue, 0 free
        for &l in assum {
            let v = l.unsigned_abs() as usize;
            if v == 0 || v > nv || fixed[v] != 0 {
                return Err(format!("fixed edge variable {v} out of range or fixed twice"));
            }
            fixed[v] = if l > 0 { 1 } else { -1 };
        }
        if assum.len() + gm.nvars != nv {
            return Err(format!("{} fixed + {} GAMMA variables != {nv} edges of K_{n}", assum.len(), gm.nvars));
        }
        for v in 1..=gm.nvars {
            let x = vmap[v] as usize;
            if x == 0 || fixed[x] != 0 {
                return Err(format!("GAMMA variable {v} maps to a fixed or missing edge variable"));
            }
        }
        // 3. K_n originals reduced under the assumption (exactly as the checkers do it): sorted literals -> id
        let originals = full_clauses(s, t, n);
        let n_orig = originals.len() as u64;
        let mut reduced: HashMap<Vec<i32>, u64> = HashMap::with_capacity(originals.len());
        for (i, c) in originals.iter().enumerate() {
            let mut key: Vec<i32> = c.iter().copied().filter(|&l| fixed[l.unsigned_abs() as usize] != if l > 0 { -1 } else { 1 }).collect();
            key.sort_unstable();
            reduced.entry(key).or_insert(i as u64 + 1);
        }
        // 4. every GAMMA clause is such a reduced original
        let mut ids: IdMap<u64> = IdMap::with_capacity_and_hasher(gm.clauses.len() * 2, Default::default());
        for (i, c) in gm.clauses.iter().enumerate() {
            let mut key: Vec<i32> = c.iter().map(|&l| vmap[l.unsigned_abs() as usize] * l.signum()).collect();
            key.sort_unstable();
            let id = reduced.get(&key).ok_or_else(|| format!("GAMMA clause {} {c:?} is not a reduced clique clause of K_{n}", i + 1))?;
            ids.insert(i as u64 + 1, *id);
        }
        writeln!(out, "c slrat {s} {t} {n}").map_err(|e| e.to_string())?;
        let a: Vec<String> = assum.iter().map(|l| l.to_string()).collect();
        writeln!(out, "a {} 0", a.join(" ")).map_err(|e| e.to_string())?;
        let rep = Report { nvars: gm.nvars, nclauses: gm.clauses.len(), n_assumption: assum.len(), ..Default::default() };
        Ok(Translator { vmap, ids, next: n_orig + 1, n_orig, out, line: String::new(), empty_id: None, rep })
    }

    fn lines(&mut self, lines: &[LratLine]) -> Result<(), String> {
        use std::fmt::Write as _;
        for l in lines {
            match l {
                LratLine::Delete { ids } => {
                    // `u 0 d id1 .. idn 0`: the checkers forget these clauses (memory follows the live database)
                    let line = &mut self.line;
                    line.clear();
                    line.push_str("u 0 d");
                    for id in ids {
                        let pid = self.ids.remove(id).ok_or_else(|| format!("deletion of unknown clause {id}"))?;
                        let _ = write!(line, " {pid}");
                    }
                    line.push_str(" 0\n");
                    self.out.write_all(line.as_bytes()).map_err(|e| e.to_string())?;
                    self.rep.deletions += ids.len() as u64;
                    self.rep.bytes += line.len() as u64;
                }
                LratLine::Image { id, .. } => return Err(format!("line {id}: image lines cannot be exported (no patterns in units)")),
                LratLine::Lemma { id, lits, hints } => {
                    let line = &mut self.line;
                    line.clear();
                    let _ = write!(line, "u 0 {}", self.next);
                    for &l in lits {
                        let _ = write!(line, " {}", self.vmap[l.unsigned_abs() as usize] * l.signum());
                    }
                    line.push_str(" 0");
                    for h in hints {
                        let pid = self.ids.get(h).ok_or_else(|| format!("lemma {id} cites unknown clause {h}"))?;
                        let _ = write!(line, " {pid}");
                    }
                    line.push_str(" 0\n");
                    self.out.write_all(line.as_bytes()).map_err(|e| e.to_string())?;
                    self.rep.lemmas += 1;
                    self.rep.literals += lits.len() as u64;
                    self.rep.hints += hints.len() as u64;
                    self.rep.bytes += line.len() as u64;
                    if lits.is_empty() && self.empty_id.is_none() {
                        self.empty_id = Some(self.next);
                    }
                    self.ids.insert(*id, self.next);
                    self.next += 1;
                }
            }
        }
        Ok(())
    }

    fn finish(mut self) -> Result<Report, String> {
        let e = self.empty_id.ok_or("the solver log derives no empty clause")?;
        let close = format!("{} a 0 {e} 0\n", self.n_orig + 1);
        self.out.write_all(close.as_bytes()).map_err(|e| e.to_string())?;
        self.rep.bytes += close.len() as u64;
        self.out.flush().map_err(|e| e.to_string())?;
        Ok(self.rep)
    }
}

/// Solve the unit (whole, under `opts.budget` conflicts, LRAT on) and stream the translated proof to `out`.
pub fn export_unit<W: Write + Send + 'static>(s: usize, t: usize, n: usize, ga: &Gen, gb: &Gen, opts: &Options, out: W) -> Result<Report, String> {
    let gm = build_gamma(s, t, ga, gb);
    let assum = assumption_lits(ga, gb);
    let tr = Translator::new(s, t, n, ga, gb, &gm, &assum, out)?;
    let mut solver = Solver::new(gm.nvars);
    solver.lrat_enable();
    solver.vivify_enabled = false;
    if std::env::var_os("MONSTER_REDUCE_DROP").is_none() {
        solver.reduce_drop = 90;
    }
    let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<LratLine>>(64);
    solver.lrat_sink = Some(tx);
    let writer = std::thread::spawn(move || -> Result<Report, String> {
        let mut tr = tr;
        for chunk in rx {
            tr.lines(&chunk)?;
        }
        tr.finish()
    });
    for c in &gm.clauses {
        solver.add_clause_dimacs(c);
    }
    let t0 = std::time::Instant::now();
    // the certified unit mode's strategy (glue.rs): the whole unit with a conflict budget, then cube-and-conquer in the
    // same solver (learned clauses kept; a refuted cube logs its core clause, siblings are resolved on the split
    // variable with LRAT hints, the root resolvent is the empty clause). Measured 2026-10-28 on d=10 units: the whole
    // unit alone did ~2x the conflicts of the cube strategy. `opts.cube_budget = 0` disables the cubes.
    let mut nodes = 0u64;
    solver.conflict_budget = if opts.cube_budget > 0 { opts.cube_budget.min(opts.budget) } else { opts.budget };
    let mut r = solver.solve(&[]);
    if r == SolveResult::Unknown && opts.cube_budget > 0 {
        r = match crate::glue::cube(&mut solver, &mut Vec::new(), opts.cube_budget, &mut nodes, 0) {
            crate::glue::CubeOut::Refuted(cl, _) => {
                debug_assert!(cl.is_empty());
                SolveResult::Unsat
            }
            crate::glue::CubeOut::Sat => SolveResult::Sat,
        };
    }
    let solve_secs = t0.elapsed().as_secs_f64();
    solver.lrat_finish();
    let joined = writer.join().unwrap_or_else(|_| Err("translator thread panicked".into()));
    match r {
        SolveResult::Unsat => {}
        SolveResult::Sat => return Err("the unit is satisfiable (a good colouring extends it): nothing to refute".into()),
        SolveResult::Unknown => return Err(format!("conflict budget {} exhausted after {} conflicts", opts.budget, solver.stats.conflicts)),
    }
    let mut rep = joined?;
    rep.conflicts = solver.stats.conflicts;
    rep.solve_secs = solve_secs;
    Ok(rep)
}

/// Run the Lean checker binary in lemma mode; returns the clause it reports.
pub fn lean_lemma(bin: &std::path::Path, path: &str) -> Result<Vec<i32>, String> {
    let out = std::process::Command::new(bin).arg("--lemma").arg(path).output().map_err(|e| format!("{}: {e}", bin.display()))?;
    let so = String::from_utf8_lossy(&out.stdout);
    if !(out.status.success() && so.contains("VERIFIED LEMMA")) {
        return Err(format!("Lean checker did not accept the proof: {} {}", so.trim(), String::from_utf8_lossy(&out.stderr).trim()));
    }
    so.split_once('[')
        .and_then(|(_, r)| r.split_once(']'))
        .map(|(l, _)| l.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .ok_or_else(|| format!("Lean output has no clause: {}", so.trim()))
}

/// `monster unit-lean`: export to `path`, then verify with the reference checker and (if `lean` is given) the
/// Lean checker binary. Prints one report; returns Err on any failure.
pub fn run(s: usize, t: usize, n: usize, ga: &Gen, gb: &Gen, path: &str, opts: &Options, check: bool, lean: Option<&std::path::Path>) -> Result<(), String> {
    let f = std::fs::File::create(path).map_err(|e| format!("{path}: {e}"))?;
    let t0 = std::time::Instant::now();
    let rep = export_unit(s, t, n, ga, gb, opts, std::io::BufWriter::with_capacity(1 << 20, f))?;
    let total = t0.elapsed().as_secs_f64();
    println!(
        "unit-lean: GAMMA {} vars {} clauses; assumption {} fixed edges; {} conflicts, solve {:.2} s; {} lemmas written ({} deletions emitted), {} literals ({:.1} per lemma), {} hints, {:.1} MB, {:.2} s total",
        rep.nvars,
        rep.nclauses,
        rep.n_assumption,
        rep.conflicts,
        rep.solve_secs,
        rep.lemmas,
        rep.deletions,
        rep.literals,
        rep.literals as f64 / rep.lemmas.max(1) as f64,
        rep.hints,
        rep.bytes as f64 / 1e6,
        total
    );
    let assum = assumption_lits(ga, gb);
    if check {
        let t1 = std::time::Instant::now();
        let f = std::fs::File::open(path).map_err(|e| e.to_string())?;
        // (false, Some(¬A)) is the expected verdict: every step checks, the final main clause is ¬A, not ⊥
        let (_, last, pure) = check_slrat_read(std::io::BufReader::with_capacity(1 << 20, f)).map_err(|e| format!("reference checker REJECTED the proof: {e}"))?;
        let last = last.ok_or("reference checker: no main clause was added")?;
        if !pure {
            return Err("reference checker: the final clause is SR-tier (satisfiability-preserving only), not a lemma".into());
        }
        is_negated_assumption(&last, &assum)?;
        println!(
            "reference checker (full::check_slrat): every step checks in {:.2} s; final clause = NOT(all {} fixed edges): no good colouring of K_{n} extends this unit",
            t1.elapsed().as_secs_f64(),
            assum.len()
        );
    }
    if let Some(bin) = lean {
        let t2 = std::time::Instant::now();
        let reported = lean_lemma(bin, path)?;
        is_negated_assumption(&reported, &assum).map_err(|e| format!("Lean reported clause: {e}"))?;
        println!("Lean checker ({} --lemma): VERIFIED LEMMA, {} literals = NOT(assumption), in {:.2} s (theorem MonsterVerified.checkLemma_sound)", bin.display(), reported.len(), t2.elapsed().as_secs_f64());
    }
    Ok(())
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

    fn export_text(s: usize, t: usize, n: usize, ga: &Gen, gb: &Gen) -> (String, Report) {
        let path = std::env::temp_dir().join(format!("monster-unit-lean-{}-{s}{t}{n}.slrat", std::process::id()));
        let f = std::fs::File::create(&path).unwrap();
        let rep = export_unit(s, t, n, ga, gb, &Options { budget: u64::MAX, cube_budget: 5_000 }, std::io::BufWriter::new(f)).unwrap();
        let text = std::fs::read_to_string(&path).unwrap();
        let _ = std::fs::remove_file(&path);
        (text, rep)
    }

    fn with_last_line(text: &str, f: impl Fn(&mut Vec<String>)) -> String {
        let mut lines: Vec<String> = text.lines().map(String::from).collect();
        let last = lines.last_mut().unwrap();
        let mut tk: Vec<String> = last.split_whitespace().map(String::from).collect();
        f(&mut tk);
        *last = tk.join(" ");
        lines.join("\n") + "\n"
    }

    /// R(3,4) <= 9, root of red degree 3: A = 3 blue vertices (one gray pair), B = C_5 with one gray edge.
    #[test]
    fn unit_lean_r34_unit_checks() {
        let ga = gen(3, &[], &[(0, 1)]);
        let gb = gen(5, &[(1, 2), (2, 3), (3, 4), (4, 0)], &[(0, 1)]);
        let (text, rep) = export_text(3, 4, 9, &ga, &gb);
        assert_eq!(rep.n_assumption, 36 - 15 - 2, "fixed edges = C(9,2) - cross - gray");
        assert!(rep.lemmas > 0);
        let assum = assumption_lits(&ga, &gb);
        assert_eq!(assum.len(), rep.n_assumption);
        // every step checks against F(3,4,9); no empty clause; the final main clause is ¬A
        let (empty, last, _) = check_slrat_last(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
        assert!(!empty);
        is_negated_assumption(&last.unwrap(), &assum).unwrap();
        // the closing line is `|F|+1 a 0 <empty clause id> 0`
        let last_line = text.lines().last().unwrap().to_string();
        let tk: Vec<&str> = last_line.split_whitespace().collect();
        assert_eq!(tk[1], "a");
        assert_eq!(tk[0], (binom(9, 3) + binom(9, 4) + 1).to_string());
        // mutants that must be rejected
        let lines: Vec<&str> = text.lines().collect();
        let empty_line = lines.iter().rposition(|l| l.starts_with("u 0 ") && l.split_whitespace().nth(3) == Some("0")).unwrap();
        // (a) the empty clause loses its last hint
        let mut m1: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
        let mut tk: Vec<String> = m1[empty_line].split_whitespace().map(String::from).collect();
        tk.remove(tk.len() - 2);
        m1[empty_line] = tk.join(" ");
        let m1 = m1.join("\n") + "\n";
        assert!(check_slrat_last(&m1).is_err());
        // (b) the close cites a clause that does not exist
        let m2 = with_last_line(&text, |tk| tk[3] = "0".into());
        assert!(check_slrat_last(&m2).is_err());
        // (c) an assumption literal is 0
        let m3 = text.replacen(&format!("a {} ", assum[0]), "a 0 ", 1);
        assert!(check_slrat_last(&m3).is_err());
        // (d) an image step under the assumption
        let m4 = text.replacen("u 0 ", "u 0 999999 i 1 0 1 2 3 4 5 6 7 8 0\nu 0 ", 1);
        assert!(check_slrat_last(&m4).is_err());
        // deletion lines (`u 0 d ids 0`): the tiny unit has no reduce_db, so insert them by hand
        let n_orig = binom(9, 3) + binom(9, 4);
        let close_line = lines.len() - 1;
        // (e) forgetting a lemma nobody cites afterwards is fine: the lemma before the empty clause, deleted just
        //     before the close (only the close follows, and it cites the empty clause)
        let prev_id: u64 = lines[empty_line - 1].split_whitespace().nth(2).unwrap().parse().unwrap();
        let mut m5: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
        m5.insert(close_line, format!("u 0 d {prev_id} 0"));
        let m5 = m5.join("\n") + "\n";
        let (_, last5, _) = check_slrat_last(&m5).unwrap_or_else(|e| panic!("valid deletion rejected: {e}"));
        is_negated_assumption(&last5.unwrap(), &assum).unwrap();
        // (f) a hint that names a deleted clause must be rejected: find a lemma citing a lemma id and delete that
        //     id right before it
        let (li, h) = lines
            .iter()
            .enumerate()
            .find_map(|(i, l)| {
                if !l.starts_with("u 0 ") {
                    return None;
                }
                let tk: Vec<&str> = l.split_whitespace().collect();
                let z = 3 + tk[3..].iter().position(|&x| x == "0").unwrap();
                tk[z + 1..tk.len() - 1].iter().find_map(|x| x.parse::<u64>().ok().filter(|&id| id > n_orig)).map(|h| (i, h))
            })
            .expect("some lemma cites an earlier lemma");
        let mut m6: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
        m6.insert(li, format!("u 0 d {h} 0"));
        let m6 = m6.join("\n") + "\n";
        assert!(check_slrat_last(&m6).is_err(), "hint to a deleted clause must be rejected");
        // (g) the close cites a deleted clause
        let mut m7: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
        let empty_id: u64 = lines[empty_line].split_whitespace().nth(2).unwrap().parse().unwrap();
        m7.insert(close_line, format!("u 0 d {empty_id} 0"));
        let m7 = m7.join("\n") + "\n";
        assert!(check_slrat_last(&m7).is_err());
        // (h) deleting an unknown id is rejected by the reference checker (strict; Lean ignores it)
        let m8 = text.replacen("u 0 ", "u 0 d 999999 0\nu 0 ", 1);
        assert!(check_slrat_last(&m8).is_err());
        let lean = std::path::Path::new("verified/.lake/build/bin/checker");
        if lean.exists() {
            let p = std::env::temp_dir().join(format!("monster-unit-lean-{}.slrat", std::process::id()));
            std::fs::write(&p, &text).unwrap();
            let reported = lean_lemma(lean, p.to_str().unwrap()).unwrap_or_else(|e| panic!("{e}"));
            is_negated_assumption(&reported, &assum).unwrap();
            std::fs::write(&p, &m1).unwrap();
            assert!(lean_lemma(lean, p.to_str().unwrap()).is_err(), "Lean must reject the hint-dropped mutant");
            std::fs::write(&p, &m5).unwrap();
            let r5 = lean_lemma(lean, p.to_str().unwrap()).unwrap_or_else(|e| panic!("Lean rejected a valid deletion: {e}"));
            is_negated_assumption(&r5, &assum).unwrap();
            std::fs::write(&p, &m6).unwrap();
            assert!(lean_lemma(lean, p.to_str().unwrap()).is_err(), "Lean must reject a hint to a deleted clause");
            std::fs::write(&p, &m7).unwrap();
            assert!(lean_lemma(lean, p.to_str().unwrap()).is_err(), "Lean must reject a close of a deleted clause");
            let _ = std::fs::remove_file(&p);
        }
    }

    /// batch lemma mode of the Lean checker (`checker --lemmas LIST [--delete]`): three R(3,4) unit proofs and a
    /// mutant in one process; runs when the built checker has the mode (probe: a one-file list must answer `s BATCH`)
    #[test]
    fn unit_lean_batch_lemma_mode() {
        let lean = std::path::Path::new("verified/.lake/build/bin/checker");
        if !lean.exists() {
            return;
        }
        let dir = std::env::temp_dir().join(format!("monster-batch-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let units = [
            (gen(3, &[], &[(0, 1)]), gen(5, &[(1, 2), (2, 3), (3, 4), (4, 0)], &[(0, 1)])),
            (gen(3, &[], &[]), gen(5, &[(0, 1), (2, 3), (3, 4), (4, 0)], &[(1, 2)])),
            (gen(3, &[], &[(1, 2)]), gen(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], &[])),
        ];
        let mut paths = Vec::new();
        for (k, (ga, gb)) in units.iter().enumerate() {
            let p = dir.join(format!("u{k}.slrat"));
            let f = std::fs::File::create(&p).unwrap();
            export_unit(3, 4, 9, ga, gb, &Options { budget: u64::MAX, cube_budget: 5_000 }, std::io::BufWriter::new(f)).unwrap();
            paths.push(p);
        }
        // the mutant: the empty clause of unit 0 loses its last hint
        let text = std::fs::read_to_string(&paths[0]).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        let empty_line = lines.iter().rposition(|l| l.starts_with("u 0 ") && l.split_whitespace().nth(3) == Some("0")).unwrap();
        let mut m: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
        let mut tk: Vec<String> = m[empty_line].split_whitespace().map(String::from).collect();
        tk.remove(tk.len() - 2);
        m[empty_line] = tk.join(" ");
        let mp = dir.join("mut.slrat");
        std::fs::write(&mp, m.join("\n") + "\n").unwrap();
        let probe_list = dir.join("probe.txt");
        std::fs::write(&probe_list, format!("{}\n", paths[0].display())).unwrap();
        let run = |args: &[&str]| -> (bool, String) {
            let out = std::process::Command::new(lean).args(args).output().unwrap();
            (out.status.success(), String::from_utf8_lossy(&out.stdout).to_string())
        };
        let (_, probe) = run(&["--lemmas", probe_list.to_str().unwrap()]);
        if !probe.contains("s BATCH") {
            let _ = std::fs::remove_dir_all(&dir);
            return; // checker built without batch mode
        }
        let list = dir.join("list.txt");
        let order = [&paths[0], &mp, &paths[1], &paths[2]];
        std::fs::write(&list, order.iter().map(|p| format!("{}\n", p.display())).collect::<String>()).unwrap();
        let (ok, so) = run(&["--lemmas", list.to_str().unwrap()]);
        assert!(!ok, "a failed file must give a non-zero exit code");
        assert_eq!(so.lines().filter(|l| l.starts_with("s VERIFIED LEMMA")).count(), 3, "{so}");
        assert_eq!(so.lines().filter(|l| l.starts_with("s NOT VERIFIED")).count(), 1, "{so}");
        assert!(so.contains("3 verified lemmas") && so.contains("1 failed"), "{so}");
        // every reported clause is the unit's ¬A
        for (k, (ga, gb)) in units.iter().enumerate() {
            let line = so.lines().find(|l| l.starts_with("s VERIFIED LEMMA") && l.contains(&format!("u{k}.slrat"))).unwrap();
            let reported: Vec<i32> = line.split_once('[').unwrap().1.split_once(']').unwrap().0.split(',').map(|x| x.trim().parse().unwrap()).collect();
            is_negated_assumption(&reported, &assumption_lits(ga, gb)).unwrap();
        }
        // --delete removes the verified files and keeps the failed one
        let (_, so2) = run(&["--lemmas", list.to_str().unwrap(), "--delete"]);
        assert!(so2.contains("3 verified lemmas"), "{so2}");
        assert!(paths.iter().all(|p| !p.exists()) && mp.exists());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// the vertex count must match: n = 1 + d + m
    #[test]
    fn unit_lean_rejects_bad_vertex_count() {
        let ga = gen(3, &[], &[]);
        let gb = gen(5, &[(1, 2), (2, 3), (3, 4), (4, 0), (0, 1)], &[]);
        let f = std::io::sink();
        let e = export_unit(3, 4, 10, &ga, &gb, &Options { budget: u64::MAX, cube_budget: 5_000 }, f).unwrap_err();
        assert!(e.contains("vertices"), "{e}");
    }
}
