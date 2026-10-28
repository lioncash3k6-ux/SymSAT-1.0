//! Independent forward RUP checker. Shares no code with the solver (own literal encoding, own propagation).
//!
//! Input: the original formula and a lemma log (DIMACS literals, each lemma 0-terminated, additions only).
//! Every lemma must be RUP with respect to the formula plus all earlier lemmas: assigning the negation of its
//! literals and unit-propagating must reach a conflict. A lemma accepted this way is implied by the formula, so
//! the final claims (the empty clause, or a clause OR(¬core) refuting an assumption set) are implied too.
//! Keeping every lemma (no deletions) can only make RUP checks easier, never unsound.

pub struct Checker {
    n: usize,
    clauses: Vec<Vec<i32>>,
    watch: Vec<Vec<usize>>, // index: lit code
    assign: Vec<i8>,        // per var (1-based): 1 true, -1 false, 0 free
    trail: Vec<i32>,
    root_conflict: bool,
    pub lemmas_checked: u64,
}

#[inline]
fn code(l: i32) -> usize {
    (l.unsigned_abs() as usize) * 2 + (l < 0) as usize
}

impl Checker {
    pub fn new(nvars: usize, formula: &[Vec<i32>]) -> Checker {
        let mut c = Checker {
            n: nvars,
            clauses: Vec::new(),
            watch: vec![Vec::new(); 2 * nvars + 2],
            assign: vec![0; nvars + 1],
            trail: Vec::new(),
            root_conflict: false,
            lemmas_checked: 0,
        };
        for cl in formula {
            c.add(cl);
        }
        c
    }

    fn value(&self, l: i32) -> i8 {
        let a = self.assign[l.unsigned_abs() as usize];
        if l > 0 {
            a
        } else {
            -a
        }
    }

    fn set(&mut self, l: i32) {
        self.assign[l.unsigned_abs() as usize] = if l > 0 { 1 } else { -1 };
        self.trail.push(l);
    }

    fn grow(&mut self, l: i32) {
        let v = l.unsigned_abs() as usize;
        if v > self.n {
            self.n = v;
            self.assign.resize(v + 1, 0);
            self.watch.resize(2 * v + 2, Vec::new());
        }
    }

    /// Add a clause (already known to be implied) at root level.
    fn add(&mut self, cl: &[i32]) {
        if self.root_conflict {
            return;
        }
        for &l in cl {
            self.grow(l);
        }
        let mut c: Vec<i32> = cl.to_vec();
        c.sort_unstable();
        c.dedup();
        if c.windows(2).any(|w| w[0] == -w[1]) {
            return; // tautology
        }
        // move non-false literals to the front so the watches are on the best two literals
        c.sort_by_key(|&l| match self.value(l) {
            1 => 0,
            0 => 1,
            _ => 2,
        });
        let nonfalse = c.iter().filter(|&&l| self.value(l) != -1).count();
        if c.is_empty() || nonfalse == 0 {
            self.root_conflict = true;
            return;
        }
        let idx = self.clauses.len();
        if c.len() >= 2 {
            self.watch[code(c[0])].push(idx);
            self.watch[code(c[1])].push(idx);
        }
        let first = c[0];
        let unit = nonfalse == 1 && self.value(first) == 0;
        self.clauses.push(c);
        if unit {
            self.set(first);
            if !self.propagate(self.trail.len() - 1) {
                self.root_conflict = true;
            }
        }
    }

    /// Propagate from trail position `from`; false on conflict.
    fn propagate(&mut self, mut from: usize) -> bool {
        while from < self.trail.len() {
            let p = self.trail[from];
            from += 1;
            let fl = -p; // literal that just became false
            let mut list = std::mem::take(&mut self.watch[code(fl)]);
            let n = list.len();
            let (mut i, mut j) = (0usize, 0usize);
            let mut ok = true;
            while i < n {
                let ci = list[i];
                i += 1;
                let c = &mut self.clauses[ci];
                if c[0] == fl {
                    c.swap(0, 1);
                }
                // c[1] == fl
                let other = c[0];
                let a = self.assign[other.unsigned_abs() as usize];
                let oval = if other > 0 { a } else { -a };
                if oval == 1 {
                    list[j] = ci;
                    j += 1;
                    continue;
                }
                let mut moved = false;
                for k in 2..c.len() {
                    let lk = c[k];
                    let a = self.assign[lk.unsigned_abs() as usize];
                    let v = if lk > 0 { a } else { -a };
                    if v != -1 {
                        c.swap(1, k);
                        let nl = c[1];
                        self.watch[code(nl)].push(ci);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                list[j] = ci;
                j += 1;
                if oval == -1 {
                    ok = false;
                    while i < n {
                        list[j] = list[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.set(other);
                }
            }
            list.truncate(j);
            self.watch[code(fl)] = list;
            if !ok {
                return false;
            }
        }
        true
    }

    /// Is `cl` RUP w.r.t. the current clause set? (Does not add it.)
    pub fn is_rup(&mut self, cl: &[i32]) -> bool {
        if self.root_conflict {
            return true;
        }
        for &l in cl {
            self.grow(l);
        }
        let mark = self.trail.len();
        let mut conflict = false;
        for &l in cl {
            match self.value(l) {
                1 => {
                    conflict = true; // literal true at root: the clause is satisfied, trivially implied
                    break;
                }
                -1 => {}
                _ => self.set(-l),
            }
        }
        if !conflict {
            conflict = !self.propagate(mark);
        }
        for k in (mark..self.trail.len()).rev() {
            let l = self.trail[k];
            self.assign[l.unsigned_abs() as usize] = 0;
        }
        self.trail.truncate(mark);
        conflict
    }

    /// Check one lemma and add it on success.
    pub fn check_and_add(&mut self, cl: &[i32]) -> bool {
        self.lemmas_checked += 1;
        if !self.is_rup(cl) {
            return false;
        }
        self.add(cl);
        true
    }

    /// Add a clause justified outside RUP (e.g. a checked symmetric image).
    pub fn check_and_add_unchecked(&mut self, cl: &[i32]) {
        self.add(cl);
    }

    pub fn proved_unsat(&self) -> bool {
        self.root_conflict
    }
}

/// Independent LRAT checker with antecedent hints: every lemma is checked by assigning its negation and running the
/// hinted clauses in order, each of which must become unit (its literal is assigned) or falsified (the check is done).
/// Linear in the proof size, unlike [`Checker::check_and_add`], which re-propagates over the whole database per lemma
/// (65x the solve time on a d=10 unit). Shares no code with the solver. Original clause i (0-based, in the order the
/// solver received them) has id i + 1, exactly as the solver numbers them (every `add_clause` call takes an id, even
/// for clauses it drops as satisfied or tautological).
/// Fx-style hasher for the clause-id map (ids are dense integers; SipHash cost dominated the checker).
#[derive(Default, Clone, Copy)]
pub struct IdHasher(u64);
impl std::hash::Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(5) ^ b as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}
type IdMap<V> = std::collections::HashMap<u64, V, std::hash::BuildHasherDefault<IdHasher>>;

pub struct HintChecker {
    db: IdMap<Vec<i32>>,
    val: Vec<i8>,
    trail: Vec<usize>,
    empty: bool,
    pub lemmas_checked: u64,
}

impl HintChecker {
    pub fn new(formula: &[Vec<i32>]) -> HintChecker {
        let mut db: IdMap<Vec<i32>> = IdMap::with_capacity_and_hasher(formula.len() * 2, Default::default());
        let mut maxv = 0usize;
        for (i, c) in formula.iter().enumerate() {
            maxv = maxv.max(c.iter().map(|l| l.unsigned_abs() as usize).max().unwrap_or(0));
            db.insert(i as u64 + 1, c.clone());
        }
        HintChecker { db, val: vec![0; maxv + 1], trail: Vec::new(), empty: false, lemmas_checked: 0 }
    }

    pub fn get(&self, id: u64) -> Option<&Vec<i32>> {
        self.db.get(&id)
    }

    pub fn proved_unsat(&self) -> bool {
        self.empty
    }

    /// Forget deleted clauses (LRAT `d` line). Strict: every id must be a known clause.
    pub fn delete(&mut self, ids: &[u64]) -> Result<(), String> {
        for id in ids {
            if self.db.remove(id).is_none() {
                return Err(format!("deletion of unknown clause id {id}"));
            }
        }
        Ok(())
    }

    /// Number of clauses currently held (originals plus live lemmas).
    pub fn live(&self) -> usize {
        self.db.len()
    }

    /// Check lemma `id` = `lits` by `hints`, and add it on success.
    pub fn check(&mut self, id: u64, lits: &[i32], hints: &[u64]) -> Result<(), String> {
        self.lemmas_checked += 1;
        if self.db.contains_key(&id) {
            return Err(format!("clause id {id} reused"));
        }
        for &l in lits {
            let v = l.unsigned_abs() as usize;
            if v == 0 {
                return Err("literal 0 in lemma".into());
            }
            if v >= self.val.len() {
                self.val.resize(v + 1, 0);
            }
        }
        let mut trail = std::mem::take(&mut self.trail);
        trail.clear();
        let mut conflict = false;
        for &l in lits {
            let v = l.unsigned_abs() as usize;
            let want: i8 = if l > 0 { -1 } else { 1 };
            if self.val[v] == -want {
                conflict = true; // tautology: trivially implied
                break;
            }
            if self.val[v] == 0 {
                self.val[v] = want;
                trail.push(v);
            }
        }
        let mut res: Result<(), String> = Ok(());
        if !conflict {
            for h in hints {
                let Some(hc) = self.db.get(h) else {
                    res = Err(format!("hint {h} is not a known clause"));
                    break;
                };
                let (mut nun, mut unassigned, mut sat) = (0, 0i32, false);
                for &l in hc {
                    let v = l.unsigned_abs() as usize;
                    let x = if v < self.val.len() { if l > 0 { self.val[v] } else { -self.val[v] } } else { 0 };
                    if x == 1 {
                        sat = true;
                        break;
                    }
                    if x == 0 {
                        nun += 1;
                        unassigned = l;
                    }
                }
                if sat {
                    res = Err(format!("hint {h} is satisfied"));
                    break;
                }
                if nun == 0 {
                    conflict = true;
                    break;
                }
                if nun > 1 {
                    res = Err(format!("hint {h} is not unit"));
                    break;
                }
                let v = unassigned.unsigned_abs() as usize;
                if v >= self.val.len() {
                    self.val.resize(v + 1, 0);
                }
                self.val[v] = if unassigned > 0 { 1 } else { -1 };
                trail.push(v);
            }
        }
        for &v in &trail {
            self.val[v] = 0;
        }
        self.trail = trail;
        res?;
        if !conflict {
            return Err("hints do not reach a conflict".into());
        }
        if lits.is_empty() {
            self.empty = true;
        }
        self.db.insert(id, lits.to_vec());
        Ok(())
    }

    /// Check every line of a solver LRAT log in order (image lines are rejected: no symmetry rule here).
    pub fn check_lines(&mut self, lines: &[crate::sat::solver::LratLine]) -> Result<(), String> {
        use crate::sat::solver::LratLine;
        for l in lines {
            match l {
                LratLine::Lemma { id, lits, hints } => self.check(*id, lits, hints).map_err(|e| format!("lemma {id} {lits:?}: {e}"))?,
                LratLine::Image { id, .. } => return Err(format!("line {id}: image lines are not accepted by the hint checker")),
                LratLine::Delete { ids } => self.delete(ids)?,
            }
        }
        Ok(())
    }
}

/// Check a whole lemma log (hint-free RUP); returns the lemmas (as parsed clauses) on success. Used by the tests.
#[allow(dead_code)]
pub fn check_log(nvars: usize, formula: &[Vec<i32>], log: &[i32]) -> Result<Vec<Vec<i32>>, String> {
    let mut ck = Checker::new(nvars, formula);
    let mut lemmas = Vec::new();
    let mut cur = Vec::new();
    for &x in log {
        if x == 0 {
            if !ck.check_and_add(&cur) {
                return Err(format!("lemma #{} {:?} is not RUP", lemmas.len() + 1, cur));
            }
            lemmas.push(std::mem::take(&mut cur));
        } else {
            cur.push(x);
        }
    }
    if !cur.is_empty() {
        return Err("lemma log truncated (missing terminating 0)".into());
    }
    Ok(lemmas)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::solver::{LratLine, SolveResult, Solver};

    #[test]
    fn solver_proofs_check() {
        // PHP 6->5 refutation logged by the solver must check
        let (p, h) = (6usize, 5usize);
        let x = |i: usize, j: usize| (i * h + j + 1) as i32;
        let mut f: Vec<Vec<i32>> = Vec::new();
        for i in 0..p {
            f.push((0..h).map(|j| x(i, j)).collect());
        }
        for j in 0..h {
            for a in 0..p {
                for b in a + 1..p {
                    f.push(vec![-x(a, j), -x(b, j)]);
                }
            }
        }
        let mut s = Solver::new(p * h);
        s.enable_proof();
        for c in &f {
            s.add_clause_dimacs(c);
        }
        assert_eq!(s.solve(&[]), SolveResult::Unsat);
        let log = s.proof.clone().unwrap();
        let lemmas = check_log(p * h, &f, &log).expect("proof must check");
        assert!(lemmas.last().unwrap().is_empty());
        // a corrupted lemma must be rejected
        let mut bad = log.clone();
        let pos = bad.iter().position(|&l| l != 0).unwrap();
        bad.insert(0, 0);
        bad.insert(0, -bad[pos + 1]);
        bad.insert(0, bad[pos + 2]);
        let _ = check_log(p * h, &f, &bad); // may or may not be RUP; the next test is the hard negative
        assert!(check_log(p * h, &f, &[x(0, 0), 0]).is_err());
    }

    #[test]
    fn streamed_proof_with_deletions() {
        // PHP 8->7 with frequent reductions: the LRAT log streams to a checker thread in chunks, carries deletion
        // lines, and the checker ends with the empty clause while holding far fewer clauses than were derived
        let (p, h) = (8usize, 7usize);
        let x = |i: usize, j: usize| (i * h + j + 1) as i32;
        let mut f: Vec<Vec<i32>> = Vec::new();
        for i in 0..p {
            f.push((0..h).map(|j| x(i, j)).collect());
        }
        for j in 0..h {
            for a in 0..p {
                for b in a + 1..p {
                    f.push(vec![-x(a, j), -x(b, j)]);
                }
            }
        }
        let mut s = Solver::new(p * h);
        s.lrat_enable();
        s.next_reduce = 100;
        let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<LratLine>>(4);
        s.lrat_sink = Some(tx);
        let cls = f.clone();
        let th = std::thread::spawn(move || {
            let mut ck = HintChecker::new(&cls);
            let (mut lemmas, mut deletes) = (0u64, 0u64);
            for chunk in rx {
                for l in &chunk {
                    match l {
                        LratLine::Lemma { .. } => lemmas += 1,
                        LratLine::Delete { ids } => deletes += ids.len() as u64,
                        LratLine::Image { .. } => {}
                    }
                }
                ck.check_lines(&chunk).expect("streamed proof must check");
            }
            (ck, lemmas, deletes)
        });
        for c in &f {
            s.add_clause_dimacs(c);
        }
        assert_eq!(s.solve(&[]), SolveResult::Unsat);
        assert!(s.stats.reductions > 0, "the test must trigger reductions");
        s.lrat_finish();
        let (ck, lemmas, deletes) = th.join().unwrap();
        assert!(ck.proved_unsat());
        assert!(deletes > 0, "no deletion lines were logged");
        assert!((ck.live() as u64) < f.len() as u64 + lemmas, "deleted clauses must leave the checker");
        assert!(s.lrat.as_ref().unwrap().is_empty(), "everything was flushed");
        // a deletion of an unknown id is rejected
        let mut ck2 = HintChecker::new(&f);
        assert!(ck2.delete(&[u64::MAX]).is_err());
    }

    #[test]
    fn hinted_proofs_check() {
        // PHP 7->6 under LRAT: every line checks by its hints; a wrong hint, a dropped hint and a forged lemma are rejected
        let (p, h) = (7usize, 6usize);
        let x = |i: usize, j: usize| (i * h + j + 1) as i32;
        let mut f: Vec<Vec<i32>> = Vec::new();
        for i in 0..p {
            f.push((0..h).map(|j| x(i, j)).collect());
        }
        for j in 0..h {
            for a in 0..p {
                for b in a + 1..p {
                    f.push(vec![-x(a, j), -x(b, j)]);
                }
            }
        }
        let mut s = Solver::new(p * h);
        s.lrat_enable();
        s.mode_switching = true;
        s.next_reduce = 100;
        for c in &f {
            s.add_clause_dimacs(c);
        }
        assert_eq!(s.solve(&[]), SolveResult::Unsat);
        let lines = s.lrat.clone().unwrap();
        let mut ck = HintChecker::new(&f);
        ck.check_lines(&lines).expect("hinted proof must check");
        assert!(ck.proved_unsat());
        // assumption cores carry hints too: PHP 6->6 (satisfiable) plus the unit ¬x(0,0); pigeons 1..4 in holes 1..4
        // and pigeon 5 kept out of hole 5 leaves pigeon 5 no hole (core by propagation); then an assumption that is
        // already false at the root (x(0,0)) at decision level > 0, whose core clause has the root unit as its hint
        let (p2, h2) = (6usize, 6usize);
        let y = |i: usize, j: usize| (i * h2 + j + 1) as i32;
        let mut f2: Vec<Vec<i32>> = Vec::new();
        for i in 0..p2 {
            f2.push((0..h2).map(|j| y(i, j)).collect());
        }
        for j in 0..h2 {
            for a in 0..p2 {
                for b in a + 1..p2 {
                    f2.push(vec![-y(a, j), -y(b, j)]);
                }
            }
        }
        f2.push(vec![-y(0, 0)]);
        let mut s2 = Solver::new(p2 * h2);
        s2.lrat_enable();
        for c in &f2 {
            s2.add_clause_dimacs(c);
        }
        let assume = [y(1, 1), y(2, 2), y(3, 3), y(4, 4), -y(5, 5), y(0, 1)];
        assert_eq!(s2.solve_dimacs(&assume), SolveResult::Unsat);
        let mut ck2 = HintChecker::new(&f2);
        ck2.check_lines(s2.lrat.as_ref().unwrap()).expect("core proof must check");
        let core = ck2.get(s2.last_lrat_id()).expect("core lemma stored").clone();
        assert!(!core.is_empty() && core.iter().all(|l| assume.contains(&-l)), "core {core:?}");
        assert_eq!(s2.solve_dimacs(&[y(1, 1), y(0, 0)]), SolveResult::Unsat);
        let n_before = ck2.lemmas_checked;
        ck2.check_lines(&s2.lrat.as_ref().unwrap()[(n_before as usize)..]).expect("root-false assumption core must check");
        assert_eq!(ck2.get(s2.last_lrat_id()), Some(&vec![-y(0, 0)]));
        // negatives
        let mut bad = HintChecker::new(&f);
        let mut lines_bad = lines.clone();
        if let crate::sat::solver::LratLine::Lemma { hints, .. } = &mut lines_bad[0] {
            hints.pop();
        }
        assert!(bad.check_lines(&lines_bad).is_err(), "dropped hint accepted");
        let mut bad2 = HintChecker::new(&f);
        assert!(bad2.check(10_000, &[x(0, 0)], &[1]).is_err(), "forged unit accepted");
    }

    #[test]
    fn vivified_proofs_check() {
        // PHP 8->7 is hard enough to trigger reductions and vivification; the log must still check
        let (p, h) = (8usize, 7usize);
        let x = |i: usize, j: usize| (i * h + j + 1) as i32;
        let mut f: Vec<Vec<i32>> = Vec::new();
        for i in 0..p {
            f.push((0..h).map(|j| x(i, j)).collect());
        }
        for j in 0..h {
            for a in 0..p {
                for b in a + 1..p {
                    f.push(vec![-x(a, j), -x(b, j)]);
                }
            }
        }
        let mut s = Solver::new(p * h);
        s.enable_proof();
        s.vivify_enabled = true;
        s.mode_switching = true;
        s.next_reduce = 100;
        for c in &f {
            s.add_clause_dimacs(c);
        }
        assert_eq!(s.solve(&[]), SolveResult::Unsat);
        assert!(s.viv_shortened > 0, "vivification never fired");
        let log = s.proof.clone().unwrap();
        let lemmas = check_log(p * h, &f, &log).expect("vivified proof must check");
        assert!(lemmas.last().unwrap().is_empty());
    }
}
