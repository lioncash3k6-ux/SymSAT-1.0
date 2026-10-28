//! CNF encodings for gluing R(s,t) on N = 1 + d + m vertices.
//!
//! Vertex v; A = red neighbourhood of v, an (s-1,t)-good graph on d vertices; B = blue neighbourhood, an
//! (s,t-1)-good graph on m vertices. Cross variable x(a,b) = 1 + a*m + b is TRUE iff edge a-b is red.
//!
//! * [`pair_clauses`] is a line-for-line port of the repo's trusted `v6/scripts/encode.py` (same clauses, same
//!   order, same literal order), so its DIMACS output can be byte-compared against the Python encoder.
//! * [`Stream`] is the "memory" formula: one side is fixed, the other side's edges become variables
//!   e(i,j) (TRUE = red). Fixing those edge variables by assumptions to a catalogue graph G reduces it to exactly
//!   F(A,B) plus clauses satisfied by G. This is the extreme Gauthier-Brown generalisation (every edge of the
//!   streamed side is gray); [`glue_check`] proves that reduction pair by pair instead of trusting it.

use crate::graph::Graph;
use std::collections::HashMap;

pub type Clause = Vec<i32>;

#[inline]
pub fn xvar(a: usize, b: usize, m: usize) -> i32 {
    (1 + a * m + b) as i32
}

fn bits(mut x: u32) -> impl Iterator<Item = usize> {
    std::iter::from_fn(move || {
        if x == 0 {
            None
        } else {
            let u = x.trailing_zeros() as usize;
            x &= x - 1;
            Some(u)
        }
    })
}

/// The pair CNF F(A,B), exactly as encode.py builds it.
pub fn pair_clauses(s: usize, t: usize, a: &Graph, b: &Graph) -> Vec<Clause> {
    let (d, m) = (a.n, b.n);
    let mut out = Vec::new();
    for (red, k, sign) in [(true, s, -1i32), (false, t, 1i32)] {
        for i in 1..k {
            let ka = a.sets(i, red);
            if ka.is_empty() {
                continue;
            }
            let cb = b.sets(k - i, red);
            for &kk in &ka {
                for &cc in &cb {
                    let mut cl = Vec::with_capacity(i * (k - i));
                    for x in bits(kk) {
                        for y in bits(cc) {
                            cl.push(sign * xvar(x, y, m));
                        }
                    }
                    out.push(cl);
                }
            }
        }
    }
    let _ = d;
    out
}

pub fn to_dimacs(nvars: usize, clauses: &[Clause]) -> String {
    let mut s = format!("p cnf {} {}\n", nvars, clauses.len());
    for c in clauses {
        for l in c {
            s.push_str(&l.to_string());
            s.push(' ');
        }
        s.push_str("0\n");
    }
    s
}

/// Which side's edges are streamed (turned into variables fixed by assumptions).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    A,
    B,
}

/// Index of edge (i,j), i<j, among the C(n,2) edges of an n-vertex graph, column-major (graph6 order:
/// (0,1),(0,2),(1,2),(0,3),...). Catalogue graphs built by vertex extension share their low-vertex edges with
/// their neighbours in the file, so this order lets consecutive assumption sets share long prefixes (trail reuse).
#[inline]
pub fn edge_index(i: usize, j: usize, n: usize) -> usize {
    debug_assert!(i < j && j < n);
    let _ = n;
    j * (j - 1) / 2 + i
}

/// The streamed formula for one fixed graph.
pub struct Stream {
    pub s: usize,
    pub t: usize,
    pub d: usize,
    pub m: usize,
    pub side: Side,
    /// number of vertices on the streamed side
    pub ns: usize,
    /// first edge variable (edge variables are evar0 .. evar0 + C(ns,2) - 1)
    pub evar0: i32,
    pub nvars: usize,
    pub clauses: Vec<Clause>,
}

impl Stream {
    /// `fixed` is the fixed graph (A if side == B, B if side == A); `ns` the streamed side's vertex count.
    pub fn build(s: usize, t: usize, fixed: &Graph, ns: usize, side: Side) -> Stream {
        let (d, m) = match side {
            Side::B => (fixed.n, ns),
            Side::A => (ns, fixed.n),
        };
        let evar0 = (d * m + 1) as i32;
        let nedges = ns * ns.saturating_sub(1) / 2;
        let ev = |i: usize, j: usize| -> i32 {
            let (i, j) = if i < j { (i, j) } else { (j, i) };
            evar0 + edge_index(i, j, ns) as i32
        };
        let all_subsets = |n: usize, k: usize| -> Vec<u32> {
            // every k-subset of an n-set, lexicographic
            let mut out = Vec::new();
            fn rec(n: usize, k: usize, start: usize, cur: u32, out: &mut Vec<u32>) {
                if cur.count_ones() as usize == k {
                    out.push(cur);
                    return;
                }
                for u in start..n {
                    rec(n, k, u + 1, cur | 1 << u, out);
                }
            }
            rec(n, k, 0, 0, &mut out);
            out
        };
        let mut clauses = Vec::new();
        for (red, k, sign) in [(true, s, -1i32), (false, t, 1i32)] {
            for i in 1..k {
                // i vertices from A, k-i from B
                let (sa, sb): (Vec<u32>, Vec<u32>) = match side {
                    Side::B => (fixed.sets(i, red), all_subsets(m, k - i)),
                    Side::A => (all_subsets(d, i), fixed.sets(k - i, red)),
                };
                if sa.is_empty() || sb.is_empty() {
                    continue;
                }
                for &ka in &sa {
                    for &cb in &sb {
                        let mut cl = Vec::new();
                        for x in bits(ka) {
                            for y in bits(cb) {
                                cl.push(sign * xvar(x, y, m));
                            }
                        }
                        // streamed-side guard: the clause only bites if that subset has colour `red` throughout
                        let free = if side == Side::B { cb } else { ka };
                        let fv: Vec<usize> = bits(free).collect();
                        for p in 0..fv.len() {
                            for q in p + 1..fv.len() {
                                cl.push(sign * ev(fv[p], fv[q]));
                            }
                        }
                        clauses.push(cl);
                    }
                }
            }
        }
        // the streamed graph itself must be good: A is (s-1,t)-good, B is (s,t-1)-good
        let (ks, kt) = match side {
            Side::A => (s - 1, t),
            Side::B => (s, t - 1),
        };
        for (k, sign) in [(ks, -1i32), (kt, 1i32)] {
            if k > ns || k < 2 {
                continue;
            }
            for sub in all_subsets(ns, k) {
                let fv: Vec<usize> = bits(sub).collect();
                let mut cl = Vec::new();
                for p in 0..fv.len() {
                    for q in p + 1..fv.len() {
                        cl.push(sign * ev(fv[p], fv[q]));
                    }
                }
                clauses.push(cl);
            }
        }
        Stream { s, t, d, m, side, ns, evar0, nvars: d * m + nedges, clauses }
    }

    pub fn nedges(&self) -> usize {
        self.ns * self.ns.saturating_sub(1) / 2
    }

    /// DIMACS literals fixing the edge variables to graph `g` (the streamed-side catalogue graph).
    pub fn assumptions(&self, g: &Graph, out: &mut Vec<i32>) {
        out.clear();
        debug_assert_eq!(g.n, self.ns);
        for j in 1..self.ns {
            for i in 0..j {
                let v = self.evar0 + edge_index(i, j, self.ns) as i32;
                out.push(if g.has_edge(i, j) { v } else { -v });
            }
        }
    }
}

/// Soundness check of the stream reduction for one pair (the v10 glue lemma, specialised): with rho = the
/// edge-variable values of the streamed graph `g`, every stream clause must be satisfied by rho or, after deleting
/// its rho-false edge literals, be literally a clause of the independently built F(A,B). Then any model M of F(A,B)
/// extends to the model (M, rho) of the stream formula, so "stream UNSAT under rho" implies "F(A,B) UNSAT".
pub fn glue_check(st: &Stream, fixed: &Graph, g: &Graph) -> Result<usize, String> {
    let (a, b) = match st.side {
        Side::B => (fixed, g),
        Side::A => (g, fixed),
    };
    let mut pair: Vec<Clause> = pair_clauses(st.s, st.t, a, b);
    for c in pair.iter_mut() {
        c.sort_unstable();
    }
    let set: std::collections::HashSet<Clause> = pair.into_iter().collect();
    let mut rho = Vec::new();
    st.assumptions(g, &mut rho);
    let val = |l: i32| -> Option<bool> {
        let v = l.unsigned_abs() as i32;
        if v < st.evar0 {
            return None;
        }
        let a = rho[(v - st.evar0) as usize];
        Some((a > 0) == (l > 0))
    };
    let mut reduced_hits = 0usize;
    for c in &st.clauses {
        if c.iter().any(|&l| val(l) == Some(true)) {
            continue;
        }
        let mut r: Clause = c.iter().copied().filter(|&l| val(l).is_none()).collect();
        r.sort_unstable();
        if !set.contains(&r) {
            return Err(format!("stream clause {c:?} reduces to {r:?}, which is not a clause of F(A,B)"));
        }
        reduced_hits += 1;
    }
    Ok(reduced_hits)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edge_index_dense() {
        let n = 9;
        let mut k = 0;
        for j in 1..n {
            for i in 0..j {
                assert_eq!(edge_index(i, j, n), k);
                k += 1;
            }
        }
    }
}

/// Degree window [lo, hi] for the red degree of EVERY vertex of an (s,t)-good colouring of K_N: the red
/// neighbourhood is (s-1,t)-good and the blue one (s,t-1)-good, so deg <= max{n : (s-1,t)-good graph on n exists}
/// and N-1-deg <= max{n : (s,t-1)-good graph on n exists}. This is the lemma the degree route itself rests on.
pub fn degree_window(s: usize, t: usize, n: usize) -> Option<(usize, usize)> {
    let maxn = |a: usize, b: usize| -> Option<usize> {
        let mut best = None;
        for k in 0..=64 {
            match crate::catalog::mckay_count(a, b, k) {
                Some(0) => {}
                Some(_) => best = Some(k),
                None => return None,
            }
        }
        best
    };
    let hi = maxn(s - 1, t)?;
    let blue = maxn(s, t - 1)?;
    let lo = (n - 1).saturating_sub(blue);
    Some((lo, hi.min(n - 1)))
}

/// Sinz sequential counter: clauses forcing at most `k` of `lits` true, fresh variables from `*next`.
pub fn at_most(lits: &[i32], k: usize, next: &mut i32, out: &mut Vec<Clause>) {
    let n = lits.len();
    if k >= n {
        return;
    }
    if k == 0 {
        for &l in lits {
            out.push(vec![-l]);
        }
        return;
    }
    // s[i][j] (i < n-1, j < k): at least j+1 of lits[0..=i] are true
    let base = *next;
    *next += ((n - 1) * k) as i32;
    let s = |i: usize, j: usize| base + (i * k + j) as i32;
    out.push(vec![-lits[0], s(0, 0)]);
    for j in 1..k {
        out.push(vec![-s(0, j)]);
    }
    for i in 1..n - 1 {
        out.push(vec![-lits[i], s(i, 0)]);
        out.push(vec![-s(i - 1, 0), s(i, 0)]);
        for j in 1..k {
            out.push(vec![-lits[i], -s(i - 1, j - 1), s(i, j)]);
            out.push(vec![-s(i - 1, j), s(i, j)]);
        }
        out.push(vec![-lits[i], -s(i - 1, k - 1)]);
    }
    out.push(vec![-lits[n - 1], -s(n - 2, k - 1)]);
}

/// Clauses (with fresh variables) forcing lo <= #true(lits) <= hi. An infeasible window yields the empty clause.
pub fn card_window(lits: &[i32], lo: isize, hi: isize, next: &mut i32, out: &mut Vec<Clause>) {
    let n = lits.len() as isize;
    if lo > n || hi < 0 || lo > hi {
        out.push(vec![]);
        return;
    }
    if hi < n {
        at_most(lits, hi.max(0) as usize, next, out);
    }
    if lo > 0 {
        let neg: Vec<i32> = lits.iter().map(|&l| -l).collect();
        at_most(&neg, (n - lo) as usize, next, out);
    }
}

/// `at_most` whose bound only applies when `guard` is true (the overflow clauses get ¬guard); the counter variables
/// themselves are definitions and stay unconditional.
fn at_most_if(lits: &[i32], k: usize, guard: Option<i32>, next: &mut i32, out: &mut Vec<Clause>) {
    let n = lits.len();
    if k >= n {
        return;
    }
    let overflow = |mut c: Clause| {
        if let Some(g) = guard {
            c.push(-g);
        }
        c
    };
    if k == 0 {
        for &l in lits {
            out.push(overflow(vec![-l]));
        }
        return;
    }
    // same sequential counter as `at_most`: s(i, j) = at least j+1 of lits[0..=i] are true
    let base = *next;
    *next += ((n - 1) * k) as i32;
    let s = |i: usize, j: usize| base + (i * k + j) as i32;
    out.push(vec![-lits[0], s(0, 0)]);
    for j in 1..k {
        out.push(vec![-s(0, j)]);
    }
    for i in 1..n - 1 {
        out.push(vec![-lits[i], s(i, 0)]);
        out.push(vec![-s(i - 1, 0), s(i, 0)]);
        for j in 1..k {
            out.push(vec![-lits[i], -s(i - 1, j - 1), s(i, j)]);
            out.push(vec![-s(i - 1, j), s(i, j)]);
        }
        out.push(overflow(vec![-lits[i], -s(i - 1, k - 1)]));
    }
    out.push(overflow(vec![-lits[n - 1], -s(n - 2, k - 1)]));
}

/// A term of a common-neighbourhood count in a pair formula: a constant or a literal (cross variable or its negation).
#[derive(Clone, Copy)]
enum Term {
    Const(bool),
    Lit(i32),
}

impl Term {
    fn and(self, o: Term, aux: &mut HashMap<(i32, i32), i32>, next: &mut i32, out: &mut Vec<Clause>) -> Term {
        match (self, o) {
            (Term::Const(false), _) | (_, Term::Const(false)) => Term::Const(false),
            (Term::Const(true), x) | (x, Term::Const(true)) => x,
            (Term::Lit(x), Term::Lit(y)) => {
                let key = (x.min(y), x.max(y));
                if key.0 == -key.1 {
                    return Term::Const(false);
                }
                if key.0 == key.1 {
                    return Term::Lit(x);
                }
                Term::Lit(*aux.entry(key).or_insert_with(|| {
                    // z is forced true when x and y are; a spuriously true z only tightens the count, so projecting
                    // onto the original variables the bound is exactly the one on x ∧ y
                    let z = *next;
                    *next += 1;
                    out.push(vec![-x, -y, z]);
                    z
                }))
            }
        }
    }
}

/// Book axioms (rooted lemmas with two roots) for a pair formula, from the lemma library's general rooted lemmas:
/// for vertices u ≠ v of the glued colouring (vertex 0, A red to it, B blue to it, cross edges x(a,b) = red),
///   uv red  -> at most R(s-2, t) - 1 common red neighbours,
///   uv blue -> at most R(s, t-2) - 1 common blue neighbours,
///   always  -> at most R(s-1, t-1) - 1 vertices red to u and blue to v,
/// because those common neighbourhoods must be (s-2,t)-, (s,t-2)- and (s-1,t-1)-good. Pairs with vertex 0 are already
/// implied by the catalogue graphs. All implied by F (each is a proved lemma of the library), so adding them is sound.
pub fn pair_book_axioms(s: usize, t: usize, a: &Graph, b: &Graph, next: &mut i32) -> Vec<Clause> {
    let (d, m) = (a.n, b.n);
    let mut out = Vec::new();
    let mut aux: HashMap<(i32, i32), i32> = HashMap::new();
    let bound = |p: usize, q: usize| crate::full::known_ramsey(p, q).map(|r| r - 1);
    let (k_rr, k_bb, k_rb) = (bound(s - 2, t), bound(s, t - 2), bound(s - 1, t - 1));
    // vertices: 0 = vertex 0, 1..=d = A, d+1..=d+m = B; colour of each pair as a term (true = red)
    let red = |u: usize, v: usize| -> Term {
        let (u, v) = (u.min(v), u.max(v));
        match (u, v) {
            (0, w) => Term::Const(w <= d),
            (x, y) if y <= d => Term::Const(a.adj[x - 1] >> (y - 1) & 1 == 1),
            (x, y) if x > d => Term::Const(b.adj[x - 1 - d] >> (y - 1 - d) & 1 == 1),
            (x, y) => Term::Lit(xvar(x - 1, y - 1 - d, m)),
        }
    };
    let not = |t: Term| match t {
        Term::Const(c) => Term::Const(!c),
        Term::Lit(l) => Term::Lit(-l),
    };
    let nv = 1 + d + m;
    for u in 1..nv {
        for v in u + 1..nv {
            let edge = red(u, v);
            // (roots' colour test for w, bound, guard): red-red | edge red, blue-blue | edge blue, red-u blue-v, red-v blue-u
            let kinds: [(bool, bool, Option<usize>, Option<Term>); 4] = [
                (true, true, k_rr, Some(edge)),
                (false, false, k_bb, Some(not(edge))),
                (true, false, k_rb, None),
                (false, true, k_rb, None),
            ];
            for (ru, rv, k, guard) in kinds {
                let Some(k) = k else { continue };
                let guard = match guard {
                    Some(Term::Const(false)) => continue, // the root edge has the other colour
                    Some(Term::Const(true)) | None => None,
                    Some(Term::Lit(l)) => Some(l),
                };
                let mut lits = Vec::new();
                let mut fixed = 0usize;
                for w in 0..nv {
                    if w == u || w == v {
                        continue;
                    }
                    let cu = if ru { red(u, w) } else { not(red(u, w)) };
                    let cv = if rv { red(v, w) } else { not(red(v, w)) };
                    match cu.and(cv, &mut aux, next, &mut out) {
                        Term::Const(true) => fixed += 1,
                        Term::Const(false) => {}
                        Term::Lit(l) => lits.push(l),
                    }
                }
                if fixed > k {
                    out.push(guard.map_or(vec![], |g| vec![-g])); // the fixed part alone breaks the bound
                    continue;
                }
                at_most_if(&lits, k - fixed, guard, next, &mut out);
            }
        }
    }
    out
}

/// Degree axioms for a pair: every vertex of A and B has red degree in [lo, hi] in the glued colouring.
/// a in A: deg = 1 (v) + deg_A(a) + #red cross(a,.); b in B: deg = deg_B(b) + #red cross(.,b) (v is blue to B).
pub fn pair_degree_axioms(a: &Graph, b: &Graph, lo: usize, hi: usize, next: &mut i32) -> Vec<Clause> {
    let (d, m) = (a.n, b.n);
    let mut out = Vec::new();
    for x in 0..d {
        let lits: Vec<i32> = (0..m).map(|y| xvar(x, y, m)).collect();
        let base = 1 + a.adj[x].count_ones() as isize;
        card_window(&lits, lo as isize - base, hi as isize - base, next, &mut out);
    }
    for y in 0..m {
        let lits: Vec<i32> = (0..d).map(|x| xvar(x, y, m)).collect();
        let base = b.adj[y].count_ones() as isize;
        card_window(&lits, lo as isize - base, hi as isize - base, next, &mut out);
    }
    out
}

#[cfg(test)]
mod card_tests {
    use super::*;
    #[test]
    fn card_window_exact() {
        // brute force: for n=5 all windows, the encoding's projection must be exactly the window
        for lo in 0..=6isize {
            for hi in -1..=5isize {
                let lits: Vec<i32> = (1..=5).collect();
                let mut next = 6;
                let mut cl = Vec::new();
                card_window(&lits, lo, hi, &mut next, &mut cl);
                for x in 0u32..32 {
                    let cnt = x.count_ones() as isize;
                    let want = lo <= cnt && cnt <= hi;
                    let mut sv = crate::sat::solver::Solver::new(next as usize);
                    let mut ok = true;
                    for c in &cl {
                        ok &= sv.add_clause_dimacs(c);
                    }
                    let assume: Vec<i32> = (1..=5).map(|v| if x >> (v - 1) & 1 == 1 { v } else { -v }).collect();
                    let got = ok && sv.solve_dimacs(&assume) == crate::sat::solver::SolveResult::Sat;
                    assert_eq!(got, want, "lo={lo} hi={hi} x={x:05b}");
                }
            }
        }
    }
    #[test]
    fn r45_window() {
        assert_eq!(degree_window(4, 5, 25), Some((7, 13)));
        assert_eq!(degree_window(4, 4, 18), Some((9, 8)));
    }
}

#[cfg(test)]
mod book_tests {
    use super::*;
    use crate::sat::solver::{SolveResult, Solver};

    /// All graphs on n vertices that are (p,q)-good (no red K_p, no blue K_q; red = adjacency), by brute force.
    fn good_graphs(n: usize, p: usize, q: usize) -> Vec<Graph> {
        let pairs: Vec<(usize, usize)> = (1..n).flat_map(|j| (0..j).map(move |i| (i, j))).collect();
        let mut out = Vec::new();
        for mask in 0..(1u64 << pairs.len()) {
            let mut g = Graph::empty(n);
            for (k, &(i, j)) in pairs.iter().enumerate() {
                if mask >> k & 1 == 1 {
                    g.adj[i] |= 1 << j;
                    g.adj[j] |= 1 << i;
                }
            }
            if g.sets(p, true).is_empty() && g.sets(q, false).is_empty() {
                out.push(g);
            }
        }
        out
    }

    fn solve(cls: &[Clause], nv: usize) -> SolveResult {
        let mut s = Solver::new(nv);
        for c in cls {
            s.add_clause_dimacs(c);
        }
        s.solve_dimacs(&[])
    }

    /// Book axioms are implied by the pair formula: every pair's satisfiability is unchanged, on instances with both
    /// SAT and UNSAT pairs (R(3,4) at N = 8 and 9, R(3,5) at N = 12..14), including conditional bounds on cross edges.
    #[test]
    fn book_axioms_preserve_satisfiability() {
        let mut seen = (0, 0);
        for (s, t, n) in [(3usize, 4usize, 8usize), (3, 4, 9), (3, 5, 12), (3, 5, 13), (3, 5, 14)] {
            for d in 1..n - 1 {
                let m = n - 1 - d;
                if m > 7 || d > 7 {
                    continue; // brute-force graph enumeration stays small
                }
                let (ga, gb) = (good_graphs(d, s - 1, t), good_graphs(m, s, t - 1));
                for a in ga.iter().take(4) {
                    for b in gb.iter().step_by((gb.len() / 6).max(1)).take(6) {
                        let base = pair_clauses(s, t, a, b);
                        let nv = d * m;
                        let mut next = nv as i32 + 1;
                        let mut with = base.clone();
                        with.extend(pair_book_axioms(s, t, a, b, &mut next));
                        let (r0, r1) = (solve(&base, nv), solve(&with, (next - 1) as usize));
                        assert_eq!(r0, r1, "R({s},{t}) N={n} d={d}: book axioms changed the result");
                        if r0 == SolveResult::Sat {
                            seen.0 += 1;
                        } else {
                            seen.1 += 1;
                        }
                    }
                }
            }
        }
        assert!(seen.0 > 0 && seen.1 > 0, "need both SAT and UNSAT pairs, got {seen:?}");
    }

    /// Exact projection check on small pairs: EVERY cross-edge assignment that satisfies the pair formula extends to a
    /// model of the formula plus the book axioms (they exclude no valid colouring), conditional bounds included.
    #[test]
    fn book_axioms_exclude_no_colouring() {
        let mut models = 0;
        for (s, t, n) in [(3usize, 4usize, 8usize), (3, 4, 7), (3, 5, 10), (3, 5, 11), (4, 4, 9)] {
            for d in 1..n - 1 {
                let m = n - 1 - d;
                if d * m > 12 || m > 7 || d > 7 {
                    continue;
                }
                let (ga, gb) = (good_graphs(d, s - 1, t), good_graphs(m, s, t - 1));
                for a in ga.iter().take(3) {
                    for b in gb.iter().take(3) {
                        let base = pair_clauses(s, t, a, b);
                        let nv = d * m;
                        let mut next = nv as i32 + 1;
                        let books = pair_book_axioms(s, t, a, b, &mut next);
                        for x in 0..(1u32 << nv) {
                            let lit = |v: usize| if x >> v & 1 == 1 { v as i32 + 1 } else { -(v as i32 + 1) };
                            let sat = base.iter().all(|c| c.iter().any(|&l| l == lit(l.unsigned_abs() as usize - 1)));
                            if !sat {
                                continue;
                            }
                            models += 1;
                            let mut sv = Solver::new((next - 1) as usize);
                            for c in base.iter().chain(books.iter()) {
                                sv.add_clause_dimacs(c);
                            }
                            let assumps: Vec<i32> = (0..nv).map(lit).collect();
                            assert_eq!(sv.solve_dimacs(&assumps), SolveResult::Sat, "R({s},{t}) N={n} d={d}: a valid colouring was excluded");
                        }
                    }
                }
            }
        }
        assert!(models > 0, "no models exercised");
    }
}
