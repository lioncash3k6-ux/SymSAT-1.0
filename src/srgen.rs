//! Generator of SR (substitution redundancy) proof lines for the Ramsey degree argument.
//!
//! `R(k,l) <= R(k-1,l) + R(k,l-1)` as a clausal proof over F(s,t,n) (`full::full_clauses`), in the style of Heule's
//! 39-line SR proof of R(4,4) <= 18: inside a vertex set S that may contain no red K_k and no blue K_l (because the
//! context `ctx`, a set of literals, says every outer vertex is red resp. blue to all of S), pick v in S, sort v's
//! edges into S (SR lines "if (v,b) is red then (v,a) is red" with the vertex swap a <-> b as witness), and split on
//! the degree of v: its first R(k-1,l) sorted neighbours are red (recurse with k-1), or its last R(k,l-1) are blue
//! (recurse with l-1). Every line carries ¬ctx, so inner "without loss of generality" steps are conditional and the
//! whole argument stays in one database (no assumption sub-databases). The leaves are propagation lines (`id p`).
//!
//! `prove(K_n, s, t)` with n >= R(s,t) derives the empty clause (R(3,3) <= 6, R(3,4) <= 9, R(3,5) <= 14,
//! R(4,4) <= 18 are the tests). For R(4,5) at N = 25 (< 32) it derives the degree bounds of the gluing route: after
//! sorting vertex 0's 24 edges, `¬x(0,a_14)` (red degree <= 13, the R(3,5) <= 14 argument) and `x(0,a_7)` (red degree
//! >= 7: a blue degree >= 18 contradicts R(4,4) <= 18). Both are SR-tier clauses (they hold after the symmetry
//! breaking), exactly the assumption the per-unit lemmas of the gluing stages are stated under (red neighbours first).
//! The reference checker decides whether every proposed line is valid; the generator proves nothing by itself.

use crate::full::{evar, full_clauses, known_ramsey};

pub struct Gen {
    pub n: usize,
    pub lines: Vec<String>,
    next_id: u64,
    pub sr_lines: usize,
    pub prop_lines: usize,
}

impl Gen {
    pub fn new(s: usize, t: usize, n: usize) -> Gen {
        Gen { n, lines: vec![format!("c slrat {s} {t} {n}")], next_id: full_clauses(s, t, n).len() as u64, sr_lines: 0, prop_lines: 0 }
    }

    fn fmt(v: &[i32]) -> String {
        v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")
    }

    /// SR line: clause `lits`, witness literals (constants of σ), and the vertex permutation `pi` (pi[x] = image of
    /// x) on every edge variable not fixed by the witness
    fn sr_line(&mut self, lits: &[i32], witness: &[i32], pi: &[usize]) -> u64 {
        self.next_id += 1;
        let fixed: std::collections::HashSet<i32> = witness.iter().map(|l| l.unsigned_abs() as i32).collect();
        let mut pairs = Vec::new();
        for y in 1..self.n {
            for x in 0..y {
                let (e, img) = (evar(x, y), evar(pi[x], pi[y]));
                if e != img && !fixed.contains(&e) {
                    pairs.push(e);
                    pairs.push(img);
                }
            }
        }
        self.lines.push(format!("{} r {} 0 {} 0 {} 0", self.next_id, Gen::fmt(lits), Gen::fmt(witness), Gen::fmt(&pairs)));
        self.sr_lines += 1;
        self.next_id
    }

    fn prop(&mut self, lits: &[i32]) -> u64 {
        self.next_id += 1;
        self.lines.push(format!("{} p {} 0", self.next_id, Gen::fmt(lits)));
        self.prop_lines += 1;
        self.next_id
    }

    /// Derive the clause ¬ctx (as literals `neg_ctx`): the vertex set `s_set` (all red to the "red" context vertices
    /// and blue to the "blue" ones, so it contains no red K_k and no blue K_l) has at least R(k,l) vertices.
    pub fn prove(&mut self, k: usize, l: usize, s_all: &[usize], neg_ctx: &[i32]) {
        let r_kl = known_ramsey(k, l).expect("Ramsey number needed by the recursion is unknown");
        assert!(s_all.len() >= r_kl, "set of {} vertices cannot force R({k},{l}) = {r_kl}", s_all.len());
        let s_set = &s_all[..r_kl];
        if k <= 2 || l <= 2 {
            // k = 2: every edge of S is forced blue by the red context, and |S| >= l gives a falsified blue clause
            // (symmetrically for l = 2): pure propagation
            self.prop(neg_ctx);
            return;
        }
        if (k, l) == (4, 3) || (k, l) == (3, 4) {
            // R(3,4) = 9 < R(2,4) + R(3,3) = 10: the recursion needs the parity argument, which unit propagation
            // cannot do; use Heule's hand-made case analysis instead
            self.template_43(s_set, neg_ctx, k == 3);
            return;
        }
        let v = s_set[0];
        let rest: Vec<usize> = s_set[1..].to_vec();
        // sort v's edges into `rest`: reds first (if (v, rest[i+1]) is red then (v, rest[i]) is red)
        self.sort_edges(v, &rest, neg_ctx, false);
        let r_red = known_ramsey(k - 1, l).unwrap();
        let r_blue = known_ramsey(k, l - 1).unwrap();
        assert!(rest.len() >= r_red + r_blue - 1, "R({k},{l}) < R({},{l}) + R({k},{}): parity case not supported here", k - 1, l - 1);
        // red case: (v, rest[r_red-1]) red => rest[0..r_red] all red to v => no red K_{k-1}, no blue K_l there
        let red_set: Vec<usize> = rest[..r_red].to_vec();
        let mut red_ctx = neg_ctx.to_vec();
        red_ctx.push(-evar(v, rest[r_red - 1]));
        for &u in &red_set[..r_red - 1] {
            red_ctx.push(-evar(v, u)); // implied by the sorting chain; kept explicit so the leaf propagation is local
        }
        self.prove(k - 1, l, &red_set, &red_ctx);
        // the chain makes the shorter clause ¬ctx ∨ ¬(v, rest[r_red-1]) propagate
        let mut red_short = neg_ctx.to_vec();
        red_short.push(-evar(v, rest[r_red - 1]));
        self.prop(&red_short);
        // blue case: (v, rest[r_red-1]) blue => rest[r_red-1..] all blue to v; the last r_blue of them
        let blue_set: Vec<usize> = rest[rest.len() - r_blue..].to_vec();
        let mut blue_ctx = neg_ctx.to_vec();
        for &u in &blue_set {
            blue_ctx.push(evar(v, u));
        }
        self.prove(k, l - 1, &blue_set, &blue_ctx);
        // ¬ctx: the red case is excluded, so (v, rest[r_red-1]) is blue, the chain makes the last r_blue blue, and
        // the blue-case clause closes
        self.prop(neg_ctx);
    }

    /// sort v's edges into `rest` (consecutive pairs; `flip`: blues first instead of reds first), all under ¬ctx
    fn sort_edges(&mut self, v: usize, q: &[usize], neg_ctx: &[i32], flip: bool) {
        // line i: C = (v,q[i+1]) first-colour -> (v,q[i]) first-colour. Witness (Heule): position 0 := first colour,
        // position i+1 := the other colour; permutation: q[0] -> q[i+1], q[j+1] -> q[j] for j <= i (insert the new
        // vertex at the front of the sorted prefix, which keeps the earlier sorting clauses satisfied)
        let sg = if flip { -1 } else { 1 };
        for i in 0..q.len() - 1 {
            let mut c = vec![sg * evar(v, q[i]), -sg * evar(v, q[i + 1])];
            c.extend_from_slice(neg_ctx);
            let witness = [sg * evar(v, q[0]), -sg * evar(v, q[i + 1])];
            let mut pi: Vec<usize> = (0..self.n).collect();
            pi[q[0]] = q[i + 1];
            for j in 0..=i {
                pi[q[j + 1]] = q[j];
            }
            self.sr_line(&c, &witness, &pi);
        }
    }

    /// R(4,3) <= 9 on the nine vertices p[0..9] (no red K4, no blue K3 under the context), transcribed from lines
    /// 18-39 of Heule's SR proof of R(4,4) <= 18 (his vertices 2..10 = p[0..9], his vertex 1 = the context):
    /// sort p0; p0 has >= 5 red neighbours (p1..p5); sort p1 over p2..p5; p1 has exactly 2 red there (p2, p3);
    /// sort p2 over p4, p5: (p2,p4) red; p0 has exactly 5 red (p6 blue); sort p1 over p6..p8: (p1,p7) red;
    /// (p2,p6) red; contradiction. `flip` gives the colour mirror R(3,4) <= 9 (no red K3, no blue K4).
    fn template_43(&mut self, p: &[usize], neg_ctx: &[i32], flip: bool) {
        assert_eq!(p.len(), 9);
        let sg = if flip { -1 } else { 1 };
        let e = |a: usize, b: usize| sg * evar(p[a], p[b]);
        let with_ctx = |lits: &[i32]| {
            let mut c = lits.to_vec();
            c.extend_from_slice(neg_ctx);
            c
        };
        self.sort_edges(p[0], &p[1..], neg_ctx, flip);
        self.prop(&with_ctx(&[e(0, 5)]));
        self.sort_edges(p[1], &p[2..6], neg_ctx, flip);
        self.prop(&with_ctx(&[-e(1, 4)]));
        self.prop(&with_ctx(&[e(1, 3)]));
        self.sort_edges(p[2], &p[4..6], neg_ctx, flip);
        self.prop(&with_ctx(&[e(2, 4)]));
        self.prop(&with_ctx(&[-e(0, 6), -e(1, 6)]));
        self.prop(&with_ctx(&[-e(0, 6)]));
        self.sort_edges(p[1], &p[6..9], neg_ctx, flip);
        self.prop(&with_ctx(&[e(1, 7)]));
        self.prop(&with_ctx(&[e(2, 6)]));
        self.prop(neg_ctx);
    }

    /// The R(4,5)-route degree bounds for vertex 0 of K_n (n < R(s,t)): sort vertex 0's edges, then derive
    /// "red degree <= R(s-1,t) - 1" and "red degree >= n - R(s,t-1)". Returns the two clause ids.
    pub fn degree_bounds(&mut self, s: usize, t: usize) -> (u64, u64) {
        let n = self.n;
        let others: Vec<usize> = (1..n).collect();
        self.sort_edges(0, &others, &[], false);
        let r_red = known_ramsey(s - 1, t).unwrap();
        let r_blue = known_ramsey(s, t - 1).unwrap();
        assert!(n - 1 >= r_red && n - 1 >= r_blue);
        // red degree >= r_red: vertices 1..=r_red red to 0 form a red-K_{s-1}-free, blue-K_t-free set
        let red_set: Vec<usize> = others[..r_red].to_vec();
        let red_ctx: Vec<i32> = red_set.iter().map(|&u| -evar(0, u)).collect();
        self.prove(s - 1, t, &red_set, &red_ctx);
        let hi = self.prop(&[-evar(0, others[r_red - 1])]);
        // blue degree >= r_blue: the last r_blue vertices blue to 0
        let blue_set: Vec<usize> = others[others.len() - r_blue..].to_vec();
        let blue_ctx: Vec<i32> = blue_set.iter().map(|&u| evar(0, u)).collect();
        self.prove(s, t - 1, &blue_set, &blue_ctx);
        let lo = self.prop(&[evar(0, others[others.len() - r_blue])]);
        (hi, lo)
    }

    pub fn text(&self) -> String {
        self.lines.join("\n") + "\n"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::full::check_slrat_last;

    fn refute(s: usize, t: usize, n: usize) -> (usize, usize) {
        let mut g = Gen::new(s, t, n);
        let all: Vec<usize> = (0..n).collect();
        g.prove(s, t, &all, &[]);
        let (empty, _, pure) = check_slrat_last(&g.text()).unwrap_or_else(|e| panic!("R({s},{t}) <= {n}: {e}"));
        assert!(empty && !pure);
        (g.sr_lines, g.prop_lines)
    }

    #[test]
    fn sr_degree_argument_refutes_small_ramsey() {
        assert_eq!(refute(3, 3, 6), (4, 4));
        refute(3, 4, 9);
        refute(4, 3, 9);
        refute(3, 5, 14);
    }

    #[test]
    fn sr_degree_argument_r44_18() {
        let (sr, p) = refute(4, 4, 18);
        assert!(sr + p < 200, "{sr} SR + {p} propagation lines");
    }

    #[test]
    fn sr_degree_bounds_r45_25() {
        let mut g = Gen::new(4, 5, 25);
        let (hi, lo) = g.degree_bounds(4, 5);
        let (empty, last, pure) = check_slrat_last(&g.text()).unwrap();
        assert!(!empty && !pure);
        assert_eq!(last.unwrap(), vec![evar(0, 7)]);
        assert!(hi < lo);
        // the clause "red degree <= 13" is ¬x(0,14)
        assert!(g.text().contains(&format!("{hi} p {} 0", -evar(0, 14))));
    }
}
