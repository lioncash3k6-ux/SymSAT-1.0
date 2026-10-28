//! McKay–Radziszowski interval gluing (r45.pdf §3-4), as a MEASUREMENT first (no proof yet; RESULTS 2026-10-28,
//! "push in the DPLL direction"). Setting (R(4,5), degree 10): x is red to the vertices of G (a (3,5,9)-graph G'),
//! blue to those of H (a (4,4,14)-graph); vertex i of G gets a cone C_i ⊆ V_H (its red H-neighbours). A cone is
//! feasible if it covers no red triangle of H. The glued 24-vertex graph is (4,5)-good iff:
//!   K2: adjacent u,v in G: C_u ∩ C_v covers no edge of H;
//!   E_t: an independent t-set of G (t = 2,3,4) and an independent (5-t)-set of H missed by the union of the cones.
//! Intervals [B,T] of cones; collapsing rules (a)-(d) with H1/H2/H3 (set functions of H, tabulated over all 2^14
//! subsets); DFS over G's vertices, each taking an interval of the feasible-cone partition; splitting at the end.
//! Solutions = (4,5,24)-graphs; each is then extended by the deleted vertex v (red to x) with the §4 interval
//! algorithm over triangles and independent 4-sets of the 24-vertex graph; no extension = the pair is refuted.

use crate::graph::Graph;

const FULL14: u16 = (1 << 14) - 1;

pub struct HTables {
    n: usize,
    adj: Vec<u16>,
    nonadj: Vec<u16>,
    h1: Vec<u16>,
    h2c: Vec<u16>, // OR of nonadj over the vertices of Y (H2(X) = h2c[~X])
    h3c: Vec<u16>, // over Y = complement of X
    feasible: Vec<bool>,
    /// disjoint intervals [B,T] partitioning the feasible cones
    pub intervals: Vec<(u16, u16)>,
}

fn popc(x: u16) -> u32 {
    x.count_ones()
}

pub fn h_tables(h: &Graph) -> HTables {
    let n = h.n;
    let mask = ((1u32 << n) - 1) as u16;
    let adj: Vec<u16> = (0..n).map(|v| (h.adj[v] & mask as u32) as u16).collect();
    let nonadj: Vec<u16> = (0..n).map(|v| mask & !adj[v] & !(1 << v)).collect();
    let total = 1usize << n;
    let mut h1 = vec![0u16; total];
    let mut h2c = vec![0u16; total];
    let mut h3c = vec![0u16; total];
    for x in 1..total {
        let low = x.trailing_zeros() as usize;
        let rest = x & (x - 1);
        h1[x] = h1[rest] | adj[low];
        h2c[x] = h2c[rest] | nonadj[low];
        // new independent pairs (low, v) with v in rest, v not adjacent to low
        let mut acc = h3c[rest];
        let mut vs = rest as u16 & nonadj[low];
        while vs != 0 {
            let v = vs.trailing_zeros() as usize;
            vs &= vs - 1;
            acc |= nonadj[low] & nonadj[v];
        }
        h3c[x] = acc;
    }
    // feasible cones: covering no triangle
    let tris: Vec<u16> = h.sets(3, true).iter().map(|&t| t as u16).collect();
    let mut feasible = vec![true; total];
    for &t in &tris {
        let rest = mask & !t;
        let mut sub = rest;
        loop {
            feasible[(t | sub) as usize] = false;
            if sub == 0 {
                break;
            }
            sub = (sub - 1) & rest;
        }
    }
    // interval partition: cones by size descending; for an unassigned top T, drop elements greedily while the whole
    // interval stays unassigned (feasibility is hereditary, so every subset of T is feasible)
    let mut assigned = vec![false; total];
    let mut order: Vec<u16> = (0..total as u32).filter(|&x| feasible[x as usize]).map(|x| x as u16).collect();
    order.sort_by_key(|&x| std::cmp::Reverse(popc(x)));
    let mut intervals = Vec::new();
    let unassigned_between = |b: u16, t: u16, assigned: &Vec<bool>| -> bool {
        let free = t & !b;
        let mut sub = free;
        loop {
            if assigned[(b | sub) as usize] {
                return false;
            }
            if sub == 0 {
                return true;
            }
            sub = (sub - 1) & free;
        }
    };
    for &t in &order {
        if assigned[t as usize] {
            continue;
        }
        let mut b = t;
        let mut bits = t;
        while bits != 0 {
            let w = bits.trailing_zeros();
            bits &= bits - 1;
            let b2 = b & !(1 << w);
            if unassigned_between(b2, t, &assigned) {
                b = b2;
            }
        }
        let free = t & !b;
        let mut sub = free;
        loop {
            assigned[(b | sub) as usize] = true;
            if sub == 0 {
                break;
            }
            sub = (sub - 1) & free;
        }
        intervals.push((b, t));
    }
    HTables { n, adj, nonadj, h1, h2c, h3c, feasible, intervals }
}

impl HTables {
    #[inline]
    fn h2(&self, x: u16) -> u16 {
        let mask = ((1u32 << self.n) - 1) as u16;
        self.h2c[(mask & !x) as usize]
    }
    #[inline]
    fn h3(&self, x: u16) -> u16 {
        let mask = ((1u32 << self.n) - 1) as u16;
        self.h3c[(mask & !x) as usize]
    }
}

/// G's structure for the rules: edges, non-edges, independent 3- and 4-sets (over the first r vertices on demand)
pub struct GSets {
    pub m: usize,
    pub adj: Vec<u16>,
    pub edges: Vec<(usize, usize)>,
    pub nonedges: Vec<(usize, usize)>,
    pub ind3: Vec<[usize; 3]>,
    pub ind4: Vec<[usize; 4]>,
}

pub fn g_sets(g: &Graph) -> GSets {
    let m = g.n;
    let adj: Vec<u16> = (0..m).map(|v| (g.adj[v] & ((1u32 << m) - 1)) as u16).collect();
    let mut edges = Vec::new();
    let mut nonedges = Vec::new();
    for u in 0..m {
        for v in u + 1..m {
            if g.has_edge(u, v) {
                edges.push((u, v));
            } else {
                nonedges.push((u, v));
            }
        }
    }
    let ind3 = g.sets(3, false).iter().map(|&s| { let v: Vec<usize> = (0..m).filter(|&i| s >> i & 1 == 1).collect(); [v[0], v[1], v[2]] }).collect();
    let ind4 = g.sets(4, false).iter().map(|&s| { let v: Vec<usize> = (0..m).filter(|&i| s >> i & 1 == 1).collect(); [v[0], v[1], v[2], v[3]] }).collect();
    GSets { m, adj, edges, nonedges, ind3, ind4 }
}

/// collapse the configuration of the first `r` vertices; false = FAIL
fn collapse(h: &HTables, g: &GSets, b: &mut [u16], t: &mut [u16], r: usize) -> bool {
    let full = ((1u32 << h.n) - 1) as u16;
    loop {
        let mut changed = false;
        macro_rules! shrink_t {
            ($u:expr, $rm:expr) => {{
                let nt = t[$u] & !$rm;
                if nt != t[$u] {
                    t[$u] = nt;
                    changed = true;
                }
                if b[$u] & !t[$u] != 0 {
                    return false;
                }
            }};
        }
        macro_rules! grow_b {
            ($u:expr, $add:expr) => {{
                let nb = b[$u] | $add;
                if nb != b[$u] {
                    b[$u] = nb;
                    changed = true;
                }
                if b[$u] & !t[$u] != 0 {
                    return false;
                }
            }};
        }
        for &(u, v) in &g.edges {
            if u >= r || v >= r {
                continue;
            }
            let x = b[u] & b[v];
            let h1 = h.h1[x as usize];
            if x & h1 != 0 {
                return false;
            }
            shrink_t!(u, h1 & b[v]);
            shrink_t!(v, h1 & b[u]);
        }
        for &(u, v) in &g.nonedges {
            if u >= r || v >= r {
                continue;
            }
            let un = t[u] | t[v];
            let h3 = h.h3(un);
            if h3 & !un != 0 {
                return false;
            }
            grow_b!(u, h3 & !t[v]);
            grow_b!(v, h3 & !t[u]);
        }
        for s in &g.ind3 {
            if s[2] >= r {
                continue;
            }
            let un = t[s[0]] | t[s[1]] | t[s[2]];
            let h2 = h.h2(un);
            if h2 & !un != 0 {
                return false;
            }
            for k in 0..3 {
                let others = (0..3).filter(|&j| j != k).fold(0u16, |a, j| a | t[s[j]]);
                grow_b!(s[k], h2 & !others);
            }
        }
        for s in &g.ind4 {
            if s[3] >= r {
                continue;
            }
            let un = t[s[0]] | t[s[1]] | t[s[2]] | t[s[3]];
            if un != full {
                return false;
            }
            for k in 0..4 {
                let others = (0..4).filter(|&j| j != k).fold(0u16, |a, j| a | t[s[j]]);
                grow_b!(s[k], full & !others);
            }
        }
        // bottoms must stay feasible cones (tops are, hereditarily)
        for i in 0..r {
            if !h.feasible[b[i] as usize] {
                return false;
            }
        }
        if !changed {
            return true;
        }
    }
}

pub struct GlueStats {
    pub nodes: u64,
    pub solutions: u64,
    pub extensions: u64,
    /// nodes tried and nodes surviving collapse, per level
    pub tried: Vec<u64>,
    pub alive: Vec<u64>,
    pub cap: u64,
    pub capped: bool,
}

/// DFS over G's vertices; at the end split intervals to single cones; each solution is checked for a v-extension.
/// Returns the number of (4,5,24)-solutions and of (4,5,25)-extensions found (0 = the pair is refuted).
pub fn glue(g: &Graph, h: &Graph, x_first: bool) -> GlueStats {
    let ht = h_tables(h);
    let gs = g_sets(g);
    let m = gs.m;
    let mut st = GlueStats { nodes: 0, solutions: 0, extensions: 0, tried: vec![0; m + 16], alive: vec![0; m + 16], cap: std::env::var("MONSTER_MR_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(u64::MAX), capped: false };
    let mut b = vec![0u16; m];
    let mut t = vec![0u16; m];
    fn rec(ht: &HTables, gs: &GSets, g: &Graph, h: &Graph, b: &mut Vec<u16>, t: &mut Vec<u16>, r: usize, st: &mut GlueStats, x_first: bool) {
        let m = gs.m;
        if r < m {
            for k in 0..ht.intervals.len() {
                let (ib, it) = ht.intervals[k];
                let (sb, stt) = (b.clone(), t.clone());
                b[r] = ib;
                t[r] = it;
                st.nodes += 1;
                st.tried[r] += 1;
                if st.nodes > st.cap {
                    st.capped = true;
                    return;
                }
                if collapse(ht, gs, b, t, r + 1) {
                    st.alive[r] += 1;
                    rec(ht, gs, g, h, b, t, r + 1, st, x_first);
                }
                *b = sb;
                *t = stt;
            }
            return;
        }
        // all vertices placed: split until singletons
        if let Some(i) = (0..m).find(|&i| b[i] != t[i]) {
            let w = (t[i] & !b[i]).trailing_zeros();
            for side in 0..2 {
                let (sb, stt) = (b.clone(), t.clone());
                if side == 0 {
                    b[i] |= 1 << w;
                } else {
                    t[i] &= !(1 << w);
                }
                st.nodes += 1;
                st.tried[m] += 1;
                if st.nodes > st.cap {
                    st.capped = true;
                    return;
                }
                if collapse(ht, gs, b, t, m) {
                    st.alive[m] += 1;
                    rec(ht, gs, g, h, b, t, m, st, x_first);
                }
                *b = sb;
                *t = stt;
            }
            return;
        }
        st.solutions += 1;
        if extend_exists(g, h, b, x_first) {
            st.extensions += 1;
        }
    }
    rec(&ht, &gs, g, h, &mut b, &mut t, 0, &mut st, x_first);
    st
}

/// §4: can a vertex v (red to x) be added to the 24-vertex graph x + G + H with cones `c`? Intervals over V_F.
fn extend_exists(g: &Graph, h: &Graph, c: &[u16], _x_first: bool) -> bool {
    // F on 1 + m + n vertices: 0 = x, 1..=m = G, m+1..=m+n = H
    let (m, n) = (g.n, h.n);
    let nf = 1 + m + n;
    let mut f = crate::graph::Graph::empty(nf);
    for u in 0..m {
        f.add_edge(0, 1 + u);
        for v in u + 1..m {
            if g.has_edge(u, v) {
                f.add_edge(1 + u, 1 + v);
            }
        }
        for w in 0..n {
            if c[u] >> w & 1 == 1 {
                f.add_edge(1 + u, 1 + m + w);
            }
        }
    }
    for w in 0..n {
        for z in w + 1..n {
            if h.has_edge(w, z) {
                f.add_edge(1 + m + w, 1 + m + z);
            }
        }
    }
    let tris = f.sets(3, true);
    let ind4 = f.sets(4, false);
    // merged list sorted by greatest element then next
    let mut xs: Vec<(u32, bool)> = tris.iter().map(|&s| (s, true)).chain(ind4.iter().map(|&s| (s, false))).collect();
    xs.sort_by(|a, b| b.0.cmp(&a.0));
    let full = ((1u64 << nf) - 1) as u32;
    // v must be red to x: start with B = {x}
    let mut ivs: Vec<(u32, u32)> = vec![(1, full)];
    for (s, is_tri) in xs {
        let mut next = Vec::with_capacity(ivs.len());
        for (b, t) in ivs {
            if is_tri {
                if s & !t != 0 {
                    next.push((b, t));
                    continue;
                }
                if s & !b == 0 {
                    continue; // covered: delete
                }
                let mut ys = s & !b;
                let mut acc = b;
                while ys != 0 {
                    let y = ys.trailing_zeros();
                    ys &= ys - 1;
                    next.push((acc, t & !(1 << y)));
                    acc |= 1 << y;
                }
            } else {
                if s & b != 0 {
                    next.push((b, t));
                    continue;
                }
                let hit = s & t;
                if hit == 0 {
                    continue;
                }
                let mut ys = hit;
                let mut excl = 0u32;
                while ys != 0 {
                    let y = ys.trailing_zeros();
                    ys &= ys - 1;
                    next.push((b | 1 << y, t & !excl));
                    excl |= 1 << y;
                }
            }
        }
        ivs = next;
        if ivs.is_empty() {
            return false;
        }
    }
    !ivs.is_empty()
}
