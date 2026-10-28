//! `monster count-kill`: how many catalogue pairs of a gluing stage are refuted by COUNTING alone (no search, no
//! proofs; a measurement for the counting route, RESULTS 2026-10-28). Pair (A, B): vertex 0 red to the d A-vertices,
//! blue to the m = n-1-d B-vertices; the unknowns are the d*m cross edges. Everything below follows from "no red K_s,
//! no blue K_t" plus the degree bounds (red degree in [lo, hi], lo = n - R(s,t-1), hi = R(s-1,t) - 1):
//! - u in A with r_u red cross edges: 1 + deg_A(u) + r_u in [lo, hi]; its red B-neighbours contain no red K_{s-1}
//!   (else a red K_s with u), so r_u <= alpha(B) = largest red-K_{s-1}-free subset of B; its blue B-neighbours contain
//!   no blue K_{t-1}, so m - r_u <= beta(B);
//! - w in B with r_w red cross edges: deg_B(w) + r_w in [lo, hi]; r_w <= alpha(A); d - r_w <= beta(A);
//! - the cross graph is bipartite with those degree windows: a max-flow feasibility check (lower bounds).
//! Kill levels: 1 = some window empty, 2 = window sums incompatible, 3 = flow infeasible.

use crate::catalog::Level;
use crate::graph::{mask, Graph};
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

fn ramsey(s: usize, t: usize) -> usize {
    match (s.min(t), s.max(t)) {
        (1, _) => 1,
        (2, k) => k,
        (3, 3) => 6,
        (3, 4) => 9,
        (3, 5) => 14,
        (3, 6) => 18,
        (3, 7) => 23,
        (3, 8) => 28,
        (3, 9) => 36,
        (4, 4) => 18,
        (4, 5) => 25,
        _ => panic!("R({s},{t}) unknown"),
    }
}

/// largest subset of the vertices containing no clique of size k of the given colour (bitmask DP over subsets)
fn free_subset_max(g: &Graph, k: usize, red: bool) -> usize {
    let n = g.n;
    let cliques = g.sets(k, red);
    let total = 1usize << n;
    let mut bad = vec![false; total];
    for &c in &cliques {
        // every superset of c is bad: iterate over subsets of the complement
        let rest = mask(n) & !c;
        let mut sub = rest;
        loop {
            bad[(c | sub) as usize] = true;
            if sub == 0 {
                break;
            }
            sub = (sub - 1) & rest;
        }
    }
    let mut best = 0;
    for s in 0..total {
        if !bad[s] {
            best = best.max(s.count_ones() as usize);
        }
    }
    best
}


/// per k: the fewest red edges (and the fewest blue edges) induced by any k-subset of the vertices
fn min_edges(g: &Graph) -> (Vec<usize>, Vec<usize>) {
    let n = g.n;
    let total = 1usize << n;
    let mut min_red = vec![usize::MAX; n + 1];
    let mut min_blue = vec![usize::MAX; n + 1];
    for s in 0..total {
        let sm = s as u32;
        let k = sm.count_ones() as usize;
        let mut e = 0usize;
        let mut rest = sm;
        while rest != 0 {
            let v = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            e += (g.adj[v] & sm).count_ones() as usize;
        }
        e /= 2;
        min_red[k] = min_red[k].min(e);
        min_blue[k] = min_blue[k].min(k * (k - 1) / 2 - e);
    }
    (min_red, min_blue)
}

/// EDGE-LEVEL CAPS of one side graph `g` (known part of the common neighbourhoods):
/// red pairs: cross common red neighbours <= (t-1) - 1[0 is a common red neighbour] - common red inside g;
/// blue pairs: cross common blue neighbours <= (R(s,t-2)-1) - 1[0 is a common blue neighbour] - common blue inside g.
/// Returns (cap for red pairs, cap for blue pairs), or None if a pair already violates its bound.
fn caps(g: &Graph, s: usize, t: usize, zero_red: bool) -> Option<(usize, usize)> {
    let n = g.n;
    let (mut cr, mut cb) = (0usize, 0usize);
    for u in 0..n {
        for v in u + 1..n {
            let both = mask(n) & !(1 << u) & !(1 << v);
            if g.has_edge(u, v) {
                let common = (g.adj[u] & g.adj[v] & both).count_ones() as usize + if zero_red { 1 } else { 0 };
                if common > t - 1 {
                    return None;
                }
                cr += t - 1 - common;
            } else {
                let common = (!g.adj[u] & !g.adj[v] & both).count_ones() as usize + if zero_red { 0 } else { 1 };
                let lim = ramsey(s, t - 2) - 1;
                if common > lim {
                    return None;
                }
                cb += lim - common;
            }
        }
    }
    Some((cr, cb))
}

/// min over degree vectors (r_i in [lo_i, hi_i], sum = R) of sum_i cost_i(r_i), for every R (knapsack DP)
fn min_cost_by_sum(lo: &[usize], hi: &[usize], cost: &dyn Fn(usize, usize) -> usize) -> Vec<usize> {
    let maxsum: usize = hi.iter().sum();
    let mut f = vec![usize::MAX; maxsum + 1];
    f[0] = 0;
    for i in 0..lo.len() {
        let mut g = vec![usize::MAX; maxsum + 1];
        for r0 in 0..=maxsum {
            if f[r0] == usize::MAX {
                continue;
            }
            for r in lo[i]..=hi[i] {
                let c = cost(i, r);
                if c == usize::MAX {
                    continue;
                }
                let v = f[r0] + c;
                if g[r0 + r] > v {
                    g[r0 + r] = v;
                }
            }
        }
        f = g;
    }
    f
}
struct Side {
    deg: Vec<Vec<usize>>,
    alpha: Vec<usize>,
    beta: Vec<usize>,
    min_red: Vec<Vec<usize>>,
    min_blue: Vec<Vec<usize>>,
    /// (cap on cross common red neighbours summed over red pairs, same for blue pairs); None = dead graph
    caps: Vec<Option<(usize, usize)>>,
}

fn side(level: &Level, s: usize, t: usize, zero_red: bool) -> Side {
    let mut deg = Vec::with_capacity(level.graphs.len());
    let mut min_red = Vec::with_capacity(level.graphs.len());
    let mut min_blue = Vec::with_capacity(level.graphs.len());
    let mut cp = Vec::with_capacity(level.graphs.len());
    let mut alpha = Vec::with_capacity(level.graphs.len());
    let mut beta = Vec::with_capacity(level.graphs.len());
    for g in &level.graphs {
        deg.push((0..g.n).map(|u| (g.adj[u] & mask(g.n)).count_ones() as usize).collect());
        alpha.push(free_subset_max(g, s - 1, true));
        beta.push(free_subset_max(g, t - 1, false));
        let (mr, mb) = min_edges(g);
        min_red.push(mr);
        min_blue.push(mb);
        cp.push(caps(g, s, t, zero_red));
    }
    Side { deg, alpha, beta, min_red, min_blue, caps: cp }
}

/// bipartite graph with degree windows: feasibility by max-flow with lower bounds (tiny graphs)
fn bipartite_feasible(lo_a: &[usize], hi_a: &[usize], lo_b: &[usize], hi_b: &[usize]) -> bool {
    let (d, m) = (lo_a.len(), lo_b.len());
    // nodes: 0 = S, 1..=d A, d+1..=d+m B, d+m+1 = T, d+m+2 = S', d+m+3 = T'
    let nn = d + m + 4;
    let (src, snk, s2, t2) = (0, d + m + 1, d + m + 2, d + m + 3);
    let mut cap = vec![vec![0i64; nn]; nn];
    let mut excess = vec![0i64; nn];
    let mut add = |x: usize, y: usize, l: i64, c: i64, cap: &mut Vec<Vec<i64>>, excess: &mut Vec<i64>| {
        cap[x][y] += c - l;
        excess[y] += l;
        excess[x] -= l;
    };
    for u in 0..d {
        add(src, 1 + u, lo_a[u] as i64, hi_a[u] as i64, &mut cap, &mut excess);
        for w in 0..m {
            add(1 + u, 1 + d + w, 0, 1, &mut cap, &mut excess);
        }
    }
    for w in 0..m {
        add(1 + d + w, snk, lo_b[w] as i64, hi_b[w] as i64, &mut cap, &mut excess);
    }
    cap[snk][src] += 1 << 30;
    let mut need = 0i64;
    for v in 0..nn - 2 {
        if excess[v] > 0 {
            cap[s2][v] += excess[v];
            need += excess[v];
        } else if excess[v] < 0 {
            cap[v][t2] += -excess[v];
        }
    }
    // Edmonds-Karp
    let mut flow = 0i64;
    loop {
        let mut prev = vec![usize::MAX; nn];
        prev[s2] = s2;
        let mut q = std::collections::VecDeque::new();
        q.push_back(s2);
        while let Some(x) = q.pop_front() {
            for y in 0..nn {
                if prev[y] == usize::MAX && cap[x][y] > 0 {
                    prev[y] = x;
                    q.push_back(y);
                }
            }
        }
        if prev[t2] == usize::MAX {
            break;
        }
        let mut f = i64::MAX;
        let mut y = t2;
        while y != s2 {
            let x = prev[y];
            f = f.min(cap[x][y]);
            y = x;
        }
        let mut y = t2;
        while y != s2 {
            let x = prev[y];
            cap[x][y] -= f;
            cap[y][x] += f;
            y = x;
        }
        flow += f;
    }
    flow == need
}

/// kill level of one pair (0 = survives)
fn kill_level(s: usize, t: usize, n: usize, d: usize, a: &Side, ia: usize, b: &Side, ib: usize) -> u8 {
    let m = n - 1 - d;
    let lo = n - ramsey(s, t - 1);
    let hi = ramsey(s - 1, t) - 1;
    let (mut lo_a, mut hi_a, mut lo_b, mut hi_b) = (vec![0; d], vec![0; d], vec![0; m], vec![0; m]);
    for u in 0..d {
        let fixed = 1 + a.deg[ia][u];
        let l = lo.saturating_sub(fixed).max(m.saturating_sub(b.beta[ib]));
        let h = (hi.saturating_sub(fixed)).min(b.alpha[ib]).min(m);
        if fixed > hi || l > h {
            return 1;
        }
        lo_a[u] = l;
        hi_a[u] = h;
    }
    for w in 0..m {
        let fixed = b.deg[ib][w];
        let l = lo.saturating_sub(fixed).max(d.saturating_sub(a.beta[ia]));
        let h = (hi.saturating_sub(fixed)).min(a.alpha[ia]).min(d);
        if fixed > hi || l > h {
            return 1;
        }
        lo_b[w] = l;
        hi_b[w] = h;
    }
    let (sla, sha): (usize, usize) = (lo_a.iter().sum(), hi_a.iter().sum());
    let (slb, shb): (usize, usize) = (lo_b.iter().sum(), hi_b.iter().sum());
    if sla > shb || slb > sha {
        return 2;
    }
    if !bipartite_feasible(&lo_a, &hi_a, &lo_b, &hi_b) {
        return 3;
    }
    // level 4: edge-level double counting. For u in A with red B-neighbourhood T_u: the red B-edges inside T_u are
    // the red pairs of B having u as a cross common red neighbour (capped by caps(B).0 in total), the blue B-edges
    // inside B \ T_u are the blue pairs of B having u as a cross common blue neighbour (caps(B).1); and symmetrically
    // for w in B with its red A-neighbourhood (caps(A)). Each sum is bounded below by the min-edge functions of the
    // degree vector; the DP minimises each over degree vectors of total R. Kill if no total R works.
    let (Some((cap_red_b, cap_blue_b)), Some((cap_red_a, cap_blue_a))) = (b.caps[ib], a.caps[ia]) else { return 1 };
    let m_red_a = min_cost_by_sum(&lo_a, &hi_a, &|_, r| b.min_red[ib][r]);
    let m_blue_a = min_cost_by_sum(&lo_a, &hi_a, &|_, r| b.min_blue[ib][m - r]);
    let m_red_b = min_cost_by_sum(&lo_b, &hi_b, &|_, r| a.min_red[ia][r]);
    let m_blue_b = min_cost_by_sum(&lo_b, &hi_b, &|_, r| a.min_blue[ia][d - r]);
    let mut ok = false;
    for r in sla.max(slb)..=sha.min(shb) {
        if m_red_a[r] <= cap_red_b && m_blue_a[r] <= cap_blue_b && m_red_b[r] <= cap_red_a && m_blue_b[r] <= cap_blue_a {
            ok = true;
            break;
        }
    }
    if !ok {
        return 4;
    }
    0
}

pub fn run(s: usize, t: usize, n: usize, d: usize, la: &Level, lb: &Level, threads: usize) {
    let t0 = std::time::Instant::now();
    let a = side(la, s, t, true);
    let b = side(lb, s, t, false);
    let prep = t0.elapsed().as_secs_f64();
    let hist = |v: &[usize]| {
        let mut h = std::collections::BTreeMap::new();
        for &x in v {
            *h.entry(x).or_insert(0usize) += 1;
        }
        h.iter().map(|(k, c)| format!("{k}:{c}")).collect::<Vec<_>>().join(" ")
    };
    println!("A: {} graphs on K_{d}; alpha (largest red-K{}-free subset) {}; beta (largest blue-K{}-free subset) {}", la.graphs.len(), s - 1, hist(&a.alpha), t - 1, hist(&a.beta));
    println!("B: {} graphs on K_{}; alpha {}; beta {}", lb.graphs.len(), n - 1 - d, hist(&b.alpha), hist(&b.beta));
    let counts: Vec<AtomicU64> = (0..5).map(|_| AtomicU64::new(0)).collect();
    let next = AtomicU64::new(0);
    let total = la.graphs.len() as u64 * lb.graphs.len() as u64;
    std::thread::scope(|sc| {
        for _ in 0..threads.max(1) {
            sc.spawn(|| loop {
                let ib = next.fetch_add(1, Relaxed) as usize;
                if ib >= lb.graphs.len() {
                    break;
                }
                let mut local = [0u64; 5];
                for ia in 0..la.graphs.len() {
                    local[kill_level(s, t, n, d, &a, ia, &b, ib) as usize] += 1;
                }
                for k in 0..5 {
                    counts[k].fetch_add(local[k], Relaxed);
                }
            });
        }
    });
    let c: Vec<u64> = counts.iter().map(|x| x.load(Relaxed)).collect();
    println!(
        "count-kill d={d}: {total} pairs; killed by a window {} ({:.2}%), by window sums {} ({:.2}%), by the bipartite flow {} ({:.2}%), by edge double counting {} ({:.2}%); SURVIVE {} ({:.2}%); prep {:.1} s, pairs {:.1} s",
        c[1],
        100.0 * c[1] as f64 / total as f64,
        c[2],
        100.0 * c[2] as f64 / total as f64,
        c[3],
        100.0 * c[3] as f64 / total as f64,
        c[4],
        100.0 * c[4] as f64 / total as f64,
        c[0],
        100.0 * c[0] as f64 / total as f64,
        prep,
        t0.elapsed().as_secs_f64() - prep
    );
}
