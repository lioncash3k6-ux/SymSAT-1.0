//! Pattern CDCL: symmetric learning for the full Ramsey formula on K_N.
//!
//! The formula F (no red K_s, no blue K_t on K_N) is invariant under every vertex permutation. A learned clause over
//! edge variables is a forbidden partial 2-colouring (a *pattern*): literal ¬x_e forbids e red, x_e forbids e blue.
//! Every image of a learned clause under a vertex permutation is implied by F (induction over the derivation,
//! because F is S_N-invariant). This propagator stores each learned pattern once (canonical form) and finds images
//! that are unit or falsified under the current partial colouring by bitset embedding search anchored at the
//! newest assigned edge, then hands the concrete image clause to the solver, which logs it as
//! `image(lemma, permutation)` before using it.

use crate::sat::solver::Lit;
use std::collections::HashSet;

#[inline]
fn evar(i: usize, j: usize) -> usize {
    let (i, j) = if i < j { (i, j) } else { (j, i) };
    j * (j - 1) / 2 + i // 0-based variable index (DIMACS var - 1), column-major like the generator
}

thread_local! {
    pub static DEPTH_NODES: std::cell::RefCell<[u64; 33]> = const { std::cell::RefCell::new([0; 33]) };
    static CORE_SLACK: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

struct Pat {
    k: usize,
    red: [u32; 32],
    blue: [u32; 32],
    edges: Vec<(u8, u8, bool)>, // (a, b, red?)
    /// per edge: number of pattern vertices adjacent to (a,b) with colours (red,red),(red,blue),(blue,red),(blue,blue)
    common: Vec<[u8; 4]>,
    /// indices of anchor-representative edges: one per (twin class, twin class, colour); twin swaps are automorphisms,
    /// so anchoring on the representative finds every image the other edges of its class would find
    anchors: Vec<usize>,
    verts: Vec<u8>,             // pattern vertex a = original vertex verts[a] (for the logged permutation)
    lemma: u64,
    /// stored as the colour-swapped image of lemma `lemma` (only when s = t)
    flip: bool,
    calls: u64,
    hits: u64,
    nodes: u64,
    skip: u32,
    /// subsumed by a smaller pattern found by vertex vivification: no longer searched
    dead: bool,
    /// already offered to vertex vivification
    viv_tried: bool,
    /// a proved library lemma (registered through `learn_forced`), not a clause CDCL learned
    lib: bool,
}

#[derive(Default, Debug, Clone)]
pub struct PatStats {
    pub learned: u64,
    pub stored: u64,
    pub duplicates: u64,
    pub rejected: u64,
    /// rejection reasons (too many or too few edges, LBD, store full, too many vertices, disconnected) and the vertex-count
    /// histogram of every learned clause offered (index 31 = 31 or more)
    pub rej_edges: u64,
    pub rej_lbd: u64,
    pub rej_full: u64,
    pub rej_k: u64,
    pub rej_disc: u64,
    pub rej_lib: u64,
    pub vhist: [u64; 32],
    pub images: u64,
    pub conflicts: u64,
    pub nodes: u64,
    pub budget_cut: u64,
    pub sum_k: u64,
    pub sum_edges: u64,
    pub sum_leaves: u64,
    pub embed_calls: u64,
    pub prop_ns: u64,
    pub canon_ns: u64,
    /// per-literal anchor scans
    pub scans: u64,
}

pub struct PatternProp {
    n: usize,
    full: u64,
    edge_of: Vec<(u8, u8)>,
    pats: Vec<Pat>,
    keys: HashSet<Vec<u64>>,
    red: Vec<u64>,
    blue: Vec<u64>,
    saved: Vec<Lit>,
    scan: usize,
    pub max_k: usize,
    pub max_edges: usize,
    pub max_lbd: u32,
    pub max_pats: usize,
    pub node_budget: u64,
    /// where the one unassigned edge of a unit image may be: 0 nowhere (conflicts only), 1 leaf edges, 2 anywhere
    pub slack_mode: u8,
    /// throttle chronically low-yield patterns
    pub adaptive: bool,
    /// colour swap preserves F (s = t): also store colour-swapped patterns (antisymmetry, S_N x Z_2)
    pub flip_ok: bool,
    /// only proved library lemmas become patterns; clauses CDCL learns are not searched for images (set on the main
    /// solver after the library exists, MONSTER_LIBONLY=1; the solvers that prove the library keep learned patterns)
    pub lib_only: bool,
    /// inside `learn_forced` (library lemmas)
    forcing: bool,
    /// MONSTER_NODE_THROTTLE=X: a pattern that has spent more than X search nodes per image (after 20X nodes) is tried on
    /// only every 4th anchor, like the per-call throttle above (skipping only loses propagations)
    node_throttle: u64,
    /// MONSTER_LEGACY_EMBED=1: the pre-2026-10-26 embedding search (`rec`) instead of the domain search
    legacy_embed: bool,
    /// MONSTER_CHECK_EMBED=1: run both searches on every call, assert they agree and that each image is valid
    check_embed: bool,
    /// rge[d] / bge[d]: vertices with >= d red / blue assigned edges (d = 0..n; rebuilt after each sync)
    rge: Vec<u64>,
    bge: Vec<u64>,
    pub stats: PatStats,
}

impl PatternProp {
    pub fn new(n: usize) -> PatternProp {
        let mut edge_of = vec![(0u8, 0u8); n * (n - 1) / 2];
        for j in 1..n {
            for i in 0..j {
                edge_of[evar(i, j)] = (i as u8, j as u8);
            }
        }
        PatternProp {
            n,
            full: if n == 64 { u64::MAX } else { (1u64 << n) - 1 },
            edge_of,
            pats: Vec::new(),
            keys: HashSet::new(),
            red: vec![0; n],
            blue: vec![0; n],
            saved: Vec::new(),
            scan: 0,
            max_k: 12,
            max_edges: 24,
            max_lbd: 12,
            max_pats: 4000,
            node_budget: 20_000,
            slack_mode: 2,
            adaptive: true,
            flip_ok: false,
            lib_only: false,
            forcing: false,
            node_throttle: std::env::var("MONSTER_NODE_THROTTLE").ok().and_then(|v| v.parse().ok()).unwrap_or(0),
            legacy_embed: std::env::var_os("MONSTER_LEGACY_EMBED").is_some(),
            check_embed: std::env::var_os("MONSTER_CHECK_EMBED").is_some(),
            rge: vec![0; n + 1],
            bge: vec![0; n + 1],
            stats: PatStats::default(),
        }
    }

    /// (patterns, embed calls, images, search nodes) for library lemmas and for learned clauses.
    pub fn source_split(&self) -> [(usize, u64, u64, u64); 2] {
        let mut out = [(0usize, 0u64, 0u64, 0u64); 2];
        for p in &self.pats {
            let o = &mut out[if p.lib { 0 } else { 1 }];
            o.0 += 1;
            o.1 += p.calls;
            o.2 += p.hits;
            o.3 += p.nodes;
        }
        out
    }

    /// Per-pattern yield table: (vertices, edges, calls, hits, nodes), most expensive first.
    pub fn yield_table(&self) -> Vec<(usize, usize, u64, u64, u64)> {
        let mut v: Vec<_> = self.pats.iter().map(|p| (p.k, p.edges.len(), p.calls, p.hits, p.nodes)).collect();
        v.sort_by_key(|x| std::cmp::Reverse(x.4));
        v
    }

    /// Live (not retired) patterns that are clauses of the solver database (not colour-swapped twins), as
    /// (index, clause in solver literals, vertex count): the input to vertex vivification.
    pub fn live_clauses(&self) -> Vec<(usize, Vec<Lit>, usize)> {
        self.pats
            .iter()
            .enumerate()
            .filter(|(_, p)| !p.dead && !p.flip && !p.viv_tried)
            .map(|(i, p)| {
                let lits = p.edges.iter().map(|&(a, b, r)| ((evar(p.verts[a as usize] as usize, p.verts[b as usize] as usize) as Lit) << 1) | r as Lit).collect();
                (i, lits, p.k)
            })
            .collect()
    }

    /// Stop searching pattern `i` (a smaller pattern now subsumes all its images).
    pub fn retire(&mut self, i: usize) {
        self.pats[i].dead = true;
    }

    pub fn mark_viv_tried(&mut self, i: usize) {
        self.pats[i].viv_tried = true;
    }

    /// Vertex count of the solver-literal clause `lits` (the edges' endpoints).
    pub fn vertices_of(&self, lits: &[Lit]) -> Vec<u8> {
        let mut vs: Vec<u8> = Vec::new();
        for &l in lits {
            let (u, v) = self.edge_of[(l >> 1) as usize];
            for w in [u, v] {
                if !vs.contains(&w) {
                    vs.push(w);
                }
            }
        }
        vs
    }

    /// Does literal `l` touch vertex `w`?
    pub fn touches(&self, l: Lit, w: u8) -> bool {
        let (u, v) = self.edge_of[(l >> 1) as usize];
        u == w || v == w
    }

    pub fn num_patterns(&self) -> usize {
        self.pats.len()
    }

    /// Register a proved lemma as a pattern regardless of the admission caps (library lemmas).
    pub fn learn_forced(&mut self, lits: &[Lit], lemma: u64) {
        let (k, e, l, p) = (self.max_k, self.max_edges, self.max_lbd, self.max_pats);
        self.max_k = 32;
        self.max_edges = 1024;
        self.max_lbd = u32::MAX;
        self.max_pats = usize::MAX;
        self.forcing = true;
        self.learn(lits, 0, lemma);
        self.forcing = false;
        self.max_k = k;
        self.max_edges = e;
        self.max_lbd = l;
        self.max_pats = p;
    }

    /// Offer a freshly learned clause (solver literals, var = edge index). `lemma` = its index in the proof log.
    pub fn learn(&mut self, lits: &[Lit], lbd: u32, lemma: u64) {
        self.stats.learned += 1;
        let mut verts: Vec<u8> = Vec::new();
        let mut es: Vec<(u8, u8, bool)> = Vec::new();
        for &l in lits {
            let (u, v) = self.edge_of[(l >> 1) as usize];
            let red = l & 1 == 1; // negative literal ¬x: the pattern edge is red
            for w in [u, v] {
                if !verts.contains(&w) {
                    verts.push(w);
                }
            }
            es.push((u, v, red));
        }
        self.stats.vhist[verts.len().min(31)] += 1;
        let reason = if self.lib_only && !self.forcing {
            Some(&mut self.stats.rej_lib)
        } else if lits.len() < 2 || lits.len() > self.max_edges {
            Some(&mut self.stats.rej_edges)
        } else if lbd > self.max_lbd {
            Some(&mut self.stats.rej_lbd)
        } else if self.pats.len() >= self.max_pats {
            Some(&mut self.stats.rej_full)
        } else if verts.len() > self.max_k {
            Some(&mut self.stats.rej_k)
        } else {
            None
        };
        if let Some(r) = reason {
            *r += 1;
            self.stats.rejected += 1;
            return;
        }
        let k = verts.len();
        let idx = |w: u8| verts.iter().position(|&x| x == w).unwrap() as u8;
        let edges: Vec<(u8, u8, bool)> = es.iter().map(|&(u, v, r)| (idx(u), idx(v), r)).collect();
        let mut red = [0u32; 32];
        let mut blue = [0u32; 32];
        for &(a, b, r) in &edges {
            let m = if r { &mut red } else { &mut blue };
            m[a as usize] |= 1 << b;
            m[b as usize] |= 1 << a;
        }
        // connected patterns only (disconnected ones make embedding search explode)
        let mut seen = 1u32;
        let mut stack = vec![0usize];
        while let Some(a) = stack.pop() {
            let nb = (red[a] | blue[a]) & !seen;
            seen |= nb;
            let mut x = nb;
            while x != 0 {
                stack.push(x.trailing_zeros() as usize);
                x &= x - 1;
            }
        }
        if seen.count_ones() as usize != k {
            self.stats.rej_disc += 1;
            self.stats.rejected += 1;
            return;
        }
        let stored = self.store(k, red, blue, edges.clone(), verts.clone(), lemma, false);
        if self.flip_ok {
            // antisymmetry: the colour-swapped pattern is the image of the lemma under the colour swap
            let fe: Vec<(u8, u8, bool)> = edges.iter().map(|&(a, b, r)| (a, b, !r)).collect();
            self.store(k, blue, red, fe, verts, lemma, true);
        }
        let _ = stored;
    }

    fn store(
        &mut self,
        k: usize,
        red: [u32; 32],
        blue: [u32; 32],
        edges: Vec<(u8, u8, bool)>,
        verts: Vec<u8>,
        lemma: u64,
        flip: bool,
    ) -> bool {
        let t0 = std::time::Instant::now();
        let key = canon_key(k, &red, &blue);
        self.stats.canon_ns += t0.elapsed().as_nanos() as u64;
        if !self.keys.insert(key) {
            self.stats.duplicates += 1;
            return false;
        }
        self.stats.stored += 1;
        self.stats.sum_k += k as u64;
        self.stats.sum_edges += edges.len() as u64;
        self.stats.sum_leaves += (0..k).filter(|&a| (red[a] | blue[a]).count_ones() == 1).count() as u64;
        let common = edges
            .iter()
            .map(|&(a, b, _)| {
                let (a, b) = (a as usize, b as usize);
                [
                    (red[a] & red[b]).count_ones() as u8,
                    (red[a] & blue[b]).count_ones() as u8,
                    (blue[a] & red[b]).count_ones() as u8,
                    (blue[a] & blue[b]).count_ones() as u8,
                ]
            })
            .collect();
        let mut class = vec![usize::MAX; k];
        for v in 0..k {
            if class[v] != usize::MAX {
                continue;
            }
            class[v] = v;
            for w in v + 1..k {
                let m = !((1u32 << v) | (1u32 << w));
                if class[w] == usize::MAX && red[v] & m == red[w] & m && blue[v] & m == blue[w] & m {
                    class[w] = v;
                }
            }
        }
        let mut seen: Vec<(usize, usize, bool)> = Vec::new();
        let mut anchors = Vec::new();
        for (i, &(a, b, r)) in edges.iter().enumerate() {
            let (ca, cb) = (class[a as usize], class[b as usize]);
            let key = (ca.min(cb), ca.max(cb), r);
            if !seen.contains(&key) {
                seen.push(key);
                anchors.push(i);
            }
        }
        self.pats.push(Pat { k, red, blue, edges, common, anchors, verts, lemma, flip, calls: 0, hits: 0, nodes: 0, skip: 0, dead: false, viv_tried: false, lib: self.forcing });
        true
    }

    fn sync(&mut self, trail: &[Lit]) {
        let mut common = 0;
        while common < self.saved.len() && common < trail.len() && self.saved[common] == trail[common] {
            common += 1;
        }
        for &l in self.saved[common..].iter().rev() {
            let (u, v) = self.edge_of[(l >> 1) as usize];
            let m = if l & 1 == 0 { &mut self.red } else { &mut self.blue };
            m[u as usize] &= !(1 << v);
            m[v as usize] &= !(1 << u);
        }
        self.saved.truncate(common);
        for &l in &trail[common..] {
            let (u, v) = self.edge_of[(l >> 1) as usize];
            let m = if l & 1 == 0 { &mut self.red } else { &mut self.blue };
            m[u as usize] |= 1 << v;
            m[v as usize] |= 1 << u;
            self.saved.push(l);
        }
        self.scan = self.scan.min(common);
        for (masks, cols) in [(&mut self.rge, &self.red), (&mut self.bge, &self.blue)] {
            masks.fill(0);
            for (v, c) in cols.iter().enumerate() {
                masks[c.count_ones() as usize] |= 1 << v;
            }
            for d in (0..masks.len() - 1).rev() {
                masks[d] |= masks[d + 1];
            }
        }
    }

    /// Find one image clause that is falsified or unit under the current assignment.
    /// Returns (clause literals, source lemma index, full vertex permutation original -> image).
    pub fn propagate(&mut self, vals: &[i8], trail: &[Lit]) -> Option<(Vec<Lit>, u64, Vec<u8>, bool)> {
        let t0 = std::time::Instant::now();
        let r = self.propagate_inner(vals, trail);
        self.stats.prop_ns += t0.elapsed().as_nanos() as u64;
        r
    }

    fn propagate_inner(&mut self, _vals: &[i8], trail: &[Lit]) -> Option<(Vec<Lit>, u64, Vec<u8>, bool)> {
        self.sync(trail);
        while self.scan < trail.len() {
            let l = trail[self.scan];
            self.stats.scans += 1;
            let (u, v) = self.edge_of[(l >> 1) as usize];
            let col_red = l & 1 == 0; // positive literal x_e true: edge red
            // per-endpoint assigned degrees (popcounts), for the anchor degree filter
            let (ru, bu) = (self.red[u as usize].count_ones(), self.blue[u as usize].count_ones());
            let (rv, bv) = (self.red[v as usize].count_ones(), self.blue[v as usize].count_ones());
            for pi in 0..self.pats.len() {
                // adaptive effort (SEL-style economy): a pattern that has yielded less than one image per 20,000
                // embedding calls is only tried on every 8th anchor. Skipping can only lose propagations (sound).
                {
                    let p = &mut self.pats[pi];
                    let costly = self.node_throttle > 0 && p.nodes > 20 * self.node_throttle && p.hits * self.node_throttle < p.nodes;
                    if (self.adaptive && p.calls > 20_000 && p.hits * 2_000 < p.calls) || costly {
                        p.skip = p.skip.wrapping_add(1);
                        if p.skip % 4 != 0 {
                            continue;
                        }
                    }
                }
                if self.pats[pi].dead {
                    continue;
                }
                let na = self.pats[pi].anchors.len();
                for ai in 0..na {
                    let ei = self.pats[pi].anchors[ai];
                    let (a, b, r) = self.pats[pi].edges[ei];
                    if r != col_red {
                        continue;
                    }
                    let p = &self.pats[pi];
                    let (ra, ba) = (p.red[a as usize].count_ones(), p.blue[a as usize].count_ones());
                    let (rb, bb) = (p.red[b as usize].count_ones(), p.blue[b as usize].count_ones());
                    let cm = p.common[ei];
                    for (x, y, rx, bx, ry, by) in [(u, v, ru, bu, rv, bv), (v, u, rv, bv, ru, bu)] {
                        // image of a needs >= ra red and >= ba blue assigned edges, minus one for the slack edge
                        if rx + 1 < ra || bx + 1 < ba || ry + 1 < rb || by + 1 < bb {
                            continue;
                        }
                        if rx + bx + ry + by + 2 < ra + ba + rb + bb {
                            continue;
                        }
                        // common neighbours by colour pair; the single slack edge can spoil at most one of them
                        let (xs, ys) = (x as usize, y as usize);
                        let have = [
                            (self.red[xs] & self.red[ys]).count_ones(),
                            (self.red[xs] & self.blue[ys]).count_ones(),
                            (self.blue[xs] & self.red[ys]).count_ones(),
                            (self.blue[xs] & self.blue[ys]).count_ones(),
                        ];
                        let short: u32 = (0..4).map(|i| (cm[i] as u32).saturating_sub(have[i])).sum();
                        if short > 1 {
                            continue;
                        }
                        if let Some(res) = self.embed(pi, a as usize, b as usize, x as usize, y as usize) {
                            return Some(res);
                        }
                    }
                }
            }
            self.scan += 1;
        }
        None
    }

    fn embed(&mut self, pi: usize, a: usize, b: usize, x: usize, y: usize) -> Option<(Vec<Lit>, u64, Vec<u8>, bool)> {
        self.stats.embed_calls += 1;
        let p = &self.pats[pi];
        let k = p.k;
        let mut phi = [u8::MAX; 32];
        phi[a] = x as u8;
        phi[b] = y as u8;
        // slack_mode 0: pretend the slack is already used (no unit images); 1: only leaves may use it
        let mut slack: Option<(usize, usize)> = if self.slack_mode == 0 { Some((usize::MAX, usize::MAX)) } else { None };
        CORE_SLACK.with(|c| c.set(self.slack_mode == 2));
        let used = (1u64 << x) | (1u64 << y);
        let (found, nodes) = if self.legacy_embed {
            let mut nodes = 0u64;
            let f = rec(p, &self.red, &self.blue, self.full, k, &mut phi, used, 2, &mut slack, &mut nodes, self.node_budget, usize::MAX);
            (f, nodes)
        } else {
            let mut ds = DomSearch::new(p, &self.red, &self.blue, &self.rge, &self.bge, self.full, self.node_budget, self.slack_mode == 2, slack.is_none());
            let f = ds.start(a, b, x, y, &mut phi, &mut slack);
            DEPTH_NODES.with(|d| {
                let mut d = d.borrow_mut();
                for (i, c) in ds.depth.iter().enumerate() {
                    d[i] += c;
                }
            });
            if self.check_embed && ds.nodes < self.node_budget {
                // cross-check against the reference search (both complete when no budget cut)
                let mut phi2 = [u8::MAX; 32];
                phi2[a] = x as u8;
                phi2[b] = y as u8;
                let mut sl2 = if self.slack_mode == 0 { Some((usize::MAX, usize::MAX)) } else { None };
                let mut n2 = 0u64;
                let f2 = rec(p, &self.red, &self.blue, self.full, k, &mut phi2, used, 2, &mut sl2, &mut n2, self.node_budget, usize::MAX);
                assert!(n2 >= self.node_budget || f == f2, "domain search {f} vs reference {f2} (pattern {pi}, anchor {a}-{b} at {x}-{y})");
            }
            (f, ds.nodes)
        };
        self.stats.nodes += nodes;
        self.pats[pi].calls += 1;
        self.pats[pi].nodes += nodes;
        if found {
            self.pats[pi].hits += 1;
        }
        if nodes >= self.node_budget {
            self.stats.budget_cut += 1;
        }
        if !found {
            return None;
        }
        let p = &self.pats[pi];
        // build the image clause
        let mut clause = Vec::with_capacity(p.edges.len());
        for &(pa, pb, r) in &p.edges {
            let var = evar(phi[pa as usize] as usize, phi[pb as usize] as usize) as Lit;
            clause.push((var << 1) | r as Lit);
        }
        // permutation of all N vertices extending verts[a] -> phi[a]
        let n = self.n;
        let mut perm = vec![u8::MAX; n];
        let mut used = 0u64;
        for q in 0..k {
            perm[p.verts[q] as usize] = phi[q];
            used |= 1 << phi[q];
        }
        let mut free = (0..n as u8).filter(|&z| used >> z & 1 == 0);
        for w in 0..n {
            if perm[w] == u8::MAX {
                perm[w] = free.next().unwrap();
            }
        }
        if self.check_embed {
            let (mut wrong, mut unas) = (0, 0);
            for &(pa, pb, r) in &p.edges {
                let (u, v) = (phi[pa as usize] as usize, phi[pb as usize] as usize);
                let (is_r, is_b) = (self.red[u] >> v & 1 == 1, self.blue[u] >> v & 1 == 1);
                if (r && is_b) || (!r && is_r) {
                    wrong += 1;
                } else if !is_r && !is_b {
                    unas += 1;
                }
            }
            let distinct = (0..k).map(|q| 1u64 << phi[q]).fold(0, |m, b| m | b).count_ones() as usize == k;
            assert!(distinct && wrong == 0 && unas <= (self.slack_mode != 0) as usize, "invalid image: distinct {distinct} wrong {wrong} unassigned {unas}");
        }
        self.stats.images += 1;
        if slack.is_none() || slack == Some((usize::MAX, usize::MAX)) {
            self.stats.conflicts += 1;
        }
        Some((clause, p.lemma, perm, p.flip))
    }
}

/// Embedding search with incremental bitset domains (Glasgow-style). Same contract as [`rec`]: every pattern edge
/// must already have its colour, except at most one unassigned (`slack`). Per unmapped pattern vertex q with a mapped
/// neighbour, `dom[q]` holds the images whose edges to all mapped neighbours' images have the pattern colour and
/// `loose[q]` those with exactly one such edge unassigned and the rest right. Placing w -> z updates only w's
/// neighbours (one AND/OR each). Each node checks for empty domains, at most one vertex relying on the slack, and
/// a Hall bound (the constrained vertices need at least as many distinct candidates), then branches on the smallest
/// domain. Independent vertices (all neighbours mapped: leaves, book pages) are placed by [`place_leaves`].
struct DomSearch<'a> {
    p: &'a Pat,
    red: &'a [u64],
    blue: &'a [u64],
    full: u64,
    budget: u64,
    core_slack: bool,
    nodes: u64,
    depth: [u64; 33],
    /// degree-feasible images of each pattern vertex (one edge short allowed while the slack is free)
    init: [u64; 32],
}

impl<'a> DomSearch<'a> {
    /// `rge[d]` / `bge[d]`: the vertices with at least d red / blue assigned edges.
    #[allow(clippy::too_many_arguments)]
    fn new(p: &'a Pat, red: &'a [u64], blue: &'a [u64], rge: &[u64], bge: &[u64], full: u64, budget: u64, core_slack: bool, slack_free: bool) -> Self {
        let sl = slack_free as usize;
        let mut init = [0u64; 32];
        for q in 0..p.k {
            let (rd, bd) = (p.red[q].count_ones() as usize, p.blue[q].count_ones() as usize);
            init[q] = rge[rd.saturating_sub(sl).min(rge.len() - 1)] & bge[bd.saturating_sub(sl).min(bge.len() - 1)];
        }
        DomSearch { p, red, blue, full, budget, core_slack, nodes: 0, depth: [0; 33], init }
    }

    /// Domains after placing w -> z, given the mapped set `prev` before w.
    #[inline]
    fn update(&self, w: usize, z: usize, prev: u32, dom: &mut [u64; 32], loose: &mut [u64; 32]) {
        let p = self.p;
        let unas = self.full & !(self.red[z] | self.blue[z]) & !(1u64 << z);
        let mut x = (p.red[w] | p.blue[w]) & !prev & !(1u32 << w);
        while x != 0 {
            let q = x.trailing_zeros() as usize;
            x &= x - 1;
            let want = if p.red[w] >> q & 1 == 1 { self.red[z] } else { self.blue[z] };
            let (d, l) = if (p.red[q] | p.blue[q]) & prev == 0 { (self.init[q], 0) } else { (dom[q], loose[q]) };
            dom[q] = d & want;
            loose[q] = (l & want) | (d & unas);
        }
    }

    fn start(&mut self, a: usize, b: usize, x: usize, y: usize, phi: &mut [u8; 32], slack: &mut Option<(usize, usize)>) -> bool {
        let (mut dom, mut loose) = ([0u64; 32], [0u64; 32]);
        if self.init[a] >> x & 1 == 0 || self.init[b] >> y & 1 == 0 {
            self.nodes += 1;
            return false;
        }
        self.update(a, x, 0, &mut dom, &mut loose);
        self.update(b, y, 1 << a, &mut dom, &mut loose);
        self.rec(phi, (1u64 << x) | (1u64 << y), (1u32 << a) | (1u32 << b), &dom, &loose, slack)
    }

    fn rec(&mut self, phi: &mut [u8; 32], used: u64, mmask: u32, dom: &[u64; 32], loose: &[u64; 32], slack: &mut Option<(usize, usize)>) -> bool {
        let p = self.p;
        let k = p.k;
        self.nodes += 1;
        self.depth[(mmask.count_ones() as usize).min(32)] += 1;
        if self.nodes > self.budget {
            return false;
        }
        let kmask: u32 = if k >= 32 { u32::MAX } else { (1u32 << k) - 1 };
        if mmask == kmask {
            return true;
        }
        let slack_free = slack.is_none();
        let (mut best, mut best_size, mut best_c) = (usize::MAX, u32::MAX, 0u32);
        let (mut need_loose, mut union, mut cnt) = (0, 0u64, 0u32);
        let mut x = kmask & !mmask;
        while x != 0 {
            let q = x.trailing_zeros() as usize;
            x &= x - 1;
            let nb = p.red[q] | p.blue[q];
            if nb & mmask == 0 {
                continue;
            }
            let st = dom[q] & !used;
            let lo = if slack_free { loose[q] & !used } else { 0 };
            if st == 0 {
                if lo == 0 {
                    return false;
                }
                need_loose += 1;
                if need_loose > 1 {
                    return false;
                }
            }
            union |= st | lo;
            cnt += 1;
            if nb & !mmask == 0 {
                continue; // independent: placed together by matching
            }
            let size = st.count_ones() + if self.core_slack { lo.count_ones() } else { 0 };
            let c = (nb & mmask).count_ones();
            if size < best_size || (size == best_size && c > best_c) {
                (best, best_size, best_c) = (q, size, c);
            }
        }
        if union.count_ones() < cnt {
            return false;
        }
        if best == usize::MAX {
            return place_leaves(p, self.red, self.blue, self.full, k, phi, used, slack, &mut self.nodes, self.budget);
        }
        let w = best;
        let (rd, bd) = (p.red[w].count_ones(), p.blue[w].count_ones());
        let (red, blue) = (self.red, self.blue);
        let filt = |z: usize, sl: u32| red[z].count_ones() + sl >= rd && blue[z].count_ones() + sl >= bd;
        let st = dom[w] & !used;
        let mut c = st;
        while c != 0 {
            let z = c.trailing_zeros() as usize;
            c &= c - 1;
            if !filt(z, slack_free as u32) {
                continue;
            }
            let (mut d2, mut l2) = (*dom, *loose);
            self.update(w, z, mmask, &mut d2, &mut l2);
            phi[w] = z as u8;
            if self.rec(phi, used | 1 << z, mmask | 1 << w, &d2, &l2, slack) {
                return true;
            }
            phi[w] = u8::MAX;
            if self.nodes > self.budget {
                return false;
            }
        }
        if slack_free && self.core_slack {
            let mut c = loose[w] & !used;
            while c != 0 {
                let z = c.trailing_zeros() as usize;
                c &= c - 1;
                if !filt(z, 1) {
                    continue;
                }
                let (mut d2, mut l2) = (*dom, *loose);
                self.update(w, z, mmask, &mut d2, &mut l2);
                phi[w] = z as u8;
                *slack = Some((w, usize::MAX));
                if self.rec(phi, used | 1 << z, mmask | 1 << w, &d2, &l2, slack) {
                    return true;
                }
                *slack = None;
                phi[w] = u8::MAX;
                if self.nodes > self.budget {
                    return false;
                }
            }
        }
        false
    }
}

/// Backtracking embedding: every pattern edge must already have its colour in the assignment, except at most one
/// that is still unassigned (`slack`). An edge assigned the opposite colour satisfies the clause: no match.
#[allow(clippy::too_many_arguments)]
fn rec(
    p: &Pat,
    red: &[u64],
    blue: &[u64],
    full: u64,
    k: usize,
    phi: &mut [u8; 32],
    used: u64,
    mapped: usize,
    slack: &mut Option<(usize, usize)>,
    nodes: &mut u64,
    budget: u64,
    last: usize,
) -> bool {
    *nodes += 1;
    DEPTH_NODES.with(|d| d.borrow_mut()[mapped.min(32)] += 1);
    if *nodes > budget {
        return false;
    }
    if mapped == k {
        return true;
    }
    if !forward_ok(p, red, blue, full, k, phi, used, slack.is_none(), last) {
        return false;
    }
    // choose the unmapped CORE vertex (degree >= 2 in the pattern) with the most edges into the mapped set;
    // leaves are placed last, all at once, by a small matching
    let mut best = usize::MAX;
    let mut best_c = 0u32;
    let mut mmask = 0u32;
    for q in 0..k {
        if phi[q] != u8::MAX {
            mmask |= 1 << q;
        }
    }
    // vertices whose neighbours are all mapped are "independent": they only need distinct images satisfying their
    // own edges, so they are placed together by matching at the end (leaves, book pages, ...)
    let umask: u32 = !mmask & (if k >= 32 { u32::MAX } else { (1u32 << k) - 1 });
    let mut fallback = usize::MAX;
    for q in 0..k {
        if phi[q] != u8::MAX {
            continue;
        }
        let nb = p.red[q] | p.blue[q];
        let c = (nb & mmask).count_ones();
        if c == 0 {
            continue;
        }
        if nb & umask == 0 {
            continue; // independent
        }
        if best == usize::MAX || c > best_c {
            best = q;
            best_c = c;
        }
        fallback = q;
    }
    let _ = fallback;
    if best == usize::MAX && (0..k).any(|q| phi[q] == u8::MAX && (p.red[q] | p.blue[q]) & !mmask & umask != 0) {
        // remaining dependent vertices are not adjacent to the mapped set yet: map an adjacent independent one
        for q in 0..k {
            if phi[q] == u8::MAX && (p.red[q] | p.blue[q]) & mmask != 0 {
                best = q;
                break;
            }
        }
    }
    if best == usize::MAX {
        return place_leaves(p, red, blue, full, k, phi, used, slack, nodes, budget);
    }
    let w = best;
    // candidate masks: strict (all constraining edges already coloured right) and, if slack is free,
    // loose sets where exactly one constraining edge is unassigned
    let mut strict = full & !used;
    let mut cons: [(u64, u64, usize); 32] = [(0, 0, 0); 32];
    let mut nc = 0;
    let mut x = mmask & (p.red[w] | p.blue[w]);
    while x != 0 {
        let q = x.trailing_zeros() as usize;
        x &= x - 1;
        let img = phi[q] as usize;
        let want = if p.red[w] >> q & 1 == 1 { red[img] } else { blue[img] };
        let unas = full & !(red[img] | blue[img]) & !(1u64 << img);
        strict &= want;
        cons[nc] = (want, unas, q);
        nc += 1;
    }
    // degree filter: z needs >= (pattern red degree of w) red-assigned edges and likewise blue, minus one if the
    // slack edge is still free (it may be one of w's edges)
    let rd = p.red[w].count_ones();
    let bd = p.blue[w].count_ones();
    let filt = |z: usize, slack_free: bool| -> bool {
        let sl = slack_free as u32;
        red[z].count_ones() + sl >= rd && blue[z].count_ones() + sl >= bd
    };
    let mut c = strict;
    while c != 0 {
        let z = c.trailing_zeros() as usize;
        c &= c - 1;
        if !filt(z, slack.is_none()) {
            continue;
        }
        phi[w] = z as u8;
        if rec(p, red, blue, full, k, phi, used | 1 << z, mapped + 1, slack, nodes, budget, w) {
            return true;
        }
        phi[w] = u8::MAX;
        if *nodes > budget {
            return false;
        }
    }
    if slack.is_none() && CORE_SLACK.with(|c| c.get()) {
        for i in 0..nc {
            let mut m = full & !used & cons[i].1;
            for (j, item) in cons.iter().enumerate().take(nc) {
                if j != i {
                    m &= item.0;
                }
            }
            while m != 0 {
                let z = m.trailing_zeros() as usize;
                m &= m - 1;
                if !filt(z, true) {
                    continue;
                }
                phi[w] = z as u8;
                *slack = Some((w, cons[i].2));
                if rec(p, red, blue, full, k, phi, used | 1 << z, mapped + 1, slack, nodes, budget, w) {
                    return true;
                }
                *slack = None;
                phi[w] = u8::MAX;
                if *nodes > budget {
                    return false;
                }
            }
        }
    }
    false
}

/// All core vertices are mapped; every unmapped vertex is a leaf hanging off a mapped parent. Find distinct images:
/// each leaf needs an edge of its colour from its parent's image, except at most one (if the slack is free) that may
/// use an unassigned edge. Small DFS, fewest-candidates first.
#[allow(clippy::too_many_arguments)]
fn place_leaves(
    p: &Pat,
    red: &[u64],
    blue: &[u64],
    full: u64,
    k: usize,
    phi: &mut [u8; 32],
    used: u64,
    slack: &mut Option<(usize, usize)>,
    nodes: &mut u64,
    budget: u64,
) -> bool {
    let mut leaves: Vec<(usize, u64, u64, usize)> = Vec::new(); // (leaf, strict mask, loose mask, parent)
    for w in 0..k {
        if phi[w] != u8::MAX {
            continue;
        }
        // all neighbours of w are mapped: strict = every edge already has its colour; loose = exactly one unassigned
        let nb = p.red[w] | p.blue[w];
        let mut cons: Vec<(u64, u64, usize)> = Vec::new();
        let mut y = nb;
        while y != 0 {
            let q = y.trailing_zeros() as usize;
            y &= y - 1;
            let img = phi[q] as usize;
            if img == u8::MAX as usize {
                return false;
            }
            let want = if p.red[w] >> q & 1 == 1 { red[img] } else { blue[img] };
            let unas = full & !(red[img] | blue[img]) & !(1u64 << img);
            cons.push((want, unas, q));
        }
        let strict = cons.iter().fold(full, |m, c| m & c.0);
        let mut loose = 0u64;
        for i in 0..cons.len() {
            let mut m = cons[i].1;
            for (j, c) in cons.iter().enumerate() {
                if j != i {
                    m &= c.0;
                }
            }
            loose |= m;
        }
        leaves.push((w, strict, loose, cons[0].2));
    }
    /// Kuhn bipartite matching: leaves -> distinct vertices; cand[i] = allowed images of leaf i.
    fn matching(cand: &[u64], nodes: &mut u64) -> Option<Vec<u8>> {
        fn augment(i: usize, cand: &[u64], seen: &mut u64, owner: &mut [u8; 64], img: &mut [u8], nodes: &mut u64) -> bool {
            let mut c = cand[i] & !*seen;
            while c != 0 {
                *nodes += 1;
                let z = c.trailing_zeros() as usize;
                c &= c - 1;
                *seen |= 1 << z;
                if owner[z] == u8::MAX || augment(owner[z] as usize, cand, seen, owner, img, nodes) {
                    owner[z] = i as u8;
                    img[i] = z as u8;
                    return true;
                }
            }
            false
        }
        let mut owner = [u8::MAX; 64];
        let mut img = vec![u8::MAX; cand.len()];
        for i in 0..cand.len() {
            let mut seen = 0u64;
            if !augment(i, cand, &mut seen, &mut owner, &mut img, nodes) {
                return None;
            }
        }
        Some(img)
    }
    *nodes += 1;
    let _ = budget;
    let slack_free = slack.is_none();
    // all independent vertices share the same candidate masks (stars, books): placing them is a count, not a search
    if leaves.len() > 1 && leaves.iter().all(|l| l.1 == leaves[0].1 && l.2 == leaves[0].2) {
        let st = leaves[0].1 & !used;
        let lo = leaves[0].2 & !used & !st;
        let need = leaves.len() as u32;
        let have = st.count_ones();
        if have >= need {
            let mut m = st;
            for l in &leaves {
                let z = m.trailing_zeros() as usize;
                m &= m - 1;
                phi[l.0] = z as u8;
            }
            return true;
        }
        if slack_free && have + 1 == need && lo != 0 {
            let mut m = st;
            for l in &leaves[..leaves.len() - 1] {
                let z = m.trailing_zeros() as usize;
                m &= m - 1;
                phi[l.0] = z as u8;
            }
            let last = leaves[leaves.len() - 1];
            phi[last.0] = lo.trailing_zeros() as u8;
            *slack = Some((last.0, last.3));
            return true;
        }
        return false;
    }
    let strict: Vec<u64> = leaves.iter().map(|l| l.1 & !used).collect();
    let empty: Vec<usize> = (0..leaves.len()).filter(|&i| strict[i] == 0).collect();
    if empty.len() > slack_free as usize {
        return false;
    }
    if empty.is_empty() {
        if let Some(img) = matching(&strict, nodes) {
            for (i, l) in leaves.iter().enumerate() {
                phi[l.0] = img[i];
            }
            return true;
        }
    }
    if !slack_free {
        return false;
    }
    // exactly one leaf uses an unassigned edge (forced if some leaf has no strict candidate)
    let tries: Vec<usize> = if empty.len() == 1 { empty.clone() } else { (0..leaves.len()).collect() };
    for i in tries {
        let mut cand = strict.clone();
        cand[i] = leaves[i].2 & !used;
        if cand[i] == 0 {
            continue;
        }
        if let Some(img) = matching(&cand, nodes) {
            for (j, l) in leaves.iter().enumerate() {
                phi[l.0] = img[j];
            }
            *slack = Some((leaves[i].0, leaves[i].3));
            return true;
        }
    }
    false
}

/// Forward check: every unmapped pattern vertex with mapped neighbours needs a candidate image. A candidate is
/// strict if all its edges to mapped images already have the pattern colour; a vertex may instead be "loose" (exactly
/// one such edge unassigned) only while the slack is free, and at most one vertex can rely on that.
#[allow(clippy::too_many_arguments)]
fn forward_ok(
    p: &Pat,
    red: &[u64],
    blue: &[u64],
    full: u64,
    k: usize,
    phi: &[u8; 32],
    used: u64,
    slack_free: bool,
    last: usize,
) -> bool {
    // only vertices adjacent to the vertex placed last gained constraints (usize::MAX: check everything)
    let focus: u32 = if last == usize::MAX { u32::MAX } else { p.red[last] | p.blue[last] };
    let mut mmask = 0u32;
    for q in 0..k {
        if phi[q] != u8::MAX {
            mmask |= 1 << q;
        }
    }
    let mut need_loose = 0;
    for x in 0..k {
        if phi[x] != u8::MAX || focus >> x & 1 == 0 {
            continue;
        }
        let nb = (p.red[x] | p.blue[x]) & mmask;
        if nb == 0 {
            continue;
        }
        let mut strict = full & !used;
        let mut cons: [(u64, u64); 32] = [(0, 0); 32];
        let mut nc = 0;
        let mut y = nb;
        while y != 0 {
            let q = y.trailing_zeros() as usize;
            y &= y - 1;
            let img = phi[q] as usize;
            let want = if p.red[x] >> q & 1 == 1 { red[img] } else { blue[img] };
            strict &= want;
            cons[nc] = (want, full & !(red[img] | blue[img]) & !(1u64 << img));
            nc += 1;
        }
        if strict != 0 {
            continue;
        }
        if !slack_free {
            return false;
        }
        let mut ok = false;
        for i in 0..nc {
            let mut m = full & !used & cons[i].1;
            for (j, c) in cons.iter().enumerate().take(nc) {
                if j != i {
                    m &= c.0;
                }
            }
            if m != 0 {
                ok = true;
                break;
            }
        }
        if !ok {
            return false;
        }
        need_loose += 1;
        if need_loose > 1 {
            return false;
        }
    }
    true
}

/// Canonical key of an edge-2-coloured graph on k <= 32 vertices: refinement by (red degree, blue degree) into each
/// cell, then individualisation search keeping the lexicographically largest (red bits, blue bits) string.
pub(crate) fn canon_key(k: usize, red: &[u32; 32], blue: &[u32; 32]) -> Vec<u64> {
    fn refine(k: usize, red: &[u32; 32], blue: &[u32; 32], cells: &mut Vec<Vec<u8>>) {
        let _ = k;
        loop {
            let mut changed = false;
            'outer: for wi in 0..cells.len() {
                let wm: u32 = cells[wi].iter().fold(0, |m, &v| m | 1 << v);
                for ci in 0..cells.len() {
                    if cells[ci].len() < 2 {
                        continue;
                    }
                    let sig = |v: u8| ((red[v as usize] & wm).count_ones(), (blue[v as usize] & wm).count_ones());
                    let s0 = sig(cells[ci][0]);
                    if cells[ci].iter().all(|&v| sig(v) == s0) {
                        continue;
                    }
                    let mut c = cells[ci].clone();
                    c.sort_by_key(|&v| sig(v));
                    let mut parts: Vec<Vec<u8>> = Vec::new();
                    for v in c {
                        match parts.last_mut() {
                            Some(pp) if sig(pp[0]) == sig(v) => pp.push(v),
                            _ => parts.push(vec![v]),
                        }
                    }
                    cells.splice(ci..ci + 1, parts);
                    changed = true;
                    break 'outer;
                }
            }
            if !changed {
                break;
            }
        }
    }
    fn key(k: usize, red: &[u32; 32], blue: &[u32; 32], order: &[u8]) -> Vec<u64> {
        let mut out = vec![k as u64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let mut bit = 0usize;
        for j in 1..k {
            for i in 0..j {
                let (a, b) = (order[i] as usize, order[j] as usize);
                let w = 1 + bit / 64;
                if red[a] >> b & 1 == 1 {
                    out[w] |= 1 << (63 - bit % 64);
                }
                if blue[a] >> b & 1 == 1 {
                    out[w + 8] |= 1 << (63 - bit % 64);
                }
                bit += 1;
            }
        }
        out
    }
    fn search(k: usize, red: &[u32; 32], blue: &[u32; 32], cells: Vec<Vec<u8>>, best: &mut Option<Vec<u64>>) {
        match cells.iter().position(|c| c.len() > 1) {
            None => {
                let order: Vec<u8> = cells.iter().map(|c| c[0]).collect();
                let kk = key(k, red, blue, &order);
                if best.as_ref().map_or(true, |b| kk > *b) {
                    *best = Some(kk);
                }
            }
            Some(ci) => {
                // twins (same red and blue neighbourhoods apart from each other) are exchanged by an automorphism:
                // their subtrees give the same keys, so individualise one representative per twin class
                let twin = |v: u8, w: u8| -> bool {
                    let (v, w) = (v as usize, w as usize);
                    let m = !((1u32 << v) | (1u32 << w));
                    red[v] & m == red[w] & m && blue[v] & m == blue[w] & m
                };
                let mut tried: Vec<u8> = Vec::new();
                for idx in 0..cells[ci].len() {
                    let v = cells[ci][idx];
                    if tried.iter().any(|&w| twin(v, w)) {
                        continue;
                    }
                    tried.push(v);
                    let mut c2 = cells.clone();
                    c2[ci].remove(idx);
                    c2.insert(ci, vec![v]);
                    refine(k, red, blue, &mut c2);
                    search(k, red, blue, c2, best);
                }
            }
        }
    }
    let mut cells = vec![(0..k as u8).collect::<Vec<u8>>()];
    refine(k, red, blue, &mut cells);
    let mut best = None;
    search(k, red, blue, cells, &mut best);
    best.unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canon_key_invariant() {
        let mut seed = 99u64;
        let mut rnd = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let k = 3 + (rnd() % 8) as usize;
            let mut red = [0u32; 32];
            let mut blue = [0u32; 32];
            for i in 0..k {
                for j in i + 1..k {
                    match rnd() % 3 {
                        0 => {
                            red[i] |= 1 << j;
                            red[j] |= 1 << i;
                        }
                        1 => {
                            blue[i] |= 1 << j;
                            blue[j] |= 1 << i;
                        }
                        _ => {}
                    }
                }
            }
            let mut p: Vec<usize> = (0..k).collect();
            for i in (1..k).rev() {
                p.swap(i, (rnd() % (i as u64 + 1)) as usize);
            }
            let mut r2 = [0u32; 32];
            let mut b2 = [0u32; 32];
            for i in 0..k {
                for j in 0..k {
                    if red[i] >> j & 1 == 1 {
                        r2[p[i]] |= 1 << p[j];
                    }
                    if blue[i] >> j & 1 == 1 {
                        b2[p[i]] |= 1 << p[j];
                    }
                }
            }
            assert_eq!(canon_key(k, &red, &blue), canon_key(k, &r2, &b2));
            // colour swap must change the key unless symmetric; check red-only vs blue-only differ
        }
        let mut r = [0u32; 32];
        r[0] = 2;
        r[1] = 1;
        let z = [0u32; 32];
        assert_ne!(canon_key(2, &r, &z), canon_key(2, &z, &r));
    }
}
