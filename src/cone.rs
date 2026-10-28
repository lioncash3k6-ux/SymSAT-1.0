//! Feasible-cone gluing engine (`glue --mode cone`, `monster cone`): an uncertified prototype, built to measure
//! whether cone-level propagation beats CDCL on the gluing pairs (IDEAS.md, "feasible-cone engine").
//!
//! v's red side A is an (s-1,t)-good graph on d vertices and its blue side B an (s,t-1)-good graph on m vertices.
//! Every b in B gets a cone: its red neighbourhood in A, a d-bit mask. A monochromatic clique of the glued K_N that
//! avoids v is a clique of A plus a clique of B with every cross edge in its colour (cliques through v are excluded
//! by the goodness of A and B), so the pair is SAT iff the cones can be chosen such that
//!   - for every red j-clique Q of B (2 <= j <= s-1), the common red neighbourhood of Q holds no red K_{s-j} of A;
//!   - for every blue j-clique P of B (1 <= j <= t-2), the common blue neighbourhood of P holds no blue K_{t-j} of A.
//! j = 1 fixes the feasible cones, j = 2 gives two compatibility bit matrices per A (red and blue edges of B), larger
//! cliques are checked when all but one of their vertices hold a cone. Search: forward checking on bitset domains,
//! smallest domain first. Options: degree windows (every vertex of K_N has red degree <= R(s-1,t)-1 and blue degree
//! <= R(s,t-1)-1, the same facts the catalogue route rests on) and maintained arc consistency. No proof is produced,
//! so a run of this engine certifies nothing.

use crate::graph::{mask, Graph};

/// Largest n with an (s,t)-good graph on n vertices, i.e. R(s,t) - 1, from McKay's table (None if unknown).
fn max_good(s: usize, t: usize) -> Option<usize> {
    let mut n = 0;
    while n <= 64 {
        match crate::catalog::mckay_count(s, t, n + 1) {
            Some(0) => return Some(n),
            Some(_) => n += 1,
            None => return None,
        }
    }
    None
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Opts {
    /// degree windows from R(s-1,t) and R(s,t-1)
    pub degrees: bool,
    /// maintained arc consistency between open vertices (on top of forward checking)
    pub mac: bool,
}

impl Opts {
    /// `MONSTER_CONE=deg,mac` (either, both or none; default both)
    pub fn from_env() -> Opts {
        match std::env::var("MONSTER_CONE") {
            Ok(v) => Opts { degrees: v.split(',').any(|x| x == "deg"), mac: v.split(',').any(|x| x == "mac") },
            Err(_) => Opts { degrees: true, mac: true },
        }
    }
}

/// Everything about one A that the search needs, computed once per A.
pub struct Table {
    pub s: usize,
    pub t: usize,
    pub d: usize,
    /// feasible cones (red neighbourhoods in A), in increasing order
    pub cones: Vec<u32>,
    /// u64 words per domain
    pub w: usize,
    /// row i: the cones compatible with cones[i] across a red (resp. blue) edge of B
    red_ok: Vec<u64>,
    blue_ok: Vec<u64>,
    /// row a: the cones containing vertex a of A
    with_a: Vec<u64>,
    /// red / blue clique number of every subset of A
    wr: Vec<u8>,
    wb: Vec<u8>,
    /// red degree of every vertex inside A
    rdeg: Vec<usize>,
    /// R(s-1,t) - 1 and R(s,t-1) - 1 when known: the largest red and blue degree of any vertex of K_N
    rmax: Option<usize>,
    bmax: Option<usize>,
}

/// Clique number (in one colour) of every vertex subset of g, by the recursion on its lowest vertex.
fn clique_numbers(g: &Graph, red: bool) -> Vec<u8> {
    let d = g.n;
    let full = mask(d);
    let mut w = vec![0u8; 1 << d];
    for x in 1..(1usize << d) {
        let v = x.trailing_zeros() as usize;
        let rest = x & (x - 1);
        let nb = if red { g.adj[v] } else { !g.adj[v] & full & !(1 << v) } as usize;
        w[x] = w[rest].max(1 + w[rest & nb]);
    }
    w
}

impl Table {
    pub fn new(s: usize, t: usize, a: &Graph) -> Table {
        let d = a.n;
        assert!(d <= 16, "cone tables need d <= 16");
        let full = mask(d);
        let wr = clique_numbers(a, true);
        let wb = clique_numbers(a, false);
        // j = 1 (blue): the blue neighbourhood of b in A holds no blue K_{t-1} of A
        let cones: Vec<u32> = (0..=full).filter(|&c| (wb[(full & !c) as usize] as usize) < t - 1).collect();
        let w = (cones.len() + 63) / 64;
        assert!(w <= 128, "more than 8192 feasible cones");
        let mut red_ok = vec![0u64; cones.len() * w];
        let mut blue_ok = vec![0u64; cones.len() * w];
        let mut with_a = vec![0u64; d * w];
        for (i, &c) in cones.iter().enumerate() {
            for (k, &e) in cones.iter().enumerate() {
                // j = 2: a red edge bb' needs no red K_{s-2} in R_b ∩ R_b', a blue one no blue K_{t-2} in S_b ∩ S_b'
                if (wr[(c & e) as usize] as usize) < s - 2 {
                    red_ok[i * w + k / 64] |= 1 << (k % 64);
                }
                if (wb[(full & !c & !e) as usize] as usize) < t - 2 {
                    blue_ok[i * w + k / 64] |= 1 << (k % 64);
                }
            }
            for x in 0..d {
                if c >> x & 1 == 1 {
                    with_a[x * w + i / 64] |= 1 << (i % 64);
                }
            }
        }
        let rdeg = (0..d).map(|x| a.adj[x].count_ones() as usize).collect();
        Table { s, t, d, cones, w, red_ok, blue_ok, with_a, wr, wb, rdeg, rmax: max_good(s - 1, t), bmax: max_good(s, t - 1) }
    }
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Stats {
    /// cone assignments tried by branching
    pub nodes: u64,
    /// branches closed by propagation
    pub fails: u64,
}

const OPEN: u32 = u32::MAX;

/// A clique of B with at least 3 vertices whose common neighbourhood is constrained.
#[derive(Clone, Copy)]
struct Clique {
    members: u32,
    j: u8,
    red: bool,
}

pub struct Search<'a> {
    tab: &'a Table,
    opts: Opts,
    m: usize,
    w: usize,
    red: [u32; 32],
    cliques: Vec<Clique>,
    by_v: Vec<Vec<u32>>,
    /// degree windows: number of b whose cone contains a must lie in [lo[a], hi[a]] (when opts.degrees)
    lo: [i32; 16],
    hi: [i32; 16],
    /// one frame per search depth: m domains of w words, and the cone index each vertex holds (OPEN = none)
    dom: Vec<u64>,
    asg: Vec<u32>,
    pub stats: Stats,
    /// on SAT: the cone of every vertex of B
    pub solution: Option<Vec<u32>>,
}

impl<'a> Search<'a> {
    pub fn new(tab: &'a Table, b: &Graph, opts: Opts) -> Search<'a> {
        let (s, t, d, m, w) = (tab.s, tab.t, tab.d, b.n, tab.w);
        let mut cliques = Vec::new();
        for j in 3..s {
            for q in b.sets(j, true) {
                cliques.push(Clique { members: q, j: j as u8, red: true });
            }
        }
        for j in 3..t - 1 {
            for q in b.sets(j, false) {
                cliques.push(Clique { members: q, j: j as u8, red: false });
            }
        }
        let mut by_v = vec![Vec::new(); m];
        for (i, c) in cliques.iter().enumerate() {
            let mut x = c.members;
            while x != 0 {
                by_v[x.trailing_zeros() as usize].push(i as u32);
                x &= x - 1;
            }
        }
        let frames = m + 2;
        let mut dom = vec![0u64; frames * m * w];
        let (mut lo, mut hi) = ([0i32; 16], [m as i32; 16]);
        let window = match (opts.degrees, tab.rmax, tab.bmax) {
            (true, Some(rmax), Some(bmax)) => Some(((d + m) as i32 - bmax as i32, rmax as i32)),
            _ => None,
        };
        for v in 0..m {
            // b's red degree in K_N is |cone| + its red degree in B (v-b is blue)
            let rb = b.adj[v].count_ones() as i32;
            for (k, &c) in tab.cones.iter().enumerate() {
                let r = c.count_ones() as i32 + rb;
                if window.map_or(true, |(rmin, rmax)| r >= rmin && r <= rmax) {
                    dom[v * w + k / 64] |= 1 << (k % 64);
                }
            }
        }
        if let Some((rmin, rmax)) = window {
            // a's red degree is 1 (to v) + its red degree in A + the number of cones containing a
            for x in 0..d {
                lo[x] = rmin - 1 - tab.rdeg[x] as i32;
                hi[x] = rmax - 1 - tab.rdeg[x] as i32;
            }
        }
        let mut red = [0u32; 32];
        red[..m].copy_from_slice(&b.adj[..m]);
        Search { tab, opts, m, w, red, cliques, by_v, lo, hi, dom, asg: vec![OPEN; frames * m], stats: Stats::default(), solution: None }
    }

    /// true iff some choice of cones meets every constraint, i.e. the glued pair is SAT
    pub fn run(&mut self) -> bool {
        if self.m == 0 {
            self.solution = Some(Vec::new());
            return true;
        }
        if (0..self.m).any(|v| self.dom[v * self.w..(v + 1) * self.w].iter().all(|&x| x == 0)) {
            return false;
        }
        self.propagate(0, None) && self.search(0)
    }

    fn search(&mut self, lvl: usize) -> bool {
        let (m, w) = (self.m, self.w);
        let mut best = u32::MAX;
        let mut bv = usize::MAX;
        for v in 0..m {
            if self.asg[lvl * m + v] == OPEN {
                let base = (lvl * m + v) * w;
                let c: u32 = self.dom[base..base + w].iter().map(|x| x.count_ones()).sum();
                if c < best {
                    best = c;
                    bv = v;
                }
            }
        }
        if bv == usize::MAX {
            self.solution = Some((0..m).map(|v| self.tab.cones[self.asg[lvl * m + v] as usize]).collect());
            return true;
        }
        let base = (lvl * m + bv) * w;
        let vals: Vec<u64> = self.dom[base..base + w].to_vec();
        for (k, &word) in vals.iter().enumerate() {
            let mut x = word;
            while x != 0 {
                let ci = k * 64 + x.trailing_zeros() as usize;
                x &= x - 1;
                // the child frame starts as a copy of this one, with bv holding cone ci
                let (lo, hi) = self.dom.split_at_mut((lvl + 1) * m * w);
                hi[..m * w].copy_from_slice(&lo[lvl * m * w..]);
                let (alo, ahi) = self.asg.split_at_mut((lvl + 1) * m);
                ahi[..m].copy_from_slice(&alo[lvl * m..]);
                let row = &mut hi[bv * w..(bv + 1) * w];
                row.fill(0);
                row[ci / 64] = 1 << (ci % 64);
                ahi[bv] = ci as u32;
                self.stats.nodes += 1;
                if self.propagate(lvl + 1, Some(bv)) {
                    if self.search(lvl + 1) {
                        return true;
                    }
                } else {
                    self.stats.fails += 1;
                }
            }
        }
        false
    }

    /// Propagation to a fixpoint in frame `lvl`: forward checking from every newly assigned vertex (starting with
    /// `start`), then the degree windows and arc consistency when enabled; a vertex whose domain shrinks to one cone
    /// is assigned and forward-checked in turn. false = some domain is empty or some constraint fails.
    fn propagate(&mut self, lvl: usize, start: Option<usize>) -> bool {
        let Search { tab, opts, m, w, red, cliques, by_v, lo, hi, dom, asg, .. } = self;
        let (tab, opts, m, w): (&Table, Opts, usize, usize) = (*tab, *opts, *m, *w);
        let full = mask(tab.d);
        let dom = &mut dom[lvl * m * w..(lvl + 1) * m * w];
        let asg = &mut asg[lvl * m..(lvl + 1) * m];
        let mut queue = [0usize; 32];
        let (mut qn, mut qi) = (0, 0);
        if let Some(u) = start {
            queue[0] = u;
            qn = 1;
        }
        // an open vertex left with one cone becomes assigned and joins the queue
        macro_rules! settle {
            ($v:expr, $cnt:expr) => {
                if $cnt == 0 {
                    return false;
                }
                if $cnt == 1 && asg[$v] == OPEN {
                    asg[$v] = first_bit(&dom[$v * w..($v + 1) * w]);
                    queue[qn] = $v;
                    qn += 1;
                }
            };
        }
        loop {
            while qi < qn {
                let u = queue[qi];
                qi += 1;
                let cu = asg[u] as usize;
                // binary constraints with every other vertex (assigned ones too, so no pair is skipped)
                for v in 0..m {
                    if v == u {
                        continue;
                    }
                    let row = if red[u] >> v & 1 == 1 { &tab.red_ok[cu * w..(cu + 1) * w] } else { &tab.blue_ok[cu * w..(cu + 1) * w] };
                    let mut cnt = 0;
                    for k in 0..w {
                        dom[v * w + k] &= row[k];
                        cnt += dom[v * w + k].count_ones();
                    }
                    settle!(v, cnt);
                }
                // cliques of B through u with at least 3 vertices
                for &ci in &by_v[u] {
                    let c = cliques[ci as usize];
                    let limit = if c.red { tab.s } else { tab.t } - c.j as usize;
                    let om = if c.red { &tab.wr } else { &tab.wb };
                    let (mut open, mut x) = (0u32, full);
                    let mut mm = c.members;
                    while mm != 0 {
                        let b = mm.trailing_zeros() as usize;
                        mm &= mm - 1;
                        if asg[b] == OPEN {
                            open |= 1 << b;
                        } else {
                            let cone = tab.cones[asg[b] as usize];
                            x &= if c.red { cone } else { full & !cone };
                        }
                    }
                    match open.count_ones() {
                        0 => {
                            if om[x as usize] as usize >= limit {
                                return false;
                            }
                        }
                        1 => {
                            let v = open.trailing_zeros() as usize;
                            let mut cnt = 0;
                            for k in 0..w {
                                let mut y = dom[v * w + k];
                                while y != 0 {
                                    let bit = y.trailing_zeros();
                                    y &= y - 1;
                                    let cone = tab.cones[k * 64 + bit as usize];
                                    let part = if c.red { cone } else { full & !cone };
                                    if om[(x & part) as usize] as usize >= limit {
                                        dom[v * w + k] &= !(1u64 << bit);
                                    }
                                }
                                cnt += dom[v * w + k].count_ones();
                            }
                            settle!(v, cnt);
                        }
                        _ => {}
                    }
                }
            }
            let mut changed = false;
            if opts.degrees && tab.rmax.is_some() && tab.bmax.is_some() {
                for x in 0..tab.d {
                    let wa = &tab.with_a[x * w..(x + 1) * w];
                    let (mut fixed, mut could) = (0i32, 0i32);
                    for v in 0..m {
                        if asg[v] != OPEN {
                            fixed += (tab.cones[asg[v] as usize] >> x & 1) as i32;
                        } else if (0..w).any(|k| dom[v * w + k] & wa[k] != 0) {
                            could += 1;
                        }
                    }
                    if fixed > hi[x] || fixed + could < lo[x] {
                        return false;
                    }
                    let (cap, need) = (fixed == hi[x], fixed + could == lo[x]);
                    if cap || need {
                        for v in 0..m {
                            if asg[v] != OPEN || !(0..w).any(|k| dom[v * w + k] & wa[k] != 0) {
                                continue;
                            }
                            // full: no further cone may contain x; short: every candidate must contain x
                            let mut cnt = 0;
                            for k in 0..w {
                                let keep = if cap { !wa[k] } else { wa[k] };
                                if dom[v * w + k] & !keep != 0 {
                                    changed = true;
                                }
                                dom[v * w + k] &= keep;
                                cnt += dom[v * w + k].count_ones();
                            }
                            settle!(v, cnt);
                        }
                    }
                }
            }
            if opts.mac {
                for v in 0..m {
                    if asg[v] != OPEN {
                        continue;
                    }
                    for u in 0..m {
                        if u == v || asg[u] != OPEN {
                            continue;
                        }
                        // support of v's cones from u's remaining cones
                        let mut sup = [0u64; 128];
                        let ok = if red[u] >> v & 1 == 1 { &tab.red_ok } else { &tab.blue_ok };
                        for k in 0..w {
                            let mut y = dom[u * w + k];
                            while y != 0 {
                                let ci = k * 64 + y.trailing_zeros() as usize;
                                y &= y - 1;
                                for j in 0..w {
                                    sup[j] |= ok[ci * w + j];
                                }
                            }
                        }
                        let mut cnt = 0;
                        for k in 0..w {
                            if dom[v * w + k] & !sup[k] != 0 {
                                changed = true;
                            }
                            dom[v * w + k] &= sup[k];
                            cnt += dom[v * w + k].count_ones();
                        }
                        settle!(v, cnt);
                        if asg[v] != OPEN {
                            break;
                        }
                    }
                }
            }
            if qi == qn && !changed {
                return true;
            }
        }
    }
}

fn first_bit(row: &[u64]) -> u32 {
    let k = row.iter().position(|&x| x != 0).unwrap();
    (k * 64) as u32 + row[k].trailing_zeros()
}

#[derive(Default, Clone, Copy, Debug)]
pub struct PropStats {
    pub calls: u64,
    pub conflicts: u64,
    pub implied: u64,
    /// literals in the returned clauses (after minimisation)
    pub lits: u64,
    pub ns: u64,
}

/// What a reason has to keep true while it is being minimised.
#[derive(Clone, Copy)]
enum Concl {
    Empty,
    /// every remaining cone contains a (the cross edge (a, b) is red)
    All(usize),
    /// no remaining cone contains a
    None(usize),
}

/// Cone reasoning as a CDCL propagator, for pair formulas (A and B fixed; cross edge (a, b) is DIMACS variable
/// 1 + a*m + b, red = true). For every b it keeps D_b, the feasible cones (inside b's degree window when known) that
/// agree with b's assigned cross edges, and filters it further by one-hop support: the cones compatible with some cone
/// of D_c, for every other c with an assigned cross edge. An empty domain is a conflict, a domain whose cones all agree
/// on an unassigned cross edge implies it. Each conclusion is returned as a clause implied by the formula: the
/// negated assigned literals of the vertices involved, greedily minimised, plus the implied literal. The solver adds it
/// like a learnt clause, so learning sees cone reasoning. The clauses are not RUP in general (they rest on the cone
/// tables and on the degree windows), so the solver never combines this with proof logging.
pub struct ConeProp {
    tab: Table,
    m: usize,
    red: [u32; 32],
    /// per b: feasible cones inside b's degree window
    base: Vec<u64>,
    /// assigned red / blue cross edges at b, as masks over A
    rm: [u32; 32],
    bm: [u32; 32],
    saved: Vec<crate::sat::solver::Lit>,
    dom: Vec<u64>,
    /// sup[(c * m + b) * w ..]: cones of b compatible with some cone of D_c
    sup: Vec<u64>,
    dirty: u32,
    /// a clause was returned before every target was checked: check them all on the next call
    recheck: bool,
    pub stats: PropStats,
}

impl ConeProp {
    pub fn new(tab: Table, b: &Graph, degrees: bool) -> ConeProp {
        let (m, w) = (b.n, tab.w);
        let s = Search::new(&tab, b, Opts { degrees, mac: false });
        let base = s.dom[..m * w].to_vec();
        drop(s);
        let mut red = [0u32; 32];
        red[..m].copy_from_slice(&b.adj[..m]);
        let dom = base.clone();
        ConeProp { tab, m, red, base, rm: [0; 32], bm: [0; 32], saved: Vec::new(), dom, sup: vec![0; m * m * w], dirty: mask(m), recheck: false, stats: PropStats::default() }
    }

    fn domain(&self, b: usize, rm: u32, bm: u32, out: &mut [u64]) {
        let w = self.tab.w;
        out.copy_from_slice(&self.base[b * w..(b + 1) * w]);
        let mut x = rm | bm;
        while x != 0 {
            let a = x.trailing_zeros() as usize;
            x &= x - 1;
            let wa = &self.tab.with_a[a * w..(a + 1) * w];
            let red = rm >> a & 1 == 1;
            for k in 0..w {
                out[k] &= if red { wa[k] } else { !wa[k] };
            }
        }
    }

    /// cones of b compatible (across the B-edge c-b) with some cone of `dc`
    fn support(&self, c: usize, b: usize, dc: &[u64], out: &mut [u64]) {
        let w = self.tab.w;
        out.fill(0);
        let ok = if self.red[c] >> b & 1 == 1 { &self.tab.red_ok } else { &self.tab.blue_ok };
        for k in 0..w {
            let mut y = dc[k];
            while y != 0 {
                let ci = k * 64 + y.trailing_zeros() as usize;
                y &= y - 1;
                for j in 0..w {
                    out[j] |= ok[ci * w + j];
                }
            }
        }
    }

    fn holds(&self, e: &[u64], concl: Concl) -> bool {
        let w = self.tab.w;
        match concl {
            Concl::Empty => e.iter().all(|&x| x == 0),
            Concl::All(a) => (0..w).all(|k| e[k] & !self.tab.with_a[a * w + k] == 0),
            Concl::None(a) => (0..w).all(|k| e[k] & self.tab.with_a[a * w + k] == 0),
        }
    }

    fn sync(&mut self, trail: &[crate::sat::solver::Lit]) {
        let nv = self.tab.d * self.m;
        let mut common = 0;
        while common < self.saved.len() && common < trail.len() && self.saved[common] == trail[common] {
            common += 1;
        }
        for &l in &self.saved[common..] {
            let v = (l >> 1) as usize;
            if v < nv {
                let (a, b) = (v / self.m, v % self.m);
                self.rm[b] &= !(1 << a);
                self.bm[b] &= !(1 << a);
                self.dirty |= 1 << b;
            }
        }
        self.saved.truncate(common);
        for &l in &trail[common..] {
            let v = (l >> 1) as usize;
            if v < nv {
                let (a, b) = (v / self.m, v % self.m);
                if l & 1 == 0 {
                    self.rm[b] |= 1 << a;
                } else {
                    self.bm[b] |= 1 << a;
                }
                self.dirty |= 1 << b;
            }
            self.saved.push(l);
        }
    }

    /// Reason for `concl` at target t: kept contributors and the assigned edges of t and of each kept contributor,
    /// greedily minimised (contributors first, then single edges). Returns the clause body (negated assigned literals).
    fn reason(&self, t: usize, contrib: u32, concl: Concl) -> Vec<crate::sat::solver::Lit> {
        let (m, w) = (self.m, self.tab.w);
        let mut rm = self.rm;
        let mut bm = self.bm;
        let mut keep = contrib;
        let mut e = vec![0u64; w];
        let mut tmp = vec![0u64; w];
        let mut doms: Vec<Vec<u64>> = (0..m).map(|c| self.dom[c * w..(c + 1) * w].to_vec()).collect();
        let eval = |rm: &[u32; 32], bm: &[u32; 32], keep: u32, doms: &Vec<Vec<u64>>, e: &mut Vec<u64>, tmp: &mut Vec<u64>| {
            self.domain(t, rm[t], bm[t], e);
            let mut x = keep;
            while x != 0 {
                let c = x.trailing_zeros() as usize;
                x &= x - 1;
                self.support(c, t, &doms[c], tmp);
                for k in 0..w {
                    e[k] &= tmp[k];
                }
            }
        };
        // contributors
        let mut x = keep;
        while x != 0 {
            let c = x.trailing_zeros() as usize;
            x &= x - 1;
            eval(&rm, &bm, keep & !(1 << c), &doms, &mut e, &mut tmp);
            if self.holds(&e, concl) {
                keep &= !(1 << c);
            }
        }
        // single edges of the target, then of each kept contributor
        let mut verts = vec![t];
        let mut x = keep;
        while x != 0 {
            verts.push(x.trailing_zeros() as usize);
            x &= x - 1;
        }
        for &v in &verts {
            let mut y = rm[v] | bm[v];
            while y != 0 {
                let a = y.trailing_zeros() as usize;
                y &= y - 1;
                let (sr, sb) = (rm[v], bm[v]);
                rm[v] &= !(1 << a);
                bm[v] &= !(1 << a);
                if v != t {
                    let mut d = vec![0u64; w];
                    self.domain(v, rm[v], bm[v], &mut d);
                    let old = std::mem::replace(&mut doms[v], d);
                    eval(&rm, &bm, keep, &doms, &mut e, &mut tmp);
                    if !self.holds(&e, concl) {
                        doms[v] = old;
                        rm[v] = sr;
                        bm[v] = sb;
                    }
                } else {
                    eval(&rm, &bm, keep, &doms, &mut e, &mut tmp);
                    if !self.holds(&e, concl) {
                        rm[v] = sr;
                        bm[v] = sb;
                    }
                }
            }
        }
        let mut out = Vec::new();
        for &v in &verts {
            let mut y = rm[v] | bm[v];
            while y != 0 {
                let a = y.trailing_zeros() as usize;
                y &= y - 1;
                let var = (a * m + v) as u32;
                // an assigned red edge (x true) contributes ¬x, a blue one x
                out.push(if rm[v] >> a & 1 == 1 { var << 1 | 1 } else { var << 1 });
            }
        }
        out
    }

    /// Next conflict or implied literal as a clause (all literals false except at most one unassigned), or None.
    pub fn propagate(&mut self, _vals: &[i8], trail: &[crate::sat::solver::Lit]) -> Option<Vec<crate::sat::solver::Lit>> {
        let t0 = std::time::Instant::now();
        self.stats.calls += 1;
        let r = self.propagate_inner(trail);
        if let Some(c) = &r {
            self.stats.lits += c.len() as u64;
        }
        self.stats.ns += t0.elapsed().as_nanos() as u64;
        r
    }

    fn propagate_inner(&mut self, trail: &[crate::sat::solver::Lit]) -> Option<Vec<crate::sat::solver::Lit>> {
        self.sync(trail);
        if self.dirty == 0 && !self.recheck {
            return None;
        }
        self.recheck = false;
        let (m, w) = (self.m, self.tab.w);
        let mut x = self.dirty;
        let mut d = vec![0u64; w];
        let mut s = vec![0u64; w];
        while x != 0 {
            let c = x.trailing_zeros() as usize;
            x &= x - 1;
            self.domain(c, self.rm[c], self.bm[c], &mut d);
            self.dom[c * w..(c + 1) * w].copy_from_slice(&d);
            if self.rm[c] | self.bm[c] != 0 {
                for b in 0..m {
                    if b != c {
                        self.support(c, b, &d, &mut s);
                        self.sup[(c * m + b) * w..(c * m + b + 1) * w].copy_from_slice(&s);
                    }
                }
            }
        }
        self.dirty = 0;
        let active: u32 = (0..m).filter(|&c| self.rm[c] | self.bm[c] != 0).fold(0, |acc, c| acc | 1 << c);
        let mut e = vec![0u64; w];
        for t in 0..m {
            let contrib = active & !(1 << t);
            e.copy_from_slice(&self.dom[t * w..(t + 1) * w]);
            let mut y = contrib;
            while y != 0 {
                let c = y.trailing_zeros() as usize;
                y &= y - 1;
                for k in 0..w {
                    e[k] &= self.sup[(c * m + t) * w + k];
                }
            }
            let concl = if e.iter().all(|&v| v == 0) {
                Some((Concl::Empty, None))
            } else {
                let open = mask(self.tab.d) & !(self.rm[t] | self.bm[t]);
                let mut found = None;
                let mut z = open;
                while z != 0 {
                    let a = z.trailing_zeros() as usize;
                    z &= z - 1;
                    let var = (a * m + t) as u32;
                    if self.holds(&e, Concl::All(a)) {
                        found = Some((Concl::All(a), Some(var << 1)));
                        break;
                    }
                    if self.holds(&e, Concl::None(a)) {
                        found = Some((Concl::None(a), Some(var << 1 | 1)));
                        break;
                    }
                }
                found
            };
            if let Some((cc, lit)) = concl {
                let mut cl = self.reason(t, contrib, cc);
                match lit {
                    Some(l) => {
                        self.stats.implied += 1;
                        cl.insert(0, l);
                    }
                    None => self.stats.conflicts += 1,
                }
                self.recheck = true;
                return Some(cl);
            }
        }
        None
    }
}

/// `MONSTER_CONEPROP=1` turns the cone propagator on in pair mode (`=nodeg`: without degree windows).
pub fn coneprop_env() -> Option<bool> {
    std::env::var("MONSTER_CONEPROP").ok().map(|v| v != "nodeg")
}

/// Plain CDCL on the pair CNF, optionally with the cone propagator: (cones of the model when SAT, conflicts, stats).
pub fn cdcl_pair(s: usize, t: usize, a: &Graph, b: &Graph, coneprop: Option<bool>) -> (Option<Vec<u32>>, u64, PropStats) {
    use crate::sat::solver::{SolveResult, Solver};
    let cls = crate::encode::pair_clauses(s, t, a, b);
    let mut sv = Solver::new(a.n * b.n);
    for c in &cls {
        sv.add_clause_dimacs(c);
    }
    if let Some(deg) = coneprop {
        sv.cones = Some(Box::new(ConeProp::new(Table::new(s, t, a), b, deg)));
    }
    let model = (sv.solve(&[]) == SolveResult::Sat).then(|| {
        (0..b.n).map(|j| (0..a.n).filter(|&i| sv.model_value(crate::encode::xvar(i, j, b.n) as usize)).fold(0u32, |c, i| c | 1 << i)).collect()
    });
    (model, sv.stats.conflicts, sv.cones.as_ref().map_or(PropStats::default(), |c| c.stats))
}

/// Glue one pair: Some(cones) when SAT, None when every choice of cones fails.
pub fn solve(tab: &Table, b: &Graph, opts: Opts) -> (Option<Vec<u32>>, Stats) {
    let mut s = Search::new(tab, b, opts);
    let sat = s.run();
    (if sat { s.solution.take() } else { None }, s.stats)
}

/// `monster cone --s S --t T --n N --d D --a I[,J..] --b K[,L..]`: glue the listed catalogue pairs with each option
/// set given by `--opts` (e.g. `deg+mac,deg,mac,none`, the default) and print verdict, nodes and time.
pub fn cmd_cone(a: &crate::Args) {
    let (s, t, n) = (a.get("s", 4usize), a.get("t", 5usize), a.get("n", 25usize));
    let d = a.get("d", 8usize);
    let dir = a.kv.get("catalogs").map(std::path::PathBuf::from).unwrap_or_else(crate::catalog::default_dir);
    let la = crate::catalog::load(&dir, s - 1, t, d).unwrap_or_else(|e| crate::die(&e));
    let lb = crate::catalog::load(&dir, s, t - 1, n - 1 - d).unwrap_or_else(|e| crate::die(&e));
    let list = |k: &str| -> Vec<usize> {
        a.kv.get(k).map(|v| v.split(',').map(|x| x.parse().unwrap_or_else(|_| crate::die(&format!("bad --{k}")))).collect()).unwrap_or_else(|| vec![0])
    };
    let sets: Vec<Opts> = a
        .kv
        .get("opts")
        .map(|s| s.as_str())
        .unwrap_or("deg+mac,deg,mac,none")
        .split(',')
        .map(|o| Opts { degrees: o.contains("deg"), mac: o.contains("mac") })
        .collect();
    let limit = a.get("secs", 600.0f64);
    if a.has("cdcl") {
        // CDCL on the pair CNF: plain, with the cone propagator, and with it but without degree windows
        for ai in list("a") {
            for bi in list("b") {
                for (name, cp) in [("cdcl", None), ("cdcl+cones", Some(true)), ("cdcl+cones-nodeg", Some(false))] {
                    let t0 = std::time::Instant::now();
                    let (model, confl, ps) = cdcl_pair(s, t, &la.graphs[ai], &lb.graphs[bi], cp);
                    let sat = model.is_some();
                    println!(
                        "R({s},{t})/K{n} d={d} A#{ai} B#{bi} {name}: {} conflicts {confl} prop calls {} implied {} conflicts {} avg clause {:.1} prop {:.2}s total {:.3}s",
                        if sat { "SAT" } else { "UNSAT" },
                        ps.calls,
                        ps.implied,
                        ps.conflicts,
                        ps.lits as f64 / (ps.implied + ps.conflicts).max(1) as f64,
                        ps.ns as f64 * 1e-9,
                        t0.elapsed().as_secs_f64()
                    );
                }
            }
        }
        return;
    }
    for ai in list("a") {
        let g = &la.graphs[ai];
        let tab = Table::new(s, t, g);
        for bi in list("b") {
            for &o in &sets {
                let t0 = std::time::Instant::now();
                let (sol, st) = solve(&tab, &lb.graphs[bi], o);
                let secs = t0.elapsed().as_secs_f64();
                println!(
                    "R({s},{t})/K{n} d={d} A#{ai} B#{bi} cones {} deg={} mac={}: {} nodes {} fails {} {:.3}s",
                    tab.cones.len(),
                    o.degrees,
                    o.mac,
                    if sol.is_some() { "SAT" } else { "UNSAT" },
                    st.nodes,
                    st.fails,
                    secs
                );
                if secs > limit {
                    return;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::BigGraph;

    const ALL: [Opts; 4] = [
        Opts { degrees: false, mac: false },
        Opts { degrees: true, mac: false },
        Opts { degrees: false, mac: true },
        Opts { degrees: true, mac: true },
    ];

    fn glue_good(s: usize, t: usize, a: &Graph, b: &Graph, cone: impl Fn(usize) -> u32) -> bool {
        let (d, m) = (a.n, b.n);
        let mut g = BigGraph::new(1 + d + m);
        for i in 0..d {
            g.set(0, 1 + i, true);
            for j in i + 1..d {
                g.set(1 + i, 1 + j, a.has_edge(i, j));
            }
        }
        for i in 0..m {
            for j in i + 1..m {
                g.set(1 + d + i, 1 + d + j, b.has_edge(i, j));
            }
            for j in 0..d {
                g.set(1 + j, 1 + d + i, cone(i) >> j & 1 == 1);
            }
        }
        g.find_mono(s, true).is_none() && g.find_mono(t, false).is_none()
    }

    /// Every labelled (s,t)-good graph on n vertices, by one-vertex extensions (induced subgraphs of good graphs
    /// are good, so this stops as soon as a size has none).
    fn labelled_good(s: usize, t: usize, n: usize) -> Vec<Graph> {
        let mut cur = vec![Graph::empty(0)];
        for k in 1..=n {
            let mut next = Vec::new();
            for g in &cur {
                for nb in 0u32..1 << (k - 1) {
                    let mut h = g.clone();
                    h.n = k;
                    for i in 0..k - 1 {
                        if nb >> i & 1 == 1 {
                            h.add_edge(i, k - 1);
                        }
                    }
                    if h.is_good(s, t) {
                        next.push(h);
                    }
                }
            }
            cur = next;
        }
        cur
    }

    #[test]
    fn cone_search_matches_brute_force() {
        let mut x = 0x2545f4914f6cdd1du64;
        let mut seen = [0usize; 2];
        for &(s, t) in &[(3, 4), (4, 4), (3, 5), (4, 5)] {
            for d in 1..=5 {
                for m in 1..=5 {
                    if d * m > 15 {
                        continue;
                    }
                    // a few labelled good graphs per side, picked pseudo-randomly
                    let pick = |all: Vec<Graph>, x: &mut u64| -> Vec<Graph> {
                        let mut v = all;
                        while v.len() > 4 {
                            *x ^= *x << 13;
                            *x ^= *x >> 7;
                            *x ^= *x << 17;
                            v.swap_remove(*x as usize % v.len());
                        }
                        v
                    };
                    let aa = pick(labelled_good(s - 1, t, d), &mut x);
                    let bb = pick(labelled_good(s, t - 1, m), &mut x);
                    for a in &aa {
                        let tab = Table::new(s, t, a);
                        for b in &bb {
                            let brute = (0u64..1 << (d * m)).any(|bits| glue_good(s, t, a, b, |i| (bits >> (i * d)) as u32 & mask(d)));
                            for o in ALL {
                                let (sol, _) = solve(&tab, b, o);
                                assert_eq!(sol.is_some(), brute, "R({s},{t}) d={d} m={m} {o:?} A={a:?} B={b:?}");
                                if let Some(c) = sol {
                                    assert!(glue_good(s, t, a, b, |i| c[i]), "cone solution is not a good colouring");
                                }
                            }
                            seen[brute as usize] += 1;
                        }
                    }
                }
            }
        }
        // pairs this small are nearly all SAT; the UNSAT side is mostly exercised by the CDCL cross-check below
        assert!(seen[0] >= 4 && seen[1] >= 100, "both verdicts exercised: {seen:?}");
    }

    /// A random (s,t)-good graph on n vertices, grown one vertex at a time (restarts when stuck).
    fn random_good(s: usize, t: usize, n: usize, x: &mut u64) -> Graph {
        let mut rnd = || {
            *x ^= *x << 13;
            *x ^= *x >> 7;
            *x ^= *x << 17;
            *x
        };
        'restart: loop {
            let mut g = Graph::empty(n);
            for k in 1..n {
                let mut ok = false;
                for _ in 0..400 {
                    let nb = rnd() as u32 & mask(k);
                    let mut h = g.clone();
                    for i in 0..k {
                        if nb >> i & 1 == 1 {
                            h.add_edge(i, k);
                        }
                    }
                    let mut sub = h.clone();
                    sub.n = k + 1;
                    if sub.is_good(s, t) {
                        g = h;
                        ok = true;
                        break;
                    }
                }
                if !ok {
                    continue 'restart;
                }
            }
            return g;
        }
    }

    #[test]
    fn cone_search_matches_cdcl_on_random_pairs() {
        use crate::sat::solver::{SolveResult, Solver};
        let mut x = 0x9e3779b97f4a7c15u64;
        let mut seen = [0usize; 2];
        for &(s, t, dmax, mmax) in &[(4, 4, 8, 8), (3, 5, 4, 8), (3, 6, 5, 10), (4, 5, 8, 10)] {
            for k in 0..40 {
                let d = 2 + k % (dmax - 1);
                let m = 3 + (k / 3) % (mmax - 2);
                let a = random_good(s - 1, t, d, &mut x);
                let b = random_good(s, t - 1, m, &mut x);
                let cls = crate::encode::pair_clauses(s, t, &a, &b);
                let mut sv = Solver::new(d * m);
                for c in &cls {
                    sv.add_clause_dimacs(c);
                }
                let cdcl = sv.solve(&[]) == SolveResult::Sat;
                let tab = Table::new(s, t, &a);
                for o in ALL {
                    let (sol, _) = solve(&tab, &b, o);
                    assert_eq!(sol.is_some(), cdcl, "R({s},{t}) d={d} m={m} {o:?} A={a:?} B={b:?}");
                    if let Some(c) = sol {
                        assert!(glue_good(s, t, &a, &b, |i| c[i]), "cone solution is not a good colouring");
                    }
                }
                // CDCL with the cone propagator (with and without degree windows) reaches the same verdict
                for deg in [true, false] {
                    let (model, _, _) = cdcl_pair(s, t, &a, &b, Some(deg));
                    assert_eq!(model.is_some(), cdcl, "cone propagator, deg={deg}: R({s},{t}) d={d} m={m} A={a:?} B={b:?}");
                    if let Some(c) = model {
                        assert!(glue_good(s, t, &a, &b, |i| c[i]), "model under the cone propagator is not a good colouring");
                    }
                }
                seen[cdcl as usize] += 1;
            }
        }
        assert!(seen[0] >= 10 && seen[1] >= 10, "both verdicts exercised: {seen:?}");
    }

    #[test]
    fn cone_gluing_gives_r33_and_r34() {
        // R(s,t) <= n iff no pair (A, B) over all red degrees d of one vertex glues
        for o in ALL {
            let any_sat = |s: usize, t: usize, n: usize| {
                (0..n).any(|d| {
                    let (aa, bb) = (labelled_good(s - 1, t, d), labelled_good(s, t - 1, n - 1 - d));
                    aa.iter().any(|a| {
                        let tab = Table::new(s, t, a);
                        bb.iter().any(|b| solve(&tab, b, o).0.is_some())
                    })
                })
            };
            assert!(any_sat(3, 3, 5) && !any_sat(3, 3, 6), "{o:?}");
            assert!(any_sat(3, 4, 8) && !any_sat(3, 4, 9), "{o:?}");
        }
    }
}
