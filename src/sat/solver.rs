//! A compact CDCL solver tuned for the small, dense, highly repetitive formulas of Ramsey gluing.
//!
//! * 2-watched literals with blocker literals, clause arena of u32 words.
//! * 1UIP learning, recursive clause minimisation, LBD, VSIDS (binary heap), phase saving.
//! * Glucose-style restarts (recent LBD vs global LBD) with trail blocking.
//! * Assumption solving with *trail reuse*: assumption levels survive restarts, and consecutive `solve` calls
//!   only undo the assumption levels from the first one that changed. Streaming thousands of catalogue graphs
//!   through one instance is the whole point, so re-deciding 91 assumptions per restart would be waste.
//! * Final-conflict analysis returns the failed-assumption core (a gray-edge generalisation of the graph).
//! * Learned memory in three tiers: core (LBD <= 2, kept forever), mid (LBD <= 6, kept while recently used),
//!   local (activity-sorted, half dropped each reduction). The budget grows with the conflict count, which is
//!   what REBUILD_PLAN.md asks for after v5's fixed budget stalled.
//! * Optional lemma log (DIMACS, additions only) for the independent RUP checker.

pub type Lit = u32;

#[inline]
pub fn lit_from_dimacs(l: i32) -> Lit {
    let v = l.unsigned_abs() - 1;
    (v << 1) | (l < 0) as u32
}

#[inline]
pub fn lit_to_dimacs(l: Lit) -> i32 {
    let v = (l >> 1) as i32 + 1;
    if l & 1 == 1 {
        -v
    } else {
        v
    }
}

#[inline]
fn var(l: Lit) -> usize {
    (l >> 1) as usize
}

const NONE: u32 = u32::MAX;

/// Percentage of the local learnt tier dropped at each reduction (`MONSTER_REDUCE_DROP`, default 50), read once.
fn reduce_drop_percent() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("MONSTER_REDUCE_DROP").ok().and_then(|v| v.parse().ok()).filter(|&p| p <= 100).unwrap_or(50))
}
const HDR: usize = 4; // [size | flags, lbd, activity(f32), LRAT clause id (low 32 bits)]
const F_LEARNT: u32 = 1 << 28;
const F_DELETED: u32 = 1 << 29;
const F_USED: u32 = 1 << 30;
const SIZE_MASK: u32 = (1 << 28) - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
}

/// One LRAT proof line. Ids: original clauses are 1..m in the order they were added; lemmas continue from m+1.
#[derive(Clone, Debug)]
pub enum LratLine {
    Lemma { id: u64, lits: Vec<i32>, hints: Vec<u64> },
    /// clause = perm applied to clause `src` (a vertex permutation of a symmetric formula); expanded later
    /// `flip`: colour swap applied after the permutation (valid only when the formula is colour-symmetric, s = t)
    Image { id: u64, lits: Vec<i32>, src: u64, perm: Vec<u8>, flip: bool },
    /// clauses dropped from the database (reduce_db): the checker may forget them, no later hint names them
    Delete { ids: Vec<u64> },
}

#[derive(Clone, Copy)]
struct Watch {
    cref: u32,
    blocker: Lit,
}

#[derive(Default, Clone, Debug)]
pub struct Stats {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub reductions: u64,
    pub learnt_lits: u64,
    pub solves: u64,
    pub reused_levels: u64,
    /// failed literals found by `lookahead_pick` and learned as clauses (cube-and-conquer)
    pub failed_lits: u64,
}

pub struct Solver {
    nvars: usize,
    arena: Vec<u32>,
    wasted: usize,
    watches: Vec<Vec<Watch>>,
    vals: Vec<i8>, // per literal: 1 true, -1 false, 0 undef
    level: Vec<u32>,
    reason: Vec<u32>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    // VSIDS
    activity: Vec<f64>,
    var_inc: f64,
    heap: Vec<u32>,
    heap_pos: Vec<u32>,
    polarity: Vec<bool>,
    // analysis scratch
    seen: Vec<u8>,
    stack: Vec<Lit>,
    to_clear: Vec<Lit>,
    level_stamp: Vec<u64>,
    stamp: u64,
    // learnt management
    learnts: Vec<u32>,
    cla_inc: f32,
    pub(crate) next_reduce: u64,
    reduce_inc: u64,
    // restarts (glucose)
    lbd_queue: [u32; 50],
    lbd_q_len: usize,
    lbd_q_pos: usize,
    lbd_q_sum: u64,
    lbd_total: u64,
    trail_queue: [u32; 5000],
    trail_q_len: usize,
    trail_q_pos: usize,
    trail_q_sum: u64,
    conflicts_since_restart: u64,
    // assumptions
    assumps: Vec<Lit>,
    pub core: Vec<Lit>, // failed assumptions (subset of assumps) after an UNSAT under assumptions
    root_unsat: bool,
    pub stats: Stats,
    pub conflict_budget: u64,
    pub proof: Option<Vec<i32>>,
    /// LRAT proof (exclusive with `proof`): lines with explicit antecedent hints
    pub lrat: Option<Vec<LratLine>>,
    /// online checking: when set, the LRAT buffer is flushed to this channel in chunks (see `lrat_flush`)
    pub lrat_sink: Option<std::sync::mpsc::SyncSender<Vec<LratLine>>>,
    next_id: u64,
    trail_pos: Vec<u32>,
    unit_id: Vec<u64>,
    ante_vars: Vec<u32>,
    pending_id: u64,
    lrat_conflict: u32,
    /// symmetric pattern propagator (full K_N formulas only)
    pub patterns: Option<Box<crate::pattern::PatternProp>>,
    /// cone propagator (pair formulas, `MONSTER_CONEPROP`; its clauses are not RUP, so never with proof logging)
    pub cones: Option<Box<crate::cone::ConeProp>>,
    /// number of lemmas written to `proof` so far
    pub proof_lemmas: u64,
    /// optional live conflict counter for dashboards (incremented in batches of 256)
    pub live: Option<std::sync::Arc<std::sync::atomic::AtomicU64>>,
    pub vivify_enabled: bool,
    viv_pending: bool,
    /// MONSTER_BRANCH=vertex: decide the lowest unassigned variable (vertex-major for edge formulas) instead of VSIDS
    vertex_order: bool,
    /// MONSTER_PATVIV=1: vertex vivification of stored patterns at the root (see `vivify_patterns`)
    patviv: bool,
    patviv_pending: bool,
    /// patterns shrunk by vertex vivification, and vertices removed in total
    pub pv_shrunk: u64,
    pub pv_vertices: u64,
    pub pv_runs: u64,
    pub pv_tried: u64,
    /// CaDiCaL/Kissat-style mode switching between focused (glucose restarts) and stable (Luby restarts + target
    /// phases) search, in geometrically growing phases
    pub mode_switching: bool,
    stable: bool,
    mode_switch_at: u64,
    mode_len: u64,
    luby_i: u32,
    target_phase: Vec<i8>,
    target_len: usize,
    /// learnt clauses shortened / literals removed by vivification
    pub viv_shortened: u64,
    pub viv_lits: u64,
    /// percentage of the local learnt tier dropped at each reduction (`MONSTER_REDUCE_DROP` overrides; default 50,
    /// unit mode sets 90)
    pub reduce_drop: usize,
}

impl Solver {
    pub fn new(nvars: usize) -> Solver {
        let mut s = Solver {
            nvars: 0,
            arena: Vec::with_capacity(1 << 16),
            wasted: 0,
            watches: Vec::new(),
            vals: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            activity: Vec::new(),
            var_inc: 1.0,
            heap: Vec::new(),
            heap_pos: Vec::new(),
            polarity: Vec::new(),
            seen: Vec::new(),
            stack: Vec::new(),
            to_clear: Vec::new(),
            level_stamp: Vec::new(),
            stamp: 0,
            learnts: Vec::new(),
            cla_inc: 1.0,
            next_reduce: 2000,
            reduce_inc: 300,
            lbd_queue: [0; 50],
            lbd_q_len: 0,
            lbd_q_pos: 0,
            lbd_q_sum: 0,
            lbd_total: 0,
            trail_queue: [0; 5000],
            trail_q_len: 0,
            trail_q_pos: 0,
            trail_q_sum: 0,
            conflicts_since_restart: 0,
            assumps: Vec::new(),
            core: Vec::new(),
            root_unsat: false,
            stats: Stats::default(),
            conflict_budget: u64::MAX,
            proof: None,
            patterns: None,
            cones: None,
            lrat: None,
            lrat_sink: None,
            ante_vars: Vec::new(),
            pending_id: 0,
            lrat_conflict: NONE,
            next_id: 1,
            trail_pos: Vec::new(),
            unit_id: Vec::new(),
            proof_lemmas: 0,
            live: None,
            vivify_enabled: false,
            viv_pending: false,
            vertex_order: std::env::var("MONSTER_BRANCH").is_ok_and(|v| v == "vertex"),
            patviv: std::env::var_os("MONSTER_PATVIV").is_some(),
            patviv_pending: false,
            pv_shrunk: 0,
            pv_vertices: 0,
            pv_runs: 0,
            pv_tried: 0,
            mode_switching: false,
            stable: false,
            mode_switch_at: 1000,
            mode_len: 1000,
            luby_i: 1,
            target_phase: Vec::new(),
            target_len: 0,
            viv_shortened: 0,
            viv_lits: 0,
            reduce_drop: reduce_drop_percent(),
        };
        s.reserve_vars(nvars);
        s
    }

    pub fn num_vars(&self) -> usize {
        self.nvars
    }

    pub fn num_learnts(&self) -> usize {
        self.learnts.len()
    }

    pub fn arena_words(&self) -> usize {
        self.arena.len()
    }

    pub fn reserve_vars(&mut self, n: usize) {
        while self.nvars < n {
            let v = self.nvars;
            self.nvars += 1;
            self.watches.push(Vec::new());
            self.watches.push(Vec::new());
            self.vals.push(0);
            self.vals.push(0);
            self.level.push(0);
            self.reason.push(NONE);
            self.activity.push(0.0);
            self.heap_pos.push(NONE);
            self.polarity.push(true); // default phase: negative literal first (blue edges)
            self.target_phase.push(-1);
            self.trail_pos.push(0);
            self.unit_id.push(0);
            self.seen.push(0);
            self.level_stamp.push(0);
            self.heap_insert(v as u32);
        }
        // levels <= assumptions + decisions <= 2 * nvars (dummy levels for already-true assumptions)
        self.level_stamp.resize(2 * self.nvars + 2, 0);
    }

    pub fn enable_proof(&mut self) {
        self.proof = Some(Vec::new());
    }

    #[inline]
    fn val(&self, l: Lit) -> i8 {
        unsafe { *self.vals.get_unchecked(l as usize) }
    }

    #[inline]
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    #[inline]
    fn csize(&self, c: u32) -> usize {
        (self.arena[c as usize] & SIZE_MASK) as usize
    }

    #[inline]
    fn clits(&self, c: u32) -> &[u32] {
        let c = c as usize;
        let n = (self.arena[c] & SIZE_MASK) as usize;
        &self.arena[c + HDR..c + HDR + n]
    }

    /// Add an original clause (DIMACS literals). Must be called at decision level 0 (it backtracks there).
    pub fn add_clause_dimacs(&mut self, cl: &[i32]) -> bool {
        let lits: Vec<Lit> = cl.iter().map(|&l| lit_from_dimacs(l)).collect();
        self.add_clause(&lits)
    }

    pub fn add_clause(&mut self, lits_in: &[Lit]) -> bool {
        if self.root_unsat {
            return false;
        }
        self.cancel_until(0);
        let maxv = lits_in.iter().map(|&l| var(l) + 1).max().unwrap_or(0);
        self.reserve_vars(maxv);
        let orig_id = self.next_id;
        self.next_id += 1;
        if self.lrat.is_some() {
            return self.add_clause_lrat(lits_in, orig_id);
        }
        let mut lits: Vec<Lit> = lits_in.to_vec();
        lits.sort_unstable();
        lits.dedup();
        // tautology / satisfied / false-literal removal at root
        let mut out = Vec::with_capacity(lits.len());
        for i in 0..lits.len() {
            if i + 1 < lits.len() && lits[i + 1] == lits[i] ^ 1 {
                return true;
            }
            match self.val(lits[i]) {
                1 => return true,
                -1 => {}
                _ => out.push(lits[i]),
            }
        }
        match out.len() {
            0 => {
                self.root_unsat = true;
                false
            }
            1 => {
                self.enqueue(out[0], NONE);
                if self.propagate() != NONE {
                    self.root_unsat = true;
                    return false;
                }
                true
            }
            _ => {
                let c = self.alloc(&out, false, 0);
                self.attach(c);
                true
            }
        }
    }

    fn alloc(&mut self, lits: &[Lit], learnt: bool, lbd: u32) -> u32 {
        self.alloc_id(lits, learnt, lbd, 0)
    }

    fn alloc_id(&mut self, lits: &[Lit], learnt: bool, lbd: u32, id: u64) -> u32 {
        let c = self.arena.len() as u32;
        self.arena.push(lits.len() as u32 | if learnt { F_LEARNT } else { 0 });
        self.arena.push(lbd);
        self.arena.push(0f32.to_bits());
        self.arena.push(id as u32);
        self.arena.extend_from_slice(lits);
        c
    }

    #[inline]
    fn cid(&self, c: u32) -> u64 {
        self.arena[c as usize + 3] as u64
    }

    /// LRAT id the next added clause will get (lets callers map their input clauses to proof ids)
    pub fn next_clause_id(&self) -> u64 {
        self.next_id
    }

    /// Initial phase of every variable: `Some(true)` = negative literal first (blue edges, the default),
    /// `Some(false)` = positive literal first (red edges), `None` = pseudo-random from `seed` (colour-neutral on
    /// average). Phase saving takes over once a variable has been assigned.
    pub fn set_initial_phase(&mut self, phase: Option<bool>, seed: u64) {
        let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
        for p in self.polarity.iter_mut() {
            *p = match phase {
                Some(neg) => neg,
                None => {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    x & 1 == 1
                }
            };
        }
    }

    pub fn lrat_enable(&mut self) {
        assert!(self.next_id == 1, "enable LRAT before adding clauses");
        self.lrat = Some(Vec::new());
    }

    fn lrat_push(&mut self, lits: &[Lit], hints: Vec<u64>) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        if let Some(l) = self.lrat.as_mut() {
            l.push(LratLine::Lemma { id, lits: lits.iter().map(|&x| lit_to_dimacs(x)).collect(), hints });
            self.lrat_flush(false);
        }
        id
    }

    /// Online checking: send the buffered LRAT lines to the sink once the buffer is large (or always when `force`).
    /// Without a sink the buffer simply grows (in-memory proof, as before).
    pub fn lrat_flush(&mut self, force: bool) {
        const CHUNK: usize = 4096;
        if let (Some(buf), Some(sink)) = (self.lrat.as_mut(), self.lrat_sink.as_ref()) {
            if force || buf.len() >= CHUNK {
                if !buf.is_empty() {
                    let chunk = std::mem::take(buf);
                    // a closed receiver means the checker failed early; the error surfaces when the result is joined
                    let _ = sink.send(chunk);
                }
            }
        }
    }

    /// End of the proof: flush everything and close the sink, so the checker thread finishes.
    pub fn lrat_finish(&mut self) {
        self.lrat_flush(true);
        self.lrat_sink = None;
    }

    /// Original clause under LRAT: never simplified silently. Root-false literals are removed by a logged lemma.
    fn add_clause_lrat(&mut self, lits_in: &[Lit], orig_id: u64) -> bool {
        let mut lits: Vec<Lit> = lits_in.to_vec();
        lits.sort_unstable();
        lits.dedup();
        if lits.windows(2).any(|w| w[1] == w[0] ^ 1) || lits.iter().any(|&l| self.val(l) == 1) {
            return true;
        }
        let falses: Vec<Lit> = lits.iter().copied().filter(|&l| self.val(l) == -1).collect();
        let out: Vec<Lit> = lits.iter().copied().filter(|&l| self.val(l) == 0).collect();
        let id = if falses.is_empty() {
            orig_id
        } else {
            let mut h: Vec<u64> = falses.iter().map(|&l| self.unit_id[var(l)]).collect();
            h.push(orig_id);
            self.lrat_push(&out, h)
        };
        match out.len() {
            0 => {
                self.root_unsat = true;
                false
            }
            1 => {
                self.unit_id[var(out[0])] = id;
                self.enqueue(out[0], NONE);
                let c = self.propagate();
                if c != NONE {
                    self.lrat_root_conflict(c);
                    self.root_unsat = true;
                    return false;
                }
                true
            }
            _ => {
                let c = self.alloc_id(&out, false, 0, id);
                self.attach(c);
                true
            }
        }
    }

    /// Empty clause from a conflict at decision level 0.
    fn lrat_root_conflict(&mut self, confl: u32) {
        if self.lrat.is_none() {
            return;
        }
        let mut h: Vec<u64> = self.clits(confl).iter().map(|&l| self.unit_id[var(l)]).collect();
        h.push(self.cid(confl));
        self.lrat_push(&[], h);
    }

    fn attach(&mut self, c: u32) {
        let l0 = self.arena[c as usize + HDR];
        let l1 = self.arena[c as usize + HDR + 1];
        self.watches[l0 as usize].push(Watch { cref: c, blocker: l1 });
        self.watches[l1 as usize].push(Watch { cref: c, blocker: l0 });
    }

    #[inline]
    fn enqueue(&mut self, l: Lit, from: u32) {
        let v = var(l);
        self.vals[l as usize] = 1;
        self.vals[(l ^ 1) as usize] = -1;
        self.level[v] = self.decision_level() as u32;
        self.reason[v] = from;
        self.trail_pos[v] = self.trail.len() as u32;
        self.trail.push(l);
        if from != NONE && self.trail_lim.is_empty() && self.lrat.is_some() {
            // root implication: log it as a unit lemma so later proofs can cite it
            let mut h: Vec<u64> = Vec::new();
            let c = from as usize;
            let size = (self.arena[c] & SIZE_MASK) as usize;
            for k in 0..size {
                let q = self.arena[c + HDR + k];
                if var(q) != v {
                    h.push(self.unit_id[var(q)]);
                }
            }
            h.push(self.cid(from));
            self.unit_id[v] = self.lrat_push(&[l], h);
        }
    }

    fn propagate(&mut self) -> u32 {
        let mut confl = NONE;
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.stats.propagations += 1;
            let false_lit = p ^ 1;
            let mut ws = std::mem::take(&mut self.watches[false_lit as usize]);
            let n = ws.len();
            let (mut i, mut j) = (0usize, 0usize);
            'outer: while i < n {
                let w = ws[i];
                i += 1;
                if self.val(w.blocker) == 1 {
                    ws[j] = w;
                    j += 1;
                    continue;
                }
                let c = w.cref as usize;
                let size = (self.arena[c] & SIZE_MASK) as usize;
                let base = c + HDR;
                if self.arena[base] == false_lit {
                    self.arena.swap(base, base + 1);
                }
                let first = self.arena[base];
                if first != w.blocker && self.val(first) == 1 {
                    ws[j] = Watch { cref: w.cref, blocker: first };
                    j += 1;
                    continue;
                }
                for k in 2..size {
                    let lk = self.arena[base + k];
                    if self.val(lk) != -1 {
                        self.arena[base + 1] = lk;
                        self.arena[base + k] = false_lit;
                        self.watches[lk as usize].push(Watch { cref: w.cref, blocker: first });
                        continue 'outer;
                    }
                }
                ws[j] = Watch { cref: w.cref, blocker: first };
                j += 1;
                if self.val(first) == -1 {
                    confl = w.cref;
                    while i < n {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                    self.qhead = self.trail.len();
                } else {
                    self.enqueue(first, w.cref);
                }
            }
            ws.truncate(j);
            self.watches[false_lit as usize] = ws;
            if confl != NONE {
                break;
            }
        }
        confl
    }

    fn cancel_until(&mut self, lvl: usize) {
        if self.decision_level() > lvl {
            let lim = self.trail_lim[lvl];
            for k in (lim..self.trail.len()).rev() {
                let l = self.trail[k];
                let v = var(l);
                self.vals[l as usize] = 0;
                self.vals[(l ^ 1) as usize] = 0;
                self.reason[v] = NONE;
                self.polarity[v] = l & 1 == 1;
                if self.heap_pos[v] == NONE {
                    self.heap_insert(v as u32);
                }
            }
            self.trail.truncate(lim);
            self.trail_lim.truncate(lvl);
            self.qhead = lim;
        }
    }

    // ---------------- VSIDS heap ----------------
    #[inline]
    fn heap_less(&self, a: u32, b: u32) -> bool {
        self.activity[a as usize] > self.activity[b as usize]
    }
    fn heap_up(&mut self, mut i: usize) {
        let v = self.heap[i];
        while i > 0 {
            let p = (i - 1) / 2;
            if self.heap_less(v, self.heap[p]) {
                self.heap[i] = self.heap[p];
                self.heap_pos[self.heap[i] as usize] = i as u32;
                i = p;
            } else {
                break;
            }
        }
        self.heap[i] = v;
        self.heap_pos[v as usize] = i as u32;
    }
    fn heap_down(&mut self, mut i: usize) {
        let v = self.heap[i];
        let n = self.heap.len();
        loop {
            let l = 2 * i + 1;
            if l >= n {
                break;
            }
            let r = l + 1;
            let c = if r < n && self.heap_less(self.heap[r], self.heap[l]) { r } else { l };
            if self.heap_less(self.heap[c], v) {
                self.heap[i] = self.heap[c];
                self.heap_pos[self.heap[i] as usize] = i as u32;
                i = c;
            } else {
                break;
            }
        }
        self.heap[i] = v;
        self.heap_pos[v as usize] = i as u32;
    }
    fn heap_insert(&mut self, v: u32) {
        self.heap.push(v);
        let i = self.heap.len() - 1;
        self.heap_pos[v as usize] = i as u32;
        self.heap_up(i);
    }
    fn heap_pop(&mut self) -> Option<u32> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        let last = self.heap.pop().unwrap();
        self.heap_pos[top as usize] = NONE;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.heap_pos[last as usize] = 0;
            self.heap_down(0);
        }
        Some(top)
    }
    fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        let p = self.heap_pos[v];
        if p != NONE {
            self.heap_up(p as usize);
        }
    }
    fn bump_clause(&mut self, c: u32) {
        let c = c as usize;
        let a = f32::from_bits(self.arena[c + 2]) + self.cla_inc;
        self.arena[c + 2] = a.to_bits();
        if a > 1e20 {
            for &lc in &self.learnts {
                let x = f32::from_bits(self.arena[lc as usize + 2]) * 1e-20;
                self.arena[lc as usize + 2] = x.to_bits();
            }
            self.cla_inc *= 1e-20;
        }
    }

    // ---------------- conflict analysis ----------------
    fn analyze(&mut self, mut confl: u32, out: &mut Vec<Lit>) -> (usize, u32) {
        out.clear();
        out.push(0); // placeholder for the asserting literal
        let lrat_on = self.lrat.is_some();
        self.ante_vars.clear();
        self.lrat_conflict = confl;
        let mut path = 0i32;
        let mut p: Lit = NONE;
        let mut idx = self.trail.len();
        let dl = self.decision_level() as u32;
        loop {
            debug_assert!(confl != NONE);
            let c = confl as usize;
            if self.arena[c] & F_LEARNT != 0 {
                self.bump_clause(confl);
                self.arena[c] |= F_USED;
            }
            let size = (self.arena[c] & SIZE_MASK) as usize;
            let start = if p == NONE { 0 } else { 1 };
            for k in start..size {
                let q = self.arena[c + HDR + k];
                let v = var(q);
                if self.seen[v] == 0 && self.level[v] > 0 {
                    self.seen[v] = 1;
                    self.bump_var(v);
                    if self.level[v] >= dl {
                        path += 1;
                    } else {
                        out.push(q);
                    }
                }
            }
            loop {
                idx -= 1;
                if self.seen[var(self.trail[idx])] != 0 {
                    break;
                }
            }
            p = self.trail[idx];
            confl = self.reason[var(p)];
            self.seen[var(p)] = 0;
            path -= 1;
            if path <= 0 {
                break;
            }
            if lrat_on {
                self.ante_vars.push(var(p) as u32);
            }
            // reason clauses keep the implied literal at position 0
            debug_assert_eq!(self.arena[confl as usize + HDR], p);
        }
        out[0] = p ^ 1;

        // recursive minimisation
        self.to_clear.clear();
        self.to_clear.extend_from_slice(out);
        let initial_len = out.len();
        let initial: Vec<Lit> = if lrat_on { out.clone() } else { Vec::new() };
        let mut abstract_levels = 0u32;
        for &l in &out[1..] {
            abstract_levels |= 1 << (self.level[var(l)] & 31);
        }
        let mut keep = 1;
        for k in 1..out.len() {
            let l = out[k];
            if self.reason[var(l)] == NONE || !self.lit_redundant(l, abstract_levels) {
                out[keep] = l;
                keep += 1;
            }
        }
        out.truncate(keep);
        if lrat_on {
            // removed literals and every literal explored by a successful redundancy check need their reasons
            for &l in &initial[1..] {
                if !out.contains(&l) {
                    self.ante_vars.push(var(l) as u32);
                }
            }
            for &l in &self.to_clear[initial_len..] {
                self.ante_vars.push(var(l) as u32);
            }
        }
        for &l in &self.to_clear {
            self.seen[var(l)] = 0;
        }

        // backjump level: put the highest-level literal at position 1
        let bt = if out.len() == 1 {
            0
        } else {
            let mut mi = 1;
            for k in 2..out.len() {
                if self.level[var(out[k])] > self.level[var(out[mi])] {
                    mi = k;
                }
            }
            out.swap(1, mi);
            self.level[var(out[1])] as usize
        };
        // LBD
        self.stamp += 1;
        let mut lbd = 0u32;
        for &l in out.iter() {
            let lv = self.level[var(l)] as usize;
            if self.level_stamp[lv] != self.stamp {
                self.level_stamp[lv] = self.stamp;
                lbd += 1;
            }
        }
        (bt, lbd)
    }

    fn lit_redundant(&mut self, p: Lit, abstract_levels: u32) -> bool {
        self.stack.clear();
        self.stack.push(p);
        let top = self.to_clear.len();
        while let Some(q) = self.stack.pop() {
            let c = self.reason[var(q)] as usize;
            let size = (self.arena[c] & SIZE_MASK) as usize;
            for k in 1..size {
                let l = self.arena[c + HDR + k];
                let v = var(l);
                if self.seen[v] == 0 && self.level[v] > 0 {
                    if self.reason[v] != NONE && (abstract_levels >> (self.level[v] & 31)) & 1 == 1 {
                        self.seen[v] = 1;
                        self.stack.push(l);
                        self.to_clear.push(l);
                    } else {
                        for &x in &self.to_clear[top..] {
                            self.seen[var(x)] = 0;
                        }
                        self.to_clear.truncate(top);
                        return false;
                    }
                }
            }
        }
        true
    }

    /// LRAT hints for the learnt clause just produced by `analyze`: root units of every root-level literal in the
    /// used clauses, then the reasons of the antecedent variables in trail order, then the conflict clause.
    fn lrat_hints_for_learnt(&mut self) -> Vec<u64> {
        let mut vars: Vec<u32> = self.ante_vars.clone();
        vars.sort_unstable_by_key(|&v| self.trail_pos[v as usize]);
        vars.dedup();
        let mut used: Vec<u32> = vars.iter().map(|&v| self.reason[v as usize]).collect();
        used.push(self.lrat_conflict);
        let mut units: Vec<u64> = Vec::new();
        for &c in &used {
            for &q in self.clits(c) {
                if self.level[var(q)] == 0 && self.val(q) != 0 {
                    let u = self.unit_id[var(q)];
                    if u != 0 && !units.contains(&u) {
                        units.push(u);
                    }
                }
            }
        }
        let mut h = units;
        for &c in &used {
            h.push(self.cid(c));
        }
        h
    }

    /// Final conflict: the assumption `p` is false. Collect `p` plus every assumption decision that the
    /// assignment ¬p depends on. Every entry of `core` is an assumption literal, and the clause OR(¬core) is
    /// implied by the formula (it is RUP: assigning the core and propagating reaches a conflict).
    fn analyze_final(&mut self, p: Lit) {
        self.core.clear();
        self.core.push(p);
        self.seen[var(p)] = 1;
        let mut used: Vec<u32> = Vec::new(); // reason clauses, collected in reverse trail order
        let start = if self.decision_level() == 0 { self.trail.len() } else { self.trail_lim[0] };
        for k in (start..self.trail.len()).rev() {
            let l = self.trail[k];
            let v = var(l);
            if self.seen[v] != 0 {
                let r = self.reason[v];
                if r == NONE {
                    if self.level[v] > 0 && l != (p ^ 1) {
                        self.core.push(l);
                    }
                } else {
                    used.push(r);
                    let c = r as usize;
                    let size = (self.arena[c] & SIZE_MASK) as usize;
                    for kk in 1..size {
                        let q = self.arena[c + HDR + kk];
                        if self.level[var(q)] > 0 {
                            self.seen[var(q)] = 1;
                        }
                    }
                }
                self.seen[v] = 0;
            }
        }
        self.seen[var(p)] = 0;
        self.core.sort_unstable();
        self.core.dedup();
        if self.lrat.is_some() {
            // hints: root units of root-level literals in the used reasons, then the reasons in trail order. When p
            // itself is false at the root (no reason above level 0 is involved), the only hint is its root unit.
            used.reverse();
            let mut h: Vec<u64> = Vec::new();
            if self.level[var(p)] == 0 {
                let u = self.unit_id[var(p)];
                if u != 0 {
                    h.push(u);
                }
            }
            for &c in &used {
                for &q in self.clits(c) {
                    if self.level[var(q)] == 0 && self.val(q) != 0 {
                        let u = self.unit_id[var(q)];
                        if u != 0 && !h.contains(&u) {
                            h.push(u);
                        }
                    }
                }
            }
            for &c in &used {
                h.push(self.cid(c));
            }
            let lits: Vec<Lit> = self.core.iter().map(|&a| a ^ 1).collect();
            self.lrat_push(&lits, h);
        }
    }

    /// Id of the most recent LRAT line (0 if LRAT is off).
    pub fn last_lrat_id(&self) -> u64 {
        if self.lrat.is_some() {
            self.next_id - 1
        } else {
            0
        }
    }

    fn log_lemma(&mut self, lits: &[Lit]) {
        if let Some(pf) = self.proof.as_mut() {
            for &l in lits {
                pf.push(lit_to_dimacs(l));
            }
            pf.push(0);
            self.proof_lemmas += 1;
        }
    }

    fn reduce_db(&mut self) {
        self.stats.reductions += 1;
        // locked clauses (reasons of current assignments) are never removed
        let mut cand: Vec<u32> = Vec::with_capacity(self.learnts.len());
        let mut kept: Vec<u32> = Vec::with_capacity(self.learnts.len());
        for &c in &self.learnts {
            let ci = c as usize;
            let lbd = self.arena[ci + 1];
            let l0 = self.arena[ci + HDR];
            let locked = self.val(l0) == 1 && self.reason[var(l0)] == c;
            if lbd <= 2 || locked {
                kept.push(c);
            } else if lbd <= 6 && self.arena[ci] & F_USED != 0 {
                self.arena[ci] &= !F_USED; // mid tier: survives while it keeps being used
                kept.push(c);
            } else {
                cand.push(c);
            }
        }
        let arena = &self.arena;
        cand.sort_unstable_by(|&a, &b| {
            let (la, lb) = (arena[a as usize + 1], arena[b as usize + 1]);
            lb.cmp(&la).then_with(|| {
                f32::from_bits(arena[a as usize + 2])
                    .partial_cmp(&f32::from_bits(arena[b as usize + 2]))
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
        });
        // `reduce_drop` percent of the local tier goes (50 historically; unit mode uses 90: the conflict rate on hard
        // units fell 4x as the learnt database grew, and 90% measured 1.8x faster at equal conflicts on the d=10 sample)
        let drop = cand.len() * self.reduce_drop / 100;
        let mut dropped_ids: Vec<u64> = Vec::new();
        for (k, &c) in cand.iter().enumerate() {
            if k < drop {
                let ci = c as usize;
                self.arena[ci] |= F_DELETED;
                self.wasted += HDR + (self.arena[ci] & SIZE_MASK) as usize;
                if self.lrat.is_some() && self.arena[ci + 3] != 0 {
                    dropped_ids.push(self.arena[ci + 3] as u64);
                }
            } else {
                kept.push(c);
            }
        }
        self.learnts = kept;
        // LRAT deletion line: the checker drops these clauses, so its memory follows the live database, not the
        // whole proof (a 17M-conflict unit logs ~4 GB of lemmas; the live database is ~100 MB)
        if !dropped_ids.is_empty() {
            if let Some(l) = self.lrat.as_mut() {
                l.push(LratLine::Delete { ids: dropped_ids });
                self.lrat_flush(false);
            }
        }
        if self.vivify_enabled {
            self.viv_pending = true; // runs at the next restart, back at the root level
        }
        if self.patviv {
            self.patviv_pending = true;
        }
        // purge watches of deleted clauses
        let arena = &self.arena;
        for ws in self.watches.iter_mut() {
            ws.retain(|w| arena[w.cref as usize] & F_DELETED == 0);
        }
        if self.wasted * 2 > self.arena.len() {
            self.garbage_collect();
        }
    }

    /// Learnt-clause vivification at decision level 0 (Luo et al. 2017): for a clause (l1..ln), assign ¬l1, ¬l2, ...
    /// one level each and propagate. A literal already false is redundant; a literal already true, or a conflict,
    /// ends the probe early. The decided literals (plus the true one) form a clause that is RUP with respect to the
    /// current database (which still contains the original), so it is logged as a lemma and replaces the original.
    fn vivify(&mut self) {
        const F_VIVIFIED: u32 = 1 << 31;
        let saved_pol = self.polarity.clone();
        let mut cands: Vec<u32> = self
            .learnts
            .iter()
            .copied()
            .filter(|&c| {
                let ci = c as usize;
                let size = (self.arena[ci] & SIZE_MASK) as usize;
                let l0 = self.arena[ci + HDR];
                let locked = self.val(l0) != 0 && self.reason[var(l0)] == c;
                self.arena[ci] & (F_VIVIFIED | F_DELETED) == 0 && self.arena[ci + 1] <= 6 && size > 2 && !locked
            })
            .collect();
        // newest first, bounded work per call
        cands.reverse();
        cands.truncate(500);
        let mut new_learnts = Vec::new();
        let mut lits: Vec<Lit> = Vec::new();
        let mut out: Vec<Lit> = Vec::new();
        for c in cands {
            let ci = c as usize;
            self.arena[ci] |= F_VIVIFIED;
            let size = (self.arena[ci] & SIZE_MASK) as usize;
            lits.clear();
            lits.extend_from_slice(&self.arena[ci + HDR..ci + HDR + size]);
            if lits.iter().any(|&l| self.val(l) == 1) {
                continue; // satisfied at root
            }
            out.clear();
            for &l in &lits {
                match self.val(l) {
                    -1 => continue, // implied false by the earlier negations: redundant literal
                    1 => {
                        out.push(l);
                        break;
                    }
                    _ => {
                        out.push(l);
                        self.trail_lim.push(self.trail.len());
                        self.enqueue(l ^ 1, NONE);
                        if self.propagate() != NONE {
                            break;
                        }
                    }
                }
            }
            self.cancel_until(0);
            if out.len() < size {
                self.viv_shortened += 1;
                self.viv_lits += (size - out.len()) as u64;
                let lbd = self.arena[ci + 1].min(out.len() as u32);
                self.log_lemma(&out.clone());
                if let Some(pp) = self.patterns.as_mut() {
                    // a vivified clause is a shorter, more general lemma: offer it as a pattern (index = just logged)
                    let key = self.proof_lemmas.saturating_sub(1);
                    if self.lrat.is_none() {
                        pp.learn(&out, lbd, key);
                    }
                }
                self.arena[ci] |= F_DELETED;
                self.wasted += HDR + size;
                if out.len() == 1 {
                    self.enqueue(out[0], NONE);
                    if self.propagate() != NONE {
                        self.log_lemma(&[]);
                        self.root_unsat = true;
                        break;
                    }
                } else {
                    // watch two unassigned literals (all literals of `out` are unassigned or false at root)
                    out.sort_by_key(|&l| (self.val(l) == -1) as u8);
                    let nc = self.alloc(&out, true, lbd);
                    self.arena[nc as usize] |= F_VIVIFIED;
                    self.attach(nc);
                    new_learnts.push(nc);
                }
            }
        }
        self.learnts.retain(|&c| self.arena[c as usize] & F_DELETED == 0);
        self.learnts.extend(new_learnts);
        self.polarity = saved_pol;
    }

    /// Vertex vivification of stored patterns, at decision level 0: for each live pattern clause, greedily delete one
    /// pattern vertex (all literals of edges at it) while the shorter clause is still RUP by unit propagation from the
    /// root (assign the negations one level each; a conflict or a literal true at the root proves it). A shrunk clause
    /// is logged as a lemma, added to the database, registered as a pattern (smaller and more general), and the old
    /// pattern is retired: every image of it contains an image of the new one. Root only, so no assumption is used.
    fn vivify_patterns(&mut self) {
        let Some(pp) = self.patterns.as_ref() else { return };
        let pats = pp.live_clauses();
        let saved_pol = self.polarity.clone();
        self.pv_runs += 1;
        self.pv_tried += pats.len() as u64;
        for (idx, clause, _k) in pats {
            if let Some(pp) = self.patterns.as_mut() {
                pp.mark_viv_tried(idx);
            }
            if clause.iter().any(|&l| self.val(l) == 1) {
                continue; // satisfied at the root
            }
            let mut cur: Vec<Lit> = clause.clone();
            let mut removed = 0u64;
            loop {
                let pp = self.patterns.as_ref().unwrap();
                let mut verts = pp.vertices_of(&cur);
                // fewest incident literals first: the cheapest deletions
                verts.sort_by_key(|&w| cur.iter().filter(|&&l| pp.touches(l, w)).count());
                let mut next: Option<Vec<Lit>> = None;
                for w in verts {
                    let pp = self.patterns.as_ref().unwrap();
                    let cand: Vec<Lit> = cur.iter().copied().filter(|&l| !pp.touches(l, w)).collect();
                    if cand.len() < 2 {
                        continue;
                    }
                    if self.rup_at_root(&cand) {
                        next = Some(cand);
                        break;
                    }
                }
                match next {
                    Some(c) => {
                        cur = c;
                        removed += 1;
                    }
                    None => break,
                }
            }
            if removed == 0 {
                continue;
            }
            self.pv_shrunk += 1;
            self.pv_vertices += removed;
            self.log_lemma(&cur);
            let key = self.proof_lemmas.saturating_sub(1);
            if let Some(pp) = self.patterns.as_mut() {
                pp.learn_forced(&cur, key);
                pp.retire(idx);
            }
            // into the database too, watching two literals that are unassigned at the root
            let mut lits: Vec<Lit> = cur.iter().copied().filter(|&l| self.val(l) != -1).collect();
            if lits.is_empty() {
                self.log_lemma(&[]);
                self.root_unsat = true;
                break;
            }
            if lits.len() == 1 {
                self.enqueue(lits[0], NONE);
                if self.propagate() != NONE {
                    self.log_lemma(&[]);
                    self.root_unsat = true;
                    break;
                }
                continue;
            }
            lits.extend(cur.iter().copied().filter(|&l| self.val(l) == -1));
            let lbd = lits.len().min(8) as u32;
            let nc = self.alloc(&lits, true, lbd);
            self.attach(nc);
            self.learnts.push(nc);
        }
        self.polarity = saved_pol;
    }

    /// The newest `max` learned clauses still in the database (solver literals), newest first.
    pub fn recent_learnts(&self, max: usize) -> Vec<Vec<Lit>> {
        self.learnts
            .iter()
            .rev()
            .filter(|&&c| self.arena[c as usize] & F_DELETED == 0)
            .take(max)
            .map(|&c| {
                let ci = c as usize;
                let size = (self.arena[ci] & SIZE_MASK) as usize;
                self.arena[ci + HDR..ci + HDR + size].to_vec()
            })
            .collect()
    }

    /// Is `cl` RUP by unit propagation from the root? Leaves the solver at level 0.
    fn rup_at_root(&mut self, cl: &[Lit]) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        if cl.iter().any(|&l| self.val(l) == 1) {
            return true;
        }
        let mut proved = false;
        for &l in cl {
            match self.val(l) {
                1 => {
                    proved = true; // forced true by the earlier negations: its negation conflicts
                    break;
                }
                -1 => continue, // already false: nothing to assign
                _ => {}
            }
            self.trail_lim.push(self.trail.len());
            self.enqueue(l ^ 1, NONE);
            if self.propagate() != NONE {
                proved = true;
                break;
            }
        }
        self.cancel_until(0);
        proved
    }

    fn garbage_collect(&mut self) {
        let mut new_arena: Vec<u32> = Vec::with_capacity(self.arena.len() - self.wasted + 1024);
        let mut map: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
        let mut c = 0usize;
        while c < self.arena.len() {
            let size = (self.arena[c] & SIZE_MASK) as usize;
            if self.arena[c] & F_DELETED == 0 {
                let nc = new_arena.len() as u32;
                map.insert(c as u32, nc);
                new_arena.extend_from_slice(&self.arena[c..c + HDR + size]);
            }
            c += HDR + size;
        }
        for r in self.reason.iter_mut() {
            if *r != NONE {
                *r = *map.get(r).expect("reason clause deleted");
            }
        }
        for l in self.learnts.iter_mut() {
            *l = map[l];
        }
        for ws in self.watches.iter_mut() {
            for w in ws.iter_mut() {
                w.cref = map[&w.cref];
            }
        }
        self.arena = new_arena;
        self.wasted = 0;
    }

    fn pick_branch(&mut self) -> Option<Lit> {
        if self.vertex_order {
            // vertex-major: the lowest unassigned variable; for edge variables (j(j-1)/2 + i) that finishes every edge
            // among vertices 0..j before touching vertex j+1, so conflicts and learned clauses stay on few vertices
            for v in 0..self.vals.len() / 2 {
                if self.vals[v << 1] == 0 {
                    self.stats.decisions += 1;
                    return Some(((v as Lit) << 1) | self.polarity[v] as u32);
                }
            }
            return None;
        }
        while let Some(v) = self.heap_pop() {
            let l0 = (v as Lit) << 1;
            if self.vals[l0 as usize] == 0 {
                self.stats.decisions += 1;
                let neg = if self.stable && self.target_phase[v as usize] >= 0 {
                    self.target_phase[v as usize] == 1
                } else {
                    self.polarity[v as usize]
                };
                return Some(l0 | neg as u32);
            }
        }
        None
    }

    fn luby(mut i: u32) -> u64 {
        // Luby sequence 1,1,2,1,1,2,4,... (1-based)
        loop {
            let mut k = 1u32;
            while (1u64 << k) - 1 < i as u64 {
                k += 1;
            }
            if (1u64 << k) - 1 == i as u64 {
                return 1 << (k - 1);
            }
            i -= (1u32 << (k - 1)) - 1;
        }
    }

    fn restart_due(&self) -> bool {
        if self.stable {
            return self.conflicts_since_restart >= Self::luby(self.luby_i) * 1024;
        }
        if self.lbd_q_len < 50 || self.stats.conflicts == 0 {
            return false;
        }
        let recent = self.lbd_q_sum as f64 / 50.0;
        let global = self.lbd_total as f64 / self.stats.conflicts as f64;
        recent * 0.8 > global
    }

    /// Solve under DIMACS assumptions.
    pub fn solve_dimacs(&mut self, assumps: &[i32]) -> SolveResult {
        let a: Vec<Lit> = assumps.iter().map(|&l| lit_from_dimacs(l)).collect();
        self.solve(&a)
    }

    pub fn solve(&mut self, assumps: &[Lit]) -> SolveResult {
        self.stats.solves += 1;
        self.core.clear();
        if self.root_unsat {
            return SolveResult::Unsat;
        }
        // trail reuse: keep the assumption levels whose literal did not change
        let mut keep = 0;
        while keep < assumps.len()
            && keep < self.assumps.len()
            && keep < self.decision_level()
            && assumps[keep] == self.assumps[keep]
        {
            keep += 1;
        }
        // levels beyond the assumption prefix are search levels: never keep them across calls
        self.cancel_until(keep);
        self.stats.reused_levels += keep as u64;
        self.assumps.clear();
        self.assumps.extend_from_slice(assumps);
        let budget_end = self.stats.conflicts.saturating_add(self.conflict_budget);
        let mut learnt: Vec<Lit> = Vec::with_capacity(64);
        loop {
            let mut confl = self.propagate();
            if confl == NONE && self.patterns.is_some() {
                confl = self.pattern_round();
            }
            if confl == NONE && self.cones.is_some() {
                assert!(self.proof.is_none() && self.lrat.is_none(), "the cone propagator writes no proof");
                confl = self.cone_round();
                if self.root_unsat {
                    return SolveResult::Unsat;
                }
            }
            if confl != NONE {
                self.stats.conflicts += 1;
                self.conflicts_since_restart += 1;
                if self.stats.conflicts & 255 == 0 {
                    if let Some(l) = &self.live {
                        l.fetch_add(256, std::sync::atomic::Ordering::Relaxed);
                    }
                }
                if self.decision_level() == 0 {
                    self.log_lemma(&[]);
                    self.lrat_root_conflict(confl);
                    self.root_unsat = true;
                    return SolveResult::Unsat;
                }
                // trail blocking (glucose): a much longer trail than usual postpones the restart
                let tl = self.trail.len() as u32;
                if self.trail_q_len == self.trail_queue.len() {
                    self.trail_q_sum -= self.trail_queue[self.trail_q_pos] as u64;
                } else {
                    self.trail_q_len += 1;
                }
                self.trail_queue[self.trail_q_pos] = tl;
                self.trail_q_sum += tl as u64;
                self.trail_q_pos = (self.trail_q_pos + 1) % self.trail_queue.len();
                if self.stats.conflicts > 10000
                    && self.lbd_q_len == 50
                    && self.trail_q_len == self.trail_queue.len()
                    && (tl as f64) > 1.4 * (self.trail_q_sum as f64 / self.trail_q_len as f64)
                {
                    self.lbd_q_len = 0;
                    self.lbd_q_sum = 0;
                    self.lbd_q_pos = 0;
                }
                if self.stable && self.trail.len() > self.target_len {
                    // target phase: the assignment of the longest conflict-free trail in this stable phase
                    self.target_len = self.trail.len();
                    for &l in &self.trail[..self.trail.len()] {
                        self.target_phase[var(l)] = (l & 1) as i8;
                    }
                }
                let (bt, lbd) = self.analyze(confl, &mut learnt);
                let mut learnt_id = 0u64;
                if self.lrat.is_some() {
                    let h = self.lrat_hints_for_learnt();
                    learnt_id = self.lrat_push(&learnt.clone(), h);
                }
                if let Some(pp) = self.patterns.as_mut() {
                    let key = if learnt_id != 0 { learnt_id } else { self.proof_lemmas };
                    pp.learn(&learnt, lbd, key);
                }
                self.cancel_until(bt);
                self.log_lemma(&learnt.clone());
                self.stats.learnt_lits += learnt.len() as u64;
                if learnt.len() == 1 {
                    if learnt_id != 0 {
                        self.unit_id[var(learnt[0])] = learnt_id;
                    }
                    self.enqueue(learnt[0], NONE);
                } else {
                    let c = self.alloc_id(&learnt, true, lbd, learnt_id);
                    self.attach(c);
                    self.learnts.push(c);
                    self.bump_clause(c);
                    self.enqueue(learnt[0], c);
                }
                // LBD queue
                if self.lbd_q_len == 50 {
                    self.lbd_q_sum -= self.lbd_queue[self.lbd_q_pos] as u64;
                } else {
                    self.lbd_q_len += 1;
                }
                self.lbd_queue[self.lbd_q_pos] = lbd;
                self.lbd_q_sum += lbd as u64;
                self.lbd_q_pos = (self.lbd_q_pos + 1) % 50;
                self.lbd_total += lbd as u64;
                self.var_inc /= 0.95;
                self.cla_inc /= 0.999;
            } else {
                if self.stats.conflicts >= budget_end {
                    self.cancel_until(self.assumps.len().min(self.decision_level()));
                    if self.patviv {
                        self.patviv_pending = true; // each new pattern is offered once, at the next root restart
                    }
                    return SolveResult::Unknown;
                }
                if self.mode_switching && self.stats.conflicts >= self.mode_switch_at {
                    self.stable = !self.stable;
                    self.mode_len = self.mode_len * 2;
                    self.mode_switch_at = self.stats.conflicts + self.mode_len;
                    self.target_len = 0;
                    self.conflicts_since_restart = u64::MAX / 2; // force a restart into the new mode
                }
                if self.restart_due() {
                    self.stats.restarts += 1;
                    if self.stable {
                        self.luby_i += 1;
                    }
                    self.lbd_q_len = 0;
                    self.lbd_q_sum = 0;
                    self.lbd_q_pos = 0;
                    self.conflicts_since_restart = 0;
                    self.cancel_until(self.assumps.len().min(self.decision_level()));
                    if self.patviv_pending && self.decision_level() == 0 && self.lrat.is_none() {
                        self.patviv_pending = false;
                        self.vivify_patterns();
                        if self.root_unsat {
                            return SolveResult::Unsat;
                        }
                    }
                    if self.viv_pending && self.decision_level() == 0 {
                        self.viv_pending = false;
                        self.vivify();
                        if self.root_unsat {
                            return SolveResult::Unsat;
                        }
                        let arena = &self.arena;
                        for ws in self.watches.iter_mut() {
                            ws.retain(|w| arena[w.cref as usize] & F_DELETED == 0);
                        }
                        if self.wasted * 2 > self.arena.len() {
                            self.garbage_collect();
                        }
                    }
                }
                if self.stats.conflicts >= self.next_reduce {
                    self.reduce_inc += 300;
                    self.next_reduce = self.stats.conflicts + 2000 + self.reduce_inc;
                    self.reduce_db();
                }
                let dl = self.decision_level();
                let next = if dl < self.assumps.len() {
                    let p = self.assumps[dl];
                    match self.val(p) {
                        1 => {
                            self.trail_lim.push(self.trail.len()); // dummy level keeps levels aligned
                            continue;
                        }
                        -1 => {
                            self.analyze_final(p);
                            if let Some(pf) = self.proof.as_mut() {
                                for &a in &self.core {
                                    pf.push(lit_to_dimacs(a ^ 1));
                                }
                                pf.push(0);
                                self.proof_lemmas += 1;
                            }
                            return SolveResult::Unsat;
                        }
                        _ => p,
                    }
                } else {
                    match self.pick_branch() {
                        Some(l) => l,
                        None => return SolveResult::Sat,
                    }
                };
                self.trail_lim.push(self.trail.len());
                self.enqueue(next, NONE);
            }
        }
    }

    /// Lookahead split choice under `assumps` (v11 / march style): every free variable is probed both ways at the
    /// assumption level; score = (props(+)+1) * (props(-)+1), a failed literal counts as 100000 propagations.
    /// Ties are broken by variable activity. Returns the polarity that propagates more, or None if no free variable
    /// is left (or the assumptions already conflict).
    pub fn lookahead_pick(&mut self, assumps: &[Lit]) -> Option<Lit> {
        if self.root_unsat {
            return None;
        }
        self.cancel_until(0);
        if self.propagate() != NONE {
            return None;
        }
        for &a in assumps {
            match self.val(a) {
                1 => {}
                -1 => {
                    self.cancel_until(0);
                    return None;
                }
                _ => {
                    self.trail_lim.push(self.trail.len());
                    self.enqueue(a, NONE);
                    if self.propagate() != NONE {
                        self.cancel_until(0);
                        return None;
                    }
                }
            }
        }
        let base = self.decision_level();
        let mut best: Option<(u64, f64, Lit)> = None;
        let mut failed: Vec<Lit> = Vec::new();
        for v in 0..self.nvars {
            let l0 = (v as Lit) << 1;
            if self.vals[l0 as usize] != 0 {
                continue;
            }
            let mut cnt = [0u64; 2];
            for (k, l) in [l0, l0 | 1].into_iter().enumerate() {
                let before = self.trail.len();
                self.trail_lim.push(before);
                self.enqueue(l, NONE);
                let confl = self.propagate();
                cnt[k] = if confl != NONE {
                    failed.push(l);
                    100_000
                } else {
                    (self.trail.len() - before) as u64
                };
                self.cancel_until(base);
            }
            let score = (cnt[0] + 1) * (cnt[1] + 1);
            let lit = if cnt[0] >= cnt[1] { l0 } else { l0 | 1 };
            let act = self.activity[v];
            if best.map_or(true, |(bs, ba, _)| score > bs || (score == bs && act > ba)) {
                best = Some((score, act, lit));
            }
        }
        // Failed-literal learning (march-style): a probe of l under the prefix reached a conflict by unit propagation,
        // so the clause (¬l ∨ ¬prefix) is RUP with respect to the database at that moment (and still is after further
        // additions). It is logged and added, so ¬l is implied at the prefix level in every cube below this node
        // instead of being rediscovered by search. The proof is DIMACS additions only (no LRAT ids here).
        if !failed.is_empty() && self.lrat.is_none() {
            let prefix_neg: Vec<Lit> =
                assumps.iter().filter(|&&a| self.val(a) == 1 && self.level[var(a)] > 0).map(|&a| a ^ 1).collect();
            for l in failed {
                if self.val(l) != 0 {
                    continue; // already decided by an earlier failed literal's propagation
                }
                let mut lits = Vec::with_capacity(prefix_neg.len() + 1);
                lits.push(l ^ 1);
                lits.extend(prefix_neg.iter().copied());
                self.log_lemma(&lits);
                self.stats.failed_lits += 1;
                self.pending_id = 0;
                let c = self.add_clause_mid_search(&lits);
                if c != NONE || self.root_unsat || self.propagate() != NONE {
                    // the prefix itself is refuted: let the caller's full solve derive and log that
                    self.cancel_until(0);
                    return None;
                }
            }
        }
        self.cancel_until(0);
        best.map(|b| b.2)
    }

    /// Log a derived clause (DIMACS) that the caller knows is RUP, e.g. the resolvent of two logged core clauses.
    pub fn log_derived(&mut self, cl: &[i32]) {
        let lits: Vec<Lit> = cl.iter().map(|&l| lit_from_dimacs(l)).collect();
        self.log_lemma(&lits);
        if cl.is_empty() {
            self.root_unsat = true;
        }
    }

    /// Log the resolvent `cl` of the logged clauses `parents` (ids in the order a hinted check needs: the first parent
    /// becomes unit under ¬cl, the second is then falsified). Returns the LRAT id, or 0 without LRAT (then the plain
    /// lemma log gets it).
    pub fn log_resolvent(&mut self, cl: &[i32], parents: &[u64]) -> u64 {
        if self.lrat.is_none() {
            self.log_derived(cl);
            return 0;
        }
        let lits: Vec<Lit> = cl.iter().map(|&l| lit_from_dimacs(l)).collect();
        let id = self.lrat_push(&lits, parents.to_vec());
        if cl.is_empty() {
            self.root_unsat = true;
        }
        id
    }

    /// Pattern round: repeatedly ask the propagator for violated/unit images until none, or a conflict.
    fn pattern_round(&mut self) -> u32 {
        loop {
            let mut pp = self.patterns.take().unwrap();
            let found = pp.propagate(&self.vals, &self.trail);
            self.patterns = Some(pp);
            let Some((clause, lemma, perm, flip)) = found else { return NONE };
            let mut img_id = 0u64;
            if self.lrat.is_some() {
                img_id = self.next_id;
                self.next_id += 1;
                let lits: Vec<i32> = clause.iter().map(|&x| lit_to_dimacs(x)).collect();
                self.lrat.as_mut().unwrap().push(LratLine::Image { id: img_id, lits, src: lemma, perm: perm.clone(), flip });
            }
            self.pending_id = img_id;
            // log the image (symmetric-proof line) before it is used
            if let Some(pf) = self.proof.as_mut() {
                pf.push(if flip { i32::MIN + 1 } else { i32::MIN }); // image marker (MIN+1: with colour swap)
                pf.push(lemma as i32);
                pf.extend(perm.iter().map(|&v| v as i32));
                for &l in &clause {
                    pf.push(lit_to_dimacs(l));
                }
                pf.push(0);
                self.proof_lemmas += 1;
            }
            let c = self.add_clause_mid_search(&clause);
            if c != NONE {
                return c;
            }
            let confl = self.propagate();
            if confl != NONE {
                return confl;
            }
        }
    }

    /// Cone round: repeatedly ask the cone propagator for a conflict or an implied cross edge until none, or a conflict.
    fn cone_round(&mut self) -> u32 {
        loop {
            let mut cp = self.cones.take().unwrap();
            let found = cp.propagate(&self.vals, &self.trail);
            self.cones = Some(cp);
            let Some(clause) = found else { return NONE };
            if clause.is_empty() {
                self.root_unsat = true;
                return NONE;
            }
            self.pending_id = 0;
            let c = self.add_clause_mid_search(&clause);
            if c != NONE || self.root_unsat {
                return c;
            }
            let confl = self.propagate();
            if confl != NONE {
                return confl;
            }
        }
    }

    /// Attach a clause (implied by the formula) during search. Every literal is false except at most one unassigned.
    /// Returns a conflicting clause reference, or NONE after enqueuing the implied literal.
    fn add_clause_mid_search(&mut self, lits_in: &[Lit]) -> u32 {
        let mut lits: Vec<Lit> = lits_in.to_vec();
        // unassigned first, then false literals by decreasing level
        lits.sort_by_key(|&l| match self.val(l) {
            0 => (0u8, 0i64),
            1 => (0u8, 0i64),
            _ => (1u8, -(self.level[var(l)] as i64)),
        });
        if lits.len() == 1 {
            let l = lits[0];
            self.cancel_until(0);
            if self.val(l) == -1 {
                self.log_lemma(&[]);
                if self.lrat.is_some() {
                    let h = vec![self.unit_id[var(l)], self.pending_id];
                    self.lrat_push(&[], h);
                }
                self.root_unsat = true;
                return NONE;
            }
            if self.val(l) == 0 {
                self.unit_id[var(l)] = self.pending_id;
                self.enqueue(l, NONE);
            }
            return NONE;
        }
        let unassigned = self.val(lits[0]) == 0;
        if unassigned {
            // unit: lits[1] is the highest false literal; imply at that level (chronological backtracking avoided)
            let lvl = self.level[var(lits[1])] as usize;
            self.cancel_until(lvl);
            let c = self.alloc_id(&lits, true, 2, self.pending_id);
            self.attach(c);
            self.learnts.push(c);
            self.enqueue(lits[0], c);
            return NONE;
        }
        let m1 = self.level[var(lits[0])] as usize;
        let m2 = self.level[var(lits[1])] as usize;
        if m1 > m2 {
            // only one literal at the top level: the clause is unit at level m2
            self.cancel_until(m2);
            let c = self.alloc_id(&lits, true, 2, self.pending_id);
            self.attach(c);
            self.learnts.push(c);
            self.enqueue(lits[0], c);
            return NONE;
        }
        self.cancel_until(m1);
        let c = self.alloc_id(&lits, true, 2, self.pending_id);
        self.attach(c);
        self.learnts.push(c);
        c
    }

    /// Value of DIMACS variable v (1-based) in the last model.
    pub fn model_value(&self, v: usize) -> bool {
        self.vals[(v - 1) << 1] == 1
    }

    pub fn is_root_unsat(&self) -> bool {
        self.root_unsat
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn php(p: usize, h: usize) -> Vec<Vec<i32>> {
        let x = |i: usize, j: usize| (i * h + j + 1) as i32;
        let mut cl = Vec::new();
        for i in 0..p {
            cl.push((0..h).map(|j| x(i, j)).collect());
        }
        for j in 0..h {
            for a in 0..p {
                for b in a + 1..p {
                    cl.push(vec![-x(a, j), -x(b, j)]);
                }
            }
        }
        cl
    }

    #[test]
    fn php_unsat_and_sat() {
        let mut s = Solver::new(0);
        for c in php(7, 6) {
            s.add_clause_dimacs(&c);
        }
        assert_eq!(s.solve(&[]), SolveResult::Unsat);
        let mut s = Solver::new(0);
        let cls = php(6, 6);
        for c in &cls {
            s.add_clause_dimacs(c);
        }
        assert_eq!(s.solve(&[]), SolveResult::Sat);
        for c in &cls {
            assert!(c.iter().any(|&l| s.model_value(l.unsigned_abs() as usize) == (l > 0)));
        }
    }

    #[test]
    fn assumptions_core() {
        // (a ∨ b), (¬a ∨ c), (¬b ∨ c); assume ¬c, d -> UNSAT with core {¬c}
        let mut s = Solver::new(4);
        s.add_clause_dimacs(&[1, 2]);
        s.add_clause_dimacs(&[-1, 3]);
        s.add_clause_dimacs(&[-2, 3]);
        assert_eq!(s.solve_dimacs(&[4, -3]), SolveResult::Unsat);
        let core: Vec<i32> = s.core.iter().map(|&l| lit_to_dimacs(l)).collect();
        assert_eq!(core, vec![-3]);
        assert_eq!(s.solve_dimacs(&[4, 3]), SolveResult::Sat);
        assert_eq!(s.solve_dimacs(&[-3]), SolveResult::Unsat);
    }

    #[test]
    fn random_3sat_cross_check() {
        // compare against brute force on small random formulas
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..300 {
            let n = 10;
            let m = 30 + (rnd() % 25) as usize;
            let cls: Vec<Vec<i32>> = (0..m)
                .map(|_| {
                    (0..3)
                        .map(|_| {
                            let v = (rnd() % n as u64) as i32 + 1;
                            if rnd() & 1 == 1 {
                                v
                            } else {
                                -v
                            }
                        })
                        .collect()
                })
                .collect();
            let brute = (0..1u32 << n).any(|a| {
                cls.iter().all(|c| c.iter().any(|&l| ((a >> (l.abs() - 1)) & 1 == 1) == (l > 0)))
            });
            let mut s = Solver::new(n);
            s.mode_switching = rnd() & 1 == 1;
            s.vivify_enabled = rnd() & 1 == 1;
            s.next_reduce = 50;
            for c in &cls {
                s.add_clause_dimacs(c);
            }
            let r = s.solve(&[]);
            assert_eq!(r == SolveResult::Sat, brute);
            // assumptions: first 3 vars positive
            let assume = [1, 2, 3];
            let brute2 = (0..1u32 << n).filter(|a| a & 7 == 7).any(|a| {
                cls.iter().all(|c| c.iter().any(|&l| ((a >> (l.abs() - 1)) & 1 == 1) == (l > 0)))
            });
            let r2 = s.solve_dimacs(&assume);
            assert_eq!(r2 == SolveResult::Sat, brute2, "assumption solve mismatch");
            if r2 == SolveResult::Unsat && !s.is_root_unsat() {
                // the core must itself be UNSAT
                let core: Vec<i32> = s.core.iter().map(|&l| lit_to_dimacs(l)).collect();
                let bc = (0..1u32 << n).any(|a| {
                    core.iter().all(|&l| ((a >> (l.abs() - 1)) & 1 == 1) == (l > 0))
                        && cls.iter().all(|c| c.iter().any(|&l| ((a >> (l.abs() - 1)) & 1 == 1) == (l > 0)))
                });
                assert!(!bc, "core {core:?} is satisfiable");
            }
        }
    }
}
