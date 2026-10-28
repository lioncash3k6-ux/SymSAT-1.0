//! Gluing driver: plans the degree stages, streams catalogue graphs through per-worker solvers, keeps a core cache
//! (automatic gray-edge generalisations), certifies sampled tasks with the independent checker, and re-checks every
//! SAT witness as a full colouring of K_N.

use crate::catalog::{self, Level};
use crate::cover::{build_gamma, unit_glue_check, Cover, Member};
use crate::encode::{self, glue_check, pair_clauses, Side, Stream};
use crate::graph::{BigGraph, Graph};
use crate::sat::checker::Checker;
use crate::sat::solver::{lit_to_dimacs, SolveResult, Solver};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering::Relaxed};
use std::sync::{Arc, Mutex};
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Route {
    /// some vertex has even red degree (needs N odd): only even d
    Parity,
    /// any one vertex: every d
    All,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// one solver per fixed graph, streamed side's edges as assumptions, core cache
    Stream,
    /// baseline: a fresh solver per pair on the plain pair CNF
    Pair,
    /// gray-edge units from v10 cover files: one GAMMA per (genA, genB), solved whole, then per pair by assumptions
    Unit,
    /// full K_N formula per worker with pattern CDCL + lemma library; each catalogue pair is an assumption cube
    Hybrid,
    /// feasible-cone search per catalogue pair (src/cone.rs); uncertified prototype, tasks are units with --covers
    Cone,
}

/// Tasks are (genA, genB) units of the cover files.
fn uses_covers(cfg: &Config) -> bool {
    cfg.mode == Mode::Unit || (matches!(cfg.mode, Mode::Hybrid | Mode::Cone) && cfg.covers.is_some())
}

#[derive(Clone, Debug)]
pub struct Config {
    pub s: usize,
    pub t: usize,
    pub n: usize,
    pub route: Route,
    pub degrees: Option<Vec<usize>>,
    pub workers: usize,
    pub chunk: usize,
    pub mode: Mode,
    pub minimize: u64,
    pub check_every: usize,
    pub sample: Option<usize>,
    /// `--shard I/N`: run only the tasks with index I mod N of the whole plan (one shard per machine; the shards'
    /// tasks.jsonl files are concatenated and a final `--resume` run over the plan certifies completeness)
    pub shard: Option<(usize, usize)>,
    pub seed: u64,
    pub catalogs: PathBuf,
    pub out: Option<PathBuf>,
    pub resume: bool,
    pub cache_cap: usize,
    pub stop_on_sat: bool,
    pub quiet: bool,
    pub max_pairs_per_task: Option<usize>,
    pub covers: Option<PathBuf>,
    pub gray_a: usize,
    pub gray_b: usize,
    pub unit_budget: u64,
    /// unit mode: only these (genA, genB) units
    pub units: Option<Vec<(usize, usize)>>,
    /// add degree-window axioms (every vertex's red degree in the window implied by the catalogue maxima)
    pub degree_axioms: bool,
    /// pair mode: book axioms (two-root lemmas as cardinality constraints, `encode::pair_book_axioms`)
    pub book_axioms: bool,
    /// learnt-clause vivification at root
    pub vivify: bool,
    /// unit mode: conflicts per cube node after the root budget (0 = no cubing, go pair by pair)
    pub cube_budget: u64,
    /// focused/stable mode switching in the solver
    pub stable: bool,
    /// hybrid mode: pattern admission LBD cap and book lemmas
    pub pat_lbd: u32,
    pub books: bool,
    /// hybrid: cube on the smaller catalogue side only; the other side is left free (one cube covers all its pairs)
    pub one_sided: bool,
    /// static task schedule (`--sched static`): worker w runs tasks w, w + W, w + 2W, .. in order, so every
    /// per-task count is reproducible for a fixed worker count (hybrid workers keep their solver across tasks)
    pub sched_static: bool,
}

pub struct Stage {
    pub d: usize,
    pub m: usize,
    pub a: Level,
    pub b: Level,
    /// streamed side (the larger catalogue)
    pub side: Side,
    pub pairs: u64,
    pub cov_a: Option<Cover>,
    pub cov_b: Option<Cover>,
}

impl Stage {
    pub fn fixed(&self) -> &Level {
        match self.side {
            Side::B => &self.a,
            Side::A => &self.b,
        }
    }
    pub fn streamed(&self) -> &Level {
        match self.side {
            Side::B => &self.b,
            Side::A => &self.a,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Task {
    pub id: usize,
    pub stage: usize,
    pub fixed: usize,
    pub lo: usize,
    pub hi: usize,
}

#[derive(Default)]
pub struct WorkerStat {
    /// live conflict counter, updated by the solver itself every 256 conflicts
    pub live: Arc<AtomicU64>,
    pub pairs: AtomicU64,
    pub unsat: AtomicU64,
    pub sat: AtomicU64,
    pub hits: AtomicU64,
    pub solves: AtomicU64,
    pub conflicts: AtomicU64,
    pub props: AtomicU64,
    pub learnts: AtomicU64,
    pub cores: AtomicU64,
    pub core_lits: AtomicU64,
    pub task: AtomicU64,
    pub stage_d: AtomicU64,
    pub fixed: AtomicU64,
    pub pos: AtomicU64,
    pub hi: AtomicU64,
    pub checking: AtomicBool,
    pub busy: AtomicBool,
    pub checked_pairs: AtomicU64,
    pub roots: AtomicU64,
    _pad: [u64; 4],
}

pub struct SatRecord {
    pub d: usize,
    pub fixed_idx: usize,
    pub streamed_idx: usize,
    pub g6: String,
}

pub struct Shared {
    pub cfg: Config,
    pub stages: Vec<Stage>,
    pub tasks: Vec<Task>,
    pub next: AtomicUsize,
    pub stop: AtomicBool,
    pub workers: Vec<WorkerStat>,
    pub stage_done: Vec<AtomicU64>,
    pub stage_unsat: Vec<AtomicU64>,
    pub stage_sat: Vec<AtomicU64>,
    pub stage_checked: Vec<AtomicU64>,
    pub stage_target: Vec<u64>,
    pub tasks_done: AtomicUsize,
    pub tasks_checked: AtomicUsize,
    pub sats: Mutex<Vec<SatRecord>>,
    pub errors: Mutex<Vec<String>>,
    pub events: Mutex<Vec<String>>,
    pub log: Mutex<Option<std::fs::File>>,
    pub library: Option<crate::full::Library>,
    pub started: Instant,
    pub skipped_pairs: Vec<u64>,
    /// tasks and pairs of the whole plan before `--sample` (to extrapolate a sample to the full run)
    pub plan_tasks: usize,
    pub plan_pairs: u64,
}

impl Shared {
    pub fn event(&self, s: String) {
        let mut ev = self.events.lock().unwrap();
        ev.push(s);
        if ev.len() > 200 {
            ev.drain(..100);
        }
    }
}

/// Degree range for the vertex v and the stages it implies.
pub fn plan(cfg: &Config) -> Result<(Vec<Stage>, Vec<String>), String> {
    let (s, t, n) = (cfg.s, cfg.t, cfg.n);
    if s < 3 || t < 3 {
        return Err("need s,t >= 3".into());
    }
    if cfg.route == Route::Parity && n % 2 == 0 {
        return Err("the parity route needs N odd (sum of 25 odd degrees would be odd)".into());
    }
    let mut notes = Vec::new();
    let mut stages = Vec::new();
    let degrees: Vec<usize> = match &cfg.degrees {
        Some(v) => v.clone(),
        None => (0..n).collect(),
    };
    for d in degrees {
        if d >= n {
            return Err(format!("degree {d} >= N"));
        }
        if cfg.route == Route::Parity && d % 2 == 1 {
            continue;
        }
        let m = n - 1 - d;
        // empty levels are decided by the McKay table without touching the disk
        let ca = catalog::mckay_count(s - 1, t, d);
        let cb = catalog::mckay_count(s, t - 1, m);
        if ca == Some(0) || cb == Some(0) {
            if cfg.degrees.is_some() {
                notes.push(format!(
                    "d={d}: no ({},{})-good graph on {d} or no ({},{})-good graph on {m} vertices: impossible",
                    s - 1,
                    t,
                    s,
                    t - 1
                ));
            }
            continue;
        }
        let a = catalog::load(&cfg.catalogs, s - 1, t, d)?;
        let b = catalog::load(&cfg.catalogs, s, t - 1, m)?;
        if a.graphs.is_empty() || b.graphs.is_empty() {
            continue;
        }
        for lv in [&a, &b] {
            match lv.count_ok() {
                Some(true) => {}
                Some(false) => {
                    return Err(format!(
                        "catalogue {} has {} graphs but McKay's table says {}",
                        lv.path.display(),
                        lv.graphs.len(),
                        lv.mckay.unwrap()
                    ))
                }
                None => notes.push(format!(
                    "{}: {} graphs, no McKay count to compare against",
                    lv.path.display(),
                    lv.graphs.len()
                )),
            }
        }
        let side = if b.graphs.len() >= a.graphs.len() { Side::B } else { Side::A };
        let pairs = a.graphs.len() as u64 * b.graphs.len() as u64;
        let (mut cov_a, mut cov_b) = (None, None);
        if uses_covers(cfg) {
            let dir = cfg.covers.as_ref().ok_or("--mode unit needs --covers DIR")?;
            // gray level 99 = "every edge gray" (one generalisation, catalogue graphs as instantiations)
            let pa = dir.join(format!("c{}{}_{d}_g{}.txt", s - 1, t, cfg.gray_a));
            let pb = dir.join(format!("c{}{}_{m}_g{}.txt", s, t - 1, cfg.gray_b));
            let ca = if cfg.gray_a == 99 { Cover::all_gray(&a.graphs, d)? } else { Cover::load(&pa, &a.graphs)? };
            let cb = if cfg.gray_b == 99 { Cover::all_gray(&b.graphs, m)? } else { Cover::load(&pb, &b.graphs)? };
            notes.push(format!(
                "covers: {} ({} gens) x {} ({} gens) = {} units",
                pa.display(),
                ca.gens.len(),
                pb.display(),
                cb.gens.len(),
                ca.gens.len() * cb.gens.len()
            ));
            cov_a = Some(ca);
            cov_b = Some(cb);
        }
        stages.push(Stage { d, m, a, b, side, pairs, cov_a, cov_b });
    }
    Ok((stages, notes))
}

/// Degrees the route must cover for a claim about R(s,t) (those whose two catalogue levels are non-empty).
pub fn admissible_degrees(cfg: &Config) -> Vec<usize> {
    (0..cfg.n)
        .filter(|&d| cfg.route == Route::All || d % 2 == 0)
        .filter(|&d| {
            let m = cfg.n - 1 - d;
            catalog::mckay_count(cfg.s - 1, cfg.t, d) != Some(0) && catalog::mckay_count(cfg.s, cfg.t - 1, m) != Some(0)
        })
        .collect()
}

/// Number of catalogue pairs a task covers.
pub fn task_pairs(cfg: &Config, stages: &[Stage], t: &Task) -> u64 {
    if cfg.mode == Mode::Hybrid && cfg.one_sided {
        return stages[t.stage].streamed().graphs.len() as u64;
    }
    if uses_covers(cfg) {
        let st = &stages[t.stage];
        let na = st.cov_a.as_ref().unwrap().members[t.fixed].len() as u64;
        let nb: u64 = (t.lo..t.hi).map(|g| st.cov_b.as_ref().unwrap().members[g].len() as u64).sum();
        na * nb
    } else {
        (t.hi - t.lo) as u64
    }
}

fn make_tasks(cfg: &Config, stages: &[Stage]) -> Vec<Task> {
    let mut tasks = Vec::new();
    if uses_covers(cfg) {
        for (si, st) in stages.iter().enumerate() {
            let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
            if let Some(list) = &cfg.units {
                for &(ga, gb) in list {
                    if ga < ca.gens.len() && gb < cb.gens.len() {
                        tasks.push(Task { id: tasks.len(), stage: si, fixed: ga, lo: gb, hi: gb + 1 });
                    }
                }
                continue;
            }
            for ga in 0..ca.gens.len() {
                for gb in 0..cb.gens.len() {
                    tasks.push(Task { id: tasks.len(), stage: si, fixed: ga, lo: gb, hi: gb + 1 });
                }
            }
        }
    }
    if cfg.mode == Mode::Hybrid && cfg.one_sided {
        for (si, st) in stages.iter().enumerate() {
            for f in 0..st.fixed().graphs.len() {
                tasks.push(Task { id: tasks.len(), stage: si, fixed: f, lo: 0, hi: 1 });
            }
        }
    }
    for (si, st) in stages.iter().enumerate() {
        if uses_covers(cfg) || (cfg.mode == Mode::Hybrid && cfg.one_sided) {
            break;
        }
        let nf = st.fixed().graphs.len();
        let ns = st.streamed().graphs.len();
        let chunk = cfg.chunk.max(1);
        for f in 0..nf {
            let mut lo = 0;
            while lo < ns {
                let hi = (lo + chunk).min(ns);
                tasks.push(Task { id: tasks.len(), stage: si, fixed: f, lo, hi });
                lo = hi;
            }
        }
    }
    if let Some((i, n)) = cfg.shard {
        tasks.retain(|t| t.id % n == i);
        for (k, t) in tasks.iter_mut().enumerate() {
            t.id = k;
        }
    }
    if let Some(k) = cfg.sample {
        // deterministic random sample of tasks (for cost estimates), kept in fixed-graph order for solver reuse
        let mut x = cfg.seed ^ 0x9e3779b97f4a7c15;
        let mut keyed: Vec<(u64, Task)> = tasks
            .into_iter()
            .map(|t| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                (x, t)
            })
            .collect();
        keyed.sort_by_key(|p| p.0);
        keyed.truncate(k);
        tasks = keyed.into_iter().map(|p| p.1).collect();
        tasks.sort_by_key(|t| (t.stage, t.fixed, t.lo));
        if let Some(cap) = cfg.max_pairs_per_task {
            for t in tasks.iter_mut() {
                t.hi = t.hi.min(t.lo + cap);
            }
        }
        for (i, t) in tasks.iter_mut().enumerate() {
            t.id = i;
        }
    }
    tasks
}

// ---------------------------------------------------------------- core cache

#[derive(Clone)]
struct Core {
    pos: [u64; 3],
    neg: [u64; 3],
    lemma: u32, // index of the refuting lemma in the proof log (checked solvers only)
    hits: u32,
}

struct CoreCache {
    cores: Vec<Core>,
    cap: usize,
}

impl CoreCache {
    fn new(cap: usize) -> CoreCache {
        CoreCache { cores: Vec::new(), cap }
    }
    #[inline]
    fn lookup(&mut self, red: &[u64; 3], blue: &[u64; 3]) -> Option<u32> {
        for k in 0..self.cores.len() {
            let c = &self.cores[k];
            if (c.pos[0] & !red[0]) | (c.pos[1] & !red[1]) | (c.pos[2] & !red[2]) == 0
                && (c.neg[0] & !blue[0]) | (c.neg[1] & !blue[1]) | (c.neg[2] & !blue[2]) == 0
            {
                self.cores[k].hits += 1;
                let lemma = self.cores[k].lemma;
                // move towards the front: popular generalisations are found first
                if k > 0 {
                    self.cores.swap(k, k / 2);
                }
                return Some(lemma);
            }
        }
        None
    }
    fn insert(&mut self, c: Core) {
        if self.cores.len() >= self.cap {
            // evict the least-hit half of the back quarter
            let n = self.cores.len();
            let start = n - n / 4;
            let mut tail: Vec<Core> = self.cores.drain(start..).collect();
            tail.sort_by_key(|c| std::cmp::Reverse(c.hits));
            tail.truncate(tail.len() / 2);
            self.cores.extend(tail);
        }
        self.cores.push(c);
    }
}

fn edge_masks(g: &Graph) -> ([u64; 3], [u64; 3]) {
    let mut red = [0u64; 3];
    let mut blue = [0u64; 3];
    let mut k = 0usize;
    for j in 1..g.n {
        for i in 0..j {
            if g.has_edge(i, j) {
                red[k >> 6] |= 1 << (k & 63);
            } else {
                blue[k >> 6] |= 1 << (k & 63);
            }
            k += 1;
        }
    }
    (red, blue)
}

// ---------------------------------------------------------------- witness check

/// Build the full colouring of K_N from a pair model and check it has no red K_s and no blue K_t.
fn glued_graph(s: usize, t: usize, a: &Graph, b: &Graph, x: impl Fn(usize, usize) -> bool) -> Result<BigGraph, String> {
    let (d, m) = (a.n, b.n);
    let n = 1 + d + m;
    let mut g = BigGraph::new(n);
    for i in 0..d {
        g.set(0, 1 + i, true);
    }
    for i in 0..d {
        for j in i + 1..d {
            g.set(1 + i, 1 + j, a.has_edge(i, j));
        }
    }
    for i in 0..m {
        for j in i + 1..m {
            g.set(1 + d + i, 1 + d + j, b.has_edge(i, j));
        }
    }
    for i in 0..d {
        for j in 0..m {
            g.set(1 + i, 1 + d + j, x(i, j));
        }
    }
    if let Some(k) = g.find_mono(s, true) {
        return Err(format!("witness has a red K{s} on {k:?}"));
    }
    if let Some(k) = g.find_mono(t, false) {
        return Err(format!("witness has a blue K{t} on {k:?}"));
    }
    Ok(g)
}

// ---------------------------------------------------------------- workers

struct Ctx {
    key: (usize, usize),
    stream: Stream,
    solver: Solver,
    cache: CoreCache,
}

fn new_ctx(sh: &Shared, stage: usize, fixed: usize, proof: bool) -> Ctx {
    let st = &sh.stages[stage];
    let fg = &st.fixed().graphs[fixed];
    let stream = Stream::build(sh.cfg.s, sh.cfg.t, fg, st.streamed().n, st.side);
    let mut solver = Solver::new(stream.nvars);
    if proof {
        solver.enable_proof();
    }
    for c in &stream.clauses {
        solver.add_clause_dimacs(c);
    }
    Ctx { key: (stage, fixed), stream, solver, cache: CoreCache::new(sh.cfg.cache_cap) }
}

struct TaskOut {
    /// pattern embedding-search nodes and embed calls in this task (hybrid mode; deterministic cost counters)
    nodes: u64,
    embed: u64,
    /// per-literal anchor scans (pattern propagator)
    scans: u64,
    unsat: u64,
    sat: u64,
    hits: u64,
    solves: u64,
    conflicts: u64,
    checked: bool,
    roots: u64,
    /// literals in learnt clauses (unit mode; average learnt length = lits / conflicts) and failed literals learned by
    /// the cuber
    lits: u64,
    failed: u64,
}

fn lemma_count(s: &Solver) -> u32 {
    s.proof_lemmas as u32
}

fn record_sat(sh: &Shared, w: usize, stage: usize, fixed: usize, idx: usize, g: BigGraph) {
    let d = sh.stages[stage].d;
    let g6 = g.to_g6();
    sh.event(format!("SAT  d={d} fixed#{fixed} streamed#{idx}: verified ({},{})-good colouring of K{} {g6}", sh.cfg.s, sh.cfg.t, g.n));
    sh.workers[w].sat.fetch_add(1, Relaxed);
    sh.stage_sat[stage].fetch_add(1, Relaxed);
    sh.sats.lock().unwrap().push(SatRecord { d, fixed_idx: fixed, streamed_idx: idx, g6 });
    if sh.cfg.stop_on_sat {
        sh.stop.store(true, Relaxed);
    }
}

fn fail(sh: &Shared, msg: String) {
    sh.event(format!("ERROR {msg}"));
    sh.errors.lock().unwrap().push(msg);
    sh.stop.store(true, Relaxed);
}

fn run_stream_task(sh: &Shared, w: usize, task: &Task, ctx_slot: &mut Option<Ctx>, check: bool) -> TaskOut {
    let st = &sh.stages[task.stage];
    let ws = &sh.workers[w];
    // in gray-cube mode task.fixed indexes A-side generalisations, not catalogue graphs
    let fixed_g = if sh.cfg.covers.is_some() && !sh.cfg.one_sided {
        &st.a.graphs[0]
    } else {
        &st.fixed().graphs[task.fixed]
    };
    let mut local;
    let ctx: &mut Ctx = if check {
        local = new_ctx(sh, task.stage, task.fixed, true);
        &mut local
    } else {
        if ctx_slot.as_ref().map(|c| c.key) != Some((task.stage, task.fixed)) {
            *ctx_slot = Some(new_ctx(sh, task.stage, task.fixed, false));
        }
        ctx_slot.as_mut().unwrap()
    };
    ctx.solver.live = Some(ws.live.clone());
    ctx.solver.vivify_enabled = sh.cfg.vivify;
    ctx.solver.mode_switching = sh.cfg.stable;
    let mut out = TaskOut { unsat: 0, sat: 0, hits: 0, solves: 0, conflicts: 0, checked: check, roots: 0, nodes: 0, embed: 0, scans: 0, lits: 0, failed: 0 };
    let c0 = ctx.solver.stats.conflicts;
    let mut last_c = c0;
    let p0 = ctx.solver.stats.propagations;
    let mut assumps: Vec<i32> = Vec::new();
    // for certification: which lemma refuted each pair
    let mut refuted_by: Vec<(usize, u32)> = Vec::new();
    for idx in task.lo..task.hi {
        if sh.stop.load(Relaxed) {
            break;
        }
        ws.pos.store(idx as u64, Relaxed);
        let g = &st.streamed().graphs[idx];
        let (red, blue) = edge_masks(g);
        if ctx.solver.is_root_unsat() {
            out.unsat += 1;
            out.roots += 1;
            refuted_by.push((idx, u32::MAX));
        } else if let Some(lemma) = ctx.cache.lookup(&red, &blue) {
            out.unsat += 1;
            out.hits += 1;
            refuted_by.push((idx, lemma));
        } else {
            ctx.stream.assumptions(g, &mut assumps);
            out.solves += 1;
            match ctx.solver.solve_dimacs(&assumps) {
                SolveResult::Unsat => {
                    out.unsat += 1;
                    if ctx.solver.is_root_unsat() {
                        out.roots += 1;
                        refuted_by.push((idx, u32::MAX));
                        sh.event(format!(
                            "ROOT d={} fixed#{}: the fixed graph is refuted for EVERY streamed graph at once",
                            st.d, task.fixed
                        ));
                    } else {
                        let mut core: Vec<i32> = ctx.solver.core.iter().map(|&l| lit_to_dimacs(l)).collect();
                        if sh.cfg.minimize > 0 {
                            core = minimize_core(ctx, core, sh.cfg.minimize);
                        }
                        let lemma = lemma_count(&ctx.solver).wrapping_sub(1);
                        let mut c = Core { pos: [0; 3], neg: [0; 3], lemma, hits: 0 };
                        for &l in &core {
                            let e = (l.unsigned_abs() as i32 - ctx.stream.evar0) as usize;
                            if l > 0 {
                                c.pos[e >> 6] |= 1 << (e & 63);
                            } else {
                                c.neg[e >> 6] |= 1 << (e & 63);
                            }
                        }
                        ws.cores.fetch_add(1, Relaxed);
                        ws.core_lits.fetch_add(core.len() as u64, Relaxed);
                        refuted_by.push((idx, lemma));
                        ctx.cache.insert(c);
                    }
                }
                SolveResult::Sat => {
                    let (a, b) = match st.side {
                        Side::B => (fixed_g, g),
                        Side::A => (g, fixed_g),
                    };
                    let m = b.n;
                    let solver = &ctx.solver;
                    match glued_graph(sh.cfg.s, sh.cfg.t, a, b, |i, j| solver.model_value(encode::xvar(i, j, m) as usize)) {
                        Ok(full) => {
                            out.sat += 1;
                            record_sat(sh, w, task.stage, task.fixed, idx, full);
                        }
                        Err(e) => fail(sh, format!("solver model failed the independent witness check: {e}")),
                    }
                }
                SolveResult::Unknown => unreachable!("no budget in stream solves"),
            }
        }
        ws.pairs.fetch_add(1, Relaxed);
        let c = ctx.solver.stats.conflicts;
        ws.conflicts.fetch_add(c - last_c, Relaxed);
        last_c = c;
    }
    out.conflicts = ctx.solver.stats.conflicts - c0;
    ws.props.fetch_add(ctx.solver.stats.propagations - p0, Relaxed);
    ws.learnts.store(ctx.solver.num_learnts() as u64, Relaxed);
    if check && !sh.stop.load(Relaxed) {
        ws.checking.store(true, Relaxed);
        if let Err(e) = certify_stream(sh, ctx, fixed_g, st, &refuted_by) {
            fail(sh, format!("certification FAILED for task {} (d={} fixed#{}): {e}", task.id, st.d, task.fixed));
        } else {
            ws.checked_pairs.fetch_add(refuted_by.len() as u64, Relaxed);
            sh.stage_checked[task.stage].fetch_add(refuted_by.len() as u64, Relaxed);
        }
        ws.checking.store(false, Relaxed);
    }
    out
}

/// Deletion-based core shrinking under a conflict budget. Every intermediate UNSAT is a genuine refutation of a
/// partial assignment (the solver logs its core clause as a lemma), so a smaller core is a wider generalisation.
fn minimize_core(ctx: &mut Ctx, mut core: Vec<i32>, budget: u64) -> Vec<i32> {
    let saved = ctx.solver.conflict_budget;
    ctx.solver.conflict_budget = budget;
    let mut i = 0;
    while i < core.len() && core.len() > 1 {
        let mut trial = core.clone();
        trial.remove(i);
        match ctx.solver.solve_dimacs(&trial) {
            SolveResult::Unsat if !ctx.solver.is_root_unsat() => {
                let mut c: Vec<i32> = ctx.solver.core.iter().map(|&l| lit_to_dimacs(l)).collect();
                c.sort_unstable_by_key(|l| l.unsigned_abs());
                core = c;
                // keep i: the element at i is new
            }
            SolveResult::Unsat => break,
            _ => i += 1,
        }
    }
    ctx.solver.conflict_budget = saved;
    // re-derive the final core so it is the most recent lemma in the log
    let r = ctx.solver.solve_dimacs(&core);
    debug_assert_eq!(r, SolveResult::Unsat);
    let mut c: Vec<i32> = ctx.solver.core.iter().map(|&l| lit_to_dimacs(l)).collect();
    c.sort_unstable_by_key(|l| l.unsigned_abs());
    c
}

/// Independent certification of one streamed task:
/// 1. every lemma in the solver's log is RUP (independent checker, against the stream formula as built);
/// 2. every UNSAT pair is refuted by a checked lemma made only of negated assumption literals of that pair
///    (or by the empty clause);
/// 3. the glue lemma holds for every pair: stream clauses reduce to clauses of the independently encoded F(A,B).
fn certify_stream(sh: &Shared, ctx: &Ctx, fixed: &Graph, st: &Stage, refuted_by: &[(usize, u32)]) -> Result<(), String> {
    let log = ctx.solver.proof.as_ref().ok_or("no proof log")?;
    let mut ck = Checker::new(ctx.stream.nvars, &ctx.stream.clauses);
    let mut lemmas: Vec<Vec<i32>> = Vec::new();
    let mut cur = Vec::new();
    for &x in log {
        if x == 0 {
            if !ck.check_and_add(&cur) {
                return Err(format!("lemma #{} {:?} is not RUP", lemmas.len(), cur));
            }
            lemmas.push(std::mem::take(&mut cur));
        } else {
            cur.push(x);
        }
    }
    let mut assumps = Vec::new();
    for &(idx, lemma) in refuted_by {
        let g = &st.streamed().graphs[idx];
        glue_check(&ctx.stream, fixed, g).map_err(|e| format!("glue check, streamed #{idx}: {e}"))?;
        if lemma == u32::MAX {
            if !ck.proved_unsat() {
                return Err(format!("pair #{idx} claimed refuted at root but no empty clause was checked"));
            }
            continue;
        }
        let cl = lemmas.get(lemma as usize).ok_or_else(|| format!("pair #{idx}: lemma {lemma} missing"))?;
        ctx.stream.assumptions(g, &mut assumps);
        let neg: std::collections::HashSet<i32> = assumps.iter().map(|&l| -l).collect();
        if !cl.iter().all(|l| neg.contains(l)) {
            return Err(format!("pair #{idx}: refuting lemma {cl:?} is not falsified by the pair's edges"));
        }
    }
    let _ = sh;
    Ok(())
}

fn run_pair_task(sh: &Shared, w: usize, task: &Task, check: bool) -> TaskOut {
    let st = &sh.stages[task.stage];
    let coneprop = crate::cone::coneprop_env();
    let ws = &sh.workers[w];
    let fixed_g = &st.fixed().graphs[task.fixed];
    let mut out = TaskOut { unsat: 0, sat: 0, hits: 0, solves: 0, conflicts: 0, checked: check, roots: 0, nodes: 0, embed: 0, scans: 0, lits: 0, failed: 0 };
    for idx in task.lo..task.hi {
        if sh.stop.load(Relaxed) {
            break;
        }
        ws.pos.store(idx as u64, Relaxed);
        let g = &st.streamed().graphs[idx];
        let (a, b) = match st.side {
            Side::B => (fixed_g, g),
            Side::A => (g, fixed_g),
        };
        let mut cls = pair_clauses(sh.cfg.s, sh.cfg.t, a, b);
        let mut nv = a.n * b.n;
        if sh.cfg.degree_axioms {
            let (lo, hi) = encode::degree_window(sh.cfg.s, sh.cfg.t, sh.cfg.n).expect("degree window unknown");
            let mut next = nv as i32 + 1;
            cls.extend(encode::pair_degree_axioms(a, b, lo, hi, &mut next));
            nv = (next - 1) as usize;
        }
        if sh.cfg.book_axioms {
            let mut next = nv as i32 + 1;
            cls.extend(encode::pair_book_axioms(sh.cfg.s, sh.cfg.t, a, b, &mut next));
            nv = (next - 1) as usize;
        }
        let mut s = Solver::new(nv);
        s.live = Some(ws.live.clone());
        s.vivify_enabled = sh.cfg.vivify;
        s.mode_switching = sh.cfg.stable;
        if check {
            // LRAT with antecedent hints, checked by the independent hint checker in linear time (the hint-free RUP
            // checker cost 65x the solve time on a d=10 unit); vivification has no LRAT logging yet, so it is off here
            s.lrat_enable();
            s.vivify_enabled = false;
        }
        for c in &cls {
            s.add_clause_dimacs(c);
        }
        if let Some(deg) = coneprop {
            // MONSTER_CONEPROP: cone reasoning inside CDCL (uncertified; build() refuses it with --check-every)
            s.cones = Some(Box::new(crate::cone::ConeProp::new(crate::cone::Table::new(sh.cfg.s, sh.cfg.t, a), b, deg)));
        }
        out.solves += 1;
        let r = s.solve(&[]);
        out.conflicts += s.stats.conflicts;
        if let Some(cp) = &s.cones {
            out.nodes += cp.stats.implied;
            out.embed += cp.stats.conflicts;
        }
        ws.conflicts.fetch_add(s.stats.conflicts, Relaxed);
        ws.props.fetch_add(s.stats.propagations, Relaxed);
        match r {
            SolveResult::Unsat => {
                out.unsat += 1;
                if check {
                    let lines = s.lrat.as_ref().unwrap();
                    let mut ck = crate::sat::checker::HintChecker::new(&cls);
                    match ck.check_lines(lines) {
                        Ok(()) if ck.proved_unsat() => {
                            ws.checked_pairs.fetch_add(1, Relaxed);
                            sh.stage_checked[task.stage].fetch_add(1, Relaxed);
                        }
                        Ok(()) => fail(sh, format!("pair proof for #{idx} has no empty clause")),
                        Err(e) => fail(sh, format!("pair proof for #{idx} rejected: {e}")),
                    }
                }
            }
            SolveResult::Sat => {
                let m = b.n;
                match glued_graph(sh.cfg.s, sh.cfg.t, a, b, |i, j| s.model_value(encode::xvar(i, j, m) as usize)) {
                    Ok(full) => {
                        out.sat += 1;
                        record_sat(sh, w, task.stage, task.fixed, idx, full);
                    }
                    Err(e) => fail(sh, format!("solver model failed the independent witness check: {e}")),
                }
            }
            SolveResult::Unknown => unreachable!(),
        }
        ws.pairs.fetch_add(1, Relaxed);
    }
    out
}

fn run_unit_task(sh: &Shared, w: usize, task: &Task, check: bool) -> TaskOut {
    let st = &sh.stages[task.stage];
    let ws = &sh.workers[w];
    let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
    let (ga, gb) = (&ca.gens[task.fixed], &cb.gens[task.lo]);
    let (mem_a, mem_b) = (&ca.members[task.fixed], &cb.members[task.lo]);
    let mut gm = build_gamma(sh.cfg.s, sh.cfg.t, ga, gb);
    if sh.cfg.degree_axioms {
        // uncertified measurement switch (build() refuses it with --check-every > 0): degree windows as cardinality
        // constraints with auxiliary variables appended after the unit's own variables
        let (lo, hi) = crate::encode::degree_window(sh.cfg.s, sh.cfg.t, sh.cfg.n).expect("degree window unknown");
        let mut next = gm.nvars as i32 + 1;
        let extra = crate::cover::unit_degree_axioms(&gm, ga, gb, lo, hi, &mut next);
        gm.clauses.extend(extra);
        gm.nvars = (next - 1) as usize;
    }
    let mut solver = Solver::new(gm.nvars);
    solver.live = Some(ws.live.clone());
    solver.vivify_enabled = sh.cfg.vivify;
    solver.mode_switching = sh.cfg.stable;
    if std::env::var_os("MONSTER_REDUCE_DROP").is_none() {
        solver.reduce_drop = 90; // measured 1.8x on the d=10 sample (RESULTS.md 2026-10-27); 95-98% was no better on probes
    }
    // MONSTER_PHASE_SEED=S: pseudo-random initial phases instead of all-blue (a semantics-preserving perturbation, to
    // measure how much of a unit's cost is solver variance: the heavy-tail / portfolio question)
    if let Some(seed) = std::env::var("MONSTER_PHASE_SEED").ok().and_then(|v| v.parse::<u64>().ok()) {
        solver.set_initial_phase(None, seed);
    }
    // online certification: the LRAT lines (with deletions) stream to a checker thread in 4,096-line chunks, so the
    // proof is never held in memory (a 17M-conflict unit logs ~4 GB) and the checker's memory follows the live database
    let mut checker: Option<std::thread::JoinHandle<Result<crate::sat::checker::HintChecker, String>>> = None;
    if check {
        // LRAT with hints (see run_pair_task); vivification is off under LRAT
        solver.lrat_enable();
        solver.vivify_enabled = false;
        let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<crate::sat::solver::LratLine>>(64);
        solver.lrat_sink = Some(tx);
        let cls: Vec<Vec<i32>> = gm.clauses.clone();
        checker = Some(std::thread::spawn(move || {
            let mut ck = crate::sat::checker::HintChecker::new(&cls);
            let mut err: Option<String> = None;
            for chunk in rx {
                if err.is_none() {
                    if let Err(e) = ck.check_lines(&chunk) {
                        err = Some(e);
                    }
                }
            }
            match err {
                None => Ok(ck),
                Some(e) => Err(e),
            }
        }));
    }
    for c in &gm.clauses {
        solver.add_clause_dimacs(c);
    }
    let mut out = TaskOut { unsat: 0, sat: 0, hits: 0, solves: 1, conflicts: 0, checked: check, roots: 0, nodes: 0, embed: 0, scans: 0, lits: 0, failed: 0 };
    let npairs = (mem_a.len() * mem_b.len()) as u64;
    ws.pos.store(0, Relaxed);
    ws.hi.store(npairs, Relaxed);
    // 1. the whole unit at once, then (optionally) cube-and-conquer inside the same instance
    solver.conflict_budget = sh.cfg.unit_budget;
    let mut whole = solver.solve(&[]);
    if whole == SolveResult::Unknown && sh.cfg.cube_budget > 0 {
        let mut nodes = 0u64;
        whole = match cube(&mut solver, &mut Vec::new(), sh.cfg.cube_budget, &mut nodes, 0) {
            CubeOut::Refuted(cl, _) => {
                debug_assert!(cl.is_empty());
                SolveResult::Unsat
            }
            CubeOut::Sat => SolveResult::Sat,
        };
        out.solves += nodes;
    }
    solver.conflict_budget = u64::MAX;
    // (member a, member b, refuting lemma: LRAT id when certifying, else index in the lemma log; MAX = root)
    let mut refuted: Vec<(usize, usize, u64)> = Vec::new();
    if whole == SolveResult::Unsat {
        out.unsat = npairs;
        out.roots = npairs;
        for i in 0..mem_a.len() {
            for j in 0..mem_b.len() {
                refuted.push((i, j, u64::MAX));
            }
        }
    } else {
        // 2. pair by pair under gray assumptions, with a core cache over the gray literals
        let mut cache = CoreCache::new(sh.cfg.cache_cap);
        let mut assumps = Vec::new();
        let gray0 = (gm.d * gm.m + 1) as i32;
        'pairs: for (i, ma) in mem_a.iter().enumerate() {
            for (j, mb) in mem_b.iter().enumerate() {
                if sh.stop.load(Relaxed) {
                    break 'pairs;
                }
                gm.assumptions(ma.t, mb.t, &mut assumps);
                let mut red = [0u64; 3];
                let mut blue = [0u64; 3];
                for (k, &l) in assumps.iter().enumerate() {
                    if l > 0 {
                        red[k >> 6] |= 1 << (k & 63);
                    } else {
                        blue[k >> 6] |= 1 << (k & 63);
                    }
                }
                if solver.is_root_unsat() {
                    out.unsat += 1;
                    out.roots += 1;
                    refuted.push((i, j, u64::MAX));
                } else if let Some(lemma) = cache.lookup(&red, &blue) {
                    out.unsat += 1;
                    out.hits += 1;
                    refuted.push((i, j, lemma as u64));
                } else {
                    out.solves += 1;
                    match solver.solve_dimacs(&assumps) {
                        SolveResult::Unsat => {
                            out.unsat += 1;
                            if solver.is_root_unsat() {
                                out.roots += 1;
                                refuted.push((i, j, u64::MAX));
                            } else {
                                let lemma = if check { solver.last_lrat_id() as u32 } else { lemma_count(&solver).wrapping_sub(1) };
                                let mut c = Core { pos: [0; 3], neg: [0; 3], lemma, hits: 0 };
                                for &l in &solver.core {
                                    let dl = lit_to_dimacs(l);
                                    let e = (dl.unsigned_abs() as i32 - gray0) as usize;
                                    if dl > 0 {
                                        c.pos[e >> 6] |= 1 << (e & 63);
                                    } else {
                                        c.neg[e >> 6] |= 1 << (e & 63);
                                    }
                                }
                                ws.cores.fetch_add(1, Relaxed);
                                ws.core_lits.fetch_add(solver.core.len() as u64, Relaxed);
                                refuted.push((i, j, lemma as u64));
                                cache.insert(c);
                            }
                        }
                        SolveResult::Sat => {
                            let (xa, xb) = (&st.a.graphs[ma.cat as usize], &st.b.graphs[mb.cat as usize]);
                            let m = gm.m;
                            let s_ = &solver;
                            let r = glued_graph(sh.cfg.s, sh.cfg.t, xa, xb, |a, b| {
                                s_.model_value(1 + ma.pi[a] as usize * m + mb.pi[b] as usize)
                            });
                            match r {
                                Ok(full) => {
                                    out.sat += 1;
                                    record_sat(sh, w, task.stage, ma.cat as usize, mb.cat as usize, full);
                                }
                                Err(e) => fail(sh, format!("unit model failed the independent witness check: {e}")),
                            }
                        }
                        SolveResult::Unknown => unreachable!(),
                    }
                }
                ws.pos.fetch_add(1, Relaxed);
            }
        }
    }
    out.conflicts = solver.stats.conflicts;
    out.lits = solver.stats.learnt_lits;
    out.failed = solver.stats.failed_lits;
    ws.conflicts.fetch_add(solver.stats.conflicts, Relaxed);
    ws.props.fetch_add(solver.stats.propagations, Relaxed);
    ws.pairs.fetch_add(out.unsat + out.sat, Relaxed);
    if let Some(h) = checker.take() {
        ws.checking.store(true, Relaxed);
        solver.lrat_finish();
        let joined = h.join().unwrap_or_else(|_| Err("checker thread panicked".into()));
        if !sh.stop.load(Relaxed) {
            match joined.and_then(|ck| certify_unit(sh, &ck, &gm, st, mem_a, mem_b, &refuted)) {
                Ok(()) => {
                    ws.checked_pairs.fetch_add(refuted.len() as u64, Relaxed);
                    sh.stage_checked[task.stage].fetch_add(refuted.len() as u64, Relaxed);
                }
                Err(e) => fail(sh, format!("certification FAILED for unit ({},{}) d={}: {e}", task.fixed, task.lo, st.d)),
            }
        }
        ws.checking.store(false, Relaxed);
    }
    out
}

pub(crate) enum CubeOut {
    /// refuted: a logged clause made only of negations of the cube literals, and its LRAT id (0 without LRAT)
    Refuted(Vec<i32>, u64),
    Sat,
}

/// The solver's refuting clause after an UNSAT `solve` under assumptions: the negated core, or the empty clause at root.
pub(crate) fn refuting_clause(solver: &Solver) -> CubeOut {
    if solver.is_root_unsat() {
        CubeOut::Refuted(vec![], solver.last_lrat_id())
    } else {
        CubeOut::Refuted(solver.core.iter().map(|&l| -lit_to_dimacs(l)).collect(), solver.last_lrat_id())
    }
}

/// DFS cube-and-conquer under the cube `prefix` (DIMACS literals) in ONE solver: learned clauses are kept across
/// cubes. A refuted cube yields its core clause (logged by the solver); two refuted children are resolved on the
/// split variable and the resolvent is logged (RUP: both parents are in the database; under LRAT its hints are the
/// two parents). If a child's clause does not mention the split literal it already refutes the parent and the
/// sibling is skipped.
pub(crate) fn cube(solver: &mut Solver, prefix: &mut Vec<i32>, budget: u64, nodes: &mut u64, depth: usize) -> CubeOut {
    *nodes += 1;
    solver.conflict_budget = budget;
    match solver.solve_dimacs(prefix) {
        SolveResult::Sat => return CubeOut::Sat,
        SolveResult::Unsat => return refuting_clause(solver),
        SolveResult::Unknown => {}
    }
    let assumps: Vec<u32> = prefix.iter().map(|&l| crate::sat::solver::lit_from_dimacs(l)).collect();
    let split = match solver.lookahead_pick(&assumps) {
        Some(l) => lit_to_dimacs(l),
        None => {
            // nothing to split on (or the prefix conflicts): finish without a budget
            solver.conflict_budget = u64::MAX;
            return match solver.solve_dimacs(prefix) {
                SolveResult::Unsat => refuting_clause(solver),
                _ => CubeOut::Sat,
            };
        }
    };
    let mut kids: Vec<(Vec<i32>, u64)> = Vec::new();
    for lit in [split, -split] {
        prefix.push(lit);
        let r = cube(solver, prefix, budget, nodes, depth + 1);
        prefix.pop();
        match r {
            CubeOut::Sat => return CubeOut::Sat,
            CubeOut::Refuted(cl, id) => {
                if !cl.contains(&-lit) {
                    return CubeOut::Refuted(cl, id); // refutes the parent cube already
                }
                kids.push((cl, id));
            }
        }
    }
    // resolvent on the split variable; hint order: kids[0] (contains ¬split) becomes unit, kids[1] is then falsified
    let mut res: Vec<i32> = kids[0].0.iter().copied().filter(|&l| l != -split).collect();
    for &l in &kids[1].0 {
        if l != split && !res.contains(&l) {
            res.push(l);
        }
    }
    let id = solver.log_resolvent(&res, &[kids[0].1, kids[1].1]);
    CubeOut::Refuted(res, id)
}

fn certify_unit(
    sh: &Shared,
    ck: &crate::sat::checker::HintChecker,
    gm: &crate::cover::Gamma,
    st: &Stage,
    mem_a: &[Member],
    mem_b: &[Member],
    refuted: &[(usize, usize, u64)],
) -> Result<(), String> {
    // 1. every LRAT line was checked by its hints as it streamed in (independent hint checker, linear in the proof)
    // 2. every pair: glue lemma, and its refuting clause is made of negated gray literals of that pair (or ⊥ was derived)
    let mut assumps = Vec::new();
    for &(i, j, lemma) in refuted {
        let (ma, mb) = (&mem_a[i], &mem_b[j]);
        let (xa, xb) = (&st.a.graphs[ma.cat as usize], &st.b.graphs[mb.cat as usize]);
        unit_glue_check(sh.cfg.s, sh.cfg.t, gm, xa, xb, ma, mb)
            .map_err(|e| format!("glue check, pair ({},{}): {e}", ma.cat, mb.cat))?;
        if lemma == u64::MAX {
            if !ck.proved_unsat() {
                return Err("unit claimed refuted at root but no empty clause was checked".into());
            }
            continue;
        }
        let cl = ck.get(lemma).ok_or("refuting lemma missing")?;
        gm.assumptions(ma.t, mb.t, &mut assumps);
        let neg: std::collections::HashSet<i32> = assumps.iter().map(|&l| -l).collect();
        if !cl.iter().all(|l| neg.contains(l)) {
            return Err(format!("pair ({},{}): refuting lemma {cl:?} is not falsified by its gray pattern", ma.cat, mb.cat));
        }
    }
    Ok(())
}

fn hybrid_solver(sh: &Shared, ws: &WorkerStat, proof: bool) -> Solver {
    let (s, t, n) = (sh.cfg.s, sh.cfg.t, sh.cfg.n);
    let cls = crate::full::full_clauses(s, t, n);
    let mut sv = Solver::new(n * (n - 1) / 2);
    if proof {
        sv.enable_proof();
    }
    for c in &cls {
        sv.add_clause_dimacs(c);
    }
    let mut pp = crate::pattern::PatternProp::new(n);
    pp.max_lbd = sh.cfg.pat_lbd;
    pp.flip_ok = s == t;
    sv.patterns = Some(Box::new(pp));
    sv.live = Some(ws.live.clone());
    sv.vivify_enabled = sh.cfg.vivify;
    if let Some(lib) = &sh.library {
        lib.import(&mut sv);
        // library-only mode for the cube solvers: the library is proved already, learned clauses are not searched
        if std::env::var_os("MONSTER_LIBONLY").is_some() {
            if let Some(pp) = sv.patterns.as_mut() {
                pp.lib_only = true;
            }
        }
    }
    sv
}

/// Assumption cube for a catalogue pair: vertex 0 red to A = 1..d, blue to B = d+1..n-1, A and B edges fixed.
/// Order: vertex-0 edges, then the fixed side, then the streamed side (long shared prefixes for trail reuse).
fn hybrid_cube(st: &Stage, fixed: &Graph, g: &Graph, out: &mut Vec<i32>) {
    use crate::full::evar;
    out.clear();
    let (a, b) = match st.side {
        Side::B => (fixed, g),
        Side::A => (g, fixed),
    };
    let (d, m) = (a.n, b.n);
    for i in 0..d {
        out.push(evar(0, 1 + i));
    }
    for j in 0..m {
        out.push(-evar(0, 1 + d + j));
    }
    let side_a = |out: &mut Vec<i32>| {
        for j in 1..d {
            for i in 0..j {
                let v = evar(1 + i, 1 + j);
                out.push(if a.has_edge(i, j) { v } else { -v });
            }
        }
    };
    let side_b = |out: &mut Vec<i32>| {
        for j in 1..m {
            for i in 0..j {
                let v = evar(1 + d + i, 1 + d + j);
                out.push(if b.has_edge(i, j) { v } else { -v });
            }
        }
    };
    if st.side == Side::B {
        side_a(out);
        side_b(out);
    } else {
        side_b(out);
        side_a(out);
    }
}

/// One-sided cube: vertex 0 red to A = 1..d and blue to B = d+1..n-1, and only the FIXED side's internal edges set.
fn hybrid_cube_one_sided(st: &Stage, fixed: &Graph, out: &mut Vec<i32>) {
    use crate::full::evar;
    out.clear();
    let (d, m) = (st.d, st.m);
    for i in 0..d {
        out.push(evar(0, 1 + i));
    }
    for j in 0..m {
        out.push(-evar(0, 1 + d + j));
    }
    let off = if st.side == Side::B { 1 } else { 1 + d }; // fixed side = A when B is streamed
    for j in 1..fixed.n {
        for i in 0..j {
            let v = evar(off + i, off + j);
            out.push(if fixed.has_edge(i, j) { v } else { -v });
        }
    }
}

/// Gray cube: vertex-0 edges plus the base edges of generalisations ga (A side) and gb (B side); gray edges stay free.
fn hybrid_cube_gray(st: &Stage, ga: &crate::cover::Gen, gb: &crate::cover::Gen, out: &mut Vec<i32>) {
    use crate::full::evar;
    out.clear();
    let (d, m) = (st.d, st.m);
    for i in 0..d {
        out.push(evar(0, 1 + i));
    }
    for j in 0..m {
        out.push(-evar(0, 1 + d + j));
    }
    for (gen, off, n) in [(ga, 1, d), (gb, 1 + d, m)] {
        for j in 1..n {
            for i in 0..j {
                if gen.gray.iter().any(|&(u, v)| (u.min(v), u.max(v)) == (i, j)) {
                    continue;
                }
                let v = evar(off + i, off + j);
                out.push(if gen.base.has_edge(i, j) { v } else { -v });
            }
        }
    }
}

fn run_hybrid_task(sh: &Shared, w: usize, task: &Task, slot: &mut Option<Solver>, check: bool) -> TaskOut {
    let st = &sh.stages[task.stage];
    let ws = &sh.workers[w];
    let fixed_g = &st.fixed().graphs[task.fixed];
    let mut local;
    let sv: &mut Solver = if check {
        local = hybrid_solver(sh, ws, true);
        &mut local
    } else {
        if slot.is_none() {
            *slot = Some(hybrid_solver(sh, ws, false));
        }
        slot.as_mut().unwrap()
    };
    let mut out = TaskOut { unsat: 0, sat: 0, hits: 0, solves: 0, conflicts: 0, checked: check, roots: 0, nodes: 0, embed: 0, scans: 0, lits: 0, failed: 0 };
    let c0 = sv.stats.conflicts;
    let pat_counts = |sv: &Solver| sv.patterns.as_ref().map_or((0, 0, 0), |p| (p.stats.nodes, p.stats.embed_calls, p.stats.scans));
    let (n0, e0, s0) = pat_counts(sv);
    let mut cube = Vec::new();
    let mut refuted: Vec<(usize, u64)> = Vec::new();
    let one = sh.cfg.one_sided;
    let gray = sh.cfg.covers.is_some() && !one;
    let npairs = if one {
        st.streamed().graphs.len() as u64
    } else if gray {
        task_pairs(&sh.cfg, &sh.stages, task)
    } else {
        1
    };
    for idx in task.lo..task.hi {
        if sh.stop.load(Relaxed) {
            break;
        }
        ws.pos.store(idx as u64, Relaxed);
        if gray {
            let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
            hybrid_cube_gray(st, &ca.gens[task.fixed], &cb.gens[task.lo], &mut cube);
        } else if one {
            hybrid_cube_one_sided(st, fixed_g, &mut cube);
        } else {
            let g = &st.streamed().graphs[idx];
            hybrid_cube(st, fixed_g, g, &mut cube);
        }
        out.solves += 1;
        match sv.solve_dimacs(&cube) {
            SolveResult::Unsat => {
                out.unsat += npairs;
                if sv.is_root_unsat() {
                    out.roots += 1;
                    refuted.push((idx, u64::MAX));
                } else {
                    ws.cores.fetch_add(1, Relaxed);
                    ws.core_lits.fetch_add(sv.core.len() as u64, Relaxed);
                    refuted.push((idx, sv.proof_lemmas.saturating_sub(1)));
                }
            }
            SolveResult::Sat => {
                let n = sh.cfg.n;
                let mut full = BigGraph::new(n);
                for j in 1..n {
                    for i in 0..j {
                        full.set(i, j, sv.model_value(crate::full::evar(i, j) as usize));
                    }
                }
                if full.find_mono(sh.cfg.s, true).is_none() && full.find_mono(sh.cfg.t, false).is_none() {
                    out.sat += 1;
                    record_sat(sh, w, task.stage, task.fixed, idx, full);
                } else {
                    fail(sh, "hybrid model failed the independent witness check".into());
                }
            }
            SolveResult::Unknown => unreachable!(),
        }
        ws.pairs.fetch_add(npairs, Relaxed);
    }
    out.conflicts = sv.stats.conflicts - c0;
    let (n1, e1, s1) = pat_counts(sv);
    (out.nodes, out.embed, out.scans) = (n1 - n0, e1 - e0, s1 - s0);
    ws.conflicts.fetch_add(out.conflicts, Relaxed);
    if let Some(pp) = &sv.patterns {
        ws.learnts.store(pp.num_patterns() as u64, Relaxed);
    }
    if check && !sh.stop.load(Relaxed) {
        ws.checking.store(true, Relaxed);
        let log = sv.proof.as_ref().unwrap();
        match crate::full::check_symmetric_lemmas(sh.cfg.s, sh.cfg.t, sh.cfg.n, log) {
            Ok((_, _, unsat, lemmas)) => {
                let mut ok = true;
                for &(idx, li) in &refuted {
                    if li == u64::MAX {
                        ok &= unsat;
                        continue;
                    }
                    if gray {
                        let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
                        hybrid_cube_gray(st, &ca.gens[task.fixed], &cb.gens[task.lo], &mut cube);
                    } else if one {
                        hybrid_cube_one_sided(st, fixed_g, &mut cube);
                    } else {
                        hybrid_cube(st, fixed_g, &st.streamed().graphs[idx], &mut cube);
                    }
                    let neg: std::collections::HashSet<i32> = cube.iter().map(|&l| -l).collect();
                    match lemmas.get(li as usize) {
                        Some(cl) if cl.iter().all(|l| neg.contains(l)) => {}
                        _ => {
                            ok = false;
                            fail(sh, format!("hybrid certification: pair #{idx} has no refuting lemma inside its cube"));
                        }
                    }
                }
                if ok {
                    ws.checked_pairs.fetch_add(refuted.len() as u64 * npairs, Relaxed);
                    sh.stage_checked[task.stage].fetch_add(refuted.len() as u64 * npairs, Relaxed);
                }
            }
            Err(e) => fail(sh, format!("hybrid symmetric proof rejected (task {}): {e}", task.id)),
        }
        ws.checking.store(false, Relaxed);
    }
    out
}

/// Cone mode (uncertified prototype, src/cone.rs): every catalogue pair of the task glued by the feasible-cone
/// search; each A's table is built once per task. SAT answers are rebuilt and brute-force checked like all others.
fn run_cone_task(sh: &Shared, w: usize, task: &Task) -> TaskOut {
    let st = &sh.stages[task.stage];
    let ws = &sh.workers[w];
    let (s, t) = (sh.cfg.s, sh.cfg.t);
    let opts = crate::cone::Opts::from_env();
    let mut out = TaskOut { unsat: 0, sat: 0, hits: 0, solves: 0, conflicts: 0, checked: false, roots: 0, nodes: 0, embed: 0, scans: 0, lits: 0, failed: 0 };
    // (A catalogue index, B catalogue indices)
    let mut groups: Vec<(usize, Vec<usize>)> = Vec::new();
    if uses_covers(&sh.cfg) {
        let (ca, cb) = (st.cov_a.as_ref().unwrap(), st.cov_b.as_ref().unwrap());
        let bs: Vec<usize> = (task.lo..task.hi).flat_map(|g| cb.members[g].iter().map(|mb| mb.cat as usize)).collect();
        groups.extend(ca.members[task.fixed].iter().map(|ma| (ma.cat as usize, bs.clone())));
    } else {
        match st.side {
            Side::B => groups.push((task.fixed, (task.lo..task.hi).collect())),
            Side::A => groups.extend((task.lo..task.hi).map(|i| (i, vec![task.fixed]))),
        }
    }
    ws.pos.store(0, Relaxed);
    ws.hi.store(groups.iter().map(|g| g.1.len() as u64).sum(), Relaxed);
    let mut done = 0u64;
    'all: for (ai, bis) in &groups {
        let a = &st.a.graphs[*ai];
        let tab = crate::cone::Table::new(s, t, a);
        for &bi in bis {
            if sh.stop.load(Relaxed) {
                break 'all;
            }
            let b = &st.b.graphs[bi];
            let (sol, stats) = crate::cone::solve(&tab, b, opts);
            out.solves += 1;
            out.nodes += stats.nodes;
            out.conflicts += stats.fails;
            match sol {
                None => out.unsat += 1,
                Some(cones) => match glued_graph(s, t, a, b, |i, j| cones[j] >> i & 1 == 1) {
                    Ok(full) => {
                        out.sat += 1;
                        record_sat(sh, w, task.stage, *ai, bi, full);
                    }
                    Err(e) => fail(sh, format!("cone solution failed the independent witness check: {e}")),
                },
            }
            done += 1;
            ws.pos.store(done, Relaxed);
            ws.pairs.fetch_add(1, Relaxed);
        }
    }
    ws.conflicts.fetch_add(out.conflicts, Relaxed);
    out
}

fn worker(sh: Arc<Shared>, w: usize) {
    let mut ctx: Option<Ctx> = None;
    let mut hyb: Option<Solver> = None;
    let mut mine = 0usize;
    loop {
        if sh.stop.load(Relaxed) {
            break;
        }
        let k = if sh.cfg.sched_static {
            mine += 1;
            w + (mine - 1) * sh.cfg.workers
        } else {
            sh.next.fetch_add(1, Relaxed)
        };
        if k >= sh.tasks.len() {
            break;
        }
        let task = sh.tasks[k];
        let st = &sh.stages[task.stage];
        let ws = &sh.workers[w];
        ws.busy.store(true, Relaxed);
        ws.task.store(task.id as u64, Relaxed);
        ws.stage_d.store(st.d as u64, Relaxed);
        ws.fixed.store(task.fixed as u64, Relaxed);
        ws.hi.store(task.hi as u64, Relaxed);
        let check = sh.cfg.check_every > 0 && task.id % sh.cfg.check_every == 0;
        let errors_before = sh.errors.lock().unwrap().len();
        let t0 = Instant::now();
        let out = match sh.cfg.mode {
            Mode::Stream => run_stream_task(&sh, w, &task, &mut ctx, check),
            Mode::Pair => run_pair_task(&sh, w, &task, check),
            Mode::Unit => run_unit_task(&sh, w, &task, check),
            Mode::Hybrid => run_hybrid_task(&sh, w, &task, &mut hyb, check),
            Mode::Cone => run_cone_task(&sh, w, &task),
        };
        let secs = t0.elapsed().as_secs_f64();
        // the task line's "checked" records the certification OUTCOME: false if any check (proof, glue, witness)
        // failed during this task, so a resumed certified run can trust "checked":true lines (before 2026-10-27 it
        // recorded only that checking was requested)
        let mut out = out;
        if out.checked && sh.errors.lock().unwrap().len() != errors_before {
            out.checked = false;
        }
        ws.unsat.fetch_add(out.unsat, Relaxed);
        ws.hits.fetch_add(out.hits, Relaxed);
        ws.solves.fetch_add(out.solves, Relaxed);
        ws.roots.fetch_add(out.roots, Relaxed);
        sh.stage_unsat[task.stage].fetch_add(out.unsat, Relaxed);
        let done = out.unsat + out.sat;
        sh.stage_done[task.stage].fetch_add(done, Relaxed);
        let complete = done == task_pairs(&sh.cfg, &sh.stages, &task);
        if complete {
            sh.tasks_done.fetch_add(1, Relaxed);
            if out.checked {
                sh.tasks_checked.fetch_add(1, Relaxed);
            }
            if let Some(f) = sh.log.lock().unwrap().as_mut() {
                let _ = writeln!(
                    f,
                    "{{\"task\":{},\"d\":{},\"fixed\":{},\"lo\":{},\"hi\":{},\"unsat\":{},\"sat\":{},\"hits\":{},\"solves\":{},\"roots\":{},\"conflicts\":{},\"nodes\":{},\"embed\":{},\"scans\":{},\"lits\":{},\"failed\":{},\"secs\":{:.3},\"checked\":{},\"worker\":{}}}",
                    task.id, st.d, task.fixed, task.lo, task.hi, out.unsat, out.sat, out.hits, out.solves, out.roots,
                    out.conflicts, out.nodes, out.embed, out.scans, out.lits, out.failed, secs, out.checked, w
                );
            }
        }
        ws.busy.store(false, Relaxed);
    }
    ws_idle(&sh, w);
}

fn ws_idle(sh: &Shared, w: usize) {
    sh.workers[w].busy.store(false, Relaxed);
}

/// Previously completed tasks (resume): keys (d, fixed, lo, hi) -> (unsat, sat, certified).
fn read_done(path: &std::path::Path) -> std::collections::HashMap<(usize, usize, usize, usize), (u64, u64, bool)> {
    let mut done = std::collections::HashMap::new();
    if let Ok(text) = std::fs::read_to_string(path) {
        for line in text.lines() {
            let get = |k: &str| -> Option<u64> {
                let i = line.find(&format!("\"{k}\":"))? + k.len() + 3;
                let rest = &line[i..];
                let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
                rest[..end].parse().ok()
            };
            if let (Some(d), Some(f), Some(lo), Some(hi), Some(u), Some(s)) =
                (get("d"), get("fixed"), get("lo"), get("hi"), get("unsat"), get("sat"))
            {
                let certified = line.contains("\"checked\":true");
                done.insert((d as usize, f as usize, lo as usize, hi as usize), (u, s, certified));
            }
        }
    }
    done
}

pub fn build(cfg: Config) -> Result<(Arc<Shared>, Vec<String>), String> {
    if cfg.mode == Mode::Cone && cfg.check_every > 0 {
        return Err("--mode cone writes no proofs yet (uncertified prototype): pass --check-every 0".into());
    }
    if cfg.mode == Mode::Pair && cfg.check_every > 0 && crate::cone::coneprop_env().is_some() {
        return Err("MONSTER_CONEPROP writes no proofs yet (uncertified prototype): pass --check-every 0".into());
    }
    if cfg.mode == Mode::Unit && cfg.check_every > 0 && cfg.degree_axioms {
        return Err("--degree-axioms in unit mode adds underived clauses (measurement only): pass --check-every 0".into());
    }
    let (stages, mut notes) = plan(&cfg)?;
    let library = if cfg.mode == Mode::Hybrid {
        let cache = std::path::PathBuf::from(format!(
            "{}/monster/results/library_R{}{}_K{}{}.bin",
            std::env::var("HOME").unwrap_or_default(),
            cfg.s,
            cfg.t,
            cfg.n,
            if cfg.books { "_books" } else { "" }
        ));
        let t0 = std::time::Instant::now();
        // uncertified runs (measurement, `ab`) trust the cache's verification stamp; certified ones re-check
        let lib = crate::full::Library::get(cfg.s, cfg.t, cfg.n, cfg.books, Some(&cache), cfg.check_every == 0)?;
        notes.push(format!(
            "lemma library: {} lemmas, proof {} lines {} ({:.1}s, cache {})",
            lib.lemmas.len(),
            lib.log_lemmas,
            if lib.stamp_trusted { "verified earlier (stamp matches the file's sha256; uncertified run)" } else { "VERIFIED by the symmetric checker" },
            t0.elapsed().as_secs_f64(),
            cache.display()
        ));
        for l in &lib.lines {
            notes.push(l.clone());
        }
        Some(lib)
    } else {
        None
    };
    let mut tasks = make_tasks(&cfg, &stages);
    let (plan_tasks, plan_pairs) = {
        let mut full_cfg = cfg.clone();
        full_cfg.sample = None;
        let all = if cfg.sample.is_some() { make_tasks(&full_cfg, &stages) } else { tasks.clone() };
        (all.len(), all.iter().map(|t| task_pairs(&full_cfg, &stages, t)).sum::<u64>())
    };
    let ns = stages.len();
    // per-stage pair targets of the tasks still to run (computed after `--resume` drops finished tasks, whose pairs
    // are reported separately as `skipped_pairs`; counting them twice made resumed runs print target > done)
    let mut stage_target: Vec<u64> = vec![0; ns];
    let mut skipped = vec![0u64; ns];
    let mut pre_done = vec![0u64; ns];
    let mut pre_unsat = vec![0u64; ns];
    let mut pre_sat = vec![0u64; ns];
    let mut pre_checked = vec![0u64; ns];
    let mut log = None;
    if let Some(dir) = &cfg.out {
        std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        let tpath = dir.join("tasks.jsonl");
        if cfg.resume {
            let done = read_done(&tpath);
            let certified_run = cfg.check_every > 0;
            tasks.retain(|t| {
                let key = (stages[t.stage].d, t.fixed, t.lo, t.hi);
                match done.get(&key) {
                    // a certified run re-runs lines that were not certified (missing or failed check)
                    Some(&(_, _, false)) if certified_run => true,
                    Some(&(u, s, certified)) => {
                        pre_done[t.stage] += u + s;
                        pre_unsat[t.stage] += u;
                        pre_sat[t.stage] += s;
                        skipped[t.stage] += u + s;
                        if certified {
                            pre_checked[t.stage] += u;
                        }
                        false
                    }
                    None => true,
                }
            });
            for (i, t) in tasks.iter_mut().enumerate() {
                t.id = i;
            }
        } else if tpath.exists() {
            return Err(format!("{} exists: use --resume or a fresh --out directory", tpath.display()));
        }
        log = Some(
            std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&tpath)
                .map_err(|e| format!("{}: {e}", tpath.display()))?,
        );
    }
    for t in &tasks {
        stage_target[t.stage] += task_pairs(&cfg, &stages, t);
    }
    let workers = (0..cfg.workers).map(|_| WorkerStat::default()).collect();
    let sh = Shared {
        stages,
        tasks,
        next: AtomicUsize::new(0),
        stop: AtomicBool::new(false),
        workers,
        stage_done: pre_done.into_iter().map(AtomicU64::new).collect(),
        stage_unsat: pre_unsat.into_iter().map(AtomicU64::new).collect(),
        stage_sat: pre_sat.into_iter().map(AtomicU64::new).collect(),
        stage_checked: pre_checked.into_iter().map(AtomicU64::new).collect(),
        stage_target,
        tasks_done: AtomicUsize::new(0),
        tasks_checked: AtomicUsize::new(0),
        sats: Mutex::new(Vec::new()),
        errors: Mutex::new(Vec::new()),
        events: Mutex::new(Vec::new()),
        log: Mutex::new(log),
        library: None,
        started: Instant::now(),
        skipped_pairs: skipped,
        plan_tasks,
        plan_pairs,
        cfg,
    };
    let mut sh = sh;
    sh.library = library;
    Ok((Arc::new(sh), notes))
}

pub fn spawn_workers(sh: &Arc<Shared>) -> Vec<std::thread::JoinHandle<()>> {
    (0..sh.cfg.workers)
        .map(|w| {
            let sh = Arc::clone(sh);
            std::thread::Builder::new()
                .name(format!("w{w:02}"))
                .stack_size(16 << 20)
                .spawn(move || worker(sh, w))
                .unwrap()
        })
        .collect()
}
