//! Gray-edge generalisations (Gauthier-Brown, as built by the repo's v10 `cover` tool). UNTRUSTED input: every pair
//! is re-checked against its own pair CNF by [`unit_glue_check`], so a wrong cover can only make a pair fail.
//!
//! Cover file lines (v10 format):
//!   `G id k u1 v1 .. uk vk base_g6`   generalisation: base graph (gray edges absent) plus k gray edges
//!   `A catidx genid t pi0 .. pi{n-1}` catalogue graph X -> generalisation genid, gray pattern t (bit i = gray edge
//!                                     i red), vertex a of X -> pi[a], with pi(X) = instantiate(gen, t)
//!
//! A unit is a pair of generalisations (ga, gb). GAMMA(ga, gb) has cross variables y(u,w) = 1 + u*m + w, then the
//! A-side gray variables, then the B-side gray variables. One clause per red K_s / blue K_t of the glued graph that
//! the fixed edges do not already rule out, with gray edges inside the clique as guard literals; plus the
//! side-internal goodness clauses (they also cover the cliques through v).

use crate::encode::{pair_clauses, Clause};
use crate::graph::Graph;
use std::path::Path;

#[derive(Clone, Debug)]
pub struct Gen {
    pub base: Graph,
    pub gray: Vec<(usize, usize)>,
}

#[derive(Clone, Copy, Debug)]
pub struct Member {
    pub cat: u32,
    pub t: u64,
    pub pi: [u8; 32],
}

pub struct Cover {
    pub gens: Vec<Gen>,
    /// members[g] = catalogue graphs instantiating generalisation g
    pub members: Vec<Vec<Member>>,
}

impl Gen {
    pub fn instantiate(&self, t: u64) -> Graph {
        let mut g = self.base.clone();
        for (i, &(u, v)) in self.gray.iter().enumerate() {
            if t >> i & 1 == 1 {
                g.add_edge(u, v);
            }
        }
        g
    }
    /// graph of edges that are red or gray (where a red clique can still appear)
    fn red_or_gray(&self) -> Graph {
        self.instantiate(u64::MAX)
    }
    /// graph of edges that are blue or gray, as the complement view: returns G' whose cliques are the sets with no
    /// fixed red edge
    fn blue_or_gray_complement(&self) -> Graph {
        // sets with no fixed red edge = independent sets of the base graph
        self.base.clone()
    }
    fn gray_index(&self, u: usize, v: usize) -> Option<usize> {
        let (u, v) = if u < v { (u, v) } else { (v, u) };
        self.gray.iter().position(|&(a, b)| (a.min(b), a.max(b)) == (u, v))
    }
}

impl Cover {
    /// The trivial cover with ONE generalisation whose every edge is gray (needs C(n,2) <= 64): each catalogue graph
    /// is an instantiation of it under the identity permutation.
    pub fn all_gray(catalogue: &[Graph], n: usize) -> Result<Cover, String> {
        let mut gray = Vec::new();
        for j in 1..n {
            for i in 0..j {
                gray.push((i, j));
            }
        }
        if gray.len() > 64 {
            return Err(format!("all-gray cover needs C(n,2) <= 64, n = {n}"));
        }
        let mut members = Vec::with_capacity(catalogue.len());
        for (cat, g) in catalogue.iter().enumerate() {
            let mut t = 0u64;
            for (k, &(i, j)) in gray.iter().enumerate() {
                if g.has_edge(i, j) {
                    t |= 1 << k;
                }
            }
            let mut pi = [0u8; 32];
            for a in 0..n {
                pi[a] = a as u8;
            }
            members.push(Member { cat: cat as u32, t, pi });
        }
        Ok(Cover { gens: vec![Gen { base: Graph::empty(n), gray }], members: vec![members] })
    }

    /// Load a cover and check it against the catalogue: every catalogue graph must be a member exactly once and
    /// pi(X) must equal the instantiation (cheap structural check; soundness never depends on it).
    pub fn load(path: &Path, catalogue: &[Graph]) -> Result<Cover, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let mut gens: Vec<Gen> = Vec::new();
        let mut assign: Vec<Option<(u32, Member)>> = vec![None; catalogue.len()];
        for (ln, line) in text.lines().enumerate() {
            let f: Vec<&str> = line.split_whitespace().collect();
            if f.is_empty() {
                continue;
            }
            let err = |m: &str| format!("{}:{}: {m}", path.display(), ln + 1);
            match f[0] {
                "G" => {
                    let id: usize = f[1].parse().map_err(|_| err("bad gen id"))?;
                    let k: usize = f[2].parse().map_err(|_| err("bad k"))?;
                    if id != gens.len() || f.len() != 4 + 2 * k {
                        return Err(err("generalisations must be numbered 0.. in order"));
                    }
                    let gray = (0..k)
                        .map(|i| -> Result<(usize, usize), String> {
                            Ok((
                                f[3 + 2 * i].parse().map_err(|_| err("bad gray edge"))?,
                                f[4 + 2 * i].parse().map_err(|_| err("bad gray edge"))?,
                            ))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let base = Graph::from_g6(f[3 + 2 * k]).map_err(|e| err(&e))?;
                    if k > 64 || gray.iter().any(|&(u, v)| u == v || u >= base.n || v >= base.n || base.has_edge(u, v)) {
                        return Err(err("gray edge out of range or present in base"));
                    }
                    gens.push(Gen { base, gray });
                }
                "A" => {
                    let cat: usize = f[1].parse().map_err(|_| err("bad catalogue index"))?;
                    let gid: u32 = f[2].parse().map_err(|_| err("bad gen id"))?;
                    let t: u64 = f[3].parse().map_err(|_| err("bad pattern"))?;
                    let n = catalogue.get(cat).ok_or_else(|| err("catalogue index out of range"))?.n;
                    if f.len() != 4 + n {
                        return Err(err("wrong permutation length"));
                    }
                    let mut pi = [0u8; 32];
                    for a in 0..n {
                        pi[a] = f[4 + a].parse().map_err(|_| err("bad permutation"))?;
                    }
                    if assign[cat].is_some() {
                        return Err(err("catalogue graph assigned twice"));
                    }
                    assign[cat] = Some((gid, Member { cat: cat as u32, t, pi }));
                }
                _ => return Err(err("unknown line type")),
            }
        }
        let mut members = vec![Vec::new(); gens.len()];
        for (cat, a) in assign.into_iter().enumerate() {
            let (gid, m) = a.ok_or_else(|| format!("{}: catalogue graph {cat} not covered", path.display()))?;
            let g = gens.get(gid as usize).ok_or_else(|| format!("{}: gen {gid} missing", path.display()))?;
            // structural check pi(X) == instantiate(g, t)
            let x = &catalogue[cat];
            let inst = g.instantiate(m.t);
            let mut seen = 0u32;
            for a in 0..x.n {
                seen |= 1 << m.pi[a];
            }
            if seen != crate::graph::mask(x.n) {
                return Err(format!("{}: catalogue graph {cat}: pi is not a permutation", path.display()));
            }
            for a in 0..x.n {
                for b in a + 1..x.n {
                    if x.has_edge(a, b) != inst.has_edge(m.pi[a] as usize, m.pi[b] as usize) {
                        return Err(format!("{}: catalogue graph {cat}: pi(X) != instantiation", path.display()));
                    }
                }
            }
            members[gid as usize].push(m);
        }
        Ok(Cover { gens, members })
    }
}

/// GAMMA for a unit.
pub struct Gamma {
    pub d: usize,
    pub m: usize,
    pub ka: usize,
    pub kb: usize,
    pub nvars: usize,
    pub clauses: Vec<Clause>,
}

impl Gamma {
    pub fn gray_a(&self, i: usize) -> i32 {
        (self.d * self.m + 1 + i) as i32
    }
    pub fn gray_b(&self, i: usize) -> i32 {
        (self.d * self.m + 1 + self.ka + i) as i32
    }
    pub fn assumptions(&self, ta: u64, tb: u64, out: &mut Vec<i32>) {
        out.clear();
        for i in 0..self.ka {
            let v = self.gray_a(i);
            out.push(if ta >> i & 1 == 1 { v } else { -v });
        }
        for i in 0..self.kb {
            let v = self.gray_b(i);
            out.push(if tb >> i & 1 == 1 { v } else { -v });
        }
    }
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

pub fn build_gamma(s: usize, t: usize, ga: &Gen, gb: &Gen) -> Gamma {
    let (d, m) = (ga.base.n, gb.base.n);
    let (ka, kb) = (ga.gray.len(), gb.gray.len());
    let mut g = Gamma { d, m, ka, kb, nvars: d * m + ka + kb, clauses: Vec::new() };
    // red cliques may only use red or gray edges; blue cliques only blue or gray edges
    let ra = ga.red_or_gray();
    let rb = gb.red_or_gray();
    let ba = ga.blue_or_gray_complement();
    let bb = gb.blue_or_gray_complement();
    let guard = |gen: &Gen, set: u32, red: bool, base_var: usize, out: &mut Clause| {
        let vs: Vec<usize> = bits(set).collect();
        for p in 0..vs.len() {
            for q in p + 1..vs.len() {
                if let Some(i) = gen.gray_index(vs[p], vs[q]) {
                    let v = (base_var + i) as i32;
                    out.push(if red { -v } else { v });
                }
            }
        }
    };
    let ga0 = d * m + 1;
    let gb0 = d * m + 1 + ka;
    for (red, k, sign) in [(true, s, -1i32), (false, t, 1i32)] {
        for i in 1..k {
            let sa = if red { ra.sets(i, true) } else { ba.sets(i, false) };
            if sa.is_empty() {
                continue;
            }
            let sb = if red { rb.sets(k - i, true) } else { bb.sets(k - i, false) };
            for &ka_ in &sa {
                for &cb in &sb {
                    let mut cl = Vec::with_capacity(i * (k - i) + 4);
                    for x in bits(ka_) {
                        for y in bits(cb) {
                            cl.push(sign * (1 + x * m + y) as i32);
                        }
                    }
                    guard(ga, ka_, red, ga0, &mut cl);
                    guard(gb, cb, red, gb0, &mut cl);
                    g.clauses.push(cl);
                }
            }
        }
    }
    // side-internal goodness (A: no red K_{s-1}, no blue K_t; B: no red K_s, no blue K_{t-1}); only clauses with at
    // least one gray edge matter (an all-fixed violation cannot occur for a cover of good graphs)
    for (gen, base_var, ks, kt, rg) in [(ga, ga0, s - 1, t, &ra), (gb, gb0, s, t - 1, &rb)] {
        if gen.gray.is_empty() {
            continue;
        }
        for (k, red) in [(ks, true), (kt, false)] {
            if k < 2 {
                continue;
            }
            let sets = if red { rg.sets(k, true) } else { gen.base.sets(k, false) };
            for set in sets {
                let mut cl = Vec::new();
                guard(gen, set, red, base_var, &mut cl);
                if !cl.is_empty() {
                    g.clauses.push(cl);
                }
            }
        }
    }
    g
}

/// Glue lemma for one catalogue pair (X_A, X_B) of a unit (v10's check): with rho = the gray values (ta, tb) and
/// sigma: x(a,b) -> y(piA(a), piB(b)), every GAMMA clause is satisfied by rho or, after dropping its rho-false gray
/// literals and renaming by sigma^-1, is literally a clause of F(X_A, X_B).
pub fn unit_glue_check(
    s: usize,
    t: usize,
    gm: &Gamma,
    xa: &Graph,
    xb: &Graph,
    ma: &Member,
    mb: &Member,
) -> Result<(), String> {
    let (d, m) = (gm.d, gm.m);
    let mut pair: Vec<Clause> = pair_clauses(s, t, xa, xb);
    for c in pair.iter_mut() {
        c.sort_unstable();
    }
    let set: std::collections::HashSet<Clause> = pair.into_iter().collect();
    let mut inv_a = [0usize; 32];
    let mut inv_b = [0usize; 32];
    for a in 0..d {
        inv_a[ma.pi[a] as usize] = a;
    }
    for b in 0..m {
        inv_b[mb.pi[b] as usize] = b;
    }
    let cross = (d * m) as i32;
    for c in &gm.clauses {
        let mut sat = false;
        let mut r: Clause = Vec::with_capacity(c.len());
        for &l in c {
            let v = l.unsigned_abs() as i32;
            if v > cross {
                let gi = (v - cross - 1) as usize;
                let val = if gi < gm.ka { ma.t >> gi & 1 == 1 } else { mb.t >> (gi - gm.ka) & 1 == 1 };
                if val == (l > 0) {
                    sat = true;
                    break;
                }
            } else {
                let u = ((v - 1) as usize) / m;
                let w = ((v - 1) as usize) % m;
                let x = (1 + inv_a[u] * m + inv_b[w]) as i32;
                r.push(if l > 0 { x } else { -x });
            }
        }
        if sat {
            continue;
        }
        r.sort_unstable();
        if !set.contains(&r) {
            return Err(format!("GAMMA clause {c:?} maps to {r:?}, not a clause of F(A,B)"));
        }
    }
    Ok(())
}

/// Greedy cover builder (UNTRUSTED, like v10's): returns the cover as v10-format text.
/// Each generalisation starts at an uncovered catalogue graph X; gray edges are added one at a time, each time
/// choosing the edge whose toggled instantiations catch the most still-uncovered catalogue graphs (canonical-key
/// lookup), until `maxgray` edges or no edge adds a member. Work is split into `threads` contiguous chunks of the
/// catalogue; members are only taken from the builder's own chunk, so chunks never conflict.
pub fn build_cover(catalogue: &[Graph], maxgray: usize, threads: usize) -> String {
    use crate::canon::{canon, Key};
    use std::collections::HashMap;
    let n = catalogue.first().map_or(0, |g| g.n);
    let keyed: Vec<(Key, Vec<u8>)> = {
        let chunk = (catalogue.len() + threads - 1) / threads.max(1);
        let mut parts: Vec<Vec<(Key, Vec<u8>)>> = Vec::new();
        std::thread::scope(|sc| {
            let hs: Vec<_> = catalogue
                .chunks(chunk.max(1))
                .map(|c| sc.spawn(move || c.iter().map(canon).collect::<Vec<_>>()))
                .collect();
            for h in hs {
                parts.push(h.join().unwrap());
            }
        });
        parts.into_iter().flatten().collect()
    };
    let index: HashMap<Key, u32> = keyed.iter().enumerate().map(|(i, (k, _))| (*k, i as u32)).collect();
    let chunk = (catalogue.len() + threads - 1) / threads.max(1);
    let ranges: Vec<(usize, usize)> =
        (0..threads).map(|t| (t * chunk, ((t + 1) * chunk).min(catalogue.len()))).filter(|r| r.0 < r.1).collect();
    let results: Vec<Vec<(Gen, Vec<Member>)>> = std::thread::scope(|sc| {
        let hs: Vec<_> = ranges
            .iter()
            .map(|&(lo, hi)| {
                let (index, keyed) = (&index, &keyed);
                sc.spawn(move || {
                    let mut covered = vec![false; hi - lo];
                    let mut out = Vec::new();
                    let member_of = |y: &Graph, covered: &[bool]| -> Option<(u32, [u8; 32])> {
                        let (k, lab_y) = canon(y);
                        let &z = index.get(&k)?;
                        let zi = z as usize;
                        if zi < lo || zi >= hi || covered[zi - lo] {
                            return None;
                        }
                        // canonical position i: Y vertex lab_y[i] <-> Z vertex lab_z[i]
                        let lab_z = &keyed[zi].1;
                        let mut pi = [0u8; 32];
                        for i in 0..y.n {
                            pi[lab_z[i] as usize] = lab_y[i];
                        }
                        Some((z, pi))
                    };
                    for x in lo..hi {
                        if covered[x - lo] {
                            continue;
                        }
                        let base_full = catalogue[x].clone();
                        // v10's rule: a gray edge is accepted only if EVERY instantiation stays a catalogue graph
                        // (covered or not), so generalisations are dense and GAMMA wastes no instantiation on
                        // non-graphs; among acceptable edges take the one adding the most uncovered graphs, and require
                        // at least 2^(k-3) new ones (v10's threshold).
                        let lookup = |y: &Graph| -> Option<u32> { index.get(&canon(y).0).copied() };
                        let mut gray: Vec<(usize, usize)> = Vec::new();
                        let mut inst: Vec<u32> = vec![x as u32];
                        let mut cur = base_full.clone(); // instantiation t=0 is X itself during growth
                        let _ = &mut cur;
                        while gray.len() < maxgray {
                            let need = if gray.len() >= 3 { 1usize << (gray.len() - 3) } else { 1 };
                            let mut pick: Option<((usize, usize), usize, Vec<u32>)> = None;
                            for j in 1..n {
                                'edge: for i in 0..j {
                                    if gray.contains(&(i, j)) {
                                        continue;
                                    }
                                    let mut tmp = Vec::with_capacity(inst.len());
                                    for t in 0..inst.len() as u64 {
                                        let mut y = base_full.clone();
                                        for (b, &(u, v)) in gray.iter().enumerate() {
                                            if t >> b & 1 == 1 {
                                                y.adj[u] ^= 1 << v;
                                                y.adj[v] ^= 1 << u;
                                            }
                                        }
                                        y.adj[i] ^= 1 << j;
                                        y.adj[j] ^= 1 << i;
                                        match lookup(&y) {
                                            Some(z) => tmp.push(z),
                                            None => continue 'edge,
                                        }
                                    }
                                    let mut newc = 0;
                                    let mut seen: Vec<u32> = Vec::new();
                                    for &z in &tmp {
                                        let zi = z as usize;
                                        if zi >= lo && zi < hi && !covered[zi - lo] && !inst.contains(&z) && !seen.contains(&z) {
                                            seen.push(z);
                                            newc += 1;
                                        }
                                    }
                                    if newc >= need && pick.as_ref().map_or(true, |p| newc > p.1) {
                                        pick = Some(((i, j), newc, tmp));
                                    }
                                }
                            }
                            match pick {
                                Some((e, _, tmp)) => {
                                    gray.push(e);
                                    inst.extend(tmp);
                                }
                                None => break,
                            }
                        }
                        // final generalisation: base = X with the gray edges removed; collect members
                        let mut base = base_full.clone();
                        for &(u, v) in &gray {
                            base.adj[u] &= !(1 << v);
                            base.adj[v] &= !(1 << u);
                        }
                        let gen = Gen { base, gray: gray.clone() };
                        let mut members = Vec::new();
                        for t in 0..(1u64 << gray.len()) {
                            let y = gen.instantiate(t);
                            if let Some((z, pi)) = member_of(&y, &covered) {
                                covered[z as usize - lo] = true;
                                members.push(Member { cat: z, t, pi });
                            }
                        }
                        debug_assert!(covered[x - lo]);
                        out.push((gen, members));
                    }
                    out
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut text = String::new();
    let mut gid = 0usize;
    let mut assigns = String::new();
    for part in results {
        for (gen, members) in part {
            text.push_str(&format!("G {gid} {}", gen.gray.len()));
            for &(u, v) in &gen.gray {
                text.push_str(&format!(" {u} {v}"));
            }
            text.push_str(&format!(" {}\n", gen.base.to_g6()));
            for m in members {
                assigns.push_str(&format!("A {} {gid} {}", m.cat, m.t));
                for a in 0..n {
                    assigns.push_str(&format!(" {}", m.pi[a]));
                }
                assigns.push('\n');
            }
            gid += 1;
        }
    }
    text.push_str(&assigns);
    text
}

/// Cover builder v2: (1) grow a dense generalisation from every `stride`-th catalogue graph in parallel (v10's rule:
/// every instantiation must be a catalogue graph; gray edges chosen to maximise distinct instantiations), then
/// (2) lazy-greedy set cover over those candidates (classic ln-n approximation). UNTRUSTED like every cover.
pub fn build_cover_setcover(catalogue: &[Graph], maxgray: usize, threads: usize, stride: usize) -> String {
    use crate::canon::{canon, Key};
    use std::collections::{BinaryHeap, HashMap};
    let n = catalogue.first().map_or(0, |g| g.n);
    let ncat = catalogue.len();
    let par_map = |f: &(dyn Fn(usize) -> Option<(Gen, Vec<u32>)> + Sync), idx: Vec<usize>| -> Vec<(Gen, Vec<u32>)> {
        let next = std::sync::atomic::AtomicUsize::new(0);
        let out = std::sync::Mutex::new(Vec::new());
        std::thread::scope(|sc| {
            for _ in 0..threads.max(1) {
                sc.spawn(|| loop {
                    let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if k >= idx.len() {
                        break;
                    }
                    if let Some(r) = f(idx[k]) {
                        out.lock().unwrap().push(r);
                    }
                });
            }
        });
        out.into_inner().unwrap()
    };
    let keys: Vec<(Key, Vec<u8>)> = {
        let next = std::sync::atomic::AtomicUsize::new(0);
        let slots: Vec<std::sync::Mutex<Option<(Key, Vec<u8>)>>> = (0..ncat).map(|_| std::sync::Mutex::new(None)).collect();
        std::thread::scope(|sc| {
            for _ in 0..threads.max(1) {
                sc.spawn(|| loop {
                    let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if k >= ncat {
                        break;
                    }
                    *slots[k].lock().unwrap() = Some(canon(&catalogue[k]));
                });
            }
        });
        slots.into_iter().map(|m| m.into_inner().unwrap().unwrap()).collect()
    };
    let index: HashMap<Key, u32> = keys.iter().enumerate().map(|(i, (k, _))| (*k, i as u32)).collect();
    let grow = |x: usize| -> Option<(Gen, Vec<u32>)> {
        let base_full = &catalogue[x];
        let mut gray: Vec<(usize, usize)> = Vec::new();
        let mut inst: Vec<u32> = vec![x as u32]; // inst[t] for t over gray toggles relative to X
        while gray.len() < maxgray {
            let need = if gray.len() >= 3 { 1usize << (gray.len() - 3) } else { 1 };
            let mut pick: Option<((usize, usize), usize, Vec<u32>)> = None;
            for j in 1..n {
                'edge: for i in 0..j {
                    if gray.contains(&(i, j)) {
                        continue;
                    }
                    let mut tmp = Vec::with_capacity(inst.len());
                    for t in 0..inst.len() as u64 {
                        let mut y = base_full.clone();
                        for (b, &(u, v)) in gray.iter().enumerate() {
                            if t >> b & 1 == 1 {
                                y.adj[u] ^= 1 << v;
                                y.adj[v] ^= 1 << u;
                            }
                        }
                        y.adj[i] ^= 1 << j;
                        y.adj[j] ^= 1 << i;
                        match index.get(&canon(&y).0) {
                            Some(&z) => tmp.push(z),
                            None => continue 'edge,
                        }
                    }
                    let mut newc = 0;
                    let mut seen: Vec<u32> = Vec::new();
                    for &z in &tmp {
                        if !inst.contains(&z) && !seen.contains(&z) {
                            seen.push(z);
                            newc += 1;
                        }
                    }
                    if newc >= need && pick.as_ref().map_or(true, |p| newc > p.1) {
                        pick = Some(((i, j), newc, tmp));
                    }
                }
            }
            match pick {
                Some((e, _, tmp)) => {
                    gray.push(e);
                    inst.extend(tmp);
                }
                None => break,
            }
        }
        // normalise: base = X with gray edges removed; instantiation t sets gray edge b present iff bit b
        let mut base = base_full.clone();
        for &(u, v) in &gray {
            base.adj[u] &= !(1 << v);
            base.adj[v] &= !(1 << u);
        }
        let gen = Gen { base, gray };
        let mut members = Vec::with_capacity(1 << gen.gray.len());
        for t in 0..(1u64 << gen.gray.len()) {
            members.push(*index.get(&canon(&gen.instantiate(t)).0)?);
        }
        members.sort_unstable();
        members.dedup();
        Some((gen, members))
    };
    let seeds: Vec<usize> = (0..ncat).step_by(stride.max(1)).collect();
    let mut cands = par_map(&grow, seeds);
    // every graph must be coverable: add singleton generalisations for graphs no candidate reaches
    let mut reach = vec![false; ncat];
    for (_, m) in &cands {
        for &z in m {
            reach[z as usize] = true;
        }
    }
    for x in 0..ncat {
        if !reach[x] {
            cands.push((Gen { base: catalogue[x].clone(), gray: vec![] }, vec![x as u32]));
        }
    }
    // lazy greedy set cover
    let mut covered = vec![false; ncat];
    let mut heap: BinaryHeap<(usize, usize)> = cands.iter().enumerate().map(|(i, (_, m))| (m.len(), i)).collect();
    let mut chosen: Vec<usize> = Vec::new();
    let mut left = ncat;
    while left > 0 {
        let (est, i) = heap.pop().expect("cover candidates exhausted");
        let real = cands[i].1.iter().filter(|&&z| !covered[z as usize]).count();
        if real == 0 {
            continue;
        }
        if real < est {
            heap.push((real, i));
            continue;
        }
        for &z in &cands[i].1 {
            if !covered[z as usize] {
                covered[z as usize] = true;
                left -= 1;
            }
        }
        chosen.push(i);
    }
    // emit in v10 format: members assigned to the first chosen generalisation containing them
    let mut owner = vec![usize::MAX; ncat];
    let mut text = String::new();
    let mut assigns = String::new();
    for (gid, &ci) in chosen.iter().enumerate() {
        let gen = &cands[ci].0;
        text.push_str(&format!("G {gid} {}", gen.gray.len()));
        for &(u, v) in &gen.gray {
            text.push_str(&format!(" {u} {v}"));
        }
        text.push_str(&format!(" {}\n", gen.base.to_g6()));
        for t in 0..(1u64 << gen.gray.len()) {
            let y = gen.instantiate(t);
            let (k, lab_y) = canon(&y);
            let z = index[&k] as usize;
            if owner[z] != usize::MAX {
                continue;
            }
            owner[z] = gid;
            let lab_z = &keys[z].1;
            let mut pi = [0u8; 32];
            for i in 0..n {
                pi[lab_z[i] as usize] = lab_y[i];
            }
            assigns.push_str(&format!("A {z} {gid} {t}"));
            for a in 0..n {
                assigns.push_str(&format!(" {}", pi[a]));
            }
            assigns.push('\n');
        }
    }
    text.push_str(&assigns);
    text
}

impl Gen {
    /// Colour of the pair (u, v) in the generalisation: 0 blue (fixed non-edge), 1 red (base edge), 2 gray.
    pub fn pair_colour(&self, u: usize, v: usize) -> u8 {
        if self.base.has_edge(u, v) {
            1
        } else if self.gray_index(u, v).is_some() {
            2
        } else {
            0
        }
    }

    /// Every vertex permutation that preserves the base graph and the gray set (the unit's symmetry group on this
    /// side), as images `perm[u]`, at most `cap` of them. Backtracking with pair-colour consistency: fine for n <= 16.
    pub fn stabiliser(&self, cap: usize) -> Vec<Vec<u8>> {
        let n = self.base.n;
        let mut col = vec![vec![0u8; n]; n];
        let mut inv = vec![(0u32, 0u32); n]; // (red degree, gray degree)
        for u in 0..n {
            for v in 0..n {
                if u != v {
                    col[u][v] = self.pair_colour(u, v);
                    match col[u][v] {
                        1 => inv[u].0 += 1,
                        2 => inv[u].1 += 1,
                        _ => {}
                    }
                }
            }
        }
        let mut out = Vec::new();
        let mut perm = vec![u8::MAX; n];
        let mut used = vec![false; n];
        fn rec(
            i: usize,
            n: usize,
            col: &[Vec<u8>],
            inv: &[(u32, u32)],
            perm: &mut Vec<u8>,
            used: &mut Vec<bool>,
            out: &mut Vec<Vec<u8>>,
            cap: usize,
        ) {
            if out.len() >= cap {
                return;
            }
            if i == n {
                out.push(perm.clone());
                return;
            }
            for w in 0..n {
                if used[w] || inv[w] != inv[i] {
                    continue;
                }
                if (0..i).all(|j| col[i][j] == col[w][perm[j] as usize]) {
                    perm[i] = w as u8;
                    used[w] = true;
                    rec(i + 1, n, col, inv, perm, used, out, cap);
                    used[w] = false;
                    perm[i] = u8::MAX;
                }
            }
        }
        rec(0, n, &col, &inv, &mut perm, &mut used, &mut out, cap);
        out
    }
}

/// Degree axioms for a unit (UNCERTIFIED experiment switch `--degree-axioms`, unit mode): every vertex of K_N has red
/// degree in [lo, hi] (R(s-1,t) and R(s,t-1) counting). For an A vertex u: 1 (the root v) + fixed red edges in ga +
/// red gray-A edges at u + red cross edges; for a B vertex w: fixed red edges in gb + red gray-B edges at w + red cross
/// edges. Encoded with `card_window` (auxiliary variables from `next`). These clauses are implied by the full K_N
/// formula but NOT derived here, so a run with them is a measurement, never a certified result (build() refuses
/// --check-every > 0 with this switch).
pub fn unit_degree_axioms(gm: &Gamma, ga: &Gen, gb: &Gen, lo: usize, hi: usize, next: &mut i32) -> Vec<Clause> {
    let (d, m) = (gm.d, gm.m);
    let mut out = Vec::new();
    for u in 0..d {
        let mut lits: Vec<i32> = (0..m).map(|w| (1 + u * m + w) as i32).collect();
        for (i, &(x, y)) in ga.gray.iter().enumerate() {
            if x == u || y == u {
                lits.push(gm.gray_a(i));
            }
        }
        let base = 1 + ga.base.adj[u].count_ones() as isize;
        crate::encode::card_window(&lits, lo as isize - base, hi as isize - base, next, &mut out);
    }
    for w in 0..m {
        let mut lits: Vec<i32> = (0..d).map(|u| (1 + u * m + w) as i32).collect();
        for (i, &(x, y)) in gb.gray.iter().enumerate() {
            if x == w || y == w {
                lits.push(gm.gray_b(i));
            }
        }
        let base = gb.base.adj[w].count_ones() as isize;
        crate::encode::card_window(&lits, lo as isize - base, hi as isize - base, next, &mut out);
    }
    out
}
