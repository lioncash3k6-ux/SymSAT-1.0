//! Idea 3, stage 1: flag-algebra (symmetric sum-of-squares) refutations of Ramsey colourings, with exact finite-N
//! coefficients and an exactly checked certificate.
//!
//! For a 2-colouring G of K_N and a colouring class H of K_K, p_H(G) is the probability that a uniform K-subset of G
//! induces H. Fix a type σ (a colouring of m labelled vertices, m + 2ℓ = K) and its flags F (colourings of m + ℓ
//! vertices whose first m vertices induce σ exactly, up to relabelling the other ℓ). For an ordered m-tuple θ of
//! distinct vertices of G let v_θ[F] be the fraction of ℓ-subsets A of the other vertices with θ ∪ A ≅ F (zero when θ
//! does not induce σ). E_θ[v_θ v_θᵀ] is positive semidefinite, and it equals Σ_H p_H(G) C_H^σ EXACTLY, with
//!   C_H^σ[F,F'] = Σ_j P_N(j) · Pr[a uniform structure (θ, A, B) inside H with |A ∩ B| = j has θ∪A ≅ F, θ∪B ≅ F'],
//! where P_N(j) = C(ℓ,j) C(N-m-ℓ, ℓ-j) / C(N-m, ℓ) is the chance that two independent ℓ-subsets of the N - m other
//! vertices meet in j vertices (given j, θ ∪ A ∪ B is a uniform (K - j)-subset, and averaging down to it from a uniform
//! K-subset is exact). So if a good colouring existed, p (a probability vector on the admissible classes, those with
//! no red K_s and no blue K_t) would make every Σ_H p_H C_H^σ PSD.
//!
//! CSDP searches for PSD Y_σ with Σ_σ ⟨C_H^σ, Y_σ⟩ ≤ -λ for every admissible H and λ > 0, which contradicts that:
//! Σ_H p_H Σ_σ ⟨C_H^σ, Y_σ⟩ = Σ_σ ⟨E_θ[v_θ v_θᵀ], Y_σ⟩ ≥ 0. The certificate is re-checked exactly: each Y_σ is replaced
//! by L Lᵀ with L its Cholesky factor rounded to integers (PSD by construction), the coefficients are scaled to
//! integers, and every Σ_σ ⟨C_H^σ, L Lᵀ⟩ is summed in checked i128 arithmetic. CSDP is untrusted; only that check counts.

use std::collections::{HashMap, HashSet};

/// A complete 2-colouring of K_k (k ≤ 8): bit v of red[u] says edge uv is red; every other pair is blue.
#[derive(Clone, Copy, Debug)]
pub struct Col {
    k: usize,
    red: [u8; 8],
}

impl Col {
    fn empty(k: usize) -> Col {
        Col { k, red: [0; 8] }
    }
    fn is_red(&self, u: usize, v: usize) -> bool {
        self.red[u] >> v & 1 == 1
    }
    fn set_red(&mut self, u: usize, v: usize) {
        self.red[u] |= 1 << v;
        self.red[v] |= 1 << u;
    }
    /// Edge colours in a fixed order (pairs u < v by v, then u): a labelled key.
    fn bits(&self) -> u64 {
        let mut b = 0u64;
        let mut i = 0;
        for v in 1..self.k {
            for u in 0..v {
                if self.is_red(u, v) {
                    b |= 1 << i;
                }
                i += 1;
            }
        }
        b
    }
    /// Isomorphism-class key (pattern.rs canonical form; blue = complement).
    fn canon(&self) -> Vec<u64> {
        let (mut r, mut b) = ([0u32; 32], [0u32; 32]);
        let all = if self.k == 0 { 0 } else { (1u32 << self.k) - 1 };
        for v in 0..self.k {
            r[v] = self.red[v] as u32;
            b[v] = all & !(self.red[v] as u32) & !(1 << v);
        }
        crate::pattern::canon_key(self.k, &r, &b)
    }
    fn induced(&self, vs: &[usize]) -> Col {
        let mut c = Col::empty(vs.len());
        for j in 1..vs.len() {
            for i in 0..j {
                if self.is_red(vs[i], vs[j]) {
                    c.set_red(i, j);
                }
            }
        }
        c
    }
    /// Does it contain a red K_size (`red`) or a blue K_size?
    fn has_clique(&self, size: usize, red: bool) -> bool {
        fn rec(adj: &[u8; 8], size: usize, cand: u8) -> bool {
            if size == 0 {
                return true;
            }
            if (cand.count_ones() as usize) < size {
                return false;
            }
            let mut c = cand;
            while c != 0 {
                let v = c.trailing_zeros() as usize;
                c &= c - 1;
                if rec(adj, size - 1, c & adj[v]) {
                    return true;
                }
            }
            false
        }
        let all: u8 = if self.k >= 8 { 0xff } else { (1u8 << self.k) - 1 };
        let mut adj = [0u8; 8];
        for v in 0..self.k {
            adj[v] = if red { self.red[v] } else { all & !self.red[v] & !(1 << v) };
        }
        rec(&adj, size, all)
    }
    fn admissible(&self, s: usize, t: usize) -> bool {
        !self.has_clique(s, true) && !self.has_clique(t, false)
    }
}

/// One representative of every colouring class of K_k, by extension from K_(k-1) and canonical deduplication.
pub fn classes(k: usize) -> Vec<Col> {
    if k == 0 {
        return vec![Col::empty(0)];
    }
    let mut cur = vec![Col::empty(1)];
    for kk in 2..=k {
        let mut seen = HashSet::new();
        let mut next = Vec::new();
        for g in &cur {
            for mask in 0..(1u32 << (kk - 1)) {
                let mut h = Col { k: kk, red: g.red };
                for u in 0..kk - 1 {
                    if mask >> u & 1 == 1 {
                        h.set_red(u, kk - 1);
                    }
                }
                if seen.insert(h.canon()) {
                    next.push(h);
                }
            }
        }
        cur = next;
    }
    cur
}

/// Number of maps from a q-set onto a u-set.
fn surjections(q: usize, u: usize) -> i128 {
    if q == 0 {
        return (u == 0) as i128;
    }
    (0..=u).map(|i| (if i % 2 == 0 { 1 } else { -1 }) * binom(u as i64, i as i64) * ((u - i) as i128).pow(q as u32)).sum()
}

fn binom(n: i64, k: i64) -> i128 {
    if k < 0 || n < 0 || k > n {
        return 0;
    }
    let mut r: i128 = 1;
    for i in 0..k {
        r = r * (n - i) as i128 / (i + 1) as i128;
    }
    r
}

fn gcd(a: i128, b: i128) -> i128 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

fn permutations(l: usize) -> Vec<Vec<usize>> {
    if l == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for p in permutations(l - 1) {
        for pos in 0..=p.len() {
            let mut q = p.clone();
            q.insert(pos, l - 1);
            out.push(q);
        }
    }
    out
}

/// A type σ on m labelled vertices and its flags on m + ℓ vertices.
pub struct Basis {
    m: usize,
    l: usize,
    sigma: Col,
    perms: Vec<Vec<usize>>,
    /// flag key (min over relabellings of the ℓ unlabelled vertices) -> index
    index: HashMap<u64, usize>,
}

impl Basis {
    /// All flags extending σ, or only the admissible ones when `filter` = Some((s, t)).
    pub fn new(sigma: Col, l: usize, filter: Option<(usize, usize)>) -> Basis {
        let m = sigma.k;
        let perms = permutations(l);
        let mut b = Basis { m, l, sigma, perms, index: HashMap::new() };
        let free: Vec<(usize, usize)> = (m..m + l).flat_map(|v| (0..v).map(move |u| (u, v))).collect();
        for mask in 0..(1u64 << free.len()) {
            let mut c = Col { k: m + l, red: sigma.red };
            for (i, &(u, v)) in free.iter().enumerate() {
                if mask >> i & 1 == 1 {
                    c.set_red(u, v);
                }
            }
            if filter.is_some_and(|(s, t)| !c.admissible(s, t)) {
                continue;
            }
            let key = b.key(&c);
            let n = b.index.len();
            b.index.entry(key).or_insert(n);
        }
        b
    }
    fn len(&self) -> usize {
        self.index.len()
    }
    fn key(&self, c: &Col) -> u64 {
        let m = self.m;
        self.perms
            .iter()
            .map(|p| {
                let order: Vec<usize> = (0..m).chain(p.iter().map(|&i| m + i)).collect();
                c.induced(&order).bits()
            })
            .min()
            .unwrap()
    }
    /// The flag index of θ ∪ A in g (θ already known to induce σ), if it is in the basis.
    fn flag_of(&self, g: &Col, theta: &[usize], a: &[usize]) -> Option<usize> {
        let order: Vec<usize> = theta.iter().chain(a.iter()).copied().collect();
        self.index.get(&self.key(&g.induced(&order))).copied()
    }
    fn matches(&self, g: &Col, theta: &[usize]) -> bool {
        (1..self.m).all(|j| (0..j).all(|i| g.is_red(theta[i], theta[j]) == self.sigma.is_red(i, j)))
    }
}

fn ordered_tuples(k: usize, m: usize) -> Vec<Vec<usize>> {
    let mut out = vec![vec![]];
    for _ in 0..m {
        let mut next = Vec::new();
        for t in &out {
            for v in 0..k {
                if !t.contains(&v) {
                    let mut u = t.clone();
                    u.push(v);
                    next.push(u);
                }
            }
        }
        out = next;
    }
    out
}

fn subsets(items: &[usize], l: usize) -> Vec<Vec<usize>> {
    if l == 0 {
        return vec![vec![]];
    }
    if items.len() < l {
        return vec![];
    }
    let mut out = subsets(&items[1..], l);
    for mut s in subsets(&items[1..], l - 1) {
        s.insert(0, items[0]);
        out.push(s);
    }
    out
}


/// One PSD block of the SDP: the flags of a type, times a polynomial g(r) = Σ c_q r^q in the red degree r of the
/// type's single vertex (localising block). E_θ[g(r_θ) v_θ v_θᵀ] is PSD whenever g(r_v) ≥ 0 at every vertex of every
/// good colouring. Plain type blocks have g = 1.
pub struct Block {
    basis: Basis,
    /// (q, c_q); q > 0 only for one-vertex types
    poly: Vec<(usize, i128)>,
    name: String,
}

/// Realisation counts for class H (K vertices), basis b and q sampled vertices, binned by union size s = |A ∪ B ∪ U|.
/// A realisation is an ordered m-tuple θ inducing σ, ordered ℓ-subsets A, B of the other K - m vertices, and q
/// vertices u_1..u_q of those (independent, repeats allowed) that are red neighbours of θ[0]; it is counted under
/// (F, F') when θ ∪ A ≅ F and θ ∪ B ≅ F'.
///
/// Exactness: drawing θ, A, B, u_1..u_q uniformly and independently in a colouring G of K_N, a realisation whose union
/// has s vertices besides θ arises with probability C(N-m, s) c / (C(N-m,ℓ)² (N-m)^q) for its overlap shape (c = the
/// number of realisations of that shape on a fixed s-set), and the same shape occurs (K)_m C(K-m, s) c times among the
/// realisations inside a K-vertex class. So E_G[f] = Σ_H p_H(G) Σ_(realisations in H) f · W(s) with
/// W(s) = C(N-m, s) / (C(N-m,ℓ)² (N-m)^q (K)_m C(K-m, s)), which depends on s only ([`weight`]).
fn counts(h: &Col, b: &Basis, q: usize) -> Vec<HashMap<(usize, usize), i128>> {
    let mut cnt = vec![HashMap::new(); h.k + 1];
    for theta in ordered_tuples(h.k, b.m) {
        if !b.matches(h, &theta) {
            continue;
        }
        let rest: Vec<usize> = (0..h.k).filter(|v| !theta.contains(v)).collect();
        let mut flags: Vec<(u8, usize)> = Vec::new();
        for a in subsets(&rest, b.l) {
            if let Some(f) = b.flag_of(h, &theta, &a) {
                flags.push((a.iter().fold(0u8, |m, &v| m | 1 << v), f));
            }
        }
        // the q sampled red neighbours of θ[0] among the other vertices, as vertex masks (with multiplicity)
        let reds: Vec<usize> = if q > 0 { rest.iter().copied().filter(|&u| h.is_red(theta[0], u)).collect() } else { vec![] };
        if b.l == 0 {
            // scalar block (A = B = empty): only the union size of the q-tuple matters, so count tuples in closed form:
            // C(ρ, u) sets of u red neighbours, each the union of surj(q, u) ordered q-tuples
            if let Some(&(_, f)) = flags.first() {
                for u in 0..=q.min(reds.len()) {
                    *cnt[u].entry((f, f)).or_insert(0) += binom(reds.len() as i64, u as i64) * surjections(q, u);
                }
            }
            continue;
        }
        let mut us: Vec<u8> = vec![0];
        for _ in 0..q {
            us = us.iter().flat_map(|&m| reds.iter().map(move |&u| m | 1 << u)).collect();
        }
        for &(ma, fa) in &flags {
            for &(mb, fb) in &flags {
                for &mu in &us {
                    *cnt[(ma | mb | mu).count_ones() as usize].entry((fa, fb)).or_insert(0) += 1;
                }
            }
        }
    }
    cnt
}

/// W(s) as (numerator, denominator): C(N-m, s) / (C(N-m,ℓ)² (N-m)^q (K)_m C(K-m, s)); with g's factor r^q =
/// (N-m)^q E_u[...] (m = 1) the (N-m)^q cancels, so callers pass `scaled` to drop it.
fn weight(n: usize, k: usize, m: usize, l: usize, q: usize, s: usize, scaled: bool) -> (i128, i128) {
    let (n, k, m, l, s) = (n as i64, k as i64, m as i64, l as i64, s as i64);
    let tuples: i128 = (0..m).map(|i| (k - i) as i128).product();
    let nq: i128 = if scaled { 1 } else { ((n - m) as i128).pow(q as u32) };
    (binom(n - m, s), binom(n - m, l) * binom(n - m, l) * nq * tuples * binom(k - m, s))
}

/// Common denominator of every weight W(s) used by `blocks`.
fn weights_lcm(blocks: &[&Block], k: usize, n: usize) -> Result<i128, String> {
    let mut lcm: i128 = 1;
    for b in blocks {
        for &(q, _) in &b.poly {
            for s in 0..=k {
                let (wn, wd) = weight(n, k, b.basis.m, b.basis.l, q, s, true);
                if wn != 0 && wd != 0 {
                    lcm = (lcm / gcd(lcm, wd)).checked_mul(wd).ok_or("lcm overflow")?;
                }
            }
        }
    }
    Ok(lcm)
}

/// Exact coefficients of a block for one class, times `lcm` (a common denominator of the weights): sparse, keyed
/// (F, F'), symmetric. Everything downstream (SDP input, exact check) starts from these integers.
fn coeff_int(cnt: &[Vec<HashMap<(usize, usize), i128>>], blk: &Block, k: usize, n: usize, lcm: i128) -> Result<HashMap<(usize, usize), i128>, String> {
    let b = &blk.basis;
    let mut c: HashMap<(usize, usize), i128> = HashMap::new();
    for (pi, &(q, cq)) in blk.poly.iter().enumerate() {
        for (s, map) in cnt[pi].iter().enumerate() {
            let (wn, wd) = weight(n, k, b.m, b.l, q, s, true);
            if wn == 0 || map.is_empty() {
                continue;
            }
            let w = (lcm / wd).checked_mul(wn).and_then(|x| x.checked_mul(cq)).ok_or("weight overflow")?;
            for (&fg, &x) in map {
                let e = c.entry(fg).or_insert(0);
                *e = w.checked_mul(x).and_then(|v| e.checked_add(v)).ok_or("coefficient overflow")?;
            }
        }
    }
    c.retain(|_, v| *v != 0);
    Ok(c)
}

/// Float coefficient matrix of a block for one class (dense, nf x nf), from the exact integers.
#[cfg(test)]
fn coeff_f64(cnt: &[Vec<HashMap<(usize, usize), i128>>], blk: &Block, k: usize, n: usize) -> Vec<f64> {
    let lcm = weights_lcm(&[blk], k, n).unwrap();
    let nf = blk.basis.len();
    let mut c = vec![0.0; nf * nf];
    for ((f, g), v) in coeff_int(cnt, blk, k, n, lcm).unwrap() {
        c[f * nf + g] = v as f64 / lcm as f64;
    }
    c
}

fn block_counts(h: &Col, blk: &Block) -> Vec<Vec<HashMap<(usize, usize), i128>>> {
    blk.poly.iter().map(|&(q, _)| counts(h, &blk.basis, q)).collect()
}

/// Neighbourhood-catalogue constraints (`--nbhd LO,HI`). In a good (s,t) colouring the red neighbourhood N(v) of every
/// vertex is an (s-1,t)-good graph on r_v vertices, so with the McKay catalogue C_j of those graphs (TRUSTED input,
/// exactly as in the gluing route) and r_v in [LO,HI], the vector of rooted subgraph counts
///   E_v[ cnt_{H'}(N(v)) ],  cnt_{H'}(G) = #{ ℓ-subsets S of V(G) : G[S] ≅ H' },  H' over the (s-1,t)-good K_ℓ classes,
/// is a convex combination Σ_G λ_G cnt_{H'}(G) over G ∈ C_LO ∪ .. ∪ C_HI, λ ≥ 0, Σ λ = 1 (λ_G = fraction of vertices
/// whose neighbourhood is G). Exact finite-N identity: Σ_v cnt_{H'}(N(v)) = C(N,ℓ+1)/C(K,ℓ+1) Σ_H p_H pairs(H',H),
/// where pairs(H',H) = #{(v, S) in class H : S ⊆ N_H(v), |S| = ℓ, H[S] ≅ H'} (count the (v,S) pairs inside each
/// (ℓ+1)-subset of K_N and average over the K-subsets containing it). The SDP gets one free multiplier μ_{H'} per
/// row and one constraint per catalogue graph G; the certificate condition becomes α + β (+ γ) > 0, see `exact_check`.
/// With `--handshake` (odd N) the row Σ_{|G| even} λ_G ≥ 1/N is added (some vertex has even red degree).
struct Nbhd {
    lo: usize,
    hi: usize,
    /// per row: (ℓ, name)
    rows: Vec<(usize, String)>,
    /// a[r][H] = C(N,ℓ+1) * pairs(H', H)
    a: Vec<Vec<i128>>,
    /// c[r][G] = N * C(K,ℓ+1) * cnt_{H'}(G)
    c: Vec<Vec<i128>>,
    /// |G| even
    even: Vec<bool>,
    handshake: bool,
}

fn col_of_subset(g: &crate::graph::Graph, vs: &[usize]) -> Col {
    let mut c = Col::empty(vs.len());
    for j in 1..vs.len() {
        for i in 0..j {
            if g.has_edge(vs[i], vs[j]) {
                c.set_red(i, j);
            }
        }
    }
    c
}

fn build_nbhd(s: usize, t: usize, n: usize, k: usize, hs: &[Col], lo: usize, hi: usize, lmax: usize, handshake: bool, dir: &std::path::Path) -> Result<Nbhd, String> {
    let mut graphs: Vec<crate::graph::Graph> = Vec::new();
    for j in lo..=hi {
        if j == 0 {
            graphs.push(crate::graph::Graph::empty(0)); // the only graph on no vertices
            continue;
        }
        let lv = crate::catalog::load(dir, s - 1, t, j)?;
        if lv.count_ok() == Some(false) {
            return Err(format!("catalogue r{}{}/n{j}: {} graphs, McKay count {:?}", s - 1, t, lv.graphs.len(), lv.mckay));
        }
        graphs.extend(lv.graphs);
    }
    let mut rows = Vec::new();
    let mut a: Vec<Vec<i128>> = Vec::new();
    let mut c: Vec<Vec<i128>> = Vec::new();
    for l in 1..=lmax.min(k - 1) {
        let types: Vec<Col> = classes(l).into_iter().filter(|h| h.admissible(s - 1, t)).collect();
        let mut index: HashMap<Vec<u64>, usize> = HashMap::new();
        let base = rows.len();
        for (i, h) in types.iter().enumerate() {
            index.insert(h.canon(), base + i);
            rows.push((l, format!("l={l} type#{i} red={}", (1..l).flat_map(|v| (0..v).map(move |u| (u, v))).filter(|&(u, v)| h.is_red(u, v)).count())));
            a.push(vec![0; hs.len()]);
            c.push(vec![0; graphs.len()]);
        }
        let cn = binom(n as i64, l as i64 + 1);
        let ck = binom(k as i64, l as i64 + 1);
        for (hi_, h) in hs.iter().enumerate() {
            for v in 0..k {
                let nb: Vec<usize> = (0..k).filter(|&u| u != v && h.is_red(v, u)).collect();
                for sset in subsets(&nb, l) {
                    let key = h.induced(&sset).canon();
                    let r = *index.get(&key).ok_or("rooted subgraph not an (s-1,t)-good class")?;
                    a[r][hi_] += cn;
                }
            }
        }
        for (gi, g) in graphs.iter().enumerate() {
            let all: Vec<usize> = (0..g.n).collect();
            for sset in subsets(&all, l) {
                let key = col_of_subset(g, &sset).canon();
                let r = *index.get(&key).ok_or_else(|| format!("catalogue graph has a {l}-subgraph that is not (s-1,t)-good"))?;
                c[r][gi] += n as i128 * ck;
            }
        }
    }
    let even = graphs.iter().map(|g| g.n % 2 == 0).collect();
    Ok(Nbhd { lo, hi, rows, a, c, even, handshake })
}

pub fn cmd_flag(a: &crate::Args) {
    let (s, t, n, k) = (a.get("s", 3usize), a.get("t", 3usize), a.get("n", 6usize), a.get("k", 3usize));
    if !(2..=8).contains(&k) {
        crate::die("--k must be in 2..=8");
    }
    let csdp = a.kv.get("csdp").cloned().unwrap_or_else(|| "csdp".into());
    // --degree auto|LO,HI: every vertex's red degree r lies in [LO, HI] (auto: from R(s-1,t) and R(s,t-1)), and is an
    // integer; adds localising blocks for (r-LO), (HI-r), (r-LO)(HI-r) and (r-j)(r-j-1), j = LO-1..HI
    // only `auto` bounds follow from theorems (R(s-1,t), R(s,t-1)); explicit bounds are assumptions, and a certificate
    // under them says nothing about R(s,t)
    let degree_assumed = a.kv.get("degree").is_some_and(|d| d != "auto");
    let degree: Option<(i128, i128)> = a.kv.get("degree").map(|d| {
        if d == "auto" {
            let hi = crate::full::known_ramsey(s - 1, t).unwrap_or_else(|| crate::die("--degree auto: R(s-1,t) unknown")) as i128 - 1;
            let blue_max = crate::full::known_ramsey(s, t - 1).unwrap_or_else(|| crate::die("--degree auto: R(s,t-1) unknown")) as i128 - 1;
            ((n as i128 - 1 - blue_max).max(0), hi)
        } else {
            let v: Vec<i128> = d.split(',').filter_map(|x| x.trim().parse().ok()).collect();
            if v.len() != 2 {
                crate::die("--degree LO,HI or --degree auto");
            }
            (v[0], v[1])
        }
    });
    // --nbhd LO,HI: every vertex's red neighbourhood is a catalogue (s-1,t)-good graph on LO..HI vertices (see `Nbhd`);
    // --nbhd-l L caps the rooted subgraph size (default K-1); --handshake adds "some vertex has even red degree" (odd N)
    let nbhd_range: Option<(usize, usize)> = a.kv.get("nbhd").map(|d| {
        let v: Vec<usize> = d.split(',').filter_map(|x| x.trim().parse().ok()).collect();
        if v.len() != 2 || v[0] > v[1] {
            crate::die("--nbhd LO,HI");
        }
        (v[0], v[1])
    });
    let tag = degree.map_or(String::new(), |(lo, hi)| format!("_deg{lo}-{hi}")) + &nbhd_range.map_or(String::new(), |(lo, hi)| format!("_nbhd{lo}-{hi}"));
    let out = std::path::PathBuf::from(a.kv.get("out").cloned().unwrap_or_else(|| format!("results/flag/R{s}{t}_N{n}_K{k}{tag}")));
    std::fs::create_dir_all(&out).unwrap_or_else(|e| crate::die(&e.to_string()));
    let t0 = std::time::Instant::now();
    let hs: Vec<Col> = classes(k).into_iter().filter(|h| h.admissible(s, t)).collect();
    let mut blocks: Vec<Block> = Vec::new();
    for l in 1..=k / 2 {
        let m = k - 2 * l;
        for sigma in classes(m) {
            if sigma.admissible(s, t) {
                let basis = Basis::new(sigma, l, Some((s, t)));
                if basis.len() > 0 {
                    blocks.push(Block { basis, poly: vec![(0, 1)], name: format!("type m={m} l={l}") });
                }
            }
        }
    }
    if let Some((lo, hi)) = degree {
        let mut polys: Vec<(String, Vec<(usize, i128)>)> = vec![
            (format!("r-{lo}"), vec![(0, -lo), (1, 1)]),
            (format!("{hi}-r"), vec![(0, hi), (1, -1)]),
            (format!("(r-{lo})({hi}-r)"), vec![(0, -lo * hi), (1, lo + hi), (2, -1)]),
        ];
        for j in (lo - 1).max(0)..=hi {
            polys.push((format!("(r-{j})(r-{})", j + 1), vec![(0, j * (j + 1)), (1, -(2 * j + 1)), (2, 1)]));
        }
        for (name, poly) in polys {
            let qmax = poly.iter().map(|p| p.0).max().unwrap_or(0);
            for l in 0..=k {
                if 1 + 2 * l + qmax > k {
                    break;
                }
                let basis = Basis::new(Col::empty(1), l, Some((s, t)));
                blocks.push(Block { basis, poly: poly.clone(), name: format!("{name} l={l}") });
            }
        }
    }
    // --parity (odd N): with red degrees integers in [lo, hi] and hi - lo < K, the Lagrange polynomials
    // P_j(r) / D_j = 1[r = j] give the exact fraction x_j = E_v[1[r_v = j]] of vertices of red degree j. Valid scalar
    // blocks: x_j >= 0 for each j, and (handshake lemma: an odd number of vertices cannot all have odd degree)
    // Σ_{j even} x_j >= 1/N, i.e. E_v[N Σ_{j even} 1[r_v = j] - 1] >= 0. Integer coefficients via positive scaling.
    // --exclude-degree j,..: one case of a case split, "no vertex has red degree j" (x_j = 0); the complementary case
    // ("some vertex has red degree j") must be refuted elsewhere, e.g. by the gluing stage d = j
    let excluded: Vec<i128> = a.kv.get("exclude-degree").map(|v| v.split(',').filter_map(|x| x.trim().parse().ok()).collect()).unwrap_or_default();
    if a.has("parity") || !excluded.is_empty() {
        let (lo, hi) = degree.unwrap_or_else(|| crate::die("--parity and --exclude-degree need --degree"));
        if a.has("parity") && n % 2 == 0 {
            crate::die("--parity needs odd N (then some vertex has even red degree)");
        }
        if (hi - lo + 1) as usize > k {
            crate::die("--parity: the degree range needs at most K points (moments up to K-1 pin the distribution)");
        }
        let lagrange = |j: i128| -> (Vec<i128>, i128) {
            let (mut p, mut d) = (vec![1i128], 1i128);
            for i in lo..=hi {
                if i == j {
                    continue;
                }
                let mut next = vec![0i128; p.len() + 1];
                for (q, &c) in p.iter().enumerate() {
                    next[q + 1] += c;
                    next[q] -= i * c;
                }
                p = next;
                d *= j - i;
            }
            (p, d)
        };
        let as_poly = |c: &[i128]| -> Vec<(usize, i128)> { c.iter().enumerate().filter(|(_, &x)| x != 0).map(|(q, &x)| (q, x)).collect() };
        let scalar = || Basis::new(Col::empty(1), 0, Some((s, t)));
        let mut even = vec![0i128; (hi - lo + 1) as usize];
        let lcm_even = (lo..=hi).filter(|j| j % 2 == 0).fold(1i128, |l, j| {
            let d = lagrange(j).1.abs();
            l / gcd(l, d) * d
        });
        for j in lo..=hi {
            let (p, d) = lagrange(j);
            let sign = d.signum();
            blocks.push(Block { basis: scalar(), poly: as_poly(&p.iter().map(|&c| sign * c).collect::<Vec<_>>()), name: format!("x_{j} >= 0") });
            if excluded.contains(&j) {
                blocks.push(Block { basis: scalar(), poly: as_poly(&p.iter().map(|&c| -sign * c).collect::<Vec<_>>()), name: format!("case: x_{j} = 0") });
            }
            if j % 2 == 0 {
                for (q, &c) in p.iter().enumerate() {
                    even[q] += n as i128 * (lcm_even / d) * c;
                }
            }
        }
        even[0] -= lcm_even;
        if a.has("parity") {
            blocks.push(Block { basis: scalar(), poly: as_poly(&even), name: "handshake: even-degree vertices >= 1".into() });
        }
    }
    // the realisation counts are independent per class: one thread per core (K=8 at N=25 took 4.4 h single-threaded)
    let threads = a.get("threads", std::thread::available_parallelism().map(|x| x.get()).unwrap_or(1)).max(1);
    let cnts: Vec<Vec<Vec<Vec<HashMap<(usize, usize), i128>>>>> = par_map(&hs, threads, |h| blocks.iter().map(|b| block_counts(h, b)).collect());
    println!(
        "flag: R({s},{t}) at N={n}, K={k}{}: {} admissible classes, {} blocks (sizes {:?}), set-up {:.1}s on {threads} threads",
        degree.map_or(String::new(), |(lo, hi)| format!(", red degrees in [{lo},{hi}]")),
        hs.len(),
        blocks.len(),
        blocks.iter().map(|b| b.basis.len()).collect::<Vec<_>>(),
        t0.elapsed().as_secs_f64()
    );
    if hs.is_empty() {
        println!("flag: no admissible class on {k} vertices, so R({s},{t}) <= {k} trivially");
        return;
    }
    let nbhd: Option<Nbhd> = nbhd_range.map(|(lo, hi)| {
        let dir = a.kv.get("catalogs").map(std::path::PathBuf::from).unwrap_or_else(crate::catalog::default_dir);
        let lmax = a.get("nbhd-l", k - 1);
        let t2 = std::time::Instant::now();
        let nb = build_nbhd(s, t, n, k, &hs, lo, hi, lmax, a.has("handshake"), &dir).unwrap_or_else(|e| crate::die(&e));
        println!(
            "flag: neighbourhood catalogue r{}{} for red degrees {lo}..{hi}: {} graphs, {} rooted-count rows (l <= {lmax}){}, {:.1}s",
            s - 1,
            t,
            nb.even.len(),
            nb.rows.len(),
            if nb.handshake { ", handshake row" } else { "" },
            t2.elapsed().as_secs_f64()
        );
        nb
    });
    // SDPA input: one PSD block per Block, then a diagonal block [slack_H..., λ+, λ-] extended, with --nbhd, by
    // [slack_G..., (μ+_r, μ-_r)..., β+, β-, (γ)].
    // constraint H: Σ_b <C_H^b, Y_b> + slack_H + λ+ - λ- + Σ_r a[r][H] (μ+_r - μ-_r) = 0; normalisation Σ_b tr Y_b = 1;
    // constraint G: slack_G - Σ_r c[r][G] (μ+_r - μ-_r) + β+ - β- + N γ [|G| even] = 0; maximise λ+ - λ- + β+ - β- + γ.
    // Dual reading (CSDP's y): y_H = p_H ≥ 0 with Σ p_H = 1, y_G = λ_G ≥ 0 with Σ λ_G = 1, the μ rows force
    // Σ_H p_H a[r][H] = Σ_G λ_G c[r][G], and the objective is the least λ with every moment matrix + λI PSD.
    let nh = hs.len();
    let nb = blocks.len();
    let ng = nbhd.as_ref().map_or(0, |x| x.even.len());
    let nr = nbhd.as_ref().map_or(0, |x| x.rows.len());
    let hsk = nbhd.as_ref().is_some_and(|x| x.handshake) as usize;
    // diagonal-block slots (1-based in the file)
    let slot_lam_p = nh + 1;
    let slot_lam_m = nh + 2;
    let slot_g = |gi: usize| nh + 3 + gi;
    let slot_mu = |r: usize, plus: bool| nh + 3 + ng + 2 * r + if plus { 0 } else { 1 };
    let slot_beta_p = nh + 3 + ng + 2 * nr;
    let slot_beta_m = slot_beta_p + 1;
    let slot_gamma = slot_beta_m + 1;
    let diag_size = nh + 2 + ng + 2 * nr + if ng > 0 { 2 + hsk } else { 0 };
    // per-row float scale for the SDPA file (exact integers are kept for the check)
    let row_scale: Vec<f64> = (0..nr)
        .map(|r| {
            let x = nbhd.as_ref().unwrap();
            let mx = x.a[r].iter().chain(x.c[r].iter()).map(|&v| (v as f64).abs()).fold(0.0, f64::max);
            if mx > 0.0 { 1.0 / mx } else { 1.0 }
        })
        .collect();
    let all: Vec<&Block> = blocks.iter().collect();
    let lcm = weights_lcm(&all, k, n).unwrap_or_else(|e| crate::die(&e));
    let coef: Vec<Vec<HashMap<(usize, usize), i128>>> =
        par_map(&cnts, threads, |cnt| blocks.iter().enumerate().map(|(bi, b)| coeff_int(&cnt[bi], b, k, n, lcm).unwrap_or_else(|e| crate::die(&e))).collect());
    // per-block power-of-two scale so that every block's largest coefficient is about 1 (the degree-6 parity blocks
    // otherwise dwarf the rest and stall the solver); the exact check multiplies the scales back in
    let shifts: Vec<i32> = (0..nb)
        .map(|bi| {
            let mx = coef.iter().flat_map(|c| c[bi].values()).map(|&v| (v as f64 / lcm as f64).abs()).fold(0.0, f64::max);
            if mx > 0.0 { (mx.log2().round() as i32).clamp(-40, 40) } else { 0 }
        })
        .collect();
    let mut sdpa = String::new();
    sdpa.push_str(&format!("{}\n{}\n", nh + 1 + ng, nb + 1));
    for b in &blocks {
        sdpa.push_str(&format!("{} ", b.basis.len()));
    }
    sdpa.push_str(&format!("-{}\n", diag_size));
    sdpa.push_str(&format!("{}1{}\n", "0 ".repeat(nh), " 0".repeat(ng)));
    let dg = nb + 1; // the diagonal block
    sdpa.push_str(&format!("0 {dg} {slot_lam_p} {slot_lam_p} 1\n0 {dg} {slot_lam_m} {slot_lam_m} -1\n"));
    if ng > 0 {
        sdpa.push_str(&format!("0 {dg} {slot_beta_p} {slot_beta_p} 1\n0 {dg} {slot_beta_m} {slot_beta_m} -1\n"));
        if hsk == 1 {
            sdpa.push_str(&format!("0 {dg} {slot_gamma} {slot_gamma} 1\n"));
        }
    }
    for (hi, row) in coef.iter().enumerate() {
        for (bi, c) in row.iter().enumerate() {
            let scale = 2f64.powi(-shifts[bi]) / lcm as f64;
            let mut entries: Vec<(&(usize, usize), &i128)> = c.iter().filter(|((f, g), _)| f <= g).collect();
            entries.sort();
            for (&(f, g), &v) in entries {
                sdpa.push_str(&format!("{} {} {} {} {:.17e}\n", hi + 1, bi + 1, f + 1, g + 1, v as f64 * scale));
            }
        }
        sdpa.push_str(&format!("{} {dg} {} {} 1\n{} {dg} {slot_lam_p} {slot_lam_p} 1\n{} {dg} {slot_lam_m} {slot_lam_m} -1\n", hi + 1, hi + 1, hi + 1, hi + 1, hi + 1));
        if let Some(x) = &nbhd {
            for r in 0..nr {
                let v = x.a[r][hi];
                if v != 0 {
                    let fv = v as f64 * row_scale[r];
                    sdpa.push_str(&format!("{} {dg} {} {} {:.17e}\n{} {dg} {} {} {:.17e}\n", hi + 1, slot_mu(r, true), slot_mu(r, true), fv, hi + 1, slot_mu(r, false), slot_mu(r, false), -fv));
                }
            }
        }
    }
    for (bi, b) in blocks.iter().enumerate() {
        for f in 0..b.basis.len() {
            sdpa.push_str(&format!("{} {} {} {} 1\n", nh + 1, bi + 1, f + 1, f + 1));
        }
    }
    if let Some(x) = &nbhd {
        for gi in 0..ng {
            let row = nh + 2 + gi;
            sdpa.push_str(&format!("{row} {dg} {} {} 1\n", slot_g(gi), slot_g(gi)));
            for r in 0..nr {
                let v = x.c[r][gi];
                if v != 0 {
                    let fv = v as f64 * row_scale[r];
                    sdpa.push_str(&format!("{row} {dg} {} {} {:.17e}\n{row} {dg} {} {} {:.17e}\n", slot_mu(r, true), slot_mu(r, true), -fv, slot_mu(r, false), slot_mu(r, false), fv));
                }
            }
            sdpa.push_str(&format!("{row} {dg} {slot_beta_p} {slot_beta_p} 1\n{row} {dg} {slot_beta_m} {slot_beta_m} -1\n"));
            if hsk == 1 && x.even[gi] {
                sdpa.push_str(&format!("{row} {dg} {slot_gamma} {slot_gamma} {n}\n"));
            }
        }
    }
    let (inp, sol) = (out.join("problem.dat-s"), out.join("problem.sol"));
    let t1 = std::time::Instant::now();
    // --reuse-sol: a finished CSDP run in `out` is reused when its input is byte-identical to the SDP built now (so the
    // solution belongs to exactly these blocks and coefficients); only the exact check is redone. CSDP keeps no
    // checkpoint, so a restart otherwise repeats hours of solving (K=8 at N=25: ~6 h after a 4.4 h set-up).
    let reuse = a.has("reuse-sol") && sol.exists() && std::fs::read(&inp).is_ok_and(|old| old == sdpa.as_bytes());
    if a.has("reuse-sol") && !reuse {
        println!("flag: --reuse-sol: no finished solution for this exact SDP in {}; running csdp", out.display());
    }
    let log = if reuse {
        println!("flag: reusing {} (the SDP input is byte-identical)", sol.display());
        std::fs::read_to_string(out.join("csdp.log")).unwrap_or_default()
    } else {
        std::fs::write(&inp, sdpa).unwrap_or_else(|e| crate::die(&e.to_string()));
        let res = std::process::Command::new(&csdp).arg(&inp).arg(&sol).output().unwrap_or_else(|e| crate::die(&format!("{csdp}: {e}")));
        let log = String::from_utf8_lossy(&res.stdout).to_string();
        let _ = std::fs::write(out.join("csdp.log"), &log);
        log
    };
    let obj = log.lines().find(|l| l.starts_with("Primal objective value:")).and_then(|l| l.split(':').nth(1)).and_then(|v| v.trim().parse::<f64>().ok());
    let status = log.lines().find(|l| l.contains("Success") || l.contains("Failure") || l.contains("nfeasib") || l.contains("Stuck")).unwrap_or("?").trim().to_string();
    println!("flag: csdp {:.1}s, {status}, objective λ = {}", t1.elapsed().as_secs_f64(), obj.map_or("?".into(), |v| format!("{v:.3e}")));
    let Some(lambda) = obj.filter(|&v| v > 0.0) else {
        println!("flag: no certificate (λ <= 0): these blocks do not rule out a good colouring of K_{n}");
        return;
    };
    let text = std::fs::read_to_string(&sol).unwrap_or_else(|e| crate::die(&e.to_string()));
    let mut ys: Vec<Vec<f64>> = blocks.iter().map(|b| vec![0.0; b.basis.len() * b.basis.len()]).collect();
    let mut diag: Vec<f64> = vec![0.0; diag_size + 1];
    for line in text.lines().skip(1) {
        let v: Vec<&str> = line.split_whitespace().collect();
        if v.len() != 5 || v[0] != "2" {
            continue;
        }
        let (bi, i, j): (usize, usize, usize) = (v[1].parse().unwrap(), v[2].parse().unwrap(), v[3].parse().unwrap());
        let x: f64 = v[4].parse().unwrap();
        if bi > nb {
            if bi == nb + 1 && i == j && i <= diag_size {
                diag[i] = x;
            }
            continue;
        }
        let nf = blocks[bi - 1].basis.len();
        ys[bi - 1][(i - 1) * nf + (j - 1)] = x;
        ys[bi - 1][(j - 1) * nf + (i - 1)] = x;
    }
    // the multipliers of the neighbourhood rows (μ_r = μ+ - μ-, in the SDPA row scaling) and β, γ
    let nb_cert = nbhd.as_ref().map(|x| {
        let mu: Vec<f64> = (0..nr).map(|r| (diag[slot_mu(r, true)] - diag[slot_mu(r, false)]) * row_scale[r]).collect();
        let beta = diag[slot_beta_p] - diag[slot_beta_m];
        let gamma = if x.handshake { diag[slot_gamma].max(0.0) } else { 0.0 };
        println!("flag: nbhd certificate parts: α = {:.3e}, β = {beta:.3e}, γ = {gamma:.3e}", diag[slot_lam_p] - diag[slot_lam_m]);
        (x, mu, beta, gamma)
    });
    match exact_check(&coef, &blocks, &ys, &shifts, lcm, nb_cert.as_ref().map(|(x, mu, b, g)| (*x, mu.as_slice(), *b, *g, n))) {
        Ok((bits, worst)) if !excluded.is_empty() && !degree_assumed => {
            let list: Vec<String> = excluded.iter().map(|j| j.to_string()).collect();
            println!(
                "flag: certificate VERIFIED in exact integer arithmetic (Cholesky factors rounded to 2^-{bits}; worst class \
                 value {worst:.3e} < 0, csdp margin {lambda:.3e}) IN THE CASE that no vertex has red degree in {{{}}}: \
                 no such good colouring of K_{n}. One half of a case split: R({s},{t}) <= {n} follows only together \
                 with a refutation of 'some vertex has red degree in {{{}}}' (e.g. the gluing stages d = {})",
                list.join(","),
                list.join(","),
                list.join(", ")
            )
        }
        Ok((bits, worst)) if degree_assumed || !excluded.is_empty() => {
            let (lo, hi) = degree.unwrap();
            println!(
                "flag: certificate VERIFIED in exact integer arithmetic (Cholesky factors rounded to 2^-{bits}; worst class \
                 value {worst:.3e} < 0, csdp margin {lambda:.3e}) UNDER THE ASSUMPTION that every red degree lies in \
                 [{lo},{hi}]: no such good colouring of K_{n}. This is not a claim about R({s},{t})"
            )
        }
        Ok((bits, worst)) if nbhd.is_some() => {
            let x = nbhd.as_ref().unwrap();
            println!(
                "flag: certificate VERIFIED in exact integer arithmetic (Cholesky factors rounded to 2^-{bits}; worst \
                 margin {worst:.3e} > 0, csdp margin {lambda:.3e}) UNDER THE TRUSTED INPUT that every vertex's red \
                 neighbourhood is one of the catalogue r{}{} graphs on {}..{} vertices{}: no such good colouring of K_{n}. \
                 Together with (a) McKay's catalogue completeness for those sizes and (b) whatever excludes red degrees \
                 outside [{},{}] (gluing stages or R(s-1,t)/R(s,t-1) counting), this gives R({s},{t}) <= {n}",
                s - 1,
                t,
                x.lo,
                x.hi,
                if x.handshake { " (plus the handshake lemma)" } else { "" },
                x.lo,
                x.hi
            )
        }
        Ok((bits, worst)) => println!(
            "flag: certificate VERIFIED in exact integer arithmetic (Cholesky factors rounded to 2^-{bits}; worst class \
             value {worst:.3e} < 0, csdp margin {lambda:.3e}): no 2-colouring of K_{n} without red K_{s} and blue K_{t}, \
             so R({s},{t}) <= {n}"
        ),
        Err(e) => println!("flag: exact check FAILED ({e}); the numerical certificate does not count"),
    }
    let used: Vec<String> = blocks
        .iter()
        .zip(&ys)
        .filter(|(b, y)| (0..b.basis.len()).map(|i| y[i * b.basis.len() + i]).sum::<f64>() > 1e-6)
        .map(|(b, _)| b.name.clone())
        .collect();
    println!("flag: blocks with trace > 1e-6 in the certificate: {}", used.join(", "));
}

/// `items.iter().map(f)` on `threads` threads, results in input order (the per-class set-up work is independent).
fn par_map<T: Sync, R: Send>(items: &[T], threads: usize, f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let slots: Vec<std::sync::Mutex<Option<R>>> = (0..items.len()).map(|_| std::sync::Mutex::new(None)).collect();
    std::thread::scope(|sc| {
        for _ in 0..threads.min(items.len()).max(1) {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= items.len() {
                    break;
                }
                let r = f(&items[i]);
                *slots[i].lock().unwrap() = Some(r);
            });
        }
    });
    slots.into_iter().map(|m| m.into_inner().unwrap().expect("par_map slot filled")).collect()
}

/// Exact check of Σ_b <C_H^b, Y_b> < 0 for every admissible class H. CSDP solved the problem with block b's
/// coefficients scaled by 2^-shift_b, so its Y'_b certifies the original blocks as Y_b = 2^-shift_b Y'_b; with
/// Y'_b replaced by L Lᵀ (L = round(chol(Y'_b) · 2^bits), PSD by construction) the test is
/// Σ_b 2^(E - shift_b) <lcm · C_H^b, L Lᵀ> < 0 with E = max shift, all in checked i128.
/// Exact certificate check. Without `nbhd`: every class value Σ_b <C_H^b, Yint_b> must be < 0 (integer Cholesky
/// factors, so Yint ⪰ 0 by construction). With `nbhd` = (rows, μ, β, γ, N): the multipliers are rounded to integers in
/// the same units (Q = lcm · 2^(2 bits) · 2^top), and the condition is α + β + γ > 0 with
/// α = min_H -(Σ_b <C_H^b, Yint_b> + Σ_r M_r a[r][H]),  β = min_G (Σ_r M_r c[r][G] - [|G| even] N γ_int),
/// γ_int = round(γ Q) ≥ 0 (0 without the handshake row), as derived in the `Nbhd` comment: for any good colouring
/// Σ_H p_H (..) ≤ -α, Σ_G λ_G (..) ≥ β + γ, and the μ terms cancel by the rooted-count identity.
fn exact_check(
    coef: &[Vec<HashMap<(usize, usize), i128>>],
    blocks: &[Block],
    ys: &[Vec<f64>],
    shifts: &[i32],
    lcm: i128,
    nbhd: Option<(&Nbhd, &[f64], f64, f64, usize)>,
) -> Result<(u32, f64), String> {
    let top = shifts.iter().copied().max().unwrap_or(0);
    let mults: Vec<i128> = shifts.iter().map(|&e| 1i128.checked_shl((top - e) as u32).unwrap_or(0)).collect();
    if mults.contains(&0) {
        return Err("block scales too far apart".into());
    }
    'bits: for bits in (8..=30u32).rev() {
        let scale = (1u64 << bits) as f64;
        let qf = lcm as f64 * scale * scale * 2f64.powi(top);
        let to_int = |x: f64| -> Option<i128> {
            let v = (x * qf).round();
            if v.abs() < 1e37 { Some(v as i128) } else { None }
        };
        let mut m_int: Vec<i128> = Vec::new();
        let mut gamma_int: i128 = 0;
        if let Some((_, mu, _, gamma, _)) = nbhd {
            for &m in mu {
                let Some(v) = to_int(m) else { continue 'bits };
                m_int.push(v);
            }
            let Some(g) = to_int(gamma.max(0.0)) else { continue 'bits };
            gamma_int = g;
        }
        // integer Cholesky factors, so Yint = L Lᵀ is PSD by construction
        let mut yint: Vec<Vec<i128>> = Vec::new();
        for (b, y) in blocks.iter().zip(ys) {
            let nf = b.basis.len();
            let tr: f64 = (0..nf).map(|i| y[i * nf + i]).sum();
            let l = cholesky(y, nf, 1e-12 * tr.max(1e-300)).ok_or("Cholesky failed")?;
            let li: Vec<i64> = l.iter().map(|x| (x * scale).round() as i64).collect();
            let mut m = vec![0i128; nf * nf];
            for i in 0..nf {
                for j in 0..nf {
                    let mut acc: i128 = 0;
                    for q in 0..nf {
                        acc += li[i * nf + q] as i128 * li[j * nf + q] as i128;
                    }
                    m[i * nf + j] = acc;
                }
            }
            yint.push(m);
        }
        let mut worst = f64::NEG_INFINITY;
        let mut alpha: Option<i128> = None; // min over classes of -(total)
        for (hi, row) in coef.iter().enumerate() {
            let mut total: i128 = 0;
            for (bi, b) in blocks.iter().enumerate() {
                let nf = b.basis.len();
                for (&(f, g), &c) in &row[bi] {
                    let Some(term) = c.checked_mul(yint[bi][f * nf + g]).and_then(|x| x.checked_mul(mults[bi])) else { continue 'bits };
                    let Some(t2) = total.checked_add(term) else { continue 'bits };
                    total = t2;
                }
            }
            if let Some((x, _, _, _, _)) = nbhd {
                for (r, &m) in m_int.iter().enumerate() {
                    let Some(term) = m.checked_mul(x.a[r][hi]) else { continue 'bits };
                    let Some(t2) = total.checked_add(term) else { continue 'bits };
                    total = t2;
                }
                alpha = Some(alpha.map_or(-total, |a| a.min(-total)));
            } else {
                if total >= 0 {
                    return Err(format!("a class has value >= 0 after rounding to 2^-{bits}"));
                }
                worst = worst.max(total as f64 / qf);
            }
        }
        if let Some((x, _, _, _, n)) = nbhd {
            let mut beta: Option<i128> = None;
            for gi in 0..x.even.len() {
                let mut total: i128 = 0;
                for (r, &m) in m_int.iter().enumerate() {
                    let Some(term) = m.checked_mul(x.c[r][gi]) else { continue 'bits };
                    let Some(t2) = total.checked_add(term) else { continue 'bits };
                    total = t2;
                }
                if x.even[gi] {
                    let Some(t2) = (n as i128).checked_mul(gamma_int).and_then(|v| total.checked_sub(v)) else { continue 'bits };
                    total = t2;
                }
                beta = Some(beta.map_or(total, |b| b.min(total)));
            }
            let (a, b) = (alpha.unwrap_or(0), beta.unwrap_or(0));
            let Some(margin) = a.checked_add(b).and_then(|v| v.checked_add(gamma_int)) else { continue 'bits };
            if margin <= 0 {
                return Err(format!("α + β + γ = {:.3e} <= 0 after rounding to 2^-{bits}", margin as f64 / qf));
            }
            return Ok((bits, margin as f64 / qf));
        }
        return Ok((bits, worst));
    }
    Err("integer overflow at every rounding precision".into())
}

fn cholesky(a: &[f64], n: usize, jitter: f64) -> Option<Vec<f64>> {
    let mut l = vec![0.0; n * n];
    for i in 0..n {
        for j in 0..=i {
            let mut s = a[i * n + j] + if i == j { jitter } else { 0.0 };
            for q in 0..j {
                s -= l[i * n + q] * l[j * n + q];
            }
            if i == j {
                if s <= 0.0 {
                    if s > -1e-9 {
                        s = 0.0;
                    } else {
                        return None;
                    }
                }
                l[i * n + i] = s.sqrt();
            } else {
                l[i * n + j] = if l[j * n + j] > 0.0 { s / l[j * n + j] } else { 0.0 };
            }
        }
    }
    Some(l)
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_counts() {
        let want = [1, 2, 4, 11, 34, 156, 1044];
        for (k, &w) in (1..=7).zip(want.iter()) {
            assert_eq!(classes(k).len(), w, "colouring classes of K_{k}");
        }
    }

    /// The exact identities behind every certificate, on random colourings G of K_n:
    /// E_θ[v_θ v_θᵀ] = Σ_H p_H(G) C_H^σ for every type, and E_v[r_v^q v_v v_vᵀ] = Σ_H p_H(G) C_H for the localising
    /// blocks of one-vertex types (q = 1, 2).
    #[test]
    fn coefficients_match_direct_expectation() {
        let mut x: u64 = 0x1234_5678_9abc_def1;
        let mut rnd = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for (n, k) in [(8usize, 4usize), (9, 5), (9, 6)] {
            let mut red = vec![vec![false; n]; n];
            for j in 1..n {
                for i in 0..j {
                    let r = rnd() % 3 != 0; // red-heavy, so degrees vary
                    red[i][j] = r;
                    red[j][i] = r;
                }
            }
            let sub = |vs: &[usize]| {
                let mut c = Col::empty(vs.len());
                for j in 1..vs.len() {
                    for i in 0..j {
                        if red[vs[i]][vs[j]] {
                            c.set_red(i, j);
                        }
                    }
                }
                c
            };
            let hs = classes(k);
            let keys: HashMap<Vec<u64>, usize> = hs.iter().enumerate().map(|(i, h)| (h.canon(), i)).collect();
            let all: Vec<usize> = (0..n).collect();
            let ksets = subsets(&all, k);
            let mut p = vec![0.0; hs.len()];
            for ks in &ksets {
                p[keys[&sub(ks).canon()]] += 1.0 / ksets.len() as f64;
            }
            let mut cases: Vec<(Col, usize, usize)> = Vec::new(); // (type, ℓ, q)
            for l in 1..=k / 2 {
                for sigma in classes(k - 2 * l) {
                    cases.push((sigma, l, 0));
                }
            }
            for l in 0..=k {
                for q in 1..=(if l == 0 { k - 1 } else { 2 }) {
                    if 1 + 2 * l + q <= k {
                        cases.push((Col::empty(1), l, q));
                    }
                }
            }
            for (sigma, l, q) in cases {
                let m = sigma.k;
                let blk = Block { basis: Basis::new(sigma, l, None), poly: vec![(q, 1)], name: String::new() };
                let b = &blk.basis;
                let nf = b.len();
                let mut mf = vec![0.0; nf * nf];
                for (h, ph) in hs.iter().zip(&p) {
                    let c = coeff_f64(&block_counts(h, &blk), &blk, k, n);
                    for i in 0..nf * nf {
                        mf[i] += ph * c[i];
                    }
                }
                let thetas = ordered_tuples(n, m);
                let mut md = vec![0.0; nf * nf];
                for theta in &thetas {
                    let g = sub(theta);
                    if !(1..m).all(|j| (0..j).all(|i| g.is_red(i, j) == sigma.is_red(i, j))) {
                        continue;
                    }
                    let rest: Vec<usize> = (0..n).filter(|v| !theta.contains(v)).collect();
                    let subs = subsets(&rest, l);
                    let mut v = vec![0.0; nf];
                    for a in &subs {
                        let order: Vec<usize> = theta.iter().chain(a.iter()).copied().collect();
                        let f = b.index[&b.key(&sub(&order))];
                        v[f] += 1.0 / subs.len() as f64;
                    }
                    let g_r = if q == 0 { 1.0 } else { (0..n).filter(|&u| u != theta[0] && red[theta[0]][u]).count() as f64 }.powi(q as i32);
                    for i in 0..nf {
                        for j in 0..nf {
                            md[i * nf + j] += g_r * v[i] * v[j] / thetas.len() as f64;
                        }
                    }
                }
                for i in 0..nf * nf {
                    assert!((mf[i] - md[i]).abs() < 1e-9 * (1.0 + md[i].abs()), "n={n} k={k} m={m} l={l} q={q}: formula {} vs direct {}", mf[i], md[i]);
                }
            }
        }
    }
}

#[cfg(test)]
mod nbhd_tests {
    use super::*;

    /// A random (3,4)-good colouring of K_N (retry until good).
    fn random_good(n: usize, seed: &mut u64) -> Col {
        loop {
            let mut c = Col::empty(n);
            for v in 1..n {
                for u in 0..v {
                    *seed ^= *seed << 13;
                    *seed ^= *seed >> 7;
                    *seed ^= *seed << 17;
                    if *seed % 3 == 0 {
                        c.set_red(u, v);
                    }
                }
            }
            if c.admissible(3, 4) {
                return c;
            }
        }
    }

    #[test]
    fn rooted_count_identity() {
        // Σ_v cnt_{H'}(N(v)) · C(K,l+1) · C(N,K) == Σ_H count_H · a[r][H]  for every row r, on random good colourings
        // of K_8 with K = 4 (and the catalogue side reproduces cnt through c[r][G] / (N C(K,l+1)))
        let (s, t, n, k) = (3usize, 4usize, 8usize, 4usize);
        let hs: Vec<Col> = classes(k).into_iter().filter(|h| h.admissible(s, t)).collect();
        let dir = crate::catalog::default_dir();
        let nb = build_nbhd(s, t, n, k, &hs, 0, 3, k - 1, false, &dir).expect("catalogue r24 is synthesised");
        let index: HashMap<Vec<u64>, usize> = hs.iter().enumerate().map(|(i, h)| (h.canon(), i)).collect();
        let mut seed = 0x9e3779b97f4a7c15u64;
        for _ in 0..5 {
            let g = random_good(n, &mut seed);
            let all: Vec<usize> = (0..n).collect();
            let mut count_h = vec![0i128; hs.len()];
            for sub in subsets(&all, k) {
                count_h[index[&g.induced(&sub).canon()]] += 1;
            }
            for (r, &(l, _)) in nb.rows.iter().enumerate() {
                // left side: direct rooted counts in the colouring
                let mut lhs: i128 = 0;
                for v in 0..n {
                    let nbr: Vec<usize> = (0..n).filter(|&u| u != v && g.is_red(v, u)).collect();
                    for sset in subsets(&nbr, l) {
                        let key = g.induced(&sset).canon();
                        // which row has this type? compare through the catalogue table: the neighbourhood N(v) is a
                        // (2,4)-good graph, i.e. one of the catalogue graphs, so cnt is read from c
                        let _ = key;
                    }
                    // cnt through the catalogue entry of N(v): find the catalogue graph isomorphic to N(v) (all are
                    // empty graphs, identified by size)
                    let gi = nbr.len(); // graphs are listed by size 0..3, one per size
                    assert!(gi <= 3, "red degree > 3 in a (3,4)-good colouring");
                    lhs += nb.c[r][gi] / (n as i128 * binom(k as i64, l as i64 + 1));
                }
                let rhs: i128 = (0..hs.len()).map(|h| count_h[h] * nb.a[r][h]).sum();
                assert_eq!(lhs * binom(k as i64, l as i64 + 1) * binom(n as i64, k as i64), rhs, "row {r} (l={l})");
            }
        }
    }
}
