//! Full Ramsey formula on K_N (no gluing), optionally with pattern CDCL, plus the independent symmetric checker.

use crate::sat::checker::Checker;

pub fn evar(i: usize, j: usize) -> i32 {
    let (i, j) = if i < j { (i, j) } else { (j, i) };
    (j * (j - 1) / 2 + i + 1) as i32
}

/// No red K_s, no blue K_t on K_n (red = variable true). Variable numbering is column-major, 1-based.
pub fn full_clauses(s: usize, t: usize, n: usize) -> Vec<Vec<i32>> {
    fn subsets(n: usize, k: usize, start: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if cur.len() == k {
            out.push(cur.clone());
            return;
        }
        for v in start..n {
            cur.push(v);
            subsets(n, k, v + 1, cur, out);
            cur.pop();
        }
    }
    let mut cl = Vec::new();
    for (k, sign) in [(s, -1i32), (t, 1i32)] {
        let mut sets = Vec::new();
        subsets(n, k, 0, &mut Vec::new(), &mut sets);
        for set in sets {
            let mut c = Vec::new();
            for a in 0..k {
                for b in a + 1..k {
                    c.push(sign * evar(set[a], set[b]));
                }
            }
            cl.push(c);
        }
    }
    cl
}

fn image(lits: &[i32], perm: &[u8], n: usize, flip: bool) -> Vec<i32> {
    // var -> edge table
    let mut edge = vec![(0usize, 0usize); n * (n - 1) / 2 + 1];
    for j in 1..n {
        for i in 0..j {
            edge[evar(i, j) as usize] = (i, j);
        }
    }
    let mut out: Vec<i32> = lits
        .iter()
        .map(|&l| {
            let (u, v) = edge[l.unsigned_abs() as usize];
            let w = evar(perm[u] as usize, perm[v] as usize);
            if (l > 0) != flip {
                w
            } else {
                -w
            }
        })
        .collect();
    out.sort_unstable();
    out
}

/// Independent checker for symmetric proofs of the full formula. The checker REGENERATES F from (s,t,n), so its
/// S_n-invariance holds by construction. Lines: an ordinary lemma (must be RUP w.r.t. F and everything earlier), or
/// an image line [i32::MIN, j, perm(n entries), lits..., 0] (must equal perm applied to lemma j, perm a bijection).
pub fn check_symmetric(s: usize, t: usize, n: usize, log: &[i32]) -> Result<(u64, u64, bool), String> {
    check_symmetric_lemmas(s, t, n, log).map(|(r, i, u, _)| (r, i, u))
}

/// Same as [`check_symmetric`], also returning every checked line (lemmas and images) in log order.
pub fn check_symmetric_lemmas(s: usize, t: usize, n: usize, log: &[i32]) -> Result<(u64, u64, bool, Vec<Vec<i32>>), String> {
    let f = full_clauses(s, t, n);
    let nv = n * (n - 1) / 2;
    let mut ck = Checker::new(nv, &f);
    let mut lemmas: Vec<Vec<i32>> = Vec::new();
    let (mut rup, mut img) = (0u64, 0u64);
    let mut i = 0;
    while i < log.len() {
        if log[i] == i32::MIN || log[i] == i32::MIN + 1 {
            let flip = log[i] == i32::MIN + 1;
            if flip && s != t {
                return Err(format!("image line at {i}: colour swap is only a symmetry when s = t"));
            }
            let j = log[i + 1] as usize;
            let perm: Vec<u8> = log[i + 2..i + 2 + n].iter().map(|&x| x as u8).collect();
            let mut seen = vec![false; n];
            for &p in &perm {
                if p as usize >= n || seen[p as usize] {
                    return Err(format!("image line at {i}: not a permutation"));
                }
                seen[p as usize] = true;
            }
            let mut k = i + 2 + n;
            let mut lits = Vec::new();
            while log[k] != 0 {
                lits.push(log[k]);
                k += 1;
            }
            let src = lemmas.get(j).ok_or_else(|| format!("image of unknown lemma {j}"))?;
            let mut want = lits.clone();
            want.sort_unstable();
            if image(src, &perm, n, flip) != want {
                return Err(format!("image line at {i} is not perm(lemma {j})"));
            }
            ck.check_and_add_unchecked(&lits);
            lemmas.push(lits);
            img += 1;
            i = k + 1;
        } else {
            let mut k = i;
            let mut lits = Vec::new();
            while log[k] != 0 {
                lits.push(log[k]);
                k += 1;
            }
            if !ck.check_and_add(&lits) {
                return Err(format!("lemma {} {:?} is not RUP", lemmas.len(), lits));
            }
            lemmas.push(lits);
            rup += 1;
            i = k + 1;
        }
    }
    Ok((rup, img, ck.proved_unsat(), lemmas))
}

/// Write an LRAT proof for cake_lpr, expanding every `Image` line into a renamed copy of the source lemma's
/// derivation. Renaming is sound because the formula is closed under vertex permutations: the image of an original
/// clause is an original clause, and the image of a hint chain is a valid hint chain for the image clause.
/// Returns (lines written, image derivations expanded).
pub fn write_lrat_expanded(
    n: usize,
    originals: &[Vec<i32>],
    lines: &[crate::sat::solver::LratLine],
    out: &mut impl std::io::Write,
) -> Result<(u64, u64), String> {
    use crate::sat::solver::LratLine;
    use std::collections::HashMap;
    let m = originals.len() as u64;
    let mut edge = vec![(0usize, 0usize); n * (n - 1) / 2 + 1];
    for j in 1..n {
        for i in 0..j {
            edge[evar(i, j) as usize] = (i, j);
        }
    }
    let apply = |lits: &[i32], perm: &[u8], flip: bool| -> Vec<i32> {
        let mut v: Vec<i32> = lits
            .iter()
            .map(|&l| {
                let (a, b) = edge[l.unsigned_abs() as usize];
                let w = evar(perm[a] as usize, perm[b] as usize);
                if (l > 0) != flip {
                    w
                } else {
                    -w
                }
            })
            .collect();
        v.sort_unstable();
        v
    };
    // clause (sorted) -> new id, for originals and everything emitted
    let mut by_clause: HashMap<Vec<i32>, u64> = HashMap::new();
    for (i, c) in originals.iter().enumerate() {
        let mut k = c.clone();
        k.sort_unstable();
        by_clause.entry(k).or_insert(i as u64 + 1);
    }
    // old id -> line index
    let mut line_of: HashMap<u64, usize> = HashMap::new();
    for (i, l) in lines.iter().enumerate() {
        let id = match l {
            LratLine::Lemma { id, .. } | LratLine::Image { id, .. } => *id,
            LratLine::Delete { .. } => continue, // deletions carry no clause; the export keeps every lemma
        };
        line_of.insert(id, i);
    }
    let mut next = m + 1;
    let mut new_of: HashMap<u64, u64> = HashMap::new(); // old id (identity image) -> new id
    let (mut written, mut expanded) = (0u64, 0u64);
    let ident: Vec<u8> = (0..n as u8).collect();
    let mut emit = |lits: &[i32], hints: &[u64], next: &mut u64, out: &mut dyn std::io::Write| -> Result<u64, String> {
        let id = *next;
        *next += 1;
        let mut s = String::with_capacity(16 + 8 * (lits.len() + hints.len()));
        s.push_str(&id.to_string());
        for l in lits {
            s.push(' ');
            s.push_str(&l.to_string());
        }
        s.push_str(" 0");
        for h in hints {
            s.push(' ');
            s.push_str(&h.to_string());
        }
        s.push_str(" 0\n");
        out.write_all(s.as_bytes()).map_err(|e| e.to_string())?;
        Ok(id)
    };
    // derive(old id, perm) -> new id of perm(clause(old id)), iteratively with an explicit stack
    fn compose(p: &[u8], q: &[u8]) -> Vec<u8> {
        // (p ∘ q)(x) = p(q(x))
        q.iter().map(|&x| p[x as usize]).collect()
    }
    let mut derive = |root: u64,
                      perm: &[u8],
                      root_flip: bool,
                      next: &mut u64,
                      by_clause: &mut HashMap<Vec<i32>, u64>,
                      out: &mut dyn std::io::Write,
                      expanded: &mut u64,
                      written: &mut u64|
     -> Result<u64, String> {
        // stack frames: (old id, perm, stage)
        let mut stack: Vec<(u64, Vec<u8>, bool)> = vec![(root, perm.to_vec(), root_flip)];
        let mut result: HashMap<(u64, Vec<u8>, bool), u64> = HashMap::new();
        while let Some((id, p, f)) = stack.last().cloned() {
            if result.contains_key(&(id, p.clone(), f)) {
                stack.pop();
                continue;
            }
            if id <= m {
                let c = apply(&originals[id as usize - 1], &p, f);
                let nid = *by_clause.get(&c).ok_or("image of an original clause is not an original clause")?;
                result.insert((id, p, f), nid);
                stack.pop();
                continue;
            }
            let li = *line_of.get(&id).ok_or_else(|| format!("unknown clause id {id}"))?;
            match &lines[li] {
                LratLine::Delete { .. } => return Err(format!("clause id {id} points at a deletion line")),
                LratLine::Image { src, perm: q, flip: fq, .. } => {
                    let pq = compose(&p, q);
                    let ff = f != *fq;
                    if let Some(&r) = result.get(&(*src, pq.clone(), ff)) {
                        result.insert((id, p, f), r);
                        stack.pop();
                    } else {
                        stack.push((*src, pq, ff));
                    }
                }
                LratLine::Lemma { lits, hints, .. } => {
                    let c = apply(lits, &p, f);
                    if let Some(&r) = by_clause.get(&c) {
                        result.insert((id, p, f), r);
                        stack.pop();
                        continue;
                    }
                    let missing: Vec<u64> =
                        hints.iter().copied().filter(|h| !result.contains_key(&(*h, p.clone(), f))).collect();
                    if missing.is_empty() {
                        let nh: Vec<u64> = hints.iter().map(|h| result[&(*h, p.clone(), f)]).collect();
                        let nl: Vec<i32> = {
                            // keep the solver's literal order (renamed) for readability; checker ignores order
                            c.clone()
                        };
                        let nid = emit(&nl, &nh, next, out)?;
                        *written += 1;
                        *expanded += 1;
                        by_clause.insert(c, nid);
                        result.insert((id, p, f), nid);
                        stack.pop();
                    } else {
                        for h in missing {
                            stack.push((h, p.clone(), f));
                        }
                    }
                }
            }
        }
        Ok(result[&(root, perm.to_vec(), root_flip)])
    };
    // backward trim: keep only lines reachable from the final empty clause through hints (images keep themselves;
    // their source cones are pulled in by `derive` on demand)
    let mut needed = vec![false; lines.len()];
    if let Some(last) = lines.iter().rposition(|l| matches!(l, LratLine::Lemma { lits, .. } if lits.is_empty())) {
        needed[last] = true;
        for i in (0..=last).rev() {
            if !needed[i] {
                continue;
            }
            if let LratLine::Lemma { hints, .. } = &lines[i] {
                for h in hints {
                    if *h > m {
                        if let Some(&j) = line_of.get(h) {
                            needed[j] = true;
                        }
                    }
                }
            }
        }
    } else {
        needed.iter_mut().for_each(|x| *x = true);
    }
    let kept = needed.iter().filter(|&&x| x).count();
    eprintln!("c trim: {} of {} solver lines needed", kept, lines.len());
    for (li, l) in lines.iter().enumerate() {
        if !needed[li] {
            continue;
        }
        match l {
            LratLine::Delete { .. } => continue,
            LratLine::Lemma { id, lits, hints } => {
                let nh: Vec<u64> = hints
                    .iter()
                    .map(|h| if *h <= m { Ok(*h) } else { new_of.get(h).copied().ok_or(format!("hint {h} unknown")) })
                    .collect::<Result<_, String>>()?;
                let nid = emit(lits, &nh, &mut next, out)?;
                written += 1;
                let mut k = lits.clone();
                k.sort_unstable();
                by_clause.entry(k).or_insert(nid);
                new_of.insert(*id, nid);
            }
            LratLine::Image { id, src, perm, flip, .. } => {
                let nid = derive(*src, perm, *flip, &mut next, &mut by_clause, out, &mut expanded, &mut written)?;
                new_of.insert(*id, nid);
            }
        }
    }
    let _ = ident;
    Ok((written, expanded))
}

/// Known small Ramsey values (used only to PROPOSE lemma sizes; every lemma is proved by the solver).
pub fn known_ramsey(a: usize, b: usize) -> Option<usize> {
    let (a, b) = (a.min(b), a.max(b));
    match (a, b) {
        (1, _) => Some(1),
        (2, b) => Some(b),
        (3, 3) => Some(6),
        (3, 4) => Some(9),
        (3, 5) => Some(14),
        (3, 6) => Some(18),
        (3, 7) => Some(23),
        (3, 8) => Some(28),
        (3, 9) => Some(36),
        (4, 4) => Some(18),
        (4, 5) => Some(25),
        _ => None,
    }
}

/// edges[v] = (i, j), i < j, for every edge variable v = evar(i, j) of K_n (index 0 unused)
pub fn edge_table(n: usize) -> Vec<(usize, usize)> {
    let mut e = vec![(0, 0); n * n.saturating_sub(1) / 2 + 1];
    for j in 1..n {
        for i in 0..j {
            e[evar(i, j) as usize] = (i, j);
        }
    }
    e
}

/// Vertex permutation for `--relabel SEED`: seed 0 is the identity, any other seed a pseudo-random permutation of
/// 0..n (Fisher–Yates on xorshift64). F(s,t,n) is invariant under it, so a relabelled run solves the same formula with
/// another clause order and other lemma roots: a semantics-preserving perturbation for measuring solver variance.
pub fn relabel_perm(n: usize, seed: u64) -> Vec<usize> {
    let mut p: Vec<usize> = (0..n).collect();
    if seed == 0 {
        return p;
    }
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    for i in (1..n).rev() {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        p.swap(i, (x % (i as u64 + 1)) as usize);
    }
    p
}

/// The clause `c` with every vertex v renamed to perm[v] (signs kept); `edges` from [`edge_table`].
pub fn permute_clause(c: &[i32], perm: &[usize], edges: &[(usize, usize)]) -> Vec<i32> {
    c.iter()
        .map(|&l| {
            let (a, b) = edges[l.unsigned_abs() as usize];
            evar(perm[a], perm[b]) * l.signum()
        })
        .collect()
}

/// How [`add_lemma_library`] builds the rooted-lemma library.
pub struct LibOpts<'a> {
    /// books, mixed books and the other multi-root lemmas, not only the stars
    pub books: bool,
    /// lemma vertex v is placed at perm[v] (identity normally; `--relabel` permutes it)
    pub perm: &'a [usize],
    /// colours swapped (`--relabel` with an odd seed when s = t): red roots become blue ones and vice versa
    pub flip: bool,
    /// leave out the stars (a + b = 1) because they are supplied otherwise (lifted from sub-instances, `--lib lift`)
    pub skip_stars: bool,
}

/// Inductive lemma library: refute a red star of size R(s-1,t) and a blue star of size R(s,t-1) at vertex 0 (and,
/// with `books`, red/blue books on edge 0-1) by assumption solves; each core clause is a logged lemma and is
/// registered as a pattern so its images propagate everywhere. When s = t and the pattern store applies colour swap,
/// only one lemma per colour-swap pair is proved: its swapped twin arrives as a flip image, so red versus blue proof
/// order cannot matter. The representative is the blue-heavy one (a ≤ b), measured about 3x cheaper than the
/// red-heavy one with this solver (MONSTER_ORBIT_REP=red picks the other; MONSTER_NO_ORBIT=1 proves both).
/// Returns human-readable lines.
pub fn add_lemma_library(sv: &mut crate::sat::solver::Solver, s: usize, t: usize, n: usize, opts: &LibOpts) -> Vec<String> {
    let books = opts.books;
    use crate::sat::solver::SolveResult;
    let mut out = Vec::new();
    let saved_budget = sv.conflict_budget;
    // each lemma gets a conflict budget; an unproved lemma is simply skipped (always sound)
    sv.conflict_budget = std::env::var("MONSTER_LEMMA_BUDGET").ok().and_then(|v| v.parse().ok()).unwrap_or(200_000);
    // General rooted lemmas (smallest first, so later proofs can use earlier ones), all proved by assumption solves:
    // a red clique A of a roots, a blue clique B of b roots, a leaf set L with A red to L and B blue to L. Then L is
    // (s-a, t-b)-good, so |L| = R(s-a, t-b) is impossible. A–B cross edges are left FREE (the lemma does not need
    // them), which makes each lemma as general as possible. (a,b) = (1,0),(0,1): stars; (2,0),(0,2): books;
    // (1,1): mixed books. `books = false` keeps only the stars.
    let mut specs: Vec<(usize, usize, usize)> = Vec::new(); // (a, b, k)
    for a in 0..s {
        for b in 0..t {
            if a + b == 0 || (!books && a + b > 1) || (opts.skip_stars && a + b == 1) {
                continue;
            }
            let Some(k) = known_ramsey(s - a, t - b) else { continue };
            if k < 2 || a + b + k > n {
                continue;
            }
            specs.push((a, b, k));
        }
    }
    let swap = s == t && sv.patterns.as_ref().is_some_and(|p| p.flip_ok) && std::env::var_os("MONSTER_NO_ORBIT").is_none();
    if swap {
        let red_reps = std::env::var("MONSTER_ORBIT_REP").is_ok_and(|v| v == "red");
        specs.retain(|&(a, b, _)| if red_reps { a >= b } else { a <= b }); // one representative per colour-swap orbit
    }
    specs.sort_by_key(|&(a, b, k)| (a + b + k, a + b));
    let perm = opts.perm;
    let lit = |u: usize, v: usize, red: bool| if red != opts.flip { evar(perm[u], perm[v]) } else { -evar(perm[u], perm[v]) };
    for (a, b, k) in specs {
        let red = |u: usize, v: usize| lit(u, v, true);
        let blue = |u: usize, v: usize| lit(u, v, false);
        // vertices (before relabelling): A = 0..a, B = a..a+b, L = a+b..a+b+k
        let mut assumps: Vec<i32> = Vec::new();
        for i in 0..a {
            for j in i + 1..a {
                assumps.push(red(i, j));
            }
        }
        for i in a..a + b {
            for j in i + 1..a + b {
                assumps.push(blue(i, j));
            }
        }
        for x in a + b..a + b + k {
            for r in 0..a {
                assumps.push(red(r, x));
            }
            for r in a..a + b {
                assumps.push(blue(r, x));
            }
        }
        let tl = std::time::Instant::now();
        let c0 = sv.stats.conflicts;
        let r = sv.solve_dimacs(&assumps);
        let name = format!("rooted lemma (red roots {a}, blue roots {b}) with {k} leaves");
        if r == SolveResult::Unsat && !sv.is_root_unsat() {
            let clause: Vec<u32> = sv.core.iter().map(|&l| l ^ 1).collect();
            let id = if sv.lrat.is_some() { sv.last_lrat_id() } else { sv.proof_lemmas.saturating_sub(1) };
            if let Some(pp) = sv.patterns.as_mut() {
                pp.learn_forced(&clause, id);
            }
            let dimacs: Vec<i32> = clause.iter().map(|&l| crate::sat::solver::lit_to_dimacs(l)).collect();
            LIB_SINK.with(|c| c.borrow_mut().push((dimacs, id)));
            out.push(format!(
                "lemma: no {name} (core {} edges) in {:.2}s / {} conflicts",
                clause.len(),
                tl.elapsed().as_secs_f64(),
                sv.stats.conflicts - c0
            ));
        } else {
            out.push(format!("lemma: {name} not refuted ({r:?})"));
        }
        if std::env::var_os("MONSTER_VERBOSE").is_some() {
            eprintln!("{}", out.last().unwrap());
        }
    }
    sv.conflict_budget = saved_budget;
    out
}

/// Cache format of `Library` files. Bump it whenever the lemma set built by `add_lemma_library_collect` changes, so
/// stale caches are rebuilt instead of silently reused. "MON1" files (before 2026-10-26) held the old stars/books/mixed
/// lemmas (6 lemmas on K25) after the code had moved to general rooted lemmas (11 on K25).
const LIBRARY_MAGIC: i32 = 0x4d4f4e32; // "MON2": general rooted lemmas, books flag stored

/// Tag of the library verifier (`Library::verify`, i.e. `check_symmetric_lemmas`). After a successful check,
/// `<cache>.verified` records "VERIFY_TAG sha256-of-the-file"; `Library::get(.., trust_stamp = true)` then skips the
/// re-check of those exact bytes (R(3,7)/K23: 67 MB, ~650 s single-threaded on every run). Bump the tag whenever the
/// symmetric checker changes. Only uncertified runs trust stamps; certified tasks re-check the library proof anyway,
/// because `import` prepends it to their proofs.
const VERIFY_TAG: &str = "symcheck-1";

fn stamp_path(p: &std::path::Path) -> std::path::PathBuf {
    let mut s = p.as_os_str().to_owned();
    s.push(".verified");
    s.into()
}

/// A proved lemma library for F(s,t,n): its proof log (lemmas + image lines, checkable by `check_symmetric`) and the
/// library lemmas with their indices in that log (so imported patterns can cite them).
pub struct Library {
    pub s: usize,
    pub t: usize,
    pub n: usize,
    pub books: bool,
    pub log: Vec<i32>,
    pub log_lemmas: u64,
    pub lemmas: Vec<(Vec<i32>, u64)>,
    pub lines: Vec<String>,
    /// loaded from a cache whose verification stamp matched, so not re-checked in this run
    pub stamp_trusted: bool,
}

impl Library {
    /// Build (or load from `cache`) and VERIFY the library. Loading from cache re-checks the proof, unless
    /// `trust_stamp` and the cache's verification stamp (`VERIFY_TAG`) matches its bytes; a cache in an older format
    /// (`LIBRARY_MAGIC`) or for other parameters is rebuilt and overwritten.
    pub fn get(s: usize, t: usize, n: usize, books: bool, cache: Option<&std::path::Path>, trust_stamp: bool) -> Result<Library, String> {
        if let Some(p) = cache {
            if let Ok(bytes) = std::fs::read(p) {
                if let Ok(mut lib) = Library::decode(&bytes) {
                    if (lib.s, lib.t, lib.n, lib.books) == (s, t, n, books) {
                        let stamp = format!("{VERIFY_TAG} {}", crate::sha256::sha256(&bytes));
                        if trust_stamp && std::fs::read_to_string(stamp_path(p)).is_ok_and(|x| x.trim() == stamp) {
                            lib.stamp_trusted = true;
                            return Ok(lib);
                        }
                        lib.verify()?;
                        let _ = std::fs::write(stamp_path(p), stamp + "\n");
                        return Ok(lib);
                    }
                }
            }
        }
        let cls = full_clauses(s, t, n);
        let mut sv = crate::sat::solver::Solver::new(n * (n - 1) / 2);
        sv.enable_proof();
        for c in &cls {
            sv.add_clause_dimacs(c);
        }
        let pp = crate::pattern::PatternProp::new(n);
        sv.patterns = Some(Box::new(pp));
        let mut lemmas = Vec::new();
        let identity: Vec<usize> = (0..n).collect();
        let opts = LibOpts { books, perm: &identity, flip: false, skip_stars: false };
        let lines = add_lemma_library_collect(&mut sv, s, t, n, &opts, &mut lemmas);
        let lib = Library {
            s,
            t,
            n,
            books,
            log: sv.proof.clone().unwrap(),
            log_lemmas: sv.proof_lemmas,
            lemmas,
            lines,
            stamp_trusted: false,
        };
        lib.verify()?;
        if let Some(p) = cache {
            let bytes = lib.encode();
            if std::fs::write(p, &bytes).is_ok() {
                let _ = std::fs::write(stamp_path(p), format!("{VERIFY_TAG} {}\n", crate::sha256::sha256(&bytes)));
            }
        }
        Ok(lib)
    }

    pub fn verify(&self) -> Result<(), String> {
        let (_, _, _, lem) = check_symmetric_lemmas(self.s, self.t, self.n, &self.log)?;
        for (c, i) in &self.lemmas {
            let mut a = c.clone();
            a.sort_unstable();
            let mut b = lem.get(*i as usize).ok_or("library lemma index out of range")?.clone();
            b.sort_unstable();
            if a != b {
                return Err("library lemma does not match its proof line".into());
            }
        }
        Ok(())
    }

    fn encode(&self) -> Vec<u8> {
        let mut v: Vec<i32> =
            vec![LIBRARY_MAGIC, self.s as i32, self.t as i32, self.n as i32, self.books as i32, self.lemmas.len() as i32];
        for (c, i) in &self.lemmas {
            v.push(*i as i32);
            v.push(c.len() as i32);
            v.extend(c);
        }
        v.push(self.log_lemmas as i32);
        v.push(self.lines.len() as i32);
        let text = self.lines.join("\n");
        v.push(text.len() as i32);
        let mut out: Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
        out.extend(text.as_bytes());
        out.extend(self.log.iter().flat_map(|x| x.to_le_bytes()));
        out
    }

    fn decode(b: &[u8]) -> Result<Library, String> {
        let mut pos = 0usize;
        let mut rd = || -> Result<i32, String> {
            let x = b.get(pos..pos + 4).ok_or("truncated")?;
            pos += 4;
            Ok(i32::from_le_bytes([x[0], x[1], x[2], x[3]]))
        };
        if rd()? != LIBRARY_MAGIC {
            return Err("stale or foreign library format".into());
        }
        let (s, t, n, books, k) = (rd()? as usize, rd()? as usize, rd()? as usize, rd()? != 0, rd()? as usize);
        let mut lemmas = Vec::new();
        for _ in 0..k {
            let i = rd()? as u64;
            let len = rd()? as usize;
            let mut c = Vec::new();
            for _ in 0..len {
                c.push(rd()?);
            }
            lemmas.push((c, i));
        }
        let log_lemmas = rd()? as u64;
        let _nl = rd()?;
        let tl = rd()? as usize;
        drop(rd);
        let text = String::from_utf8(b.get(pos..pos + tl).ok_or("truncated")?.to_vec()).map_err(|e| e.to_string())?;
        pos += tl;
        let log: Vec<i32> = b[pos..].chunks(4).map(|x| i32::from_le_bytes([x[0], x[1], x[2], x[3]])).collect();
        Ok(Library { s, t, n, books, log, log_lemmas, lemmas, lines: text.lines().map(String::from).collect(), stamp_trusted: false })
    }

    /// Give a solver the library: lemma clauses into the database, patterns registered, and (if the solver logs a
    /// proof) the library's proof prepended so pattern lemma indices line up and certified proofs stay complete.
    pub fn import(&self, sv: &mut crate::sat::solver::Solver) {
        if sv.proof.is_some() {
            sv.proof = Some(self.log.clone());
            sv.proof_lemmas = self.log_lemmas;
        }
        for (c, idx) in &self.lemmas {
            sv.add_clause_dimacs(c);
            let lits: Vec<u32> = c.iter().map(|&l| crate::sat::solver::lit_from_dimacs(l)).collect();
            if let Some(pp) = sv.patterns.as_mut() {
                pp.learn_forced(&lits, *idx);
            }
        }
    }
}

/// Like [`add_lemma_library`], also collecting (clause, proof index) for each proved lemma.
/// (i, j), i < j, of edge variable v = j(j-1)/2 + i (0-based, the solver's variable index).
fn edge_of_var(v: usize) -> (usize, usize) {
    let mut j = 1usize;
    while (j + 1) * j / 2 <= v {
        j += 1;
    }
    (v - j * (j - 1) / 2, j)
}

/// Lemma mining. On tight Ramsey formulas CDCL's learned clauses span almost every vertex, so they are useless as
/// patterns. For a recent learned clause, keep only its literals among its `k` densest vertices and test that
/// sub-clause with a bounded assumption solve in the same solver, exactly the library's mechanism: on a refutation
/// (not at the root) the negated failed-assumption core is a logged lemma, registered as a pattern (`learn_forced`)
/// and already a clause of the database. Returns (sub-clauses tried, lemmas mined, conflicts spent).
pub fn mine_lemmas(
    sv: &mut crate::sat::solver::Solver,
    k: usize,
    budget: u64,
    tries: usize,
    seen: &mut std::collections::HashSet<Vec<i32>>,
) -> (usize, usize, u64) {
    use crate::sat::solver::{lit_to_dimacs, SolveResult};
    let c0 = sv.stats.conflicts;
    let saved = sv.conflict_budget;
    let (mut tried, mut mined) = (0, 0);
    for cl in sv.recent_learnts(8 * tries) {
        if tried >= tries || sv.is_root_unsat() {
            break;
        }
        let mut cnt: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
        for &l in &cl {
            let (i, j) = edge_of_var((l >> 1) as usize);
            *cnt.entry(i).or_insert(0) += 1;
            *cnt.entry(j).or_insert(0) += 1;
        }
        if cnt.len() <= k {
            continue; // small already: the pattern store admits it on its own
        }
        let mut vs: Vec<(usize, usize)> = cnt.into_iter().map(|(v, c)| (c, v)).collect();
        vs.sort_by(|a, b| b.cmp(a));
        let w: std::collections::HashSet<usize> = vs.iter().take(k).map(|&(_, v)| v).collect();
        let sub: Vec<u32> = cl
            .iter()
            .copied()
            .filter(|&l| {
                let (i, j) = edge_of_var((l >> 1) as usize);
                w.contains(&i) && w.contains(&j)
            })
            .collect();
        if sub.len() < 3 {
            continue;
        }
        let mut key: Vec<i32> = sub.iter().map(|&l| lit_to_dimacs(l)).collect();
        key.sort_unstable();
        if !seen.insert(key) {
            continue;
        }
        tried += 1;
        // assume the sub-clause false: its partial colouring
        let assumps: Vec<i32> = sub.iter().map(|&l| lit_to_dimacs(l ^ 1)).collect();
        sv.conflict_budget = budget;
        let r = sv.solve_dimacs(&assumps);
        if r == SolveResult::Unsat && !sv.is_root_unsat() {
            let clause: Vec<u32> = sv.core.iter().map(|&l| l ^ 1).collect();
            let id = if sv.lrat.is_some() { sv.last_lrat_id() } else { sv.proof_lemmas.saturating_sub(1) };
            if let Some(pp) = sv.patterns.as_mut() {
                pp.learn_forced(&clause, id);
            }
            mined += 1;
        } else if r == SolveResult::Sat {
            break; // the formula itself is satisfiable: the caller's next solve returns it
        }
    }
    sv.conflict_budget = saved;
    (tried, mined, sv.stats.conflicts - c0)
}

pub fn add_lemma_library_collect(
    sv: &mut crate::sat::solver::Solver,
    s: usize,
    t: usize,
    n: usize,
    opts: &LibOpts,
    lemmas: &mut Vec<(Vec<i32>, u64)>,
) -> Vec<String> {
    LIB_SINK.with(|c| c.borrow_mut().clear());
    let lines = add_lemma_library(sv, s, t, n, opts);
    LIB_SINK.with(|c| lemmas.extend(c.borrow_mut().drain(..)));
    lines
}

thread_local! {
    static LIB_SINK: std::cell::RefCell<Vec<(Vec<i32>, u64)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Native symmetric LRAT ("SLRAT"), no expansion. Header `c slrat s t n`, then lines:
///   `id l1 .. lk 0 h1 .. hm 0`      LRAT addition: the hints, in order, unit-propagate the negated clause to conflict
///   `id i src p0 .. p{n-1} 0`        image: clause id := p applied to clause src (p a permutation of the n vertices)
/// Original clauses are 1..m in the order of `full_clauses(s,t,n)`.
///
/// `SlratWriter` assembles a proof from one or more solver logs. Every line gets the next proof id after the m
/// originals (the Lean checker requires id = database size), so logs of several solvers, relabelled clause orders and
/// interleaved ids all come out valid. For each log, `map` takes that solver's ids to proof ids: put the originals
/// (their canonical positions 1..m) and any imported clauses in it before `emit`; `emit` adds every line it writes,
/// so a later log can cite an earlier one's clauses.
pub struct SlratWriter<W: std::io::Write> {
    out: W,
    next: u64,
    /// next free id in each opened sub-instance database
    subs: Vec<u64>,
    pub lines: u64,
}

impl<W: std::io::Write> SlratWriter<W> {
    pub fn new(s: usize, t: usize, n: usize, mut out: W) -> std::io::Result<Self> {
        writeln!(out, "c slrat {s} {t} {n}")?;
        Ok(SlratWriter { out, next: binom(n, s) + binom(n, t) + 1, subs: Vec::new(), lines: 0 })
    }

    /// Open sub-instance F(s',t',m) on vertices 0..m-1 (`o s' t' m`); returns its index.
    pub fn open_sub(&mut self, s: usize, t: usize, m: usize) -> std::io::Result<usize> {
        writeln!(self.out, "o {s} {t} {m}")?;
        self.subs.push(binom(m, s) + binom(m, t) + 1);
        self.lines += 1;
        Ok(self.subs.len() - 1)
    }

    /// Emit a solver log into sub-instance `k` (`s k <line>`), numbered in that sub-instance's own database; `map`
    /// must hold the sub-solver's original clause ids (canonical positions in F(s',t',m)).
    pub fn emit_sub(&mut self, k: usize, log: &[crate::sat::solver::LratLine], map: &mut std::collections::HashMap<u64, u64>) -> Result<(), String> {
        self.emit_into(Some(k), log, map)
    }

    /// Main clause := lift of clause `src` of sub-instance `k` with apex `v` of colour `red` and embedding `emb`
    /// (`id l k src v r|b e0..e{m-1} 0`). Returns its proof id.
    pub fn lift(&mut self, k: usize, src: u64, v: usize, red: bool, emb: &[usize]) -> std::io::Result<u64> {
        let id = self.next;
        let e: Vec<String> = emb.iter().map(|x| x.to_string()).collect();
        writeln!(self.out, "{id} l {k} {src} {v} {} {} 0", if red { "r" } else { "b" }, e.join(" "))?;
        self.next += 1;
        self.lines += 1;
        Ok(id)
    }

    pub fn emit(&mut self, log: &[crate::sat::solver::LratLine], map: &mut std::collections::HashMap<u64, u64>) -> Result<(), String> {
        self.emit_into(None, log, map)
    }

    fn emit_into(&mut self, sub: Option<usize>, log: &[crate::sat::solver::LratLine], map: &mut std::collections::HashMap<u64, u64>) -> Result<(), String> {
        use crate::sat::solver::LratLine;
        use std::fmt::Write as _;
        let get = |map: &std::collections::HashMap<u64, u64>, x: &u64| {
            map.get(x).copied().ok_or_else(|| format!("proof cites clause {x}, which is not original, imported or derived"))
        };
        let prefix = sub.map(|k| format!("s {k} ")).unwrap_or_default();
        let mut line = String::new();
        for l in log {
            line.clear();
            line.push_str(&prefix);
            let id = match sub {
                Some(k) => self.subs[k],
                None => self.next,
            };
            let old = match l {
                LratLine::Delete { .. } => continue,
                LratLine::Lemma { id: old, lits, hints } => {
                    let _ = write!(line, "{id}");
                    for x in lits {
                        let _ = write!(line, " {x}");
                    }
                    line.push_str(" 0");
                    for h in hints {
                        let _ = write!(line, " {}", get(map, h)?);
                    }
                    line.push_str(" 0\n");
                    *old
                }
                LratLine::Image { id: old, src, perm, flip, .. } => {
                    let _ = write!(line, "{id} {} {}", if *flip { "f" } else { "i" }, get(map, src)?);
                    for p in perm {
                        let _ = write!(line, " {p}");
                    }
                    line.push_str(" 0\n");
                    *old
                }
            };
            self.out.write_all(line.as_bytes()).map_err(|e| e.to_string())?;
            map.insert(old, id);
            match sub {
                Some(k) => self.subs[k] += 1,
                None => self.next += 1,
            }
            self.lines += 1;
        }
        Ok(())
    }

    pub fn finish(mut self) -> std::io::Result<u64> {
        self.out.flush()?;
        Ok(self.lines)
    }
}

/// C(n, k)
pub fn binom(n: usize, k: usize) -> u64 {
    if k > n {
        return 0;
    }
    (0..k.min(n - k)).fold(1u64, |acc, i| acc * (n - i) as u64 / (i + 1) as u64)
}

/// One clause database of the reference checker: F(s,t,m) on vertices 0..m-1 and everything derived in it.
struct SlratDb {
    s: usize,
    t: usize,
    m: usize,
    db: std::collections::HashMap<u64, Vec<i32>>,
    /// SR tier: ids of clauses that are only satisfiability-preserving (added by an `r` line, or derived from one).
    /// Everything else holds in every good colouring. Images and lifts may only use pure clauses; a lemma-mode result
    /// is a lemma only when pure. The empty clause in either tier means: no good colouring exists.
    sr: std::collections::HashSet<u64>,
}

/// Substitution of one variable under an SR witness.
#[derive(Clone, Copy, PartialEq)]
enum Sub {
    Id,
    True,
    False,
    Lit(i32),
}

/// What an SR check produces for the hinted form: either the clause was RUP outright (hints of the conflict), or
/// the α hints (units propagated from ¬C over the database) and one hint group per clause whose image needs
/// propagation (in id order, C itself last under the new id).
enum SrHints {
    Rup(Vec<u64>),
    Sr { alpha: Vec<u64>, groups: Vec<(u64, Vec<u64>)> },
}

/// σ from an SR line: var |w| := true/false for each witness literal, var |a| := b (negated if a < 0) for each
/// pair, identity elsewhere. Every literal must be in range and no variable substituted twice.
fn sigma_of(nv: usize, lits: &[i32], witness: &[i32], pairs: &[i32]) -> Result<Vec<Sub>, String> {
    let bad = |l: i32| l == 0 || l.unsigned_abs() as usize > nv;
    if lits.iter().chain(witness).chain(pairs).any(|&l| bad(l)) {
        return Err("literal out of range".into());
    }
    if pairs.len() % 2 != 0 {
        return Err("substitution pairs must come in pairs".into());
    }
    let mut sigma = vec![Sub::Id; nv + 1];
    for p in pairs.chunks(2) {
        let (a, b) = (p[0], p[1]);
        let v = a.unsigned_abs() as usize;
        if sigma[v] != Sub::Id {
            return Err("variable substituted twice".into());
        }
        sigma[v] = Sub::Lit(if a > 0 { b } else { -b });
    }
    for &w in witness {
        let v = w.unsigned_abs() as usize;
        if sigma[v] != Sub::Id {
            return Err("witness variable substituted twice".into());
        }
        sigma[v] = if w > 0 { Sub::True } else { Sub::False };
    }
    Ok(sigma)
}

/// D|σ: None if satisfied by σ (a literal mapped to true, or a tautology), else the remaining literals (sorted,
/// duplicates removed; literals mapped to false dropped)
fn reduce_sigma(sigma: &[Sub], d: &[i32]) -> Option<Vec<i32>> {
    let mut out = Vec::with_capacity(d.len());
    for &l in d {
        let v = l.unsigned_abs() as usize;
        match sigma[v] {
            Sub::Id => out.push(l),
            Sub::Lit(x) => out.push(if l > 0 { x } else { -x }),
            Sub::True => {
                if l > 0 {
                    return None;
                }
            }
            Sub::False => {
                if l < 0 {
                    return None;
                }
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    if out.windows(2).any(|w| w[0] == -w[1]) {
        return None; // tautology
    }
    Some(out)
}

/// Unit propagation over a snapshot of a clause database (occurrence lists), for hint-less RUP and SR checks.
struct Prop {
    /// the database's clauses in id order, with their ids (so hint lists refer to ids)
    clauses: Vec<Vec<i32>>,
    ids: Vec<u64>,
    occ: Vec<Vec<u32>>, // occ[code(l)] = clauses containing literal l; code(l) = 2*var + (l < 0)
    val: Vec<i8>,
    trail: Vec<usize>,
    /// reason[v] = index of the clause that propagated v (NO_REASON for assumptions)
    reason: Vec<u32>,
    /// the database itself is contradictory under unit propagation (then every clause is RUP); the conflicting
    /// clause index when known
    dead: bool,
    dead_confl: Option<u32>,
}

const NO_REASON: u32 = u32::MAX;

impl Prop {
    fn new(db: &std::collections::HashMap<u64, Vec<i32>>, nv: usize) -> Prop {
        let mut ids: Vec<u64> = db.keys().copied().collect();
        ids.sort_unstable();
        let clauses: Vec<Vec<i32>> = ids.iter().map(|i| db[i].clone()).collect();
        let mut occ = vec![Vec::new(); 2 * nv + 2];
        for (i, c) in clauses.iter().enumerate() {
            for &l in c {
                occ[Prop::code(l)].push(i as u32);
            }
        }
        Prop { clauses, ids, occ, val: vec![0; nv + 1], trail: Vec::new(), reason: vec![NO_REASON; nv + 1], dead: false, dead_confl: None }
    }

    /// Assign the database's unit clauses (propagation is driven by assignments only) and propagate to a fixpoint.
    /// Called AFTER the assumed literals (¬C) are on the trail, in the order the hinted checkers replay: a unit
    /// clause already satisfied needs no hint, one already falsified is the conflict. Returns the conflicting clause.
    fn init_units(&mut self) -> Option<u32> {
        let from = self.trail.len();
        for i in 0..self.clauses.len() {
            if self.clauses[i].len() == 1 {
                let l = self.clauses[i][0];
                if self.lit_val(l) == 1 {
                    continue;
                }
                if !self.assign_reason(l, i as u32) {
                    self.dead = true;
                    self.dead_confl = Some(i as u32);
                    return self.dead_confl;
                }
            }
        }
        let _ = from;
        let c = self.propagate(0);
        if c.is_some() {
            self.dead = true;
            self.dead_confl = c;
        }
        c
    }

    /// LRAT-style hints for the conflict `confl` reached by propagation above trail position `base`: the reasons
    /// of the variables involved (in trail order, so each is unit when processed), then the conflicting clause
    fn conflict_hints(&self, confl: u32, base: usize) -> Vec<u64> {
        let mut seen = vec![false; self.val.len()];
        for &l in &self.clauses[confl as usize] {
            seen[l.unsigned_abs() as usize] = true;
        }
        let mut out = Vec::new();
        for pos in (base..self.trail.len()).rev() {
            let v = self.trail[pos];
            if seen[v] && self.reason[v] != NO_REASON {
                let ci = self.reason[v];
                out.push(self.ids[ci as usize]);
                for &l in &self.clauses[ci as usize] {
                    seen[l.unsigned_abs() as usize] = true;
                }
            }
        }
        out.reverse();
        out.push(self.ids[confl as usize]);
        out
    }

    /// the reasons of every propagated literal on the trail, in order (a hint list that rebuilds the assignment)
    fn trail_hints(&self) -> Vec<u64> {
        self.trail.iter().filter(|&&v| self.reason[v] != NO_REASON).map(|&v| self.ids[self.reason[v] as usize]).collect()
    }
    fn code(l: i32) -> usize {
        2 * l.unsigned_abs() as usize + (l < 0) as usize
    }
    fn lit_val(&self, l: i32) -> i8 {
        let v = self.val[l.unsigned_abs() as usize];
        if l > 0 {
            v
        } else {
            -v
        }
    }
    /// assign literal l true; false if it is already false
    fn assign(&mut self, l: i32) -> bool {
        self.assign_reason(l, NO_REASON)
    }
    fn assign_reason(&mut self, l: i32, reason: u32) -> bool {
        match self.lit_val(l) {
            1 => true,
            -1 => false,
            _ => {
                let v = l.unsigned_abs() as usize;
                self.val[v] = if l > 0 { 1 } else { -1 };
                self.reason[v] = reason;
                self.trail.push(v);
                true
            }
        }
    }
    /// propagate from trail position `from` to a fixpoint; the conflicting clause if a conflict was reached
    fn propagate(&mut self, mut from: usize) -> Option<u32> {
        while from < self.trail.len() {
            let v = self.trail[from];
            from += 1;
            let falsified = if self.val[v] > 0 { -(v as i32) } else { v as i32 };
            let occ = std::mem::take(&mut self.occ[Prop::code(falsified)]);
            let mut conflict = None;
            for &ci in &occ {
                let mut unit = None;
                let mut nun = 0;
                let mut sat = false;
                for &l in &self.clauses[ci as usize] {
                    match self.lit_val(l) {
                        1 => {
                            sat = true;
                            break;
                        }
                        0 => {
                            nun += 1;
                            unit = Some(l);
                        }
                        _ => {}
                    }
                }
                if sat {
                    continue;
                }
                if nun == 0 {
                    conflict = Some(ci);
                    break;
                }
                if nun == 1 {
                    self.assign_reason(unit.unwrap(), ci);
                }
            }
            self.occ[Prop::code(falsified)] = occ;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }
    fn backtrack(&mut self, to: usize) {
        while self.trail.len() > to {
            let v = self.trail.pop().unwrap();
            self.val[v] = 0;
        }
    }
}

impl SlratDb {
    fn new(s: usize, t: usize, m: usize) -> SlratDb {
        let mut db = std::collections::HashMap::new();
        for (i, c) in full_clauses(s, t, m).into_iter().enumerate() {
            db.insert(i as u64 + 1, c);
        }
        SlratDb { s, t, m, db, sr: Default::default() }
    }

    /// SR line `id r l1 .. lk 0 w1 .. wj 0 a1 b1 .. ap bp 0`: C = {l1..lk} is added to the SR tier when the
    /// substitution σ (var |w| := true/false for each witness literal w; var |a| := b (negated if a < 0) for each
    /// pair; identity elsewhere) satisfies: for every clause D of the database and for C itself, D|σ is satisfied
    /// or F ∧ ¬C derives D|σ by unit propagation (Buss–Thapen substitution redundancy; the DSR check of dsr-trim
    /// / sr2drat). Sound for satisfiability: if F has a model then so has F ∧ C (map a model falsifying C through σ).
    /// Returns the hints that let the Lean checker (and `sr_step_hinted`) redo the check without propagation.
    fn sr_step(&mut self, id: u64, lits: &[i32], witness: &[i32], pairs: &[i32]) -> Result<SrHints, String> {
        let nv = self.m * self.m.saturating_sub(1) / 2;
        if self.db.contains_key(&id) {
            return Err("id reused".into());
        }
        let sigma = sigma_of(nv, lits, witness, pairs)?;
        let mut prop = Prop::new(&self.db, nv);
        let present: std::collections::HashMap<Vec<i32>, u64> = prop
            .clauses
            .iter()
            .zip(&prop.ids)
            .map(|(c, &i)| {
                let mut s = c.clone();
                s.sort_unstable();
                s.dedup();
                (s, i)
            })
            .collect();
        // α = ¬C first (as the hinted checkers replay it), then the database units and propagation
        let mut alpha_confl = None;
        for &l in lits {
            if !prop.assign(-l) {
                // C is a tautology: accept it as RUP (its hints: none needed by the reference checker; the hinted
                // form asks for a RUP line, which the tautology check of `step` handles)
                self.db.insert(id, lits.to_vec());
                self.sr.insert(id);
                return Ok(SrHints::Rup(Vec::new()));
            }
        }
        alpha_confl = prop.init_units();
        if let Some(c) = alpha_confl {
            // C is RUP already: no substitution needed
            let hints = prop.conflict_hints(c, 0);
            self.db.insert(id, lits.to_vec());
            self.sr.insert(id);
            return Ok(SrHints::Rup(hints));
        }
        let alpha = prop.trail_hints();
        let base = prop.trail.len();
        let mut todo: Vec<(u64, Vec<i32>)> = Vec::new();
        let clauses = std::mem::take(&mut prop.clauses);
        for (d, &did) in clauses.iter().zip(&prop.ids).map(|(c, i)| (c, i)).chain(std::iter::once((&lits.to_vec(), &id))) {
            if let Some(r) = reduce_sigma(&sigma, d) {
                if r.iter().any(|&l| prop.lit_val(l) == 1) {
                    continue; // satisfied by α: ¬(D|σ) contradicts α
                }
                todo.push((did, r));
            }
        }
        prop.clauses = clauses;
        let mut groups: Vec<(u64, Vec<u64>)> = Vec::new();
        for (did, r) in todo {
            if let Some(&eid) = present.get(&r) {
                groups.push((did, vec![eid])); // D|σ is a clause of F: falsifying it is an immediate conflict
                continue;
            }
            let mut confl = None;
            for &l in &r {
                prop.assign(-l); // no literal of r is true under α, so this never fails
            }
            if r.is_empty() {
                // ¬(D|σ) is already a contradiction only if the database is dead, which was handled above
            } else {
                confl = prop.propagate(base);
            }
            let hints = confl.map(|c| prop.conflict_hints(c, base));
            prop.backtrack(base);
            match hints {
                Some(h) => groups.push((did, h)),
                None => return Err(format!("SR check fails: F ∧ ¬C does not derive the image {r:?} by unit propagation")),
            }
        }
        self.db.insert(id, lits.to_vec());
        self.sr.insert(id);
        Ok(SrHints::Sr { alpha, groups })
    }

    /// The hinted SR line (what the Lean checker implements): `id r lits 0 witness 0 pairs 0 ahints 0 (Did hints 0)* 0`.
    /// α' = ¬C extended by the unit hints `ahints`; then every clause D of the database in id order, and C itself,
    /// must have D|σ satisfied by σ (a literal mapped to true, or a tautology), or a literal true under α', or the
    /// next group `Did hints` with Did = D's id (C: the new id) whose hints derive a conflict from α' ∧ ¬(D|σ).
    fn sr_step_hinted(&mut self, id: u64, lits: &[i32], witness: &[i32], pairs: &[i32], alpha: &[u64], groups: &[(u64, Vec<u64>)], val: &mut [i8]) -> Result<(), String> {
        let nv = self.m * self.m.saturating_sub(1) / 2;
        if self.db.contains_key(&id) {
            return Err("id reused".into());
        }
        let sigma = sigma_of(nv, lits, witness, pairs)?;
        let mut trail: Vec<usize> = Vec::new();
        let mut set = |val: &mut [i8], trail: &mut Vec<usize>, l: i32| -> i8 {
            // make l true; returns the previous status of l (1 true, -1 false, 0 unassigned)
            let v = l.unsigned_abs() as usize;
            let cur = if l > 0 { val[v] } else { -val[v] };
            if cur == 0 {
                val[v] = if l > 0 { 1 } else { -1 };
                trail.push(v);
            }
            cur
        };
        let lv = |val: &[i8], l: i32| -> i8 {
            let v = l.unsigned_abs() as usize;
            if l > 0 {
                val[v]
            } else {
                -val[v]
            }
        };
        let mut res: Result<(), String> = Ok(());
        // α = ¬C (first assignment of a variable wins, as negAssign in Lean), then the α hints, each unit
        for &l in lits {
            set(val, &mut trail, -l);
        }
        let run_hints = |db: &std::collections::HashMap<u64, Vec<i32>>, val: &mut [i8], trail: &mut Vec<usize>, hints: &[u64], need_conflict: bool| -> Result<(), String> {
            for h in hints {
                let hc = db.get(h).ok_or_else(|| format!("hint {h} is not a known clause"))?;
                let (mut nun, mut unit, mut sat) = (0, 0i32, false);
                for &l in hc {
                    match lv(val, l) {
                        1 => {
                            sat = true;
                            break;
                        }
                        0 => {
                            nun += 1;
                            unit = l;
                        }
                        _ => {}
                    }
                }
                if sat {
                    return Err(format!("hint {h} is satisfied"));
                }
                if nun == 0 {
                    return if need_conflict { Ok(()) } else { Err(format!("hint {h} is falsified: C is RUP, use a RUP line")) };
                }
                if nun > 1 {
                    return Err(format!("hint {h} is not unit"));
                }
                set(val, trail, unit);
            }
            if need_conflict {
                Err("hints do not reach a conflict".into())
            } else {
                Ok(())
            }
        };
        if let Err(e) = run_hints(&self.db, val, &mut trail, alpha, false) {
            res = Err(format!("alpha hints: {e}"));
        }
        let base = trail.len();
        if res.is_ok() {
            let mut ids: Vec<u64> = self.db.keys().copied().collect();
            ids.sort_unstable();
            let mut g = 0usize;
            let c_vec = lits.to_vec();
            for (did, d) in ids.iter().map(|i| (*i, &self.db[i])).chain(std::iter::once((id, &c_vec))) {
                let Some(r) = reduce_sigma(&sigma, d) else { continue };
                if r.iter().any(|&l| lv(val, l) == 1) {
                    continue;
                }
                let Some((gid, hints)) = groups.get(g) else {
                    res = Err(format!("clause {did}: image {r:?} needs a hint group, none left"));
                    break;
                };
                if *gid != did {
                    res = Err(format!("clause {did}: image {r:?} needs a hint group, next group is for {gid}"));
                    break;
                }
                g += 1;
                for &l in &r {
                    set(val, &mut trail, -l);
                }
                let r2 = run_hints(&self.db, val, &mut trail, hints, true);
                while trail.len() > base {
                    let v = trail.pop().unwrap();
                    val[v] = 0;
                }
                if let Err(e) = r2 {
                    res = Err(format!("clause {did}: image {r:?}: {e}"));
                    break;
                }
            }
            if res.is_ok() && g != groups.len() {
                res = Err(format!("{} unused hint groups", groups.len() - g));
            }
        }
        for v in trail {
            val[v] = 0;
        }
        res?;
        self.db.insert(id, lits.to_vec());
        self.sr.insert(id);
        Ok(())
    }

    /// `id p lits 0`: RUP by full unit propagation; returns the hints of the conflict (for the hinted form) and
    /// whether the result is pure (no SR clause in the database could take part)
    fn rup_full(&mut self, id: u64, lits: &[i32]) -> Result<(Vec<u64>, bool), String> {
        let nv = self.m * self.m.saturating_sub(1) / 2;
        let mut prop = Prop::new(&self.db, nv);
        let mut taut = false;
        for &l in lits {
            if !prop.assign(-l) {
                taut = true;
            }
        }
        let confl = if taut { None } else { prop.init_units() };
        let hints = match confl {
            Some(c) => prop.conflict_hints(c, 0),
            None if taut => Vec::new(),
            None => return Err("not RUP: unit propagation does not reach a conflict".into()),
        };
        let pure = self.sr.is_empty();
        if !pure {
            self.sr.insert(id);
        }
        self.db.insert(id, lits.to_vec());
        Ok((hints, pure))
    }

    /// F(s,t,n) reduced under the assumption `a`: every literal whose negation is assumed is removed (clauses
    /// satisfied by the assumption are kept as they are), ids 1..|F| as in `full_clauses` (Lean: `reduceUnder`)
    fn new_under(s: usize, t: usize, n: usize, a: &[i32]) -> SlratDb {
        let neg: std::collections::HashSet<i32> = a.iter().map(|&l| -l).collect();
        let mut db = std::collections::HashMap::new();
        for (i, c) in full_clauses(s, t, n).into_iter().enumerate() {
            db.insert(i as u64 + 1, c.into_iter().filter(|l| !neg.contains(l)).collect());
        }
        SlratDb { s, t, m: n, db, sr: Default::default() }
    }

    /// an addition (`id lits 0 hints 0`; `id p lits 0` = RUP by full unit propagation, reference checker only) or
    /// image (`id i|f src p0 .. p{m-1} 0`) line; returns the added clause and whether it is pure (not SR tier)
    fn step(&mut self, toks: &[&str], edge: &[(usize, usize)], val: &mut [i8]) -> Result<(Vec<i32>, bool), String> {
        let (s, t, m) = (self.s, self.t, self.m);
        let id: u64 = toks[0].parse().map_err(|_| "bad id")?;
        if self.db.contains_key(&id) {
            return Err("id reused".into());
        }
        if toks.get(1) == Some(&"i") || toks.get(1) == Some(&"f") {
            let db = &mut self.db;
            let flip = toks[1] == "f";
            if flip && s != t {
                return Err("colour swap is only a symmetry when s = t".into());
            }
            let src: u64 = toks.get(2).ok_or("missing src")?.parse().map_err(|_| "bad src")?;
            if self.sr.contains(&src) {
                return Err("image of an SR-tier clause (symmetry breaking is not a symmetry)".into());
            }
            if toks.len() != 4 + m {
                return Err("image line has the wrong length".into());
            }
            let perm: Vec<usize> = toks[3..3 + m].iter().map(|x| x.parse().map_err(|_| "bad perm")).collect::<Result<_, _>>()?;
            if toks[3 + m] != "0" {
                return Err("image line must end with 0".into());
            }
            let mut seen = vec![false; m];
            for &p in &perm {
                if p >= m || seen[p] {
                    return Err("not a permutation".into());
                }
                seen[p] = true;
            }
            let c = db.get(&src).ok_or("unknown src")?;
            let img: Vec<i32> = c
                .iter()
                .map(|&l| {
                    let (a, b) = edge[l.unsigned_abs() as usize];
                    let w = evar(perm[a], perm[b]);
                    if (l > 0) != flip {
                        w
                    } else {
                        -w
                    }
                })
                .collect();
            db.insert(id, img.clone());
            return Ok((img, true));
        }
        let nv = m * m.saturating_sub(1) / 2;
        let prop_line = toks.get(1) == Some(&"p");
        let z = toks.iter().position(|&x| x == "0").ok_or("missing 0")?;
        let lits: Vec<i32> = toks[1 + prop_line as usize..z].iter().map(|x| x.parse().map_err(|_| "bad literal")).collect::<Result<_, _>>()?;
        if lits.iter().any(|&l| l == 0 || l.unsigned_abs() as usize > nv) {
            return Err("literal out of range".into());
        }
        if prop_line {
            if z != toks.len() - 1 {
                return Err("a propagation line is `id p lits 0`".into());
            }
        } else if toks.len() < z + 2 || toks[toks.len() - 1] != "0" {
            return Err("hints must end with 0".into());
        }
        let hints: Vec<u64> = if prop_line { Vec::new() } else { toks[z + 1..toks.len() - 1].iter().map(|x| x.parse().map_err(|_| "bad hint")).collect::<Result<_, _>>()? };
        if prop_line {
            // `id p lits 0`: RUP by full unit propagation (reference checker only); pure iff no SR clause could take part
            let (_, pure) = self.rup_full(id, &lits)?;
            return Ok((lits, pure));
        }
        let db = &mut self.db;
        // RUP with hints: assign the negation of the clause, then each hint must be unit (extend) or falsified (done)
        let mut trail: Vec<usize> = Vec::new();
        let mut conflict = false;
        let mut res = Ok(());
        for &l in &lits {
            let v = l.unsigned_abs() as usize;
            let want = if l > 0 { -1 } else { 1 };
            if val[v] == -want {
                conflict = true; // clause contains complementary literals: tautology, trivially sound
                break;
            }
            if val[v] == 0 {
                val[v] = want;
                trail.push(v);
            }
        }
        if !conflict {
            for hid in &hints {
                let Some(hc) = db.get(hid) else {
                    res = Err("unknown hint");
                    break;
                };
                let mut unassigned = None;
                let mut nun = 0;
                let mut sat = false;
                for &l in hc {
                    let v = l.unsigned_abs() as usize;
                    let x = if l > 0 { val[v] } else { -val[v] };
                    if x == 1 {
                        sat = true;
                        break;
                    }
                    if x == 0 {
                        nun += 1;
                        unassigned = Some(l);
                    }
                }
                if sat {
                    res = Err("hint clause satisfied");
                    break;
                }
                if nun == 0 {
                    conflict = true;
                    break;
                }
                if nun > 1 {
                    res = Err("hint clause not unit");
                    break;
                }
                let l = unassigned.unwrap();
                let v = l.unsigned_abs() as usize;
                val[v] = if l > 0 { 1 } else { -1 };
                trail.push(v);
            }
        }
        for v in trail {
            val[v] = 0;
        }
        res?;
        if !conflict {
            return Err("hints do not reach a conflict".into());
        }
        let pure = hints.iter().all(|h| !self.sr.contains(h));
        if !pure {
            self.sr.insert(id);
        }
        self.db.insert(id, lits.clone());
        Ok((lits, pure))
    }
}

/// Convert a DSR/PPR proof in the format of Heule's `sr2drat` / `dsr-trim` (`lemma.. pivot witness.. pivot a b .. 0`:
/// the lemma up to the first repeat of its first literal, then witness literals up to the second repeat, then
/// substitution pairs; a line without a repeat is a hint-less RUP lemma) over F(s,t,n) into SLRAT (`c slrat` header,
/// `id r ..` and `id lits 0 0` lines, ids after the |F| originals). Deletion lines are rejected.
pub fn sr_to_slrat(s: usize, t: usize, n: usize, sr: &str) -> Result<String, String> {
    let nf = full_clauses(s, t, n).len() as u64;
    let mut out = format!("c slrat {s} {t} {n}\n");
    let mut id = nf;
    for (ln, line) in sr.lines().enumerate() {
        let toks: Vec<&str> = line.split_whitespace().collect();
        if toks.is_empty() || toks[0] == "c" {
            continue;
        }
        if toks[0] == "d" {
            return Err(format!("line {}: deletions are not supported", ln + 1));
        }
        let lits: Vec<i32> = toks.iter().map(|x| x.parse::<i32>().map_err(|_| format!("line {}: bad literal {x}", ln + 1))).collect::<Result<_, _>>()?;
        if lits.last() != Some(&0) || lits.len() < 1 {
            return Err(format!("line {}: must end with 0", ln + 1));
        }
        let body = &lits[..lits.len() - 1];
        id += 1;
        if body.is_empty() {
            out.push_str(&format!("{id} p 0\n"));
            continue;
        }
        let pivot = body[0];
        let mut parts: Vec<Vec<i32>> = vec![vec![pivot]];
        for &l in &body[1..] {
            if l == pivot && parts.len() < 3 {
                parts.push(Vec::new());
            } else {
                parts.last_mut().unwrap().push(l);
            }
        }
        let fmt = |v: &[i32]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
        if parts.len() == 1 {
            out.push_str(&format!("{id} p {} 0\n", fmt(&parts[0])));
        } else {
            // PR/SR convention: the repeated pivot starts the witness and belongs to it (ω satisfies C)
            let mut witness = vec![pivot];
            witness.extend_from_slice(&parts[1]);
            let pairs: &[i32] = if parts.len() == 3 { &parts[2] } else { &[] };
            if pairs.len() % 2 != 0 {
                return Err(format!("line {}: odd substitution list", ln + 1));
            }
            out.push_str(&format!("{id} r {} 0 {} 0 {} 0\n", fmt(&parts[0]), fmt(&witness), fmt(pairs)));
        }
    }
    Ok(out)
}

/// The hinted conversion of a DSR/PPR proof: the same lines as `sr_to_slrat`, checked while converting, with the
/// hints the Lean checker needs (`id lits 0 hints 0` for RUP lemmas, the `r` form with α hints and one hint group
/// per clause whose image needs propagation). Returns the text and whether the empty clause was derived.
pub fn sr_to_slrat_hinted(s: usize, t: usize, n: usize, sr: &str) -> Result<(String, bool), String> {
    slrat_add_hints(&sr_to_slrat(s, t, n, sr)?)
}

/// Add hints to an SLRAT text whose lines are `id p lits 0` (hint-less RUP) and unhinted `id r lits 0 witness 0
/// pairs 0` (plus the header), e.g. the output of `sr_to_slrat` or of the SR generator (`monster sr-gen`): every line is
/// checked and rewritten with the hints the Lean checker needs. Returns the text and whether ⊥ was derived.
pub fn slrat_add_hints(plain: &str) -> Result<(String, bool), String> {
    let hdr: Vec<&str> = plain.lines().next().ok_or("empty proof")?.split_whitespace().collect();
    if hdr.len() != 5 || hdr[0] != "c" || hdr[1] != "slrat" {
        return Err("bad header".into());
    }
    let (s, t, n): (usize, usize, usize) = (hdr[2].parse().map_err(|_| "bad s")?, hdr[3].parse().map_err(|_| "bad t")?, hdr[4].parse().map_err(|_| "bad n")?);
    let mut main = SlratDb::new(s, t, n);
    let mut out = String::new();
    let mut empty = false;
    let fmt = |v: &[i32]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    let fmth = |v: &[u64]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    for (ln, line) in plain.lines().enumerate() {
        let toks: Vec<&str> = line.split_whitespace().collect();
        let err = |m: &str| format!("line {}: {m}", ln + 1);
        if toks.is_empty() || toks[0] == "c" {
            out.push_str(line);
            out.push('\n');
            continue;
        }
        let id: u64 = toks[0].parse().map_err(|_| err("bad id"))?;
        if toks.get(1) != Some(&"p") && toks.get(1) != Some(&"r") {
            return Err(err("only `p` and unhinted `r` lines can be given hints"));
        }
        let nums: Vec<i32> = toks[2..].iter().map(|x| x.parse().map_err(|_| err("bad literal"))).collect::<Result<_, _>>()?;
        let mut parts: Vec<Vec<i32>> = vec![Vec::new()];
        for &x in &nums {
            if x == 0 {
                parts.push(Vec::new());
            } else {
                parts.last_mut().unwrap().push(x);
            }
        }
        if (toks[1] == "p" && parts.len() != 2) || (toks[1] == "r" && parts.len() != 4) {
            return Err(err("line already hinted or malformed"));
        }
        let lits = parts[0].clone();
        if toks[1] == "p" {
            let (hints, _) = main.rup_full(id, &lits).map_err(|e| err(&e))?;
            out.push_str(&format!("{id} {} 0 {} 0\n", fmt(&lits), fmth(&hints)));
        } else {
            match main.sr_step(id, &parts[0], &parts[1], &parts[2]).map_err(|e| err(&e))? {
                SrHints::Rup(hints) => out.push_str(&format!("{id} {} 0 {} 0\n", fmt(&lits), fmth(&hints))),
                SrHints::Sr { alpha, groups } => {
                    let g: Vec<String> = groups.iter().map(|(did, h)| format!("{did} {} 0", fmth(h))).collect();
                    let line = format!("{id} r {} 0 {} 0 {} 0 {} 0 {} 0", fmt(&parts[0]), fmt(&parts[1]), fmt(&parts[2]), fmth(&alpha), g.join(" "));
                    out.push_str(&line.split_whitespace().collect::<Vec<_>>().join(" "));
                    out.push('\n');
                }
            }
        }
        if lits.is_empty() {
            empty = true;
        }
    }
    Ok((out, empty))
}

/// Reference checker for SLRAT (unverified, but independent of the solver; the specification the Lean checker
/// implements). Invariant: every main clause holds in every good colouring of K_n, and every clause of sub-instance
/// k = F(s',t',m) in every good colouring of K_m. Returns true iff the empty clause is derived in the main database.
/// Lines besides additions and images:
///   `o s' t' m`                         open the next sub-instance F(s',t',m), clauses 1..|F| as in `full_clauses`
///   `s k <addition or image line>`     a step inside sub-instance k (images permute its m vertices)
///   `id l k src v r|b e0 .. e{m-1} 0`  lift: id := e(C) ∨ (some edge v–e_x is not of the apex colour), C = clause src
///                                       of sub-instance k; needs (s,t) = (s'+1,t') for r, (s',t'+1) for b
///   `a l1 .. lk 0`                      open the next assumption sub-database: F(s,t,n) reduced under A = {l1..lk}
///                                       (non-zero literals); invariant: its clauses hold in every good colouring
///                                       that satisfies A
///   `u k <addition line>`              an LRAT step inside assumption sub-database k (no images there)
///   `u k d id1 .. idn 0`                forget clauses of assumption sub-database k (no later hint may name them)
///   `id a k src 0`                      close: main clause id := ¬A ∨ C, C = clause src of assumption sub-database k
pub fn check_slrat(text: &str) -> Result<bool, String> {
    check_slrat_last(text).map(|(e, _, _)| e)
}

/// `check_slrat`, also returning the last clause added to the main database and whether it is pure (holds in every
/// good colouring: what a lemma-mode proof establishes; an SR-tier clause is only satisfiability-preserving).
///   `id r l1 .. lk 0 w1 .. wj 0 a1 b1 .. ap bp 0`  SR addition to the main database (see `SlratDb::sr_step`)
///   `id p l1 .. lk 0`                              RUP by full unit propagation (no hints; reference checker only)
pub fn check_slrat_last(text: &str) -> Result<(bool, Option<Vec<i32>>, bool), String> {
    check_slrat_read(text.as_bytes())
}

/// Streaming form of the reference checker: reads the proof line by line, holds only the live databases.
pub fn check_slrat_read<R: std::io::BufRead>(r: R) -> Result<(bool, Option<Vec<i32>>, bool), String> {
    let mut lines = r.lines().map(|l| l.map_err(|e| e.to_string()));
    let hdr = lines.next().ok_or("empty proof")??;
    let h: Vec<&str> = hdr.split_whitespace().collect();
    if h.len() != 5 || h[0] != "c" || h[1] != "slrat" {
        return Err("bad header".into());
    }
    let (s, t, n): (usize, usize, usize) = (
        h[2].parse().map_err(|_| "bad s")?,
        h[3].parse().map_err(|_| "bad t")?,
        h[4].parse().map_err(|_| "bad n")?,
    );
    let mut main = SlratDb::new(s, t, n);
    let mut subs: Vec<SlratDb> = Vec::new();
    let nv = n * (n - 1) / 2;
    let mut edge = vec![(0usize, 0usize); nv + 1];
    for j in 1..n {
        for i in 0..j {
            edge[evar(i, j) as usize] = (i, j);
        }
    }
    let mut val = vec![0i8; nv + 1];
    let mut derived_empty = false;
    let mut last_main: Option<Vec<i32>> = None;
    let mut last_pure = true;
    // assumption sub-databases: (A, reduced F(s,t,n) plus what was derived in it)
    let mut asms: Vec<(Vec<i32>, SlratDb)> = Vec::new();
    for (ln, line) in lines.enumerate() {
        let line = line?;
        let toks: Vec<&str> = line.split_whitespace().collect();
        if toks.is_empty() || toks[0] == "c" {
            continue;
        }
        let err = |m: &str| format!("line {}: {m}", ln + 2);
        match toks[0] {
            "o" => {
                if toks.len() != 4 {
                    return Err(err("open line must be `o s t m`"));
                }
                let p: Vec<usize> = toks[1..4].iter().map(|x| x.parse().map_err(|_| err("bad sub-instance"))).collect::<Result<_, _>>()?;
                if p[2] > n {
                    return Err(err("sub-instance larger than K_n"));
                }
                subs.push(SlratDb::new(p[0], p[1], p[2]));
            }
            "a" => {
                if toks.len() < 2 || toks[toks.len() - 1] != "0" {
                    return Err(err("assumption line must be `a l1 .. lk 0`"));
                }
                let a: Vec<i32> = toks[1..toks.len() - 1].iter().map(|x| x.parse().map_err(|_| err("bad assumption literal"))).collect::<Result<_, _>>()?;
                if a.iter().any(|&l| l == 0 || l.unsigned_abs() as usize > nv) {
                    return Err(err("assumption literal out of range"));
                }
                let db = SlratDb::new_under(s, t, n, &a);
                asms.push((a, db));
            }
            "u" => {
                let k: usize = toks.get(1).ok_or_else(|| err("missing assumption sub-database"))?.parse().map_err(|_| err("bad assumption sub-database"))?;
                let (_, sub) = asms.get_mut(k).ok_or_else(|| err("assumption sub-database not open"))?;
                if toks.len() < 4 {
                    return Err(err("empty assumption step"));
                }
                if toks[2] == "d" {
                    // forget clauses (strict: every id must be a live clause; the Lean checker ignores unknown ids)
                    if toks[toks.len() - 1] != "0" {
                        return Err(err("deletion line must end with 0"));
                    }
                    for x in &toks[3..toks.len() - 1] {
                        let id: u64 = x.parse().map_err(|_| err("bad deletion id"))?;
                        if sub.db.remove(&id).is_none() {
                            return Err(err(&format!("deletion of unknown clause {id}")));
                        }
                    }
                    continue;
                }
                if toks[3] == "i" || toks[3] == "f" {
                    return Err(err("no image steps under an assumption"));
                }
                sub.step(&toks[2..], &edge, &mut val).map_err(|e| err(&e))?;
            }
            _ if toks.get(1) == Some(&"a") => {
                let id: u64 = toks[0].parse().map_err(|_| err("bad id"))?;
                if main.db.contains_key(&id) {
                    return Err(err("id reused"));
                }
                if toks.len() != 5 || toks[4] != "0" {
                    return Err(err("close line must be `id a k src 0`"));
                }
                let k: usize = toks[2].parse().map_err(|_| err("bad assumption sub-database"))?;
                let src: u64 = toks[3].parse().map_err(|_| err("bad src"))?;
                let (a, sub) = asms.get(k).ok_or_else(|| err("assumption sub-database not open"))?;
                let c = sub.db.get(&src).ok_or_else(|| err("unknown src in assumption sub-database"))?;
                let mut closed: Vec<i32> = a.iter().map(|&l| -l).collect();
                closed.extend_from_slice(c);
                if closed.is_empty() {
                    derived_empty = true;
                }
                last_main = Some(closed.clone());
                last_pure = true;
                main.db.insert(id, closed);
            }
            "s" => {
                let k: usize = toks.get(1).ok_or_else(|| err("missing sub-instance"))?.parse().map_err(|_| err("bad sub-instance"))?;
                let sub = subs.get_mut(k).ok_or_else(|| err("sub-instance not open"))?;
                if toks.len() < 3 {
                    return Err(err("empty sub-instance step"));
                }
                sub.step(&toks[2..], &edge, &mut val).map_err(|e| err(&e))?;
            }
            _ if toks.get(1) == Some(&"l") => {
                let id: u64 = toks[0].parse().map_err(|_| err("bad id"))?;
                if main.db.contains_key(&id) {
                    return Err(err("id reused"));
                }
                if toks.len() < 7 {
                    return Err(err("lift line too short"));
                }
                let k: usize = toks[2].parse().map_err(|_| err("bad sub-instance"))?;
                let src: u64 = toks[3].parse().map_err(|_| err("bad src"))?;
                let v: usize = toks[4].parse().map_err(|_| err("bad apex"))?;
                let red = match toks[5] {
                    "r" => true,
                    "b" => false,
                    _ => return Err(err("apex colour must be r or b")),
                };
                let sub = subs.get(k).ok_or_else(|| err("sub-instance not open"))?;
                if toks.len() != 7 + sub.m || toks[6 + sub.m] != "0" {
                    return Err(err("embedding must name exactly m vertices and end with 0"));
                }
                let emb: Vec<usize> = toks[6..6 + sub.m].iter().map(|x| x.parse().map_err(|_| err("bad embedding"))).collect::<Result<_, _>>()?;
                let ok_params = if red { s == sub.s + 1 && t == sub.t } else { s == sub.s && t == sub.t + 1 };
                if !ok_params {
                    return Err(err("sub-instance parameters do not match the apex colour"));
                }
                if v >= n {
                    return Err(err("apex out of range"));
                }
                let mut seen = vec![false; n];
                for &x in &emb {
                    if x >= n || x == v || seen[x] {
                        return Err(err("embedding not injective into K_n minus the apex"));
                    }
                    seen[x] = true;
                }
                let c = sub.db.get(&src).ok_or_else(|| err("unknown src in sub-instance"))?;
                let mut lifted: Vec<i32> = c
                    .iter()
                    .map(|&l| {
                        let (a, b) = edge[l.unsigned_abs() as usize];
                        evar(emb[a], emb[b]) * l.signum()
                    })
                    .collect();
                lifted.extend(emb.iter().map(|&x| if red { -evar(v, x) } else { evar(v, x) }));
                if lifted.is_empty() {
                    derived_empty = true;
                }
                last_main = Some(lifted.clone());
                last_pure = true;
                main.db.insert(id, lifted);
            }
            _ if toks.get(1) == Some(&"r") => {
                let id: u64 = toks[0].parse().map_err(|_| err("bad id"))?;
                let nums: Vec<i64> = toks[2..].iter().map(|x| x.parse().map_err(|_| err("bad number in SR line"))).collect::<Result<_, _>>()?;
                // lits 0 witness 0 pairs 0 [ahints 0 (Did hints 0)* 0]
                let mut parts: Vec<Vec<i32>> = vec![Vec::new()];
                let mut pos = 0;
                while parts.len() < 4 && pos < nums.len() {
                    let x = nums[pos];
                    pos += 1;
                    if x == 0 {
                        parts.push(Vec::new());
                    } else {
                        parts.last_mut().unwrap().push(i32::try_from(x).map_err(|_| err("literal out of range"))?);
                    }
                }
                if parts.len() != 4 {
                    return Err(err("SR line must be `id r lits 0 witness 0 pairs 0 [hints]`"));
                }
                if pos == nums.len() {
                    main.sr_step(id, &parts[0], &parts[1], &parts[2]).map_err(|e| err(&e))?;
                } else {
                    let take_ids = |pos: &mut usize| -> Result<Vec<u64>, String> {
                        let mut v = Vec::new();
                        loop {
                            let x = *nums.get(*pos).ok_or_else(|| err("unterminated hint list in SR line"))?;
                            *pos += 1;
                            if x == 0 {
                                return Ok(v);
                            }
                            v.push(u64::try_from(x).map_err(|_| err("bad hint"))?);
                        }
                    };
                    let alpha = take_ids(&mut pos)?;
                    let mut groups: Vec<(u64, Vec<u64>)> = Vec::new();
                    loop {
                        let x = *nums.get(pos).ok_or_else(|| err("unterminated hint groups in SR line"))?;
                        pos += 1;
                        if x == 0 {
                            break;
                        }
                        let did = u64::try_from(x).map_err(|_| err("bad group id"))?;
                        groups.push((did, take_ids(&mut pos)?));
                    }
                    if pos != nums.len() {
                        return Err(err("trailing tokens after the SR hint groups"));
                    }
                    main.sr_step_hinted(id, &parts[0], &parts[1], &parts[2], &alpha, &groups, &mut val).map_err(|e| err(&e))?;
                }
                if parts[0].is_empty() {
                    derived_empty = true;
                }
                last_main = Some(parts[0].clone());
                last_pure = false;
            }
            _ => {
                let (c, pure) = main.step(&toks, &edge, &mut val).map_err(|e| err(&e))?;
                if c.is_empty() {
                    derived_empty = true;
                }
                last_main = Some(c);
                last_pure = pure;
            }
        }
    }
    Ok((derived_empty, last_main, last_pure))
}

/// Catalogue-guided cube lemmas: for every admissible red degree d of vertex 0 and every catalogue pair (A, B), refute
/// the cube "vertex 0 red to 1..d (inducing A), blue to the rest (inducing B)" by an assumption solve. Each core
/// clause is a lemma of F (logged) and becomes a pattern, so any labelled copy of the cube is refuted by an image.
/// The catalogues are only HINTS: nothing here assumes they are complete; the final derivation of ⊥ must establish
/// coverage itself.
pub fn add_cube_lemmas(sv: &mut crate::sat::solver::Solver, s: usize, t: usize, n: usize, dir: &std::path::Path) -> Vec<String> {
    use crate::sat::solver::SolveResult;
    let mut out = Vec::new();
    let saved = sv.conflict_budget;
    sv.conflict_budget = u64::MAX;
    for d in 0..n {
        let m = n - 1 - d;
        if crate::catalog::mckay_count(s - 1, t, d) == Some(0) || crate::catalog::mckay_count(s, t - 1, m) == Some(0) {
            continue;
        }
        let (Ok(la), Ok(lb)) = (crate::catalog::load(dir, s - 1, t, d), crate::catalog::load(dir, s, t - 1, m)) else {
            out.push(format!("cubes d={d}: catalogue missing, skipped"));
            continue;
        };
        let t0 = std::time::Instant::now();
        let c0 = sv.stats.conflicts;
        let mut k = 0;
        for a in &la.graphs {
            for b in &lb.graphs {
                let mut cube = Vec::new();
                for i in 0..d {
                    cube.push(evar(0, 1 + i));
                }
                for j in 0..m {
                    cube.push(-evar(0, 1 + d + j));
                }
                for j in 1..d {
                    for i in 0..j {
                        let v = evar(1 + i, 1 + j);
                        cube.push(if a.has_edge(i, j) { v } else { -v });
                    }
                }
                for j in 1..m {
                    for i in 0..j {
                        let v = evar(1 + d + i, 1 + d + j);
                        cube.push(if b.has_edge(i, j) { v } else { -v });
                    }
                }
                match sv.solve_dimacs(&cube) {
                    SolveResult::Unsat if !sv.is_root_unsat() => {
                        let clause: Vec<u32> = sv.core.iter().map(|&l| l ^ 1).collect();
                        let id = if sv.lrat.is_some() { sv.last_lrat_id() } else { sv.proof_lemmas.saturating_sub(1) };
                        if let Some(pp) = sv.patterns.as_mut() {
                            pp.learn_forced(&clause, id);
                        }
                        k += 1;
                    }
                    SolveResult::Unsat => {}
                    r => out.push(format!("cube d={d}: {r:?} (a SAT cube means a counterexample candidate)")),
                }
            }
        }
        out.push(format!(
            "cube lemmas d={d}: {k} of {} refuted in {:.2}s / {} conflicts",
            la.graphs.len() * lb.graphs.len(),
            t0.elapsed().as_secs_f64(),
            sv.stats.conflicts - c0
        ));
        if std::env::var_os("MONSTER_VERBOSE").is_some() {
            eprintln!("{}", out.last().unwrap());
        }
    }
    sv.conflict_budget = saved;
    out
}

#[cfg(test)]
mod sr_tests {
    use super::*;

    /// Heule's 39-line SR proof of R(4,4) <= 18 (github.com/marijnheule/sr2drat, MIT) checks with our SR rule, and
    /// tampered versions do not.
    #[test]
    fn heule_r44_sr_proof_checks() {
        let sr = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/R_18_4_4.sr")).unwrap();
        let slrat = sr_to_slrat(4, 4, 18, &sr).unwrap();
        let (empty, _, pure) = check_slrat_last(&slrat).unwrap();
        assert!(empty && !pure, "the proof derives ⊥ in the SR tier");
        // flip the unit lemma -37 (vertex 1 has at most 8 red neighbours after sorting) to 37
        let m1 = sr.replacen("\n-37 -37 -37 ", "\n37 37 37 ", 1);
        assert_ne!(m1, sr);
        assert!(check_slrat_last(&sr_to_slrat(4, 4, 18, &m1).unwrap()).is_err());
        // drop the substitution of the first line (keep only the witness): no longer SR
        let first = sr.lines().next().unwrap();
        let toks: Vec<&str> = first.split_whitespace().collect();
        let short = format!("{} {} {} {} {} 0", toks[0], toks[1], toks[2], toks[3], toks[4]);
        let m2 = sr.replacen(first, &short, 1);
        assert!(check_slrat_last(&sr_to_slrat(4, 4, 18, &m2).unwrap()).is_err());
        // an image of an SR-tier clause is refused
        let mut m3 = slrat.clone();
        m3.push_str("99999 i 6121 1 0 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 0\n");
        assert!(check_slrat_last(&m3).is_err());
        // the hinted form (what the Lean checker takes): converted with hints, re-checked by the hinted path
        let (hinted, empty_h) = sr_to_slrat_hinted(4, 4, 18, &sr).unwrap();
        assert!(empty_h);
        let (empty, _, pure) = check_slrat_last(&hinted).unwrap();
        assert!(empty && !pure);
        assert!(sr_to_slrat_hinted(4, 4, 18, &m1).is_err(), "the flipped unit must fail while converting");
        // tamper with the hinted text itself: flip the -37 unit (its hints no longer reach a conflict)
        let unit37 = hinted
            .lines()
            .find(|l| {
                let t: Vec<&str> = l.split_whitespace().collect();
                t.get(1) == Some(&"r") && t.get(2) == Some(&"-37") && t.get(3) == Some(&"0")
            })
            .expect("SR unit -37 line")
            .to_string();
        let h1 = hinted.replacen(&unit37, &unit37.replacen(" r -37 0 ", " r 37 0 ", 1), 1);
        assert_ne!(h1, hinted);
        assert!(check_slrat_last(&h1).is_err());
        // drop one hint group of the first SR line
        let first = hinted.lines().nth(1).unwrap().to_string();
        let tk: Vec<&str> = first.split_whitespace().collect();
        let zs: Vec<usize> = tk.iter().enumerate().filter(|(_, &x)| x == "0").map(|(i, _)| i).collect();
        assert!(zs.len() > 5, "{first}");
        let cut = format!("{} {}", tk[..=zs[3]].join(" "), tk[zs[4] + 1..].join(" ")); // remove the first group
        let h2 = hinted.replacen(&first, &cut, 1);
        assert!(check_slrat_last(&h2).is_err());
        // the Lean checker joins in when it is built with the SR rule (probe: a one-line SR proof it must accept)
        let lean = std::path::Path::new("verified/.lake/build/bin/checker");
        let p = std::env::temp_dir().join(format!("monster-sr-{}.slrat", std::process::id()));
        let probe = {
            // F(3,3,3) (satisfiable) with the genuine SR line "edge 1 red" under the colour swap σ = (v ↦ -v):
            // a binary without the SR rule answers PARSE ERROR in lemma mode
            let nf = full_clauses(3, 3, 3).len() as u64;
            let (text, _) = slrat_add_hints(&format!("c slrat 3 3 3\n{} r 1 0 0 1 -1 2 -2 3 -3 0\n", nf + 1)).unwrap();
            assert!(text.lines().nth(1).unwrap().starts_with(&format!("{} r 1 0 0 1 -1 2 -2 3 -3 0 ", nf + 1)), "{text}");
            std::fs::write(&p, &text).unwrap();
            lean.exists() && std::process::Command::new(lean).arg("--lemma").arg(&p).output().map(|o| !String::from_utf8_lossy(&o.stdout).contains("PARSE ERROR")).unwrap_or(false)
        };
        if probe {
            for (text, want) in [(&hinted, true), (&h1, false), (&h2, false)] {
                std::fs::write(&p, text).unwrap();
                let out = std::process::Command::new(lean).arg(&p).output().unwrap();
                let so = String::from_utf8_lossy(&out.stdout);
                if so.contains("PARSE ERROR") {
                    eprintln!("Lean checker without the SR rule yet: skipping the Lean half of this test");
                    break;
                }
                assert_eq!(so.contains("VERIFIED UNSAT"), want, "Lean on the SR proof: {so}");
            }
            let _ = std::fs::remove_file(&p);
        }
    }

    #[test]
    fn hintless_rup_and_tiers() {
        // K_3 with no red K_2 (s = 2) and no blue K_3: F(2,3,3) is unsat; derive ⊥ by hint-less RUP
        let mut p = String::from("c slrat 2 3 3\n");
        let nf = full_clauses(2, 3, 3).len() as u64;
        p.push_str(&format!("{} p 0\n", nf + 1));
        let (empty, _, pure) = check_slrat_last(&p).unwrap();
        assert!(empty && pure);
        // a clause that is not RUP is rejected: F(3,3,3) is satisfiable
        let mut q = String::from("c slrat 3 3 3\n");
        q.push_str(&format!("{} p -1 0\n", full_clauses(3, 3, 3).len() as u64 + 1));
        assert!(check_slrat_last(&q).is_err());
    }
}
