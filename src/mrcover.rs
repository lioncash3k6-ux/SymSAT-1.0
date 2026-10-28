//! `monster cover-mr --d D --out DIR`: McKay–Radziszowski-style covers (RESULTS 2026-10-28, "what's left"): the A side
//! is covered by generalisations "(s-1,t,d-1)-graph + one free vertex" (vertex d-1 with all its d-1 edges gray), using
//! a small family of vertex-deleted subgraphs chosen greedily (most catalogue graphs hit first, sparser first on ties:
//! MR95 used 53 sparse (3,5,9)-graphs for d = 10); the B side is every catalogue graph itself (no gray edge). Files in
//! the v10 cover format, DIR/c{s-1}{t}_{d}_g{d-1}.txt and DIR/c{s}{t-1}_{m}_g0.txt, loadable by `Cover::load`, which
//! verifies pi(X) == instantiation for every catalogue graph. UNTRUSTED like every cover.

use crate::canon::canon;
use crate::catalog::Level;
use crate::graph::Graph;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;

/// X minus vertex v, vertices renumbered in order
fn delete_vertex(x: &Graph, v: usize) -> Graph {
    let mut h = Graph::empty(x.n - 1);
    let idx = |a: usize| if a < v { a } else { a - 1 };
    for a in 0..x.n {
        for b in a + 1..x.n {
            if a != v && b != v && x.has_edge(a, b) {
                h.add_edge(idx(a), idx(b));
            }
        }
    }
    h
}

/// the A cover text and its number of generalisations
pub fn vertex_deletion_cover(la: &Level) -> Result<(String, usize), String> {
    let d = la.n;
    let xs = &la.graphs;
    // candidates: canonical key of X - v -> list of (cat, v, lab)
    let mut by_key: HashMap<[u64; 8], Vec<(usize, usize, Vec<u8>)>> = HashMap::new();
    let mut edges_of: HashMap<[u64; 8], usize> = HashMap::new();
    for (cat, x) in xs.iter().enumerate() {
        for v in 0..d {
            let sub = delete_vertex(x, v);
            let (key, lab) = canon(&sub);
            edges_of.entry(key).or_insert_with(|| sub.edge_count());
            by_key.entry(key).or_default().push((cat, v, lab));
        }
    }
    // greedy set cover, sparse first on ties
    let mut covered = vec![false; xs.len()];
    let mut chosen: Vec<([u64; 8], Vec<(usize, usize, Vec<u8>)>)> = Vec::new();
    let mut assigned: Vec<Option<(usize, usize, Vec<u8>)>> = vec![None; xs.len()]; // (gen, v, lab)
    while covered.iter().any(|&c| !c) {
        let mut best: Option<([u64; 8], usize, usize)> = None; // key, hits, edges
        for (key, mem) in &by_key {
            let mut hit = 0;
            let mut seen = vec![false; xs.len()];
            for &(cat, _, _) in mem {
                if !covered[cat] && !seen[cat] {
                    seen[cat] = true;
                    hit += 1;
                }
            }
            if hit == 0 {
                continue;
            }
            let e = edges_of[key];
            if best.map_or(true, |(_, bh, be)| hit > bh || (hit == bh && e < be)) {
                best = Some((*key, hit, e));
            }
        }
        let (key, _, _) = best.ok_or("no candidate hits an uncovered graph")?;
        let gen_id = chosen.len();
        let mem = by_key[&key].clone();
        for (cat, v, lab) in &mem {
            if !covered[*cat] {
                covered[*cat] = true;
                assigned[*cat] = Some((gen_id, *v, lab.clone()));
            }
        }
        chosen.push((key, mem));
    }
    // emit: base = canonical G' (the first member's X - v relabelled) + isolated vertex d-1; gray edges (k, d-1)
    let mut out = String::new();
    let mut bases: Vec<Graph> = Vec::new();
    for (gid, (_, mem)) in chosen.iter().enumerate() {
        let (cat, v, lab) = &mem[0];
        let sub = delete_vertex(&xs[*cat], *v);
        let canon_sub = crate::canon::relabel(&sub, lab);
        let mut base = Graph::empty(d);
        for a in 0..d - 1 {
            for b in a + 1..d - 1 {
                if canon_sub.has_edge(a, b) {
                    base.add_edge(a, b);
                }
            }
        }
        let _ = write!(out, "G {gid} {}", d - 1);
        for k in 0..d - 1 {
            let _ = write!(out, " {k} {}", d - 1);
        }
        let _ = writeln!(out, " {}", base.to_g6());
        bases.push(base);
    }
    for (cat, x) in xs.iter().enumerate() {
        let (gid, v, lab) = assigned[cat].clone().ok_or("uncovered graph")?;
        // pi: X vertex -> gen vertex. lab[pos] = sub vertex at canonical position pos; sub vertex i = X vertex (i < v ? i : i+1)
        let mut pi = vec![0usize; d];
        for pos in 0..d - 1 {
            let sub_v = lab[pos] as usize;
            let xv = if sub_v < v { sub_v } else { sub_v + 1 };
            pi[xv] = pos;
        }
        pi[v] = d - 1;
        // t: gray edge k = (k, d-1) is red iff X has the edge (X vertex at canonical position k, v)
        let mut t = 0u64;
        for k in 0..d - 1 {
            let sub_v = lab[k] as usize;
            let xv = if sub_v < v { sub_v } else { sub_v + 1 };
            if x.has_edge(xv, v) {
                t |= 1 << k;
            }
        }
        let _ = write!(out, "A {cat} {gid} {t}");
        for a in 0..d {
            let _ = write!(out, " {}", pi[a]);
        }
        out.push('\n');
    }
    Ok((out, chosen.len()))
}

/// the trivial cover: every catalogue graph is its own generalisation, no gray edge
pub fn trivial_cover(lb: &Level) -> String {
    let m = lb.n;
    let mut out = String::new();
    for (j, g) in lb.graphs.iter().enumerate() {
        let _ = writeln!(out, "G {j} 0 {}", g.to_g6());
    }
    for j in 0..lb.graphs.len() {
        let _ = write!(out, "A {j} {j} 0");
        for a in 0..m {
            let _ = write!(out, " {a}");
        }
        out.push('\n');
    }
    out
}

pub fn write(la: &Level, lb: &Level, s: usize, t: usize, d: usize, out: &Path) -> Result<(usize, usize), String> {
    std::fs::create_dir_all(out).map_err(|e| format!("{}: {e}", out.display()))?;
    let (ta, na) = vertex_deletion_cover(la)?;
    let pa = out.join(format!("c{}{}_{d}_g{}.txt", s - 1, t, d - 1));
    std::fs::write(&pa, ta).map_err(|e| format!("{}: {e}", pa.display()))?;
    let m = lb.n;
    let pb = out.join(format!("c{}{}_{m}_g0.txt", s, t - 1));
    std::fs::write(&pb, trivial_cover(lb)).map_err(|e| format!("{}: {e}", pb.display()))?;
    // verify both by loading them (pi(X) == instantiation for every member)
    let ca = crate::cover::Cover::load(&pa, &la.graphs)?;
    let cb = crate::cover::Cover::load(&pb, &lb.graphs)?;
    println!(
        "cover-mr d={d}: A side {} graphs covered by {na} vertex-deletion generalisations ({} gray edges each) -> {}; B side {} graphs as themselves -> {}; units {}",
        la.graphs.len(),
        d - 1,
        pa.display(),
        lb.graphs.len(),
        pb.display(),
        ca.gens.len() * cb.gens.len()
    );
    Ok((ca.gens.len(), cb.gens.len()))
}
