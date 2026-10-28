//! Canonical labelling for small graphs (n <= 32): equitable-partition refinement plus individualisation search.
//! The canonical form is the lexicographically largest adjacency bit-string over all leaves of the search tree.
//! It is exact (no heuristics) because every leaf is a discrete partition reached by refining after individualising
//! each cell member, so isomorphic graphs explore isomorphic trees. Speed comes from refinement; Ramsey graphs
//! have small automorphism groups, so the tree stays small.
//!
//! Used only by the (untrusted) cover builder: a wrong canonical form can only produce a bad cover, which the
//! glue check then rejects pair by pair.

use crate::graph::Graph;

/// Canonical key: the adjacency upper triangle in canonical order, packed into 8 u64 words (n <= 32).
pub type Key = [u64; 8];

fn refine(g: &Graph, cells: &mut Vec<Vec<u8>>) {
    // split cells by the number of neighbours in each cell until stable
    loop {
        let mut changed = false;
        let mut k = 0;
        while k < cells.len() {
            let mut split_done = false;
            for wi in 0..cells.len() {
                let wmask: u32 = cells[wi].iter().fold(0, |m, &v| m | 1 << v);
                let cell = &cells[k];
                if cell.len() == 1 {
                    break;
                }
                let first = (g.adj[cell[0] as usize] & wmask).count_ones();
                if cell.iter().all(|&v| (g.adj[v as usize] & wmask).count_ones() == first) {
                    continue;
                }
                let mut c = cells[k].clone();
                c.sort_by_key(|&v| (g.adj[v as usize] & wmask).count_ones());
                let mut parts: Vec<Vec<u8>> = Vec::new();
                for v in c {
                    let d = (g.adj[v as usize] & wmask).count_ones();
                    match parts.last_mut() {
                        Some(p) if (g.adj[p[0] as usize] & wmask).count_ones() == d => p.push(v),
                        _ => parts.push(vec![v]),
                    }
                }
                cells.splice(k..k + 1, parts);
                changed = true;
                split_done = true;
                break;
            }
            if !split_done {
                k += 1;
            }
        }
        if !changed {
            break;
        }
    }
}

fn key_of(g: &Graph, order: &[u8]) -> Key {
    let n = g.n;
    let mut k = [0u64; 8];
    let mut bit = 0usize;
    for j in 1..n {
        for i in 0..j {
            if g.has_edge(order[i] as usize, order[j] as usize) {
                k[bit >> 6] |= 1 << (63 - (bit & 63));
            }
            bit += 1;
        }
    }
    k
}

/// Canonical key plus a labelling: `lab[i]` = the original vertex placed at canonical position i.
pub fn canon(g: &Graph) -> (Key, Vec<u8>) {
    let n = g.n;
    let mut cells: Vec<Vec<u8>> = vec![(0..n as u8).collect()];
    if n == 0 {
        return ([0; 8], vec![]);
    }
    refine(g, &mut cells);
    let mut best: Option<(Key, Vec<u8>)> = None;
    search(g, cells, &mut best);
    best.unwrap()
}

fn search(g: &Graph, cells: Vec<Vec<u8>>, best: &mut Option<(Key, Vec<u8>)>) {
    // first non-singleton cell (smallest first would be better; first is deterministic and isomorphism-invariant)
    match cells.iter().position(|c| c.len() > 1) {
        None => {
            let order: Vec<u8> = cells.iter().map(|c| c[0]).collect();
            let k = key_of(g, &order);
            if best.as_ref().map_or(true, |(bk, _)| k > *bk) {
                *best = Some((k, order));
            }
        }
        Some(ci) => {
            for idx in 0..cells[ci].len() {
                let mut c2 = cells.clone();
                let v = c2[ci].remove(idx);
                c2.insert(ci, vec![v]);
                refine(g, &mut c2);
                search(g, c2, best);
            }
        }
    }
}

/// Relabel g so that canonical position i holds original vertex lab[i].
pub fn relabel(g: &Graph, lab: &[u8]) -> Graph {
    let mut h = Graph::empty(g.n);
    for i in 0..g.n {
        for j in i + 1..g.n {
            if g.has_edge(lab[i] as usize, lab[j] as usize) {
                h.add_edge(i, j);
            }
        }
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invariant_under_relabelling() {
        let mut seed = 12345u64;
        let mut rnd = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let n = 4 + (rnd() % 10) as usize;
            let mut g = Graph::empty(n);
            for i in 0..n {
                for j in i + 1..n {
                    if rnd() % 3 == 0 {
                        g.add_edge(i, j);
                    }
                }
            }
            let (k1, lab) = canon(&g);
            assert_eq!(key_of(&g, &lab), k1);
            // random permutation
            let mut p: Vec<u8> = (0..n as u8).collect();
            for i in (1..n).rev() {
                p.swap(i, (rnd() % (i as u64 + 1)) as usize);
            }
            let h = relabel(&g, &p);
            let (k2, _) = canon(&h);
            assert_eq!(k1, k2);
        }
    }
}

#[cfg(test)]
mod catalog_tests {
    use super::*;
    #[test]
    fn catalogue_keys_distinct() {
        let dir = crate::catalog::default_dir();
        for (s, t, n) in [(4usize, 4usize, 8usize), (3, 5, 10), (4, 4, 15)] {
            let Ok(lv) = crate::catalog::load(&dir, s, t, n) else { continue };
            let mut keys: Vec<Key> = lv.graphs.iter().map(|g| canon(g).0).collect();
            keys.sort();
            let before = keys.len();
            keys.dedup();
            assert_eq!(keys.len(), before, "isomorphic duplicates or a non-canonical key in r{s}{t}/n{n}");
        }
    }
}
