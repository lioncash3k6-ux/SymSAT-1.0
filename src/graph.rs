//! Bit-packed graphs. Small side graphs (<= 32 vertices) use one u32 row per vertex; full colourings of K_N
//! (N <= 64) use u64 rows. "Edge" always means RED; a non-edge is BLUE.

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Graph {
    pub n: usize,
    pub adj: [u32; 32],
}

impl Graph {
    pub fn empty(n: usize) -> Graph {
        assert!(n <= 32);
        Graph { n, adj: [0; 32] }
    }

    pub fn from_g6(line: &str) -> Result<Graph, String> {
        let b = line.trim().as_bytes();
        if b.is_empty() {
            return Err("empty graph6 line".into());
        }
        if b[0] < 63 || b[0] > 126 {
            return Err(format!("bad graph6 header in {line:?}"));
        }
        let n = (b[0] - 63) as usize;
        if n > 32 {
            return Err(format!("graph6 n={n} > 32 not supported for side graphs"));
        }
        let need = (n * n.saturating_sub(1) / 2 + 5) / 6;
        if b.len() != 1 + need {
            return Err(format!("graph6 length mismatch for n={n} in {line:?}"));
        }
        let mut g = Graph::empty(n);
        let mut k = 0usize;
        for j in 1..n {
            for i in 0..j {
                let byte = b[1 + k / 6];
                if byte < 63 || byte > 126 {
                    return Err(format!("bad graph6 byte in {line:?}"));
                }
                if ((byte - 63) >> (5 - k % 6)) & 1 == 1 {
                    g.add_edge(i, j);
                }
                k += 1;
            }
        }
        Ok(g)
    }

    pub fn to_g6(&self) -> String {
        let n = self.n;
        let mut out = vec![(n as u8) + 63];
        let mut acc = 0u8;
        let mut k = 0usize;
        for j in 1..n {
            for i in 0..j {
                acc = (acc << 1) | self.has_edge(i, j) as u8;
                k += 1;
                if k % 6 == 0 {
                    out.push(acc + 63);
                    acc = 0;
                }
            }
        }
        if k % 6 != 0 {
            out.push((acc << (6 - k % 6)) + 63);
        }
        String::from_utf8(out).unwrap()
    }

    #[inline]
    pub fn has_edge(&self, i: usize, j: usize) -> bool {
        self.adj[i] >> j & 1 == 1
    }

    pub fn add_edge(&mut self, i: usize, j: usize) {
        self.adj[i] |= 1 << j;
        self.adj[j] |= 1 << i;
    }

    pub fn complement(&self) -> Graph {
        let mut g = Graph::empty(self.n);
        let full = mask(self.n);
        for i in 0..self.n {
            g.adj[i] = !self.adj[i] & full & !(1 << i);
        }
        g
    }

    pub fn edge_count(&self) -> usize {
        (0..self.n).map(|i| self.adj[i].count_ones() as usize).sum::<usize>() / 2
    }

    /// All `k`-subsets that are cliques (`red = true`) or independent sets (`red = false`), as bitmasks, in
    /// lexicographic order of their sorted vertex tuples (the order encode.py produces).
    pub fn sets(&self, k: usize, red: bool) -> Vec<u32> {
        let g = if red { self.clone() } else { self.complement() };
        let mut out = Vec::new();
        if k == 0 {
            out.push(0);
            return out;
        }
        fn rec(g: &Graph, k: usize, cur: u32, cand: u32, out: &mut Vec<u32>) {
            if cur.count_ones() as usize == k {
                out.push(cur);
                return;
            }
            let mut c = cand;
            while c != 0 {
                let u = c.trailing_zeros() as usize;
                c &= c - 1;
                // only vertices above u stay candidates, which keeps tuples increasing (lex order)
                rec(g, k, cur | 1 << u, c & g.adj[u], out);
            }
        }
        rec(&g, k, 0, mask(self.n), &mut out);
        out
    }

    /// Does the graph contain a red clique (`red`) or blue clique (`!red`) of size k?
    pub fn has_mono(&self, k: usize, red: bool) -> bool {
        let g = if red { self.clone() } else { self.complement() };
        fn rec(g: &Graph, need: usize, cand: u32) -> bool {
            if need == 0 {
                return true;
            }
            if (cand.count_ones() as usize) < need {
                return false;
            }
            let mut c = cand;
            while c != 0 {
                let u = c.trailing_zeros() as usize;
                c &= c - 1;
                if rec(g, need - 1, c & g.adj[u]) {
                    return true;
                }
            }
            false
        }
        rec(&g, k, mask(self.n))
    }

    /// (s,t)-good: no red K_s and no blue K_t.
    pub fn is_good(&self, s: usize, t: usize) -> bool {
        !self.has_mono(s, true) && !self.has_mono(t, false)
    }
}

impl std::fmt::Debug for Graph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Graph({} {})", self.n, self.to_g6())
    }
}

#[inline]
pub fn mask(n: usize) -> u32 {
    if n >= 32 {
        u32::MAX
    } else {
        (1u32 << n) - 1
    }
}

/// A full 2-colouring of K_N (N <= 64), used to independently re-check every SAT witness.
#[derive(Clone)]
pub struct BigGraph {
    pub n: usize,
    pub adj: Vec<u64>,
}

impl BigGraph {
    pub fn new(n: usize) -> BigGraph {
        assert!(n <= 64);
        BigGraph { n, adj: vec![0; n] }
    }

    pub fn set(&mut self, i: usize, j: usize, red: bool) {
        if red {
            self.adj[i] |= 1 << j;
            self.adj[j] |= 1 << i;
        } else {
            self.adj[i] &= !(1 << j);
            self.adj[j] &= !(1 << i);
        }
    }

    fn full(&self) -> u64 {
        if self.n == 64 {
            u64::MAX
        } else {
            (1u64 << self.n) - 1
        }
    }

    /// Brute-force search for a monochromatic K_k (red if `red`).
    pub fn find_mono(&self, k: usize, red: bool) -> Option<Vec<usize>> {
        let full = self.full();
        let rows: Vec<u64> = (0..self.n)
            .map(|i| if red { self.adj[i] } else { !self.adj[i] & full & !(1 << i) })
            .collect();
        fn rec(rows: &[u64], need: usize, cand: u64, cur: &mut Vec<usize>) -> bool {
            if need == 0 {
                return true;
            }
            if (cand.count_ones() as usize) < need {
                return false;
            }
            let mut c = cand;
            while c != 0 {
                let u = c.trailing_zeros() as usize;
                c &= c - 1;
                cur.push(u);
                if rec(rows, need - 1, c & rows[u], cur) {
                    return true;
                }
                cur.pop();
            }
            false
        }
        let mut cur = Vec::new();
        if rec(&rows, k, full, &mut cur) {
            Some(cur)
        } else {
            None
        }
    }

    pub fn to_g6(&self) -> String {
        let n = self.n;
        let mut out = vec![(n as u8) + 63];
        let mut acc = 0u8;
        let mut k = 0usize;
        for j in 1..n {
            for i in 0..j {
                acc = (acc << 1) | (self.adj[i] >> j & 1) as u8;
                k += 1;
                if k % 6 == 0 {
                    out.push(acc + 63);
                    acc = 0;
                }
            }
        }
        if k % 6 != 0 {
            out.push((acc << (6 - k % 6)) + 63);
        }
        String::from_utf8(out).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn g6_roundtrip_and_paley17() {
        // Paley(17): i~j iff i-j is a nonzero square mod 17. It is (4,4)-good.
        let sq: Vec<usize> = (1..17).map(|x| x * x % 17).collect();
        let mut g = Graph::empty(17);
        for i in 0..17 {
            for j in i + 1..17 {
                if sq.contains(&((j - i) % 17)) {
                    g.add_edge(i, j);
                }
            }
        }
        assert!(g.is_good(4, 4));
        assert!(!g.is_good(4, 3));
        let s = g.to_g6();
        assert_eq!(Graph::from_g6(&s).unwrap(), g);
    }

    #[test]
    fn sets_lex_order() {
        let g = Graph::empty(4).complement(); // K4
        let s = g.sets(2, true);
        let tup: Vec<Vec<usize>> = s
            .iter()
            .map(|&m| (0..4).filter(|&i| m >> i & 1 == 1).collect())
            .collect();
        assert_eq!(tup, vec![vec![0, 1], vec![0, 2], vec![0, 3], vec![1, 2], vec![1, 3], vec![2, 3]]);
    }
}
