//! Isomorph-free catalogues of (s,t)-good graphs, read from graph6 files laid out as `<dir>/r<s><t>/n<k>.g6`
//! (the layout of the repo's v5/catalogs). Every graph is re-checked to be (s,t)-good on load, and every level's
//! count is compared with McKay's published table.

use crate::graph::Graph;
use std::path::{Path, PathBuf};

/// McKay, "Combinatorial Data: Ramsey graphs" (counts of (s,t)-good graphs on n vertices up to isomorphism),
/// as recorded in the repo's v3-abandoned/ref/mckay_counts.json. Small trivial families are derived:
/// (2,t)-good on n vertices = the empty graph for n < t.
pub fn mckay_count(s: usize, t: usize, n: usize) -> Option<u64> {
    let (s, t) = if s <= t { (s, t) } else { (t, s) }; // complement symmetry
    if s == 1 {
        return Some(0); // nothing is (1,t)-good on n >= 1 vertices... (a single vertex is a red K_1)
    }
    if s == 2 {
        return Some(if n < t { 1 } else { 0 });
    }
    let tab: &[u64] = match (s, t) {
        (3, 3) => &[1, 2, 2, 3, 1],
        (3, 4) => &[1, 2, 3, 6, 9, 15, 9, 3],
        (3, 5) => &[1, 2, 3, 7, 13, 32, 71, 179, 290, 313, 105, 12, 1],
        (3, 6) => &[
            1, 2, 3, 7, 14, 37, 100, 356, 1407, 6657, 30395, 116792, 275086, 263520, 64732, 2576, 7,
        ],
        (4, 4) => &[
            1, 2, 4, 9, 24, 84, 362, 2079, 14701, 103706, 546356, 1449166, 1184231, 130816, 640, 2, 1,
        ],
        (3, 7) => {
            return match n {
                21 => Some(1118436),
                22 => Some(191),
                23.. => Some(0),
                _ => None,
            }
        }
        (4, 5) => {
            return match n {
                24 => Some(352366),
                25.. => Some(0),
                _ => None,
            }
        }
        _ => return None,
    };
    if n == 0 {
        return Some(1);
    }
    Some(tab.get(n - 1).copied().unwrap_or(0))
}

pub struct Level {
    pub s: usize,
    pub t: usize,
    pub n: usize,
    pub path: PathBuf,
    pub graphs: Vec<Graph>,
    pub g6: Vec<String>,
    pub mckay: Option<u64>,
}

impl Level {
    pub fn count_ok(&self) -> Option<bool> {
        self.mckay.map(|c| c == self.graphs.len() as u64)
    }
}

/// Load the catalogue of (s,t)-good graphs on n vertices. The trivial (2,t) family is synthesised.
pub fn load(dir: &Path, s: usize, t: usize, n: usize) -> Result<Level, String> {
    let path = dir.join(format!("r{s}{t}")).join(format!("n{n}.g6"));
    let mckay = mckay_count(s, t, n);
    if s == 2 || t == 2 {
        // (2,t)-good: no red edge and fewer than t vertices -> the empty graph; (s,2): complete graph, n < s
        let mut graphs = Vec::new();
        let k = if s == 2 { t } else { s };
        if n < k {
            let g = if s == 2 { Graph::empty(n) } else { Graph::empty(n).complement() };
            graphs.push(g);
        }
        let g6 = graphs.iter().map(|g| g.to_g6()).collect();
        return Ok(Level { s, t, n, path, graphs, g6, mckay });
    }
    if n == 0 {
        return Ok(Level { s, t, n, path, graphs: vec![Graph::empty(0)], g6: vec![String::new()], mckay });
    }
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut graphs = Vec::new();
    let mut g6 = Vec::new();
    for (ln, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let g = Graph::from_g6(line).map_err(|e| format!("{}:{}: {e}", path.display(), ln + 1))?;
        if g.n != n {
            return Err(format!("{}:{}: graph has {} vertices, expected {n}", path.display(), ln + 1, g.n));
        }
        graphs.push(g);
        g6.push(line.to_string());
    }
    // re-check goodness in parallel (cheap, but levels can hold 1.4M graphs)
    let threads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(1).min(16);
    let chunk = (graphs.len() + threads - 1) / threads.max(1);
    let bad = std::sync::atomic::AtomicUsize::new(usize::MAX);
    if chunk > 0 {
        std::thread::scope(|sc| {
            for (ci, part) in graphs.chunks(chunk).enumerate() {
                let bad = &bad;
                sc.spawn(move || {
                    for (k, g) in part.iter().enumerate() {
                        if !g.is_good(s, t) {
                            bad.fetch_min(ci * chunk + k, std::sync::atomic::Ordering::Relaxed);
                        }
                    }
                });
            }
        });
    }
    let b = bad.into_inner();
    if b != usize::MAX {
        return Err(format!("{}: graph #{} ({}) is not ({s},{t})-good", path.display(), b + 1, g6[b]));
    }
    Ok(Level { s, t, n, path, graphs, g6, mckay })
}

/// Default catalogue directory: the repo checkout next to us, if present.
pub fn default_dir() -> PathBuf {
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
    for cand in [
        "cascade-solver-ramsey-v4-algebraic/v5/catalogs",
        "cs-ramsey-algebraic/v5/catalogs",
    ] {
        let p = Path::new(&home).join(cand);
        if p.is_dir() {
            return p;
        }
    }
    PathBuf::from("catalogs")
}
