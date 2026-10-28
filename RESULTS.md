# Measured results (raw data in `results/<date>/`)

Machine: 16 vCPU Intel Xeon E3-12xx v2 (Ivy Bridge, KVM guest, about 15% steal), 62 GiB RAM, no AVX2. All timings are wall-clock with 16 workers unless noted.

## 2026-10-25

### Correctness ladder
Each rung ran `monster glue --route all --check-every 1`, so every task was certified by the independent RUP checker plus the glue check:

| R(s,t) | N | result | pairs | certified | time |
|---|---|---|---|---|---|
| R(3,3) | 5 / 6 | SAT (R>5) / UNSAT (R≤6) | 1 / 0 | all | 0.06 s |
| R(3,4) | 8 / 9 | SAT / UNSAT | 4 / 1 | all | 0.06 s |
| R(3,5) | 13 / 14 | SAT / UNSAT | 3 / 0 | all | 0.06 s |
| R(4,4) | 17 / 18 | SAT (Paley(17) pair) / UNSAT | 9 / 0 | all | 0.06 s |
| R(3,6) | 17 / 18 | SAT (17 witnesses) / UNSAT | 118 / 13 | all | 6.6 s / 0.6 s |
| R(3,7) | 23 | UNSAT | 2,583 | none (pair mode, 12 s) | 12 s |

Every SAT witness was rebuilt as a full colouring of K_N and brute-force checked.

### Encoder trust
`monster cnf` output is byte-identical (sha256) to the repo's `v6/scripts/encode.py` on 7 R(4,5) pairs, d=8..12.

### R(4,5) N=25, stage d=8 (358 pairs)
- Pair mode: all 358 pairs UNSAT in 135 s. Not certified in this run.
  Note: this run printed "R(4,5) ≤ 25", which was an overclaim bug. It is fixed: degree-restricted runs now report only the stage result.
- Stream mode: more than 2× slower (stopped at 57%).

### Engines on R(3,7) N=23 (2,583 pairs, no certification)
pair 12 s, stream 68 s. Stream mode (every streamed edge gray, plus a core cache) is a **measured negative**: its formula is 10–40× the pair formula.

### R(4,5) d=10: cost per pair
| engine | sample | conflicts/pair | CPU-s/pair |
|---|---|---|---|
| pair (fresh solver per catalogue pair) | 832 random pairs | 179,446 | 7.37 |
| unit (v10 covers c35_10_g6 × c44_14_g6, GAMMA solved whole) | 16 random units, 11,901 pairs | **3,079** | 0.47 (under contention; one unit took 2,422 s) |

For reference, v11 (CaDiCaL plus cubes) on its 206 production units averaged 3,500 conflicts/pair and 0.295 solve-s/pair on an 8-core box.
Gray-edge units are therefore essential for d=10 (pair mode would need years). monster's per-conflict speed on GAMMA
(about 7.5k conflicts/s/thread) is the next thing to improve.

### Solver speed against CaDiCaL 2.1.3 (repo-pinned commit f13d744), one GAMMA unit each, same box
| unit (d=10, v10 covers) | CaDiCaL | monster |
|---|---|---|
| (17,698), 64 pairs | 28.3 s, 487,897 conflicts | 26 s, 502,512 conflicts (16-way loaded box) |
| (10,3190), 40 pairs | 66.3 s, 897,341 conflicts | 72 s, 985,008 conflicts (16-way loaded box) |

### Degree-window axioms (every vertex's red degree in [7,13]), R(4,5) d=8, pair mode, 14 workers
| | conflicts/pair | CPU-s/pair | wall |
|---|---|---|---|
| baseline | 122,575 | 3.84 | 141 s |
| + degree axioms | 110,845 (−10%) | 5.18 (+35%) | 169 s |

### All-gray A × v10 B cover units, R(4,5) d=8, 2 tasks
Stopped after 37 min with more than 73 core-minutes spent; pair mode needs about 23 core-minutes. Measured negative.

### Fixed 24-unit d=10 benchmark (v11's own production units, covers_r2 A6B6, 18,218 pairs)
| engine | conflicts | conflicts/pair | note |
|---|---|---|---|
| v11 (CaDiCaL 2.1.3 + JW-lookahead cubes), from its results.jsonl | 37,789,389 | 2,074 | 2,076 solve-s on v11's 8-core box |
| monster whole-unit (no cubes, no vivification) | 65,131,959 | 3,575 | CPU time not comparable: the box was shared with other runs |

So on these units monster needs **1.72× the conflicts of v11**. Single-unit runs matched plain CaDiCaL, so the gap is
v11's cubing plus CaDiCaL's inprocessing. Vivification and cube fallback are being A/B'd next.

### Own cover builder (canonical labelling + greedy/star gray-edge selection)
| level | v10 cover | monster cover |
|---|---|---|
| r35/n10, gray ≤ 6 | 17 generalisations | **17** generalisations (1.1 s) |
| r35/n10, gray ≤ 4 | 39 | 47 (global greedy only) |
| r44/n14, gray ≤ 6 | 4,157 | 22,197 (greedy, holes allowed) → 44,166 (star) → 11,788 (v10 density rule) → **4,915** (grow from every seed + lazy greedy set cover, 2m42s) |
| r35/n10, gray ≤ 6, set cover | 17 | 22 |

Lesson from v10's code: a gray edge is accepted only if **every** instantiation is a catalogue graph. Dense
generalisations matter both for coverage and for GAMMA tightness.

## 2026-10-25 (night): direction change to ideas 1–3 (NS, pattern CDCL, symmetric SOS)

### Idea 1: Nullstellensatz on gluing pairs is a proved dead end
For R(4,5) d=8 pairs (128 cross variables), two-thirds of the axioms (blue K5 through cross edges) have degree 6.
**The axioms of degree ≤ 5 alone are satisfiable** (CaDiCaL, pairs 0 and 268), so no NS certificate of degree ≤ 5
exists, at any size. At degree 6 the NS system is about 1.6e8 rows × 5.7e9 columns per pair, against CDCL's ~4 s.
Without the S_n compression of the full formula, algebra cannot compete on pairs.

### cake_lpr verifies as you solve
CaDiCaL `--lrat` streamed through a FIFO into cake_lpr (CakeML, formally verified) on GAMMA unit (17,698):
solver about 28 s, checker done at 31.8 s with `s VERIFIED UNSAT`, 3.5 GB peak. monster needs LRAT hints to use it (todo).

### Idea 2: pattern CDCL (symmetric learning on the full K_N formula)
Learned clauses are stored as canonical forbidden 2-coloured patterns. Vertex-permuted images propagate lazily
(bitset embedding search anchored at the newest assigned edge). Proof: RUP lemmas plus `image(lemma, permutation)`
lines, checked by an independent checker that regenerates F from (s,t,N).

| full formula | CaDiCaL 2.1.3 | monster plain | monster pattern CDCL | proof |
|---|---|---|---|---|
| R(3,3)/K6 UNSAT | – | 35 conflicts | 16 conflicts | verified |
| R(3,4)/K9 UNSAT | – | 8,949 | **180** | verified |
| R(3,4)/K8 SAT | – | 43 | 11 | witness checked |
| R(3,5)/K14 UNSAT | **timeout 300 s (4.39M conflicts)** | timeout 120 s | **46 s, 40,737 conflicts** | **verified (8 s)** |
| R(4,4)/K17 SAT | – | 17,449 (0.1 s) | 4,679 (3.6 s) | witness checked |
| R(4,4)/K18 UNSAT | timeout 300 s (4.71M) | – | pending | |
| R(3,6)/K18 UNSAT | timeout 300 s (2.34M) | – | pending | |

On R(3,5)/K14 only 26 patterns were stored (40,707 rejected by the size/LBD/vertex caps), and the time is dominated
by embedding search (590M nodes). Both are the obvious next levers.

### Verification of pattern-CDCL proofs (two tiers)
1. **Symmetric checker** (`src/full.rs::check_symmetric`). It regenerates F from (s,t,N), RUP-checks every lemma,
   and checks every image line as perm(lemma), with perm a bijection. Linear cost; used on every run.
2. **cake_lpr** (CakeML, formally verified). The solver now emits LRAT with antecedent hints, and every symmetric
   image is expanded into a renamed copy of its source derivation, so cake_lpr checks plain LRAT against a CNF it
   can regenerate. No monster code is trusted.

| instance | mode | LRAT lines | cake_lpr |
|---|---|---|---|
| R(3,3)/K6 | plain | 43 | s VERIFIED UNSAT |
| R(3,3)/K6 | pattern CDCL | 70 (46 from image expansion) | s VERIFIED UNSAT |
| R(3,4)/K9 | plain | 8,973 | s VERIFIED UNSAT (0.13 s) |
| R(3,4)/K9 | pattern CDCL | 4,569,562 (expansion of 537 images) | s VERIFIED UNSAT (76 s) |

Verdict: the symmetric rule is confirmed by a formally verified checker. Expansion grows very fast (each image
re-derives its whole cone under a new permutation), so cake_lpr is the gold standard for small instances, and the
symmetric checker is used at scale.

### Where pattern-CDCL time goes (R(3,5)/K14, admission LBD ≤ 12)
959 conflicts, 1m30s, **474M embedding-search nodes**. Stored patterns average 8.5 vertices, 10.6 edges and
4.2 leaves. Placing leaves by matching after core backtracking: 1m07s, nodes unchanged (502M). So the cost is the
unassigned "slack" edge inside the pattern core, not the leaves. Next: signature (WL-invariant) indexing, or a strict
search on the pattern minus each edge.

Admission cap matters a lot: LBD ≤ 8 needed 40,737 conflicts; LBD ≤ 12 needed 959 (42× fewer).

### Pattern-CDCL speed-ups (R(3,5)/K14, LBD ≤ 12, symmetric proof verified every time)
| step | wall | search nodes | note |
|---|---|---|---|
| first version | 1m30s | 474M | 8,176 searches hit the node budget, so propagation was incomplete |
| + leaf placement after core | 1m07s | 502M | |
| + forward checking + Kuhn matching for leaves | 1m09s | **78M**, 0 budget cuts | propagation now complete; time unchanged |
| instrumentation | | | **61 s of 64 s was canonical labelling** of learned patterns |
| + twin pruning in canonical labelling (exact: twins swap by an automorphism) | **3.1 s** | 78M | **21× faster** |

From 46 s (first measurement, LBD ≤ 8) to 3.1 s. Plain CDCL did not finish in 120 s.

### Other repos checked (ESSENCE family, Sophyra), verdicts
- ESSENCE v4.5–v6.4 (CDCL in C++): standard techniques (blockers, LBD restarts, minimisation, VSIDS heap, phase
  saving, chronological backtracking, Thompson-sampling parameter bandit, "hyperbolic/spectral" perturbation
  restarts, an 8-thread portfolio). No proof output. Its "PR clause detection" adds binary clauses **without any
  witness or proof**, so it is not usable under the repo's rule that every claim must check.
- ESSENCE-COMPLETE exact-cover proof system: **unsound as an UNSAT certificate**. `verify_elimination` always
  returns true, choice lines are unchecked branch decisions with no requirement that every branch be closed, and
  the first conflict sets `verified = true`. A "proof" only shows that one partial assignment fails.
- Sophyra (SLS/CDCL hybrid, GPU walkers): SAT-side heuristics; no UNSAT certificates.
Nothing from these is adopted beyond CDCL basics monster already has.

### Inductive lemma library (2026-10-26)
Before the main solve, monster refutes a red star of size R(s-1,t) and a blue star of size R(s,t-1) at vertex 0 by
assumption solves in the same solver. Each core clause is a logged RUP lemma and is registered as a pattern, so its
images (the star at every vertex, on every leaf set) propagate. The Ramsey table only proposes k; nothing is trusted.
Theory: the Greenwood–Gleason recursion R(s,t) ≤ R(s-1,t)+R(s,t-1), with degree bounds as proved pattern lemmas.

| full formula | patterns only | + lemma library | proof |
|---|---|---|---|
| R(3,5)/K14 | 3.1 s, 983 conflicts | **0.5 s**, 1,226 conflicts | symmetric checker: VERIFIED |
| R(4,4)/K18 | not solved in 600 s | **2.2 s**, 1,491 conflicts | symmetric checker: VERIFIED |
(R(4,4) ≤ 18 was already certified by the gluing ladder; this is the full formula solved directly.)

## 2026-10-26 (night): hybrid mode, recursive library, propagation speed-ups

### Recursive rooted lemma library on K25 (R(4,5), proved inside the formula, verified, cached)
| lemma | meaning | before anchor filters | after |
|---|---|---|---|
| red book, 5 pages | red edge with 5 common red neighbours | 0.00 s | 0.00 s |
| blue book, 9 pages | blue edge with 9 common blue neighbours | 1.90 s | 0.21 s |
| mixed book (edge red), 9 | one root red, one blue to 9 leaves | 5.13 s | 0.12 s |
| mixed book (edge blue), 9 | | 0.02 s | 0.02 s |
| red star 14 | red degree ≤ 13 | 7.92 s | 0.04 s |
| blue star 18 | blue degree ≤ 17, i.e. red degree ≥ 7 | 434 s | 238 s (before matching generalisation) |
Together these prove inside F the red-degree window [7,13] that the gluing route takes as input. The library proof
(about 26k lines) is checked by the symmetric checker each time it is loaded (about 10 s).

### Embedding-search speed (K25, library loaded, 3,000 conflicts)
| change | wall | search nodes | budget cuts |
|---|---|---|---|
| core-first + leaf matching | 315 s | 2.30B | 20,038 (incomplete propagation) |
| + independent vertices (leaves, book pages) placed by one matching | **51 s** | 359M | **0** |
| + common-neighbour anchor filter | 43 s (box loaded) | 355M | 0 |

### Hybrid mode (full-formula pattern CDCL + catalogue cubes)
Correct on the ladder with every task certified: R(3,4) N=8/9, R(3,5) N=13/14, R(4,4) N=17/18, R(3,6) N=18 (UNSAT,
certified). R(4,5) d=8 production run in progress (results/overnight/hyb_d8).

### Verdicts
- R(3,6)/K18 as one formula: not solved in 900 s even with book lemmas. The recursion is not tight, so it needs
  cubes (hybrid mode solves it).
- LRAT expansion through cake_lpr: works and is formally verified for small cases (R(3,4)/K9 with the lemma library),
  but too large from R(3,5)/K14 up. The symmetric checker carries scale.

### Later the same night (all proofs verified by the symmetric checker)
| change | effect |
|---|---|
| twin independent vertices placed by counting | K25 nodes 355M → 126M; R(4,4)/K18 0.74 s |
| anchor only on twin-class representative edges (twin swaps are automorphisms) | K25 6000-conflict profile 69 s → **43 s**, calls 5.8M → 2.6M; R(3,5)/K14 0.24 s, R(4,4)/K18 0.59 s |
| incremental forward checking | small gain (62.5 → 60 s) |
| adaptive per-pattern throttle | negligible: patterns all yield 1e-4 to 1e-3, so nothing meets a safe threshold |
| common-neighbour anchor filter | ~7% fewer calls |

Hybrid R(4,5) d=8 (first 11 tasks): ~44k conflicts/pair (pair mode ~122k), ~600 s/pair (pair mode ~4 s).
Progress suite rows: bench/progress.jsonl.

### Does pattern memory compound across cubes? (hybrid R(4,5) d=8, 38 tasks / 76 pairs)
Conflicts per pair, per worker in task order (memory was reset once by a restart):
worker 10: 60.7k, 31.8k, 10.2k, 30.1k, 24.6k; worker 12: 35.2k, 32.8k, 23.9k; worker 14: 39.2k, 44.0k, 28.3k, 28.0k.
Average 38.6k/pair (first 16 pairs: 43.8k). **Verdict: mild compounding (~25–30%), far short of the ~100× needed to
beat pair mode on d=8 in wall time.** Pattern CDCL is the strongest engine on full formulas whose recursion is tight;
for R(4,5) gluing its per-conflict cost is still too high.

### One-sided cubes (hybrid --one-sided), certified ladder (every cube's proof checked)
| rung | result | wall |
|---|---|---|
| R(3,5) N=13 | SAT, witness verified | 0.8 s |
| R(3,5) N=14 | UNSAT | 0.4 s |
| R(4,4) N=17 | SAT, witness verified | 2m02s |
| R(3,6) N=17 | **not finished in 900 s** (8 workers) | |
| R(3,6) N=18 | **not finished in 900 s** | |
For R(4,5) the cube counts become d=8: 2, d=10: 313, d=12: 12 (pair counts 358 / 40.9M / 17.4M).
Lemma proofs now have a conflict budget (MONSTER_LEMMA_BUDGET, default 200k); unproved lemmas are skipped (sound).

Verdict so far: one-sided cubes leave a whole neighbourhood free, which for R(3,6) is about as hard as the single
R(3,6)/K18 formula (also unsolved in 900 s). Pair cubes solve R(3,6) N=18 in seconds. Warning sign for the R(4,5)
one-sided runs (d=8: 2 cubes, d=12: 12 cubes), which continue overnight; if they stall, the middle ground is
partial cubes (fix the small side plus part of the large side, e.g. by v10 gray-edge generalisations).

## 2026-10-26: SymSAT repo, Lean-verified checker, antisymmetry (colour swap)

### Lean 4 verified checker (verified/)
`MonsterVerified.check_sound`: if the checker accepts an SLRAT proof, every 2-colouring of K_n has a red K_s or a
blue K_t. Axioms: propext, Classical.choice, Quot.sound (no sorry, no custom axioms). The symmetry rule (S_n, and
S_n × Z_2 when s = t) is proved via "relabelling (and complementing) a good colouring gives a good colouring".
Negative tests (dropped hint, flipped literal, non-permutation, truncated proof, forged R(4,4) ≤ 17 header, wrong
formula, injected empty clause, colour-swap image in an s ≠ t proof): all rejected.

### Colour-swap antisymmetry for R(s,s) (patterns stored colour-swapped too; image lines `f`)
| instance | before | with colour swap | Lean checker |
|---|---|---|---|
| R(3,3)/K6 | 16 conflicts, 27-line proof | 4 conflicts, 19 lines | VERIFIED (also kernel-only theorem) |
| R(4,4)/K18 | 890 conflicts, ~0.4–0.6 s, 4,310 lines | **599 conflicts, 0.11 s, 2,371 lines** (497 colour-swap images) | VERIFIED |
R(3,4)/K9 and R(3,5)/K14 are unchanged (colour swap is not a symmetry when s ≠ t, and both checkers reject it there).

### Lemma library on K25 is now fast (cumulative effect of the embedding-search work)
R(4,5) library (red/blue books, mixed books, red star 14, blue star 18), proved inside F on K25:
blue star 18: 434 s (first version) → 238 s → **0.77 s**; whole library < 2 s. On K19 (the smallest graph where
the blue star lives) it takes 1.0 s, so importing lemmas proved on smaller graphs (injective-map image rule) is not
needed for speed now; it stays a sound generalisation for reuse across N.

### General rooted lemmas (red clique of a roots, blue clique of b roots, R(s-a,t-b) leaves; A–B edges free)
| instance | before (stars + books) | general rooted lemmas | Lean checker |
|---|---|---|---|
| R(3,5)/K14 | 1,136 conflicts, 0.21 s | 762 conflicts, 0.16 s, 2,033-line proof | VERIFIED |
| R(4,4)/K18 (with colour swap) | 599 conflicts, 0.11 s | **129 conflicts, 0.022 s, 689-line proof** | VERIFIED |

### Review checks (2026-10-26)
- `check_sound` axioms: propext, Classical.choice, Quot.sound only. Concrete theorems via native_decide additionally
  trust the Lean compiler; kernel-only: R(3,3) ≤ 6 done, R(4,4) ≤ 18 attempt running.
- The conclusion is the Ramsey statement on colourings; the formula is generated inside Lean with a soundness proof
  (6,120 clauses / 153 vars for K18, evaluated in Lean). Details: verified/SOUNDNESS.md.
- R(3,6)/K18 as one formula with general rooted lemmas: **not solved in 1,200 s** (colour swap does not apply; the
  recursion is not tight). Needs cubes or the local-symmetry rule.

## 2026-10-26: lift rule (local symmetry), verified
New SLRAT lines: `o s' t' m` opens a sub-instance with its own database, `s k <line>` runs a step inside it, and
`id l k src v r|b e0..e{m-1} 0` lifts a sub-instance clause into the main formula under an apex context. Soundness
is proved in Lean (`lift_sound`, `stepFn_ok`). `check_sound` still depends only on propext, Classical.choice and
Quot.sound. The Rust reference checker mirrors the rule.

Test proofs come from `monster lift-demo` (src/lift.rs) and follow R(s,t) ≤ R(s-1,t) + R(s,t-1). monster's own CDCL
refutes each sub-instance inside its database, with pattern CDCL there if `--patterns` is given. The empty clauses
are lifted to apex 0, and CDCL derives ⊥ from the lifted clauses. These test the rule; they are not new results.

| proof (`monster lift-demo ...`) | lines | sub-instance images / swaps | Lean checker |
|---|---|---|---|
| R(3,3) ≤ 6, `--s 3 --t 3 --n 6` | 34 | 0 / 0 | VERIFIED, also kernel-only |
| R(3,4) ≤ 10, `--s 3 --t 4 --n 10 --patterns` | 311 | 10 / **7 swaps inside the (3,3) sub-instance** | VERIFIED |
| R(3,5) ≤ 14, `--s 3 --t 5 --n 14 --patterns` | 3,996 (13,451 without sub-instance patterns) | 1,134 / 0 | VERIFIED |
| R(4,4) ≤ 18, `--s 4 --t 4 --n 18 --flip --patterns` | 63,243 (not committed, 1 s to regenerate) | 1,134 / 0 | VERIFIED |

The R(3,4) proof is the first in which the solver itself uses local symmetry: pattern CDCL in the symmetric (3,3)
neighbourhood sub-instance learns colour-swapped images, and the proof checks in Lean.

Negative tests: `monster lift-test --lean verified/.lake/build/bin/checker` (also run by `cargo test`). It covers
3 base proofs and 20 mutants. Each mutant must be rejected by both checkers, and the reference error must name the
reason. The mutants are: non-injective embedding, embedding containing the apex, embedding or apex outside K_n,
wrong apex colour (both directions), missing or extra context vertex, a main-only id as a sub-instance src, a
lemma from the wrong sub-instance, use of an unopened sub-instance, failed RUP inside a sub-instance, a sub-instance
below its Ramsey number, colour swap in an asymmetric sub-instance or main instance, a sub-instance image with a
K_n permutation or a non-permutation, a reused id, and a malformed open line. All pass, and there are 17 cargo tests.

Not done yet: `monster full` does not emit lift lines. The context is still m literals; see CONTINUE.md for the
descriptor and support-shrinking steps.

## 2026-10-26 09:20 UTC: current solve times (commit 07a4387, idle box)
Full formula, `monster full --patterns --lemmas --books --slrat FILE`; every UNSAT proof checked by the Lean checker:

| instance | result | time | conflicts | SLRAT lines | Lean check |
|---|---|---|---|---|---|
| R(3,3)/K6 | UNSAT | 0.000 s | 4 | 19 | VERIFIED, 0.00 s |
| R(3,4)/K9 | UNSAT | 0.003 s | 27 | 162 | VERIFIED, 0.00 s |
| R(3,5)/K14 | UNSAT | 0.164 s | 762 | 2,033 | VERIFIED, 0.05 s |
| R(4,4)/K18 | UNSAT | 0.021 s | 129 | 689 | VERIFIED, 0.03 s |
| R(3,3)/K5, R(3,4)/K8, R(3,5)/K13, R(4,4)/K17 | SAT | 0.000, 0.000, 0.298, 0.268 s | 1, 6, 757, 212 | | witnesses verified |

Stars only (`--lemmas` without `--books`): R(4,4)/K18 2,607 conflicts, 9.3 s (599 / 0.10 s before 1a60950).

| gluing / hybrid | result |
|---|---|
| R(3,6) ≤ 18, hybrid, `--check-every 1` | 13/13 pairs UNSAT, all certified, 2.5 s |
| R(3,7) ≤ 23, pair mode, `--chunk 64` | 12.1 s uncertified; **34.6 s with all 2,583 pairs certified** |
| R(3,7) ≤ 23, pair mode, default `--chunk 2048` | 107.8 s (only 3 tasks for 16 workers) |

R(4,5)/K25: the rooted-lemma library (11 lemmas; red degree in [7,13]) is proved inside F in 1.5 s, 23,069 conflicts.
The full R(4,5) formula is not solved. R(3,6)/K18 as one formula: not solved in 1,200 s.

## 2026-10-26: what happened to the lemmas (every lemma/pattern/solver commit re-measured)
Each commit built in a scratch worktree and run with the same flags (`full --patterns --lemmas --max-lbd 12 --proof`,
stars only or `--books`); conflict counts are deterministic, seconds on an idle box.

| commit (time UTC) | change | R(4,4)/K18 stars | R(4,4)/K18 books | R(3,5)/K14 stars | R(3,5)/K14 books |
|---|---|---|---|---|---|
| f761b79 (01:05) | recursive library (books, mixed books) | 1,491 (2.20 s) | 1,123 (0.90 s) | 1,226 | 1,149 |
| 1a906bc (01:07) | pattern anchors | 1,491 (1.34 s) | 1,123 (0.45 s) | 1,226 | 1,149 |
| 8d86c50 (01:27) | embedding: vertex cover + matching (complete propagation) | 1,098 | 1,341 | 1,236 | 915 |
| 61c09b3 (01:32) | anchor filter | 1,098 | 1,341 | 1,236 | 915 |
| ad8b523 (01:45) | twin placement | 890 (0.74 s) | 921 (0.30 s) | 1,136 | 1,090 |
| 9e3d4d7, 36f8cb8, bec9302 | forward checking, twin anchors, vivify | 890 (0.39 s) | 921 (0.18 s) | 1,136 | 1,090 |
| 8739f36 (03:17 auto-backup), fd99652 | WIP code swept in by cron, build fix | 890 | 921 | 1,136 | 1,090 |
| 0e7760a (03:56) | colour swap for R(s,s) | 599 (0.10 s) | 406 (0.08 s) | 1,136 | 1,090 |
| 1a60950 (04:10) | general rooted lemmas | **2,607 (9.3 s)** | **129 (0.021 s)** | 1,136 | 762 |
| 8cf47db (05:17 auto-backup) | untested cube lemmas, learn_forced 64 → 1024 edges | 2,607 | 129 | 1,136 | 762 |
| 07a4387, today's tree | Rust tooling; `--books` default | 2,607 (`--no-books`) | 129 | 1,136 | 762 |

(31d5975, the first star library, predates the RESULT line and is not comparable.) Verdicts:
- Nothing was lost; the books path improved at every lemma step. The auto-backups changed no counts.
- The stars-only jump at 1a60950 is **proof order**: with the red star proved first, stars only gives 599 again, and the
  same reorder makes the books path 713 instead of 129. R(4,4)/K18 therefore spans 129–2,607 conflicts on lemma order
  alone. Equivalent-propagation changes move counts both ways too (8d86c50: stars 1,491 → 1,098, books 1,123 → 1,341).
  Solve cost is chaotic in these choices; consistency needs the main search decoupled from the library's proof process.
- Stale caches: every `results/library_*.bin` predated 1a60950 and was still loaded (K25: 6 old lemmas instead of the
  current 11), because the cache was keyed only by (s,t,n). Fixed with a format tag; see CONTINUE.md 5a''.

## 2026-10-26 (late morning): library modes over relabellings, domain-based embedding search
### Library modes, 32 relabellings each (`monster bench --samples 32 --patterns --lemmas --lib MODE`), every run verified
Conflicts (median / p90 / max). Relabelling (a random vertex permutation, plus colour swap for odd seeds when s = t)
gives an equivalent formula, so the spread is pure solver variance. Raw: `results/bench/libmodes_2026-10-26.jsonl`.

| instance | inline | separate | lift | lift-inline |
|---|---|---|---|---|
| R(4,4)/K18 | 269 / 498 / **27,272** | 279 / 453 / 577 | **62 / 68 / 78** | 63 / 131 / 162 |
| R(3,5)/K14 | 628 / 786 / 845 | 639 / 775 / 856 | 53 / 59 / 62 | **42 / 48 / 52** |
| R(4,4)/K17 (SAT) | 684 / 1,494 / 3,603 | 749 / 913 / 1,012 | **539 / 632 / 732** | 5,972 / 65,838 / **152,077** |
| R(3,4)/K9 | **31 / 37 / 40** | 76 / 125 / 210 | 76 / 122 / 210 | 45 / 61 / 75 |

Verdicts: `lift` (library in its own solver, stars lifted from the sub-instances, imported in canonical order) removes
the heavy tail everywhere except the tiny R(3,4)/K9 and is now the default (`--lrat` still uses inline). `lift-inline`
has a catastrophic tail on satisfiable K17. Inline's K18 tail (27,272) is why single-run numbers were misleading. The
regression gate now runs seeds 0–3 and gates the worst. `lift` proofs pass the reference and Lean checkers
(R(3,3)/K6 .. R(4,4)/K18, seeds 0/3/8). K25 library: inline 23,069 conflicts / 1.46 s, lift 10,292 / 0.79 s.

### Domain-based embedding search (`DomSearch`, src/pattern.rs)
Incremental bitset domains per pattern vertex (strict and one-unassigned-edge candidates), degree-threshold initial
domains, empty-domain and slack checks, a Hall bound, smallest-domain-first branching. Cross-checked against the old
search on every call (`MONSTER_CHECK_EMBED=1`): no disagreement on 2.9M K25 calls or the small ladder.

| K25 profile, 6000 conflicts, cached library | old (`MONSTER_LEGACY_EMBED=1`) | domain search |
|---|---|---|
| propagation time | 34.4 s | 13.5 s |
| total | 39.1 s | 18.2 s |
| search nodes / embed calls | 283.8M / 2.86M (99 per call) | 205.7M / 2.94M (70 per call) |

Tried and dropped (deterministic node counts): candidate filter on edges to unused vertices (-0.2% nodes), most mapped
neighbours first (240M nodes), domain-size / mapped-neighbours ratio (207M).

### Domain search on the real hybrid workload; measurement harness
R(3,7)/K23 hybrid (`glue --route all --mode hybrid --chunk 32 --workers 7 --check-every 0`), both runs at the same
time, the same 12 tasks (359 pairs) compared: old embedding search 1,155 s, domain search 229 s (**5.0x**), conflicts
108,958 vs 110,071. The domain-search run then completed all 2,583 pairs (UNSAT, uncertified) in 3m54s of solving
(666,449 conflicts, 1,615 CPU-s). Both runs had first spent ~650 s re-verifying the 67 MB cached library; that is now
done once per library file (verification stamp, uncertified runs only).
From here on, full-run effects are measured with `monster ab` (paired task sample, verdict agreement checked,
bootstrap intervals, extrapolation to the full plan); rows accumulate in `bench/ab.jsonl`.

### R(4,5) d=8 standing sample, domain search vs old search (`monster ab`, 16 of 358 pairs, seed 1, 8+8 workers)
Verdicts agree on all 16 pairs (UNSAT). cand/base ratio of totals (95% bootstrap CI): **secs 0.321 (0.279–0.390)**,
conflicts 0.709 (0.590–0.891), search nodes 0.435 (0.366–0.533), embed calls 0.665 (0.567–0.826). Extrapolated
full d=8 run: **55.6 → 17.9 CPU-h** (3.5 h → 1.1 h at 16 workers). Raw: `results/ab/r45d8_domain_vs_legacy/`,
row in `bench/ab.jsonl`. This is the reference row for later changes on the target run.

### Incremental matching across assignments: two cheap forms measured, both negative (2026-10-26 ~13:30)
- **Exact memo of fruitless scans** (Zobrist hash of the colouring + literal + pattern count; deterministic search, so
  an exact repeat must fail again): only 0.8% of literal scans repeat on the K25 profile, ~1.2% on 4 R(4,5) d=8
  hybrid pairs. Reason: `sync` keeps the unchanged trail prefix and never rescans it, so restarts and replayed cube
  assumptions are already not searched twice. Removed.
- **Global candidate sets** (continuous-subgraph-matching / WL style: arc consistency over the whole colouring with
  one slack edge, recomputed per scan): rule out 19,277 of 2.94M embed calls (0.66%) holding 21,789 of 205.7M search
  nodes (0.01%), at 1.5 s to compute. An assertion confirmed no ruled-out call ever had an image (sound, just useless).
  The anchor filters (degrees, common neighbours by colour pair) already catch what local consistency catches; the
  searches that cost nodes fail deep, for global reasons (the one-unassigned-edge limit, distinctness). Removed.
- Conclusion: the per-literal anchored search is already a delta (semi-naive) evaluation with no exploitable
  repetition here. What remains is a Rete-style store of partial matches, whose size (embeddings of 5-vertex cores
  in a 25-vertex colouring) makes it unattractive, or cheaper deep search / fewer searches (per-pattern yield
  throttling, the RL #1 bandit): the top pattern (k=9, e=22) spends 77M of 206M nodes for 610 images.

## 2026-10-26 (afternoon): idea 3, flag-algebra / symmetric-SOS refutations with exact certificates (`monster flag`)
Finite-N flag SDP: variables are the densities p_H of the admissible K-vertex colouring classes; for every type σ
(m labelled vertices, m + 2ℓ = K) the matrix Σ_H p_H C_H^σ must be PSD, with exact rational coefficients for finite N
(hypergeometric overlap terms, src/flag.rs). CSDP (untrusted) finds PSD Y_σ with Σ_σ <C_H^σ, Y_σ> < 0 for all admissible
H; the certificate is re-checked in exact integer arithmetic with Y_σ = L Lᵀ, L the rounded Cholesky factor (PSD by
construction). Unit tests: class counts 1, 2, 4, 11, 34, 156, 1044 and the exact identity E_θ[v_θ v_θᵀ] = Σ_H p_H C_H^σ
on random colourings (to 1e-12).

| statement | K (flag order) | classes / types | time | result |
|---|---|---|---|---|
| R(3,3) ≤ 6 | 3 | 2 / 1 | 0.0 s | **certificate, exact check passed** (Goodman) |
| R(3,4) ≤ 9 | 5 (4 fails) | 9 / 4 | 0.0 s | **certificate, exact check passed** |
| R(3,5) ≤ 14 | 6 | 32 / 10 | 0.07 s | **certificate, exact check passed** (tight) |
| R(4,4) ≤ 18 | 6 | 84 / 12 | 0.28 s | **certificate, exact check passed** (tight) |
| R(4,4) ≤ 18 | 7 | 362 / 29 | 24 s | certificate, exact check passed |
| R(4,5) ≤ 25, 26, 27 | 6, 7 | 627 / 33 at K=7 | ~67 s | no certificate (optimum ≈ -1e-7 to -5e-8: at the boundary) |
| R(4,5) ≤ 28 | 7 | 627 / 33 | ~60 s | **certificate, exact check passed** |
Positive controls (good colourings exist): R(3,3) N=5 (K=3, 5), R(3,4) N=8 (K=6), R(3,5) N=13 (K=6, 7), R(4,4) N=17
(K=6, 7): no certificate in every case, as required. K=8 for R(4,5) N=25 is running (capped unit symsat-flag-r45-k8).

### Flag SDP with degree constraints (`--degree auto`: every red degree in [LO,HI] and integer), 2026-10-26 14:05
Localising blocks E_v[g(r_v) v vᵀ] ⪰ 0 for g = r-LO, HI-r, (r-LO)(HI-r) and (r-j)(r-j-1); exact union-size weights
(src/flag.rs `weight`), identity tested against direct E_v[r_v^q v vᵀ] on random colourings (q = 1, 2).
| instance | without degrees | with degrees [7,13] |
|---|---|---|
| R(4,5) N=25 K=6 | λ = -6.376e-6 | λ = -6.346e-6 |
| R(4,5) N=25 K=7 | λ = -1.386e-7 | λ = -1.150e-7 (stuck at the feasibility edge) |
| control R(4,5) N=24 K=7 (good colourings exist; degrees [6,13]) | | λ = -1.741e-7 |
Verdict: degree facts do not help, and at K ≤ 7 the SDP scores N = 24 (feasible) and N = 25 alike; its threshold
is N = 28. Regression: R(4,4) N=18 K=6 unchanged (λ = 3.274e-5); controls R(4,4) N=17 negative with and without degrees.

### How far the gluing route is (R(4,5) ≤ 25 needs stages d = 8, 10, 12 on the parity route)
- d=8: 358 pairs, ~17.9 CPU-h with the domain search (~1.1 h wall at 16 workers), uncertified (`monster ab` sample).
- d=10: the A6B6 gray-edge cover (v10 covers_r2) has 17 × 4,157 = 70,669 units. v11 (CaDiCaL + cubes) needed
  ~1.57M conflicts and ~86 core-s per unit on its 24-unit benchmark: ~1,690 CPU-h (~4.4 days at 16 cores); monster's
  unit mode needs ~2.7M conflicts per unit (~18 days at 7.5k conflicts/s/thread).
- d=12: 12 r35 graphs × the (4,4)-good graphs on 12 vertices (17.4M pairs); the A0B8 cover for that side was never
  finished (covers_r2/c44_12_g8.txt.log only).

### Flag SDP: what K=7 can and cannot refute for R(4,5) at N=25 (2026-10-26 ~14:30)
All runs K=7, 627 admissible classes; coefficients now computed exactly in integers and each block scaled by a power
of two for conditioning (the exact check multiplies the scales back in). Controls with --degree auto --parity at odd N
where good colourings exist (R(4,4) N=17, R(3,5) N=13, R(3,6) N=17): no certificate, as required.
| constraints (all valid for every good K25 colouring unless marked) | λ | result |
|---|---|---|
| degrees in [7,13] (theorems) | -1.15e-7 | no certificate |
| + exact degree distribution, x_j >= 0, handshake Σ_{j even} x_j >= 1/25 (`--parity`) | -1.64e-6 | no certificate |
| + case "no vertex of red degree 10" (`--exclude-degree 10`, half of a case split) | -1.29e-9 | no certificate |
| ASSUMPTION every red degree = 8 (`--degree 8,8`) | +1.18e-4 | refuted (assumption only) |
| ASSUMPTION every red degree = 10 | -4.86e-9 | not refuted |
| ASSUMPTION every red degree = 12 | +1.49e-6 | refuted (assumption only) |
Verdict: at K=7 the SDP keeps a fractional solution that looks 10-regular, and removing degree 10 leaves another one;
the flag route cannot settle any K25 case at K=7. d=10 is the hard core for both the SDP and the gluing route. K=8
(no degree blocks, old binary) has been in set-up since 13:45.

### R(4,5) d=10 engine decision, interim (`monster ab`, 16 of 70,669 A6B6 units, seed 1, 4+4 workers, box loaded)
| side | units done (14:45) | s / unit | conflicts / unit |
|---|---|---|---|
| unit mode (plain CDCL on the unit formula) | 9 | 417 | 2.29M |
| hybrid (pattern CDCL + library on the unit cubes) | 1 | 612 (same unit: unit mode 54.6 s) | 0.33M (same unit: 0.68M) |
Hybrid needs half the conflicts but ~11x the time on gray units: pattern search per conflict is too expensive here.
Unit mode extrapolates to ~8,200 CPU-h for the whole d=10 stage (~3 weeks on 16 cores, inflated by the shared box).
The final paired row lands in bench/ab.jsonl when the hybrid side finishes.

### Flag ladder for R(3,t) (2026-10-26 ~15:10), exact certificates, controls at N-1
| statement | K=6 | K=7 | control N-1, K=7 |
|---|---|---|---|
| R(3,6) <= 18 | no (λ = -4.6e-5) | **certificate, exact check passed** (2.3 s) | no certificate |
| R(3,7) <= 23 | (blue K7 invisible) | no (λ = -3.2e-6) | no certificate |
Tight by flags so far: R(3,3), R(3,4), R(3,5), R(4,4), R(3,6). R(3,7) needs K >= 8 (a blue K7 only just fits at K=7).

### d=12 cover, engine kill criterion, throttle and vertex vivification (2026-10-26 ~15:30)
- **d=12 cover built** (`monster cover --s 4 --t 4 --n 12 --gray 8`, 1 h 15 min, 9.5 CPU-h, self-checked on load):
  1,449,166 (4,4)-good graphs on 12 vertices -> **18,517 generalisations** (avg 78.3 members, max 256; v10 had 20,346).
  d=12 = 12 r35 graphs x 18,517 = **222,204 units**. A 16-unit unit-mode sample is running (results/ab/r45d12_unit_sample).
- **d=10 engine: kill criterion met.** Hybrid on gray units was 11x and 24x slower than unit mode on the two units both
  finished (half the conflicts), far outside "within 2-3x"; the hybrid side was stopped. Unit mode is the d=10 engine:
  14 units done, 536 s and 2.74M conflicts per unit on a shared box (spread 11 s to 2,243 s) -> ~10,500 CPU-h for d=10.
- **Node throttle** (`MONSTER_NODE_THROTTLE=X`: a pattern spending more than X search nodes per image is tried on 1
  anchor in 4). K25 profile (6,000 conflicts): off 205.7M nodes / 6,900 images; 100k: 134.2M / 5,828; 30k: 130.2M / 5,836;
  10k: 32.3M / 3,692. Whether the lost images cost conflicts needs complete solves: `monster ab` on the d=8 sample
  (throttle 30k vs off) is running (results/ab/r45d8_throttle30k).
- **Vertex vivification of patterns** (`MONSTER_PATVIV=1`: at root restarts, delete a pattern vertex while the shorter
  clause stays RUP by unit propagation; log it, store the smaller pattern, retire the old one): K25 profile, all 18
  stored patterns offered, **0 shrunk**. The stored patterns are vertex-minimal under unit propagation; a bounded-solve
  test (instead of BCP) is the stronger untried variant. Symmetric proofs still verify with it on.
- **Certified d=8 banking** started (`glue --d 8 --mode hybrid --check-every 1`, 4 workers, results/overnight/d8_certified):
  every task's proof is checked by the symmetric checker; 8/358 tasks after ~25 min, so many hours at this width.

### New angles, 2026-10-26 ~16:00 (user: "there has to be some angle on this we havent tried")
- **Minimum-degree case split + flags.** Choose vertex 0 as a vertex of minimum red degree δ (every colouring has
  one); then every vertex has degree >= δ. Catalogue sizes per δ: 71 / 358 / 185,600 / 40.9M / 124.3M / 17.4M pairs for
  δ = 7..12, δ = 13 impossible (25 x 13 odd). Flag SDP (K=7) on the cases: **[12,13] refuted** (exact certificate,
  margin 4.6e-5; would replace 17.4M pairs), **[11,13] not refuted** (also not with the handshake constraint), so the
  δ = 11 stage (124M pairs) stays and the route loses to the parity route. Also not refuted: "no vertex of degree 8 or
  10" with handshake (would have removed the d=12 stage). K=7 flags refute only extreme degree cases ({8}, {12}, [12,13]).
- **Lemma library as cardinality constraints in pair mode** (`--book-axioms`, `encode::pair_book_axioms`: for every
  vertex pair, red edge -> <= R(2,5)-1 = 4 common red neighbours, blue edge -> <= R(4,3)-1 = 8 common blue, and <= R(3,4)-1
  = 8 vertices red to u and blue to v; guarded by the root edge's colour when it is a cross edge). Soundness tests:
  equisatisfiability on SAT and UNSAT pairs, exact projection check (every valid cross assignment extends), and a
  mutant with dropped guards is caught. d=8 pair mode, 24 common pairs: **conflicts -21%, time x21** (encoding bloat).
  Even a native propagator would be capped near 1.27x: not the d=10 lever.
- **Running:** d=10 with the small side completely free (`--gray-a 99 --gray-b 6`): 4,157 units instead of 70,669;
  it wins if one unit costs less than ~17 A6B6 units (~9,000 s). results/ab/r45d10_allgrayA.

### Tails change the gluing estimate (2026-10-26 16:36)
- d=12 unit sample complete: 16 units, **485 s per unit** (first 14 averaged 57 s; two very slow units dominate) ->
  222,204 units ~ 29,900 CPU-h (~78 days on 16 cores).
- d=10 unit mode: 15 units, **961 s per unit** -> 70,669 units ~ 18,900 CPU-h (~49 days on 16 cores).
- Node throttle 30k, final paired d=8 sample (16 pairs): secs ratio 0.986 (95% CI 0.81-1.21), conflicts 1.33x:
  no gain on complete solves (the interim -30% was noise). Kept opt-in only.
- So the uncertified gluing route is ~4 months of this box; all its stages are heavy-tailed.

### Why symmetric learning stalls at scale (2026-10-26 ~17:00, `MONSTER_ADMIT=1` admission statistics)
| run (main conflicts) | kept as patterns | rejected (by: > 24 edges / LBD / vertices) | learned clauses spanning ALL vertices | pattern search share |
|---|---|---|---|---|
| R(3,6)/K18, VSIDS (30k) | 27 of 30,009 | 29,289 / 644 / 49 | 13,567 of 30,009 (18 of 18) | 218.5 s of 226 s |
| R(3,6)/K18, vertex-major (30k) | 28 of 30,009 | 29,745 / 186 / 47 | 16,680 of 30,009 | 75.3 s of 79.8 s |
| R(4,5)/K25 profile, VSIDS (6k) | 18 of 6,012 | 5,815 / 179 / 0 | peak at 22 of 25 vertices | 14.6 s of 20 s |
On tight Ramsey formulas CDCL learns global clauses (most span all or nearly all vertices), so there is little to share
across images, and searching for images of the few small patterns costs 94-97% of the run time. Vertex-major branching
(`MONSTER_BRANCH=vertex`: lowest unassigned edge variable first, i.e. finish vertices 0..j before j+1) is 2.8x faster per
conflict on R(3,6)/K18 (fewer embed calls) but does not make learning local. Small instances (library-dominated):
R(3,4)/K9 51 vs 267 conflicts, R(3,5)/K14 58 vs 46, R(4,4)/K18 236 vs 61 (vertex vs VSIDS); all proofs verified.
Consequence: the scalable form of the SymSAT idea is symmetric LEMMAS (deliberately local, proved once, applied to every
image: the library), not symmetric sharing of whatever CDCL learns.
Ladder, rest of the VSIDS vs vertex-major comparison (full formula, default library): R(3,6)/K17 (SAT): VSIDS 16.5 s,
24,762 main conflicts; **vertex-major 0.46 s, 125 main conflicts**. R(4,4)/K17 (SAT): VSIDS 0.97 s; vertex-major no
result in 900 s. So vertex-major is instance-dependent (36x faster on R(3,6)/K17, far slower on R(4,4)/K17 and 4x more
conflicts on R(4,4)/K18): a candidate for a portfolio, not a default.
- 17:49: d=10 unit-mode sample complete: 16 units, **1,316 s per unit** (heavy tail) -> ~25,800 CPU-h (~67 days on 16
  cores) for the whole d=10 stage. Break-even for the small-side-free variant (4,157 units): ~22,400 s per unit; its 4
  sample units have run 1 h 27 min without finishing. Certified d=8: 180/358 pairs, all checked UNSAT.

### Library-only patterns and lemma mining (2026-10-26 ~18:30)
Pattern sources (`MONSTER_ADMIT=1` now reports them): on R(3,6)/K18 (30k conflicts) the 18 learned patterns cost 4.95G
of 5.05G search nodes for 24,371 images, the 9 library lemmas 99.5M nodes for 19,338 images; on the K25 profile learned
patterns cost 165M of 206M nodes for 1,766 images. `MONSTER_LIBONLY=1` (only proved library lemmas are searched;
applied to the main or cube solvers after the library exists, never to the solvers that prove it):
| workload | all patterns | library only |
|---|---|---|
| R(3,6)/K18, 30k main conflicts | 228.5 s | 10.5 s (22x faster per conflict) |
| K25 profile, 6k conflicts | 19.8 s | 7.1 s |
| R(4,4)/K18 complete (main search) | 21 conflicts, 0.008 s | 12,986 conflicts, 0.67 s |
| R(3,6)/K17 complete (SAT) | 24,762 conflicts, 21 s | 696,872 conflicts, 127 s |
| R(4,4)/K17 complete (SAT) | 370 conflicts, 1.4 s | 823 conflicts, 0.13 s |
| **R(4,5) d=8 hybrid sample, 15 common pairs** | 694,532 conflicts, 3,400 s | **970,749 conflicts (1.39x), 575 s (0.16x)** |
Verdict: on full small formulas the learned patterns earn their cost; on the hybrid cubes (the R(4,5) workload) library
only is ~6x faster. Running: library-only hybrid on the 16-unit d=10 sample, compared with unit mode's stored results.
Lemma mining (`MONSTER_MINE=k,budget,tries,every`, `full::mine_lemmas`: sub-clauses of recent learned clauses on their k
densest vertices, refuted by bounded assumption solves in the same solver; proofs verified by the reference and Lean
checkers on R(3,4)/K9 with 10 mined lemmas): on library-free R(4,4)/K18 it cut main-search conflicts 596 -> 406 (k=6, 5
lemmas) and -> 344 (k=7, 30 lemmas) but spent ~28,000-31,000 conflicts mining (~50x the saving). Mining pays only when
amortised: mine once (e.g. for K25) and reuse across all cubes like the cached library.
Mining on library-free full formulas (complete solves, every proof verified; total conflicts include mining):
| instance | baseline | k=6 | k=7 | k=8 (budget 2000, 20 tries per 100 conflicts) |
|---|---|---|---|---|
| R(3,5)/K14 | 6,084, 3.07 s | 7,371, 4.2 s | 2,257, 1.6 s | **656, 0.19 s (16x), 20/20 mined** |
| R(4,4)/K18 | 596, 0.28 s | 28,492, 167 s | 31,110, 247 s | 31,333, 185 s |
| R(3,4)/K9 | 246, 0.12 s | 157, 0.05 s | 177, 0.06 s | 329, 0.15 s |
Strongly instance-dependent: big win when the sub-clause tests refute quickly (R(3,5)/K14), heavy loss when they are
expensive (R(4,4)/K18). Next: offline mining for K25, cached with the library and reused by every cube.

### 18:49 final rows
- **d=8 library-only, final paired row (16 pairs): time ratio 0.169 (95% CI 0.147-0.207), conflicts 1.55x; full d=8 run
  extrapolated 27.8 -> 4.7 CPU-h.**
- d=10 library-only hybrid vs unit mode, same units: 1/28 (3,392 pairs): unit 54 s / 0.68M conflicts, old hybrid 611 s,
  library-only hybrid 432 s / 0.75M; 2/2025 (1,209 pairs): unit 101 s / 1.05M, old hybrid 2,405 s, library-only hybrid
  344 s / 0.55M. Library-only is 1.4-7x faster than the old hybrid but still 3.4-8x slower than unit mode: unit mode
  stays the d=10 engine (run continuing for more units).
- K=8 flag SDP for R(4,5) N=25: set-up finished after ~5 h; SDPA input 1.0 GB; CSDP running (40G cap).

### 22:47 rows: d=10 engine settled, small side free loses, R(3,6)/K18 library-only unsolved
- **d=10 library-only hybrid vs unit mode** (same 16-unit A6B6 sample, seed 1, 4 workers each, static schedule;
  results/ab/r45d10_hybrid_libonly vs results/ab/r45d10_unit_vs_hybrid/base): 8 units finished, **every one slower**.

  | unit | unit mode | library-only hybrid | ratio |
  |---|---|---|---|
  | 0 | 669 s | 5,579 s | 8.3x |
  | 1 | 55 s | 432 s | 7.9x |
  | 2 | 1,585 s | 13,271 s | 8.4x |
  | 3 | 2,243 s | 8,644 s | 3.9x |
  | 4 | 100 s | 465 s | 4.7x |
  | 5 | 101 s | 344 s | 3.4x |
  | 6 | 139 s | 1,862 s | 13.4x |
  | 8 | 636 s | 1,288 s | 2.0x |
  | **total** | 5,528 s | 31,886 s | **5.8x** |

  Unfinished when stopped (22:47, after 15,579 s): unit 9 had run ~14,800 s (unit mode 462 s), unit 7 ~6,900 s
  (178 s), unit 12 ~8,200 s (6,913 s). Library-only hybrid needs fewer conflicts on some units (unit 4: 0.60M vs
  1.11M) but costs far more per conflict. **Unit mode stays the d=10 engine; library-only is for the d=8 hybrid.**
- **d=10 with the small side free (`--gray-a 99`, 4,157 units; results/ab/r45d10_allgrayA): negative.** None of the
  4 sample units finished in 23,095 s (16:22-22:47), past the ~22,400 s per unit at which it would beat the A6B6 cover
  (70,669 units x 1,316 s). Stopped.
- **R(3,6)/K18 as one formula, library-only, 1 h each: not solved**, with VSIDS or vertex-major branching (timeout,
  exit 124, before the counters print; peak memory 1.7 GB and 4 GB). R(3,6)/K18 stays open as one CDCL formula.
- Certified d=8 at 22:42: 342/358 pairs, all UNSAT, every proof checked; 25.1 CPU-h of task time so far (median
  179 s, max 2,959 s). At the server restart (2026-10-27 ~00:15): 357/358, all UNSAT and checked; only task 268 left
  (resume with `--resume`, CONTINUE.md 5-LATEST). The K=8 SDP was ended by the restart before CSDP finished.
- K=8 flag SDP (5,589 constraints, 128 blocks of size 45-64): CSDP had made ~13 iterations after 4.5 h, ~20 min each
  (estimated from its write count: monster saves CSDP's output only when it exits). Single core, reference BLAS.

### Feasible-cone engine prototype (`src/cone.rs`, `glue --mode cone`, uncertified), 2026-10-26 ~23:30
Correctness: agrees with brute force on 419 small pairs and with the CDCL pair encoding on 160 random larger pairs
(both verdicts), and reproduces R(3,3) = 6 and R(3,4) = 9 by gluing, under every option set.
| R(4,5) d=8 pair A#136 x B#0 (UNSAT) | nodes | time |
|---|---|---|
| forward checking only | 529M | 390 s |
| + degree windows | 638M | 562 s |
| + arc consistency | | > 600 s (stopped) |
| + degree windows + arc consistency | | > 549 s (stopped) |
| plain CDCL on the pair CNF (same pair) | 95,474 conflicts | 2.2 s |

**Cone reasoning inside CDCL** (`MONSTER_CONEPROP`, `cone::ConeProp`: per b the cones that agree with b's assigned
cross edges, filtered by one-hop support from every other b with an assigned edge; conflicts and implied edges come
back as clauses over the assigned edges of the vertices involved, greedily minimised; uncertified):
| pair | plain CDCL | CDCL + cone propagator | propagator output |
|---|---|---|---|
| d=8 A#136 x B#0 | 95,474 conflicts, 2.2 s | 79,572 (-17%), 3.8 s | 251 implied edges, 0 conflicts in 93k calls |
| d=10 A#0 x B#0 | 159,433, 4.0 s | 158,822, 36.5 s | 4,077 implied |
| d=10 A#100 x B#5000 | 84,281, 1.9 s | 46,760 (-45%), 7.7 s | 6,213 implied |
| d=10 A#200 x B#77777 | 66,861, 1.3 s | 73,750 (+10%), 11.4 s | 9,666 implied |
| d=10 A#312 x B#130000 | 95,993, 2.1 s | 81,832 (-15%), 15.0 s | 11,104 implied |
Without degree windows the counts are within a few percent of these. **Verdict: negative.** As a standalone search the
cone engine is >= 175x slower than CDCL (no learning: it re-derives the same small contradictions in every branch);
inside CDCL it cuts conflicts by ~11% on the d=10 pairs (-45% to +10%), so even a free propagator would gain little,
and this one makes the solve 2-8x slower. Unit propagation on the pair CNF already does most of what per-vertex
cone consistency adds; what makes the pairs hard is not local to one or two vertices of B. Both stay in as opt-in
switches (README); nothing else changes.

## 2026-10-27: where d=10 unit time goes; cube-and-conquer, stable mode and vivification on single units
Box idle except two background jobs; every run `glue --mode unit --covers results/covers_r45 --gray-a 6 --gray-b 6 --workers 1
--check-every 0 --units FILE`, whole unit (`--unit-budget` MAX unless cubing). Conflict counts are deterministic.
- **Unit size** (`monster gamma`): units (8,1487), (15,1042), (13,3857), (1,28) have 151 / 152 / 147 / 152 variables and
  4,506 / 4,851 / 4,944 / 4,906 clauses of average length 5.7-5.9. The hard units need 17M conflicts on ~150 variables.
- **Conflict rate falls with the conflict count** (learnt-clause database growth): unit (1,28) 684k conflicts in 40.2 s
  (17k/s), unit (7,2559) 2.64M in 386 s (6.8k/s, box partly loaded), units 12 and 15 of the sample 17M in ~6,900 s
  (2.5k/s, loaded box, 4 workers). A per-second trace of unit (8,1487) is being recorded (CONTINUE.md 5-LATEST+1).

| unit | baseline | `--stable` | `--vivify` | cube 1k | cube 2k | cube 5k | cube 5k + vivify | cube 20k | cube 50k | cube 100k |
|---|---|---|---|---|---|---|---|---|---|---|
| (1,28) conflicts / s | 683,802 / 40.2 | 631,482 / 37.5 | 583,195 / 33.3 | 563,818 / 29.3 | 469,862 / 22.4 | **441,349 / 20.1** | 439,071 / 19.6 | 550,150 / 24.6 | 567,274 / 28.4 | 635,382 / 33.0 |
| (7,2559) conflicts / s | 2,635,977 / 386 | 2,918,046 / 496 | 2,919,083 / 548 | | | | | **1,843,062 / 166** | | |
| (13,3857) conflicts / s | 254,986 / 9.9 | | | | | **226,763 / 7.8** | | | | |

(cube B = `--unit-budget B --cube-budget B`: solve B conflicts, then lookahead-split and recurse inside the same solver,
learned clauses kept; cube 20k + vivify + stable on (1,28): 530,506 / 29.4 s.) Verdicts so far: cube-and-conquer 1.3-2.3x
on these three units; `--stable` negative on both units tried; `--vivify` mixed (-17% time on (1,28), +42% on (7,2559)).
Decided by the paired 16-unit sample (`symsat-ab-d10-cube5k`, `symsat-ab-d10-cube5k-viv`; rows land in bench/ab.jsonl).
Early paired rows show cubing is not better on every unit (unit 4: 1.53M vs 1.11M conflicts; unit 0: 2.69M vs 3.67M).
- `monster flag`: set-up parallelised (`--threads`), `--reuse-sol`; R(4,4)/K18 K=6 and R(3,5)/K14 K=6 certificates re-verified.
- **Is the heavy tail solver variance?** No, on the units tried. `MONSTER_PHASE_SEED=S` (pseudo-random initial phases
  instead of all-blue, a semantics-preserving perturbation): unit (1,28) 683,802 (default) / 576,942 / 599,224 / 622,669
  conflicts for seeds 1-3; unit (13,3857) 254,986 / 240,800 / 246,524. A spread of about 15%, against a 150x spread
  between units of the sample (11 s to 6,913 s). The tail is in the units, so a per-unit portfolio over seeds would not pay;
  splitting the hard units (cubing) or making every conflict cheaper would.

### 2026-10-27 ~01:50: hinted certification, failed literals, learnt length, vivify A/B, d=7 stage
- **Certification was 65x the solve time.** Unit (13,3857) with cube 5k: 8.4 s uncertified, 546 s with `--check-every 1`
  (the hint-free RUP checker re-propagates over the whole database for each of 225k lemmas). Pair and unit modes now
  log LRAT with antecedent hints and are checked by the new independent `HintChecker` (src/sat/checker.rs, linear in
  the proof): the same unit certifies in **9.7 s** (cube 5k), 9.0 s (cube 20k), and 144 s on the pair-by-pair path
  (1.48M conflicts, uncertified 143 s). R(3,6) N=18 pair mode, all 13 pairs certified: 0.1 s. A bug found by the
  checker and fixed: `analyze_final` logged a core clause without hints when the failed assumption was already false at
  the root (hint = its root unit). Tests: `hinted_proofs_check` (PHP proof, assumption cores, root-false assumption,
  dropped hint and forged unit rejected); all 33 tests pass.
- **Failed-literal learning in the cuber** (`lookahead_pick`: a probe that conflicts yields the RUP clause ¬l ∨ ¬prefix,
  logged and added): sound (certified runs pass) but rare here: 0, 3, 4, 1 failed literals on units (1,28), (13,3857),
  (7,2559) at 5k and 20k; conflicts within 1% of cubing without it. Kept (free), not a lever.
- **Learnt clause length** (`lits` / `conflicts` in tasks.jsonl, new fields): 15.3 on (1,28), 14.2 on (13,3857), 17.4 on
  (7,2559) under cube 5k.
- **Vivify A/B on the 16-unit d=10 sample (cube 5k vs cube 5k + `--vivify`, 3+3 workers): neutral.** secs ratio 1.028
  (95% CI 0.931-1.137), conflicts 1.027 (0.957-1.093), verdicts agree. Cube 5k alone: 5,544 s and 38.5M conflicts for
  the 16 units (the whole-unit run of 2026-10-26 took 21,058 s / 70.7M conflicts on a comparably loaded box; the paired
  row is still running). Vivify stays off.
- **d=7 stage of R(4,5) N=25 (route all): 71 pairs, all UNSAT, every pair certified** (`results/overnight/d7_certified`;
  8 pairs by the RUP checker before the change, 63 by the hint checker; ~84k conflicts per pair). A stage result only.
- `monster cover` for d=9: r35/n9 290 graphs -> 23 generalisations, r44/n15 640 graphs -> 69; d=9 = 1,587 units. The
  certified d=9 run (unit mode, cube 5k, 4 workers) does ~70 s per unit so far.

### 2026-10-27 ~02:20: conflict-rate decay measured; reduce-fraction knob; jobs trimmed; the d=7,8,9 run
- **Conflict rate on the hardest d=10 unit (8,1487), 1 worker, loaded box, live dashboard sampled every 5 min:**
  6,632 → 5,622 → 4,391 → 3,762 → 3,658 → 3,452 → 2,961 → 2,590 → 2,556 → 2,874 → 2,647 → 2,644 → 1,990 → 1,277 → 1,547 →
  1,734 → 1,508 → 1,516 → 1,507 → 1,348 → 1,205 → 1,574 → 1,688 → 1,754 → 1,810 → 1,921 → 1,977 → 1,861 → 1,815 → 1,874 →
  1,607 → 1,766 → 1,822 → 1,715 conflicts/s (stopped after 2 h 50 min, unfinished): a 4x decay as the learnt database grows.
- **`MONSTER_REDUCE_DROP=P`** (new opt-in: drop P% of the local learnt tier per reduction, default 50), cube 5k, 1 worker:

  | unit | 50% | 75% | 90% |
  |---|---|---|---|
  | (7,2559) | 1,709,159 conflicts / 157 s | 1,804,458 / 112 s | **1,717,122 / 90 s** |
  | (1,28) | 441,349 / 20.1 s | 494,814 / 22.4 s | 676,837 / 26.9 s |

  Hard units gain 1.75x at equal conflicts (cheaper conflicts), easy units lose a little; the sample decides
  (`symsat-ab-d10-drop90`, cube 5k with 90% vs 50%, row in bench/ab.jsonl).
- Stopped as redundant (user-approved): `symsat-d8-certified` (hybrid, 3+ h on its last pair; d=8 is redone inside the
  combined run), `symsat-trace-u8` (data above), `symsat-d9-certified` (its 214 finished units were carried into the
  combined run by `--resume`). **Combined certified run `symsat-mindeg-d789`**: stages d = 7, 8, 9 in unit mode (own
  covers: d=7 8x1, d=8 15x2, d=9 23x69 generalisations), cube 5k, every unit certified by the hint checker, 6 workers,
  one `results/overnight/mindeg_d789/summary.json` for the whole gluing half of the minimum-degree route.
- **Reduce drop 90% vs 50%, paired 16-unit d=10 sample (cube 5k both sides, 2+2 workers, verdicts agree): secs ratio
  0.554 (95% CI 0.493-0.624), conflicts 1.054 (0.945-1.157); wall 2,694 s -> 1,474 s; extrapolated d=10 stage 2,965 ->
  1,642 CPU-h.** Cheaper conflicts, same search: the learnt database was the cost. Adopted as the unit-mode default
  (`Solver::reduce_drop`, env `MONSTER_REDUCE_DROP` overrides).

### 2026-10-27 ~05:30: cube-and-conquer adopted; the d=7,8,9 gluing half of the minimum-degree route is done
- **Cube-and-conquer 5k vs whole-unit CDCL, paired 16-unit d=10 sample (seed 1, 3+3 workers, verdicts agree): secs
  ratio 0.268 (95% CI 0.196-0.434), conflicts 0.529 (0.435-0.715); wall 16,464 s -> 3,596 s; extrapolated d=10 stage
  13,339 -> 3,570 CPU-h (both sides at reduce drop 50).** Adopted: unit mode now defaults to
  `--unit-budget 5000 --cube-budget 5000`. With the reduce-drop row (measured with cube on both sides) the d=10 stage
  estimate is ~1,642 CPU-h (~4.3 days on 16 cores) if it is ever needed.
- **Combined certified run `results/overnight/mindeg_d789` finished 04:02 UTC: `complete:true, errors:0`,
  1,625 units, 186,029 pairs, all UNSAT** (d=7: 8 units / 71 pairs; d=8: 30 units / 358 pairs; d=9: 1,587 units /
  185,600 pairs). The run's own process did 1,411 units (85,477 pairs) in 1 h 46 min wall on 6 workers (10 h 35 min
  CPU, 6.9 GB peak); the other 214 d=9 units (100,552 pairs) came from the earlier `symsat-d9-certified` process
  (1 h 56 min CPU) via `--resume`. Unit-time sums from tasks.jsonl: d=7+8 1,805 s, d=9 43,251 s (hardest unit 250 s);
  752.9 M conflicts in all. Every unit in both processes ran with `--check-every 1` under the hint checker.
- **Accounting gap found and closed.** `summary.json` said `certified_pairs 85477` of 186,029: pairs skipped by
  `--resume` were never added to the certified count, and a task line's `"checked":true` only meant that checking
  was requested (a failed check went to the errors list, which the stopped d=9 process never wrote out). Fixed:
  the task line now records the certification OUTCOME (`checked:false` if any proof/glue/witness check failed
  during the task), a certified `--resume` re-runs lines that are not `checked:true`, and certified skipped pairs
  count towards `certified_pairs`. To leave no unaudited record, the 214 early d=9 units are being re-certified in
  `results/overnight/mindeg_d789_recert9` (seeded with the 1,411 fresh lines, `--resume`, 8 workers): its summary
  must say `certified_pairs 186029, errors 0, complete true`. Only then is the gluing half of the route recorded
  as certified end to end.
- **What the gluing half proves (once the recert summary is in):** no K25 2-colouring without red K4 and without blue K5
  has a vertex of red degree 7, 8 or 9 -- modulo the McKay catalogues being complete for R(3,5;d)-graphs on d vertices
  and R(4,4;24-d)-graphs (trusted input, sha256 in meta.json). Degrees >= 14 are excluded by R(3,5)=14 (red neighbourhood) and
  degrees <= 6 by R(4,4)=18 (blue neighbourhood); degrees 10-13 are the flag certificate's job (three CSDP jobs still running).
- **05:32 UTC: re-certification done.** `results/overnight/mindeg_d789_recert9/summary.json`:
  `pairs_done 186029, unsat 186029, certified_pairs 186029, complete true, errors 0` (the 214 re-run d=9 units:
  100,552 pairs, 5,335 unit-seconds, 1 h 29 min CPU on 8 workers, 11 min wall, 6.2 GB peak; all 1,625 task lines
  `checked:true` under the outcome semantics). **The gluing half of the minimum-degree route (red degrees 7, 8, 9) is
  certified end to end**, modulo catalogue completeness (trusted input). Remaining for R(4,5) <= 25 by this route:
  the K=8 flag certificate for red degrees in [10,13].
- **Plain K=8 flag SDP (no degree assumption) finished 05:20 UTC: no certificate.** `symsat-flag-r45-k8`: 5,588
  admissible classes, 127 types, CSDP 40,297 s single-threaded (15.5 h, 5 GB), objective λ = -3.3e-8, i.e. zero to
  solver precision: K=8 flags alone do not rule out a good colouring of K_25 (K=7 gave <= 28 only). So the degree
  assumption must carry the [10,13] certificate on its own; the two degree-restricted CSDP jobs are still running
  (started 01:12 UTC, ~3.8 h in; the plain one took 15.5 h on a problem of the same size).

### 2026-10-27 ~10:55: K=8 flag SDP with red degrees in [10,13]: NO certificate (λ = 0 to precision)
- **CSDP speed-up first.** Ubuntu's `csdp` is single-threaded on the reference BLAS (20 min per iteration on this
  problem). OpenBLAS alone: 12 threads SLOWER (never finished iteration 1 in 30 min; CSDP's BLAS calls are on
  hundreds of 45-64 blocks, thread overhead dominates), 1 thread 12.6 min (1.6x). **Coin-OR Csdp built with
  `-fopenmp -DUSEOPENMP -DSETNUMTHREADS -O3 -march=native` + OpenBLAS (`~/opt/bin/csdp-omp`, run with
  `OMP_NUM_THREADS=12 OPENBLAS_NUM_THREADS=1`): 3.2 min per iteration early, 1.5 min late; whole solve 39 iterations
  in 65.5 min wall (10.5 CPU-h; Elements 2,519 s, Factor 73 s, Other 1,338 s), 0.86 GB.** 6-13x per iteration vs the
  stock build. Sanity: test/theta1 = 23.0. The three single-thread jobs were stopped (user decision) after 8.2 h each.
- **Verdict for `--degree 10,13 --parity`, K=8, N=25:** CSDP converged cleanly (DIMACS errors <= 3.5e-9), primal
  objective -3.4e-9, dual -2.7e-13: **the best SOS multiplier is λ = 0, so there is no certificate in this flag
  space**, exactly as for the plain K=8 run (λ = -3.3e-8). The exact integer check was not run: with the optimum at
  zero there is nothing to round. The degree assumption adds nothing at K=8: the SDP admits a "pseudo-colouring"
  of K25 with all red degrees in [10,13].
- Solution file: `results/flag/R45_N25_K8_deg10-13_parity_omp/problem.sol` (35 MB), input hard-linked from
  `results/flag/R45_N25_K8_deg10-13_parity/problem.dat-s`. The [11,13] fallback is running on the same binary
  (`symsat-flag-omp-deg11-13`, ~1 h): its assumption is stronger, so λ[11,13] >= λ[10,13] = 0 and it could still be
  positive.

### 2026-10-27 ~11:40: unit symmetry measured: the covers leave (almost) no symmetry -> symmetric learning inside units is dead
- New `monster cover-aut --d 10 --covers results/covers_r45 --gray-a 6 --gray-b 6 [--tasks tasks.jsonl]` computes
  |Stab(gen)| (vertex permutations preserving the base graph and the gray set) for every generalisation of a stage
  (`Gen::stabiliser`, backtracking on pair colours). **d=10: A side 17 gens, orders 1:13 2:1 6:1 8:1 200:1; B side
  4,157 gens, orders 1:4032 2:116 4:5 7:2 14:2.** On the standing 16-unit sample every unit has group order 1 except
  the two with A-gen 8 (order 8); the three hardest units (15,1042) 6.5M conflicts, (8,1487) 6.0M, (1,711) 4.6M have
  orders 1, 8, 1. The generalisations already fix the structure that the catalogue graphs' automorphisms permute.
- Consequence: pattern images / SR symmetry breaking inside units cannot pay (nothing to permute); option 1 of the
  evolution list is closed by measurement, not built. The hardness of the tail is genuine CDCL hardness of a
  150-variable, 4,500-clause formula with long (avg 5.8) clauses.

### 2026-10-27 ~11:40: online proof checking with deletions (unit mode): the proof never sits in memory
- `LratLine::Delete`: `reduce_db` logs the LRAT ids of dropped learnt clauses; the hint checker forgets them
  (strict: unknown id = error). Unit mode streams the LRAT lines to a checker thread in 4,096-line chunks
  (`Solver::lrat_sink`, `lrat_flush`, `lrat_finish`); `certify_unit` then only does the glue and refuting-lemma
  checks on the checker's final state. Memory per worker follows the live clause database instead of the whole
  proof (17M-conflict units logged ~4 GB before). The check runs concurrently with the solve (1.1x the solve work,
  on another core). Pair mode keeps the in-memory log (small per pair) and accepts deletion lines. The SLRAT export
  and the lift tool skip deletion lines (they keep every lemma). Test `streamed_proof_with_deletions` (PHP 8->7,
  reductions forced, deletions present, checker ends with the empty clause holding fewer clauses than derived).
- External CDCL check on the same unit formulas (`monster gamma` DIMACS, 150 vars / ~4,800 clauses): easy unit
  (13,3857): monster 7.7 s (cube 5k, drop 50) vs cadical 2.1.3 9.9 s vs kissat 4.0.3 48 s. Hard units (8,1487)
  and (15,1042): both external solvers still running after 18 min on a saturated box (monster: 1,022 s and 1,556 s
  with cube 5k, drop 50, before drop 90). Verdict pending; so far no external engine is clearly faster.
- **End to end (11:40-12:02 UTC): d=7 and d=8 stages re-run with the streaming checker, 3 workers on a saturated
  box: 429 pairs, 429 certified, errors 0, `complete true`; peak RSS of the whole process 87 MB** (the in-memory
  version held every lemma of every unit until the end of the unit).
- **External engines, hard units, final (12:23 UTC):** cadical 2.1.3 UNSAT in 41.5 min CPU on (8,1487) and 62.7 min
  on (15,1042) (78-90 MB); kissat 4.0.3 unfinished after 64 min on both (stopped). monster unit mode on the same
  formulas: 17.0 min and 25.9 min (cube 5k, drop 50; drop 90 is now the default and measured 1.8x on the sample).
  **Our conquer engine is 2.4x faster than cadical and >2.5x faster than kissat on the tail units**; replacing it is
  not a gain. (All runs on a saturated 16-core box, 12 CSDP threads + 4 solvers + a 3-worker certified run.)

### 2026-10-27 ~12:45: d=12 stage costed with the current defaults (cube 5k + drop 90)
- 16-unit seeded sample (seed 1, same units as the whole-unit sample of 2026-10-26), unit mode, uncertified, 3 workers
  beside the 12-thread CSDP: **1,636.5 unit-seconds (hardest unit 989 s, 24.4 M conflicts) vs 7,768.6 s whole-unit
  before cube/drop: 4.75x.** Extrapolated d=12 stage (222,204 units): **~6,300 CPU-h, ~16 days on 16 cores** (was
  ~30,000 CPU-h / 78 days). Parity route total with d=10 (~1,642 CPU-h): ~8,000 CPU-h, ~21 days on 16 cores,
  every unit certified by the streaming hint checker. If the [11,13] flag SDP certifies, only d=10 (~4.3 days) remains.

### 2026-10-27 12:51: K=8 flag SDP with red degrees in [11,13]: NO certificate either -> the flag route is closed at K=8
- `symsat-flag-omp-deg11-13` (csdp-omp, 12 threads, 45 iterations, 1 h 58 min wall on the loaded box, 15.3 CPU-h):
  primal objective -2.7e-9, dual 4.6e-12, converged (DIMACS errors ~1e-9): **λ = 0 to precision.** Together with
  [10,13] (λ = 0) and plain K=8 (λ = 0): K=8 flags cannot certify any degree case of K25 beyond what K=7 already
  refuted ({8}, {12}, [12,13]). Both solutions are kept (`results/flag/R45_N25_K8_deg1{0,1}-13_parity*/problem.sol`).
- **Where R(4,5) <= 25 stands now:** degrees 7, 8, 9 excluded by certified gluing (186,029 pairs). What remains is
  gluing: the parity route (an even-degree vertex exists, d=8 done) needs the d=10 stage (~1,642 CPU-h) and the
  d=12 stage (~6,300 CPU-h), ~21 days on 16 cores; the min-degree route would need d=10..13 and is worse. The d=10
  stage is required under every remaining route and is started now (certified, streaming checker).

### 2026-10-27 ~13:15: streaming checker cost measured; hasher change neutral; d=10 stage running
- 3 d=10 units (seed 7, 1 worker, 8.4 M conflicts): solve only 434 s CPU / 434 s wall; certified (streaming
  hint checker, deletions) 530 s CPU / 495 s wall with the SipHash map, **517.5 s CPU / 491 s wall with the Fx-style
  integer hasher + reused trail** (2.4%, noise). **Certification costs ~20% CPU and ~13% wall**, not the 1.1x the
  in-memory version measured; the checker's time is literal scanning, not hashing. Kept the hasher, no restart for it.
- `symsat-d10-certified`: 166 units in the first 22 min with 8 workers (load ~12 of 16); restarted at 13:17 UTC with
  12 workers (`--resume`, finished units kept). Expected ~4-5 days for 70,669 units if the sample rate holds.

### 2026-10-27 ~14:00: catalogue-constrained flag SDP (`monster flag --nbhd LO,HI`): R(4,4) <= 18 certified at K=4
- New constraint family (src/flag.rs `Nbhd`): in a good (s,t) colouring the red neighbourhood of every vertex is an
  (s-1,t)-good graph, so with McKay's catalogue (trusted input, as in gluing) the rooted subgraph counts
  E_v[#{l-subsets of N(v) inducing H'}] form a convex combination of the catalogue graphs' counts. Exact finite-N
  identity Σ_v cnt_{H'}(N(v)) = C(N,l+1)/C(K,l+1) Σ_H p_H pairs(H',H) (unit test `rooted_count_identity`, random good
  colourings of K_8). SDP: free multipliers μ per rooted type, one row per catalogue graph, objective α + β (+ γ for
  the handshake row); exact integer check extended (`exact_check` with the nbhd part; condition α + β + γ > 0).
- **R(4,4) at N=18: plain flags fail at K=4 (λ = -2.7e-2) and K=5 (λ = -1.9e-4); with `--nbhd 0,8` (49 catalogue
  graphs r34/n0..8) the SDP certifies at K=4 (λ = 1.24e-3) and K=5 (λ = 1.47e-3), both VERIFIED in exact integer
  arithmetic, in 0.2 s.** The certificate's meaning: no good colouring of K_18 whose red neighbourhoods are catalogue
  graphs; with catalogue completeness this is R(4,4) <= 18. This is the first time the gluing information and the
  global counting are combined in one certificate.

### 2026-10-27 ~14:20: Lean-checked per-unit refutations (`monster unit-lean`, Lean `checker --lemma`)
- New `src/leanunit.rs`: solves one unit (whole formula, LRAT on) and rewrites the proof over the full K_25 formula in
  the Lean checker's own variable numbering (root v = 0, A-vertex u -> 1+u, B-vertex w -> 1+d+w): every GAMMA clause is
  matched to a K_25 clique clause reduced under the unit's fixed edges (no trust in `build_gamma`), and each lemma
  carries the negated fixed-edge literals it depends on. The last lemma is "¬(fixed edges)": no good colouring of
  K_25 extends this unit. New Lean mode `checker --lemma FILE` with `theorem checkLemma_sound` (Lemma.lean: the
  returned clause holds in every good colouring; axioms = propext, Classical.choice, Quot.sound; no sorry), `lake
  build` 94 s.
- Measured (box shared with ~20 threads): d=7 unit (0,0): 71k conflicts, 71k lemmas, 40 MB, reference checker 1.6 s,
  Lean 18.5 s VERIFIED LEMMA; d=7 (3,0): 107k lemmas, Lean 29 s; d=8 (0,0): 123k lemmas, 68 MB, Lean 60.5 s
  (520 MB); d=7 (1,0) (re-run by the main session): 255k conflicts, 255k lemmas, reference 5.4 s, Lean 65 s, 1.0 GB.
  Mutants (flipped literal, dropped hint, dropped literal) are rejected by both checkers. Tests
  `unit_lean_r34_unit_checks`, `unit_lean_rejects_bad_vertex_count`.
- Limits: the assumption literals dominate (93-99 of ~110 literals per lemma), ~570 bytes per conflict, so a
  17M-conflict d=10 unit would be ~10 GB and the Lean checker parses whole files into memory: the d=7 and d=8 stages
  are Lean-checkable unit by unit, the d=10 tail is not. The fix (not built) is an assumption rule in the verified
  checker (a sub-database under fixed literals, closed by one lifted clause), ~8x smaller files. Whole-unit solving
  only (no cubes); combining the per-unit lemmas with catalogue coverage into ⊥ is not done.
- **R(4,5) at N=25 with `--nbhd` (+handshake): K=6 and K=7 give no certificate** (λ = -7.6e-6 / -2.1e-6 at K=6 for
  degrees 7..13 / 10..13; -1.5e-6 / -1.2e-7 at K=7, CSDP "stuck at edge of primal feasibility", 11-12 min each with
  csdp-omp). K=7 sees at most 6-subsets of a 10-13-vertex neighbourhood. K=8 (7-subsets) for 10..13 launched 14:20 UTC
  (`symsat-flag-k8-nbhd10-13`, ~35 min set-up + CSDP).
- **~14:30: assumption rule in the Lean checker** (`verified/MonsterVerified/Assume.lean`, Checker.lean steps
  `openAsm`/`asm`/`close`, `close_sound`; SLRAT lines `a l1..lk 0`, `u k <lrat line>`, `id a k src 0`; reference
  checker in `full.rs` in sync; `unit-lean` emits it). Lemmas carry no assumption literals any more.
  d=7 (0,0): 10.9 MB (was 40.5), Lean 2.3 s / 115 MB (was 18.5 s / 313 MB); d=8 (0,0): 20.5 MB, Lean 4-13 s / 168 MB
  (was 60.5 s / 520 MB); **d=9 (0,0): 1,288,190 lemmas, 267 MB, reference 33 s, Lean 124 s / 2.0 GB VERIFIED.**
  Axioms unchanged (propext, Classical.choice, Quot.sound), no sorry. Mutants rejected by both checkers; the
  exporter compares the final clause with ¬A so a "valid but different" statement cannot pass as the unit's refutation.
  Pitfall found: `setIfInBounds` on a shared array element copied the sub-database per step (quadratic); `Array.modify`
  fixed it. Remaining limit: Lean holds the whole proof (~1.5 KB/lemma), so 17M-conflict d=10 units (~25 GB) need
  deletion lines in the sub-database plus streaming parsing (next).

### 2026-10-27 ~19:30: three results: degree axioms closed, d=12 cover 4x, Lean checker streams d=10 units
- **Degree-window axioms in unit mode (option 1): closed.** Paired A/B `symsat-ab-d12-degax` (d=12, 16-unit seed-1
  sample, `--gray-a 0 --gray-b 8`, `--check-every 0`, 2 workers a side): the base side finished all 16 units in
  2,122 s; the axiom side had finished only the first 12 of the same units after 6 h 10 min (33,800 CPU-s) when it was
  stopped: those 12 units took 188 s without axioms and 6,083 s with them (**32x slower**; the two slowest 1,741 s and
  3,427 s vs 43 s and 74 s). Consistent with the earlier pair-mode measurement (counter bloat). No `bench/ab.jsonl` row
  (the run was stopped). The exact follow-up (degree bounds as derived constraints) is not worth building.
- **d=12 covers (option 3, subagent report in the session scratchpad covers12/REPORT.md): A-side gray edges cut the
  stage ~4x.** New covers `results/covers_r45/c35_12_g4.txt` and `c35_12_g6.txt` (2 generalisations of the 12
  R(3,5;12) graphs, built in 0.09 s) and `c44_12_g6.txt` (59,134 generalisations, 1 h 22 min). 16-unit seed-1 samples
  (uncertified, loaded box, so seconds are inflated; conflicts are exact), extrapolated by units and by pairs
  (12 x 1,449,166 = 17,389,992 pairs):

  | gray-a, gray-b | units | sample s | conflicts | pairs | CPU-h by units | CPU-h by pairs | conflicts x1e9 |
  |---|---|---|---|---|---|---|---|
  | 0, 8 (old) | 222,204 | 2,980 | 24.4M | 1,018 | 11,496 | 14,140 | 338 |
  | 4, 8 | 37,034 | 4,741 | 49.4M | 8,012 | 3,048 | 2,858 | 114 |
  | **6, 8** | 37,034 | 4,307 | 47.2M | 8,012 | **2,769** | **2,597** | **109** |
  | 0, 6 | 709,608 | 1,312 | 17.5M | 363 | 16,162 | 17,458 | 776 |
  | 4, 6 | 118,268 | 5,607 | 55.2M | 4,176 | 11,513 | 6,486 | 408 |
  | 6, 6 | 118,268 | 5,097 | 53.1M | 4,176 | 10,465 | 5,895 | 392 |

  Reading: gray-b 6 is worse than 8 everywhere; gray-a 6 with gray-b 8 is the d=12 setting (**~2,600-2,800 CPU-h,
  about 7 days on 16 cores, instead of ~11,500-14,100**). `c44_12_g10` is being built (`symsat-cover12-g10`); the same
  lever is being measured on d=10 (covers c35_10_g8, c44_14_g8; report section 4).
- **Lean checker part 3 (option 5, subagent; verified by the main session: `lake build` ok, 31 + 6 tests ok, d=7 unit
  with 15 deletion lines VERIFIED LEMMA in 3.5 s / 51 MB):** deletion lines `u k d id.. 0` in the assumption
  sub-database (`Step.asmDel`, `delete_sound_under`; unknown ids are ignored by Lean and rejected by the reference
  checker) and a streaming `--lemma` mode (`Stream.lean`: `OKSt` carries the state with its invariant; `Main.lean`
  reads line by line, never holds the text). Axioms unchanged (propext, Classical.choice, Quot.sound), no sorry.
  Measured: d=9 (0,0) 1.29M conflicts, 276 MB: Lean 90-112 s / **67 MB** (was 2.0 GB); d=10 (13,3857) 293k
  conflicts: 26 s / 55 MB; **d=10 (0,522), the hardest certified unit so far: 23.2M whole-unit conflicts, 6.1 GB proof,
  Lean 2,563 s / 307 MB VERIFIED** (solve 6,735 s, reference checker 400 s). Every d=10 unit is now Lean-checkable
  (~0.4x solve time, ~110 µs/lemma, ~260 B/conflict on disk). Not done: cube-mode proofs through `unit-lean`.
- d=10 certified stage: 1,072 / 70,669 units at 19:10 UTC, all checked, errors 0; 244.6 s/unit average on a box at
  load ~26 (the sample predicted 83 s unloaded). K=8 `--nbhd 10,13` SDP: csdp-omp 4 h 52 min wall / 13.3 CPU-h so far
  (the plain K=8 run took 15.3 CPU-h), no verdict yet.
- **(~21:30) d=10 covers: no win (subagent, REPORT.md section 4).** New covers `c35_10_g8.txt` (14 generalisations,
  0.5 s) and `c44_14_g8.txt` (2,988, 9 min). 16-unit seed-1 samples, by pairs (40,945,408 pairs): (6,6) 0.223 s/pair,
  2,532 CPU-h; (8,6) 0.232 s/pair, +13% conflicts; (6,8) 0.215 s/pair on 10 units, +5% conflicts; all within sample
  noise. The A side is already grouped at gray 6 (17 generalisations for 313 graphs), so the d=12 lever (12 singletons ->
  2 generalisations) has no counterpart here. The running (6,6) stage stays; (8,8) was not run (sample stopped at 21:22
  to free the box). The gray-10 B cover for d=12 was not built (~40 CPU-h estimated; deferred).
- (~21:25) CSDP on the K=8 nbhd problem uses only ~2.3 cores of its 12 threads (17.4 CPU-h over 6.7 h wall), so the
  d=10 stage is not what slows it: the 560 dense rooted-count/catalogue rows defeat CSDP's per-constraint OpenMP
  parallelism. Set `CPUWeight` 1000 (SDP) / 30 (d=10) anyway; no restart (no checkpoint).

### 2026-10-27 22:17: K=8 catalogue-constrained flag SDP (`--nbhd 10,13 --handshake`): NO certificate -> option 2 closed at K=8
- `symsat-flag-k8-nbhd10-13`: 5,588 classes, 127 blocks, 431 catalogue graphs (R(3,5)-good on 10..13 vertices), 129
  rooted-count rows (l <= 7), m = 6,020 constraints, 1.01 GB SDPA input. csdp-omp: 40 iterations, 7 h 39 min wall,
  19.8 CPU-h, "Stuck at edge of primal feasibility", **λ = -3.83e-8** (dual -8.7e-10, DIMACS errors <= 4.1e-8): the
  same "λ = 0 to precision" as plain K=8 (-3.3e-8), [10,13] and [11,13]. No exact check possible (λ <= 0).
- So at K=8, knowing that every red neighbourhood is a catalogue graph adds nothing the plain flags did not already
  see. The flag route is closed at K=8 with and without catalogue constraints; K=9 would be ~10x the classes
  (set-up and CSDP far beyond this box). The parity gluing route (d=10 running, then d=12 with the new covers) is
  the only remaining route to R(4,5) <= 25.
- CSDP note: the nbhd problem ran at 2.3-4.4 cores of its 12 threads (99% of samples in libgomp barrier spinning;
  csdp's own breakdown: Elements 4,343 s, Factor 948 s, **Other 22,237 s**), vs ~7.8 cores on the plain K=8 problem.
  Pinning the SDP and the d=10 stage to disjoint cores (taskset) doubled its throughput. Iteration lines were read
  from the parent's pipe buffer in memory (`/proc/PID/mem`); a future `monster flag` should tee CSDP's stdout to
  csdp.log as it runs.

### 2026-10-27 ~22:50: SR proofs (Heule's GitHub) and the HOL4 proof of R(4,5)=25, as yardsticks for proof size
- `marijnheule/sr2drat` and `sr-proofs/Ramsey` contain a **39-line, 17 KB SR proof of R(4,4) <= 18** (153 vars,
  6,120 clauses; Codel, Avigad, Heule, FMCAD 2024 "Verified substitution redundancy checking": 38 SR clauses, checked by
  a Lean-verified SR checker; SR proofs reported 99.6% smaller than RAT on their benchmarks). It is short because
  R(4,4) <= 18 has a short human proof (degree argument + R(3,4) = 9) and SR witnesses carry substitutions, so each
  "without loss of generality" step is one line. The file was downloaded to the session scratchpad (heule/); compiling
  sr2drat + drat-trim to re-check it was blocked by the sandbox classifier (needs the user's go).
- Gauthier & Brown, "A Formal Proof of R(4,5)=25" (arXiv 2404.01761, HOL4, 2024): the same gluing route (d in
  {8,10,12} by the parity argument; MiniSat through HOL4; covers with <= 10 gray edges; cover completeness proved by
  a custom labelled-graph solver + nauty), **"less than 950 CPU days"** (naive estimate "more than 16,000 CPU days").
  Their covers: R*(3,5,12) = 12 generalisations (ours: 2 with 6 gray edges), R*(4,4,12) = 26,845 (ours: 18,517 with 8),
  R*(4,4,14) = 11,752 (ours: 2,988 with 8). Our route's total is ~5,000 CPU-h = ~210 CPU-days including certification.
- Consequence for "a short SR proof of R(4,5) <= 25": no short mathematical proof of R(4,5) = 25 is known; every proof
  is the gluing computation. SR removes symmetry, and the symmetry here is already quotiented by the catalogues
  (units have trivial groups, RESULTS "~11:40"), so SR cannot shrink the ~100-180 G conflicts of d=10 or the ~110 G of
  d=12. What SR could do is make the trusted input (catalogue completeness) a checked step: a canonical-form
  ("WLOG") SR argument that every (3,5)-good graph on d vertices is one of the catalogue graphs. That is a research
  build, not a speed-up for the running stages. Disk: 1.2 TB free; the certified run stores verdict lines only (proofs
  are checked online), a stored LRAT/SLRAT of d=10 would be 25-45 TB.

### 2026-10-27 ~23:10: `--shard` for many machines; SR rule in the reference checker verifies Heule's R(4,4) proof
- **`glue --shard I/N`** (src/glue.rs `make_tasks`, src/main.rs): keeps the tasks with index I mod N of the whole
  plan; a shard never reports `complete`. Merge = concatenate the shards' tasks.jsonl into one `--out` dir and run the
  same command without `--shard` with `--resume`. Test: the d=7 stage in 3 shards (3 + 3 + 2 tasks, each certified,
  `complete:false`), merged run: 71/71 pairs, certified_pairs 71, `complete:true`, errors 0, 0.1 s, nothing re-solved.
  Per machine: the `monster` binary, 57 MB catalogues, 143 MB covers, < 1 GB RAM per 12 workers.
- **SR (substitution redundancy) in the reference checker** (src/full.rs `SlratDb::sr_step`, `Prop`): line
  `id r l1..lk 0 w1..wj 0 a1 b1..ap bp 0` adds C = {l1..lk} to a new SR tier when, for σ = (witness literals true,
  var |a| := b, identity elsewhere), every clause D of the database and C itself has D|σ satisfied or unit-propagated
  from F ∧ ¬C (fast path: D|σ already a clause of F). `id p lits 0` = hint-less RUP by full propagation. Tiers: images
  and lifts refuse SR-tier sources (symmetry breaking is not a symmetry); RUP results inherit the tier of their hints;
  `check_slrat_last` reports whether the final clause is pure; `unit-lean` refuses an SR-tier final clause as a lemma.
  The Lean checker has no SR rule yet (next, with the soundness proof: F satisfiable => F ∧ C satisfiable).
- **Heule's 39-line SR proof of R(4,4) <= 18 verifies with our checker**: `monster sr-check --s 4 --t 4 --n 18
  tests/data/R_18_4_4.sr` -> `s VERIFIED` in 0.25 s (his sr2drat + drat-trim: 888,337 DRAT lines, 33.8 MB, 7.5 s).
  Tests: `heule_r44_sr_proof_checks` (plus three mutants rejected: flipped unit, dropped substitution, image of an SR
  clause), `hintless_rup_and_tiers`; the lift battery still passes (dropped hints are still rejected: propagation
  lines are explicit). The proof's shape: 16 "sort the neighbours of vertex 1" SR lines (witness = swap of two
  vertices), one colour-swap line (vertex 1 has <= 8 red neighbours), then sorting lines for vertices 2, 3 and unit
  clauses derived by propagation (the R(3,4) = 9 degree argument). The same shape gives the degree bounds
  7 <= d <= 13 of the R(4,5) route as SR lines over F(4,5,25) (next: a generator).

### 2026-10-27 ~23:35: SR degree-argument generator (`monster sr-gen`): R(3,3), R(3,4), R(3,5), R(4,4) refuted, K_25 degree bounds derived
- `src/srgen.rs`: the classical recursion R(k,l) <= R(k-1,l) + R(k,l-1) as SR lines over F(s,t,n): inside a vertex set
  that may hold no red K_k and no blue K_l (because of a context of literals), sort one vertex's edges (SR lines with
  Heule's cyclic-shift witness: the first sorted vertex moves to the current position, the prefix shifts down, which
  keeps the earlier sorting clauses satisfied; a plain transposition fails at the second line), then split on its
  degree (first R(k-1,l) sorted neighbours red, or last R(k,l-1) blue), recursing with the context extended; leaves and
  case closures are propagation lines. Every line carries the negated context, so inner "WLOG" steps are conditional
  and no sub-database is needed. R(3,4) <= 9 is parity-tight (9 < 4 + 6), so it uses Heule's hand-made case analysis
  (his lines 18-39, transcribed as a template over nine vertices, with a colour mirror).
- Verified by the reference checker (`monster sr-gen --s S --t T --n N OUT.slrat`):

  | claim | SR lines | propagation lines | bytes | check |
  |---|---|---|---|---|
  | R(3,3) <= 6 | 4 | 4 | 344 | 0.00 s |
  | R(3,4) <= 9 | 13 | 9 | 1,962 | 0.00 s |
  | R(3,5) <= 14 | 25 | 12 | 9,127 | 0.08 s |
  | R(4,4) <= 18 | 42 | 20 | 23,556 | 0.29 s (Heule's hand proof: 39 lines, 17 KB) |
  | **R(4,5) at N=25, `--bounds`: red degree of vertex 0 in [7,13]** | 90 | 34 | 102,577 | 14.2 s, 35 MB |

  The two final clauses are `-x(0,14)` (red degree <= 13: the R(3,5) <= 14 argument inside the first 14 sorted
  neighbours) and `x(0,7)` (red degree >= 7: a blue degree >= 18 contradicts R(4,4) <= 18). They are SR-tier (they
  hold after sorting vertex 0's edges, reds first) and are exactly the assumption the gluing units are stated under
  (A-vertices 1..d red to 0). So the degree bounds of the route are no longer trusted input: they are 124 checked lines.
  Tests: `sr_degree_argument_refutes_small_ramsey`, `sr_degree_argument_r44_18`, `sr_degree_bounds_r45_25`.
- Still trusted: catalogue completeness (every (3,5)-good graph on d vertices is a catalogue graph up to relabelling,
  same for (4,4)) and the parity step (some vertex has even red degree). Lean: the SR rule is being added by the Lean
  agent (part 4); until then these SR lines are checked by the reference checker only.

### 2026-10-28 ~00:20: the assembled Lean theorem `r45_le_25` (parity, degree bounds, assembly: parts 5a-5c)
- New Lean files (a subagent; verified by the main session: `lake build` ok, no sorry, `#print axioms` as stated):
  `verified/MonsterVerified/Parity.lean` (`redDegree`, handshake `sum_redDegree_even`, `exists_even_red_degree_odd`
  for odd n, `exists_even_red_degree` for 25; axioms propext, Classical.choice, Quot.sound), `Degree.lean`
  (`good_induced`: the colouring induced on a list of red (blue) neighbours of v is Good with s (t) one smaller;
  `red_degree_le_13_of`, `red_degree_ge_7_of` from any proof of ¬Good 3 5 14 / ¬Good 4 4 18), `Assembly.lean`
  (`Catalogue`, `CatalogueComplete`, `UnitShape d a b c` = vertex 0 red to 1..d inducing a there and blue to d+1..24
  inducing b there, `UnitsRefuted`, and
  **`theorem r45_le_25 (cat) (hcat : CatalogueComplete cat) (hunits : UnitsRefuted cat) : ∀ c, ¬ Good 4 5 25 c`**).
  Axioms of `r45_le_25`: propext, Classical.choice, Quot.sound and the native_decide axioms inherited from
  `R35_le_14` and `R44_le_18` (Theorems.lean, proved from monster's pattern-CDCL proofs with `native_decide`).
- So the whole route is now one kernel-checked statement with two hypotheses: `CatalogueComplete` (the trusted
  input) and `UnitsRefuted` (what the gluing stages establish: each certified unit refutes a generalisation, hence
  every catalogue pair it covers). What remains to connect: (a) `UnitsRefuted` from the per-unit Lean lemmas (a bridge
  "clause ¬A holds in every good colouring ⇒ ¬UnitShape d a b" and a batch lemma mode over all units, docs/ASSEMBLY.md),
  (b) a `Catalogue` instance read from the g6 files. (c) optional: re-prove R35_le_14 / R44_le_18 from the 37- and
  62-line SR proofs once the Lean SR rule lands, dropping the native_decide axioms.

### 2026-10-28 ~00:30: SR rule in the Lean checker (part 4): Heule's R(4,4) <= 18 and the K_25 degree bounds Lean-verified
- Verified by the main session after the subagent's hand-back: `lake build` ok, `cargo test --release` 36 + 6,
  axioms of `check_sound` and `checkLemma_sound` = [propext, Classical.choice, Quot.sound], no sorry.
- Hinted SR line (`id r lits 0 witness 0 pairs 0 alpha-hints 0 (Did hints 0)* 0`): the Rust `sr_step` records the
  unit-propagation reasons and `sr-check --slrat OUT` / `monster slrat-hints IN OUT` write them; the Lean checker
  replays them (SR.lean: substitution, `srClause_sound`; Checker.lean: `Step.sr`, SR tier, six-part invariant with
  "if a good colouring exists, some good colouring satisfies both tiers", `good_of_originals`; Parse/Lemma/Stream/
  Main updated; `--lemma` reports VERIFIED STEPS for an SR-tier final clause).
- Numbers (this session's runs): Heule's 39-line proof -> hinted 1.9 MB -> **Lean `s VERIFIED UNSAT: R(4,4) <= 18` in
  1.07 s / 28 MB**; flipped-unit mutant NOT VERIFIED. `sr-gen` proofs Lean-verified: R(3,3) 0.02 s, R(3,4) 0.04 s,
  R(3,5) 0.33 s, R(4,4) 1.5 s. **K_25 degree bounds (124 lines): hinted 70 MB, Lean checks every line in 56 s / 63 MB**
  ("VERIFIED STEPS": the two final clauses are SR-tier, as intended).
- Status of the proof skeleton: degree bounds, parity, assembly (`r45_le_25`) and the small Ramsey theorems are
  Lean-checked; gluing units are certified online (Lean-checkable per unit); trusted: catalogue completeness only.

### 2026-10-28 ~00:55: batch lemma mode `checker --lemmas LIST [--delete]` (part 6), verified
- Lean `Verified s t n` (clause + proof) with `OKSt.verified` as its only constructor (pure last clause of a
  streamed check), driver theorem `batch_sound : ∀ v ∈ L, ∀ c, Good s t n c → ClauseSat (edgeTable n) c v.clause`
  (axioms [propext, Quot.sound]). One process verifies a list of per-unit SLRAT files one after another, holding one
  file's live database at a time; `--delete` removes each verified file. Main session's run: three d=7 unit proofs +
  a hint-dropped mutant -> 3 VERIFIED LEMMA, 1 NOT VERIFIED, exit 1, 16.5 s / 65 MB (single files are ~3 s / 51 MB,
  so the batch adds no memory). Rust test `unit_lean_batch_lemma_mode` (gated on the built checker); 37 + 6 tests pass.
- This is the mechanism that discharges `UnitsRefuted` at scale (docs/ASSEMBLY.md): per shard, export each unit with
  `unit-lean`, verify-and-delete in a batch, keep the list of verified clauses; memory stays bounded by the largest
  unit (307 MB for the 23M-conflict d=10 unit).

### 2026-10-28 ~00:46: stage driver `monster unit-lean-stage` (part 7): the d=7 and d=8 gluing stages Lean-verified
- `monster unit-lean-stage --s 4 --t 5 --n 25 --d D --covers results/covers_r45 --gray-a 6 --gray-b 6 --out results/leanstage/dD
  --workers 3 --batch 8` (src/leanstage.rs, built by the SR subagent; the run finished after the session died at 00:32).
  Workers export every unit (whole-unit solve, assumption rule, deletion lines); a collector verifies batches of 8 files in one
  Lean process each (`checker --lemmas LIST --delete`); `verified.jsonl` records the Lean-printed clause per unit.
- d=7: 8/8 units verified, 0 failed, `complete: true`; solve 29.7 CPU-s, export 31.4 CPU-s, Lean 57.4 CPU-s (1 batch, peak
  61 MB), 184 MB exported, wall 69 s.
- d=8: 30/30 units verified, 0 failed, `complete: true`; solve 1,127 CPU-s, export 1,134 CPU-s, Lean 990 CPU-s (4 batches,
  peak 136 MB), 3.19 GB exported, 15.1 M conflicts, wall 1,487 s.
- Records: `results/leanstage/d{7,8}/{summary.json,verified.jsonl}` (tracked). The proof files are deleted after verification
  and gitignored (six of them, 0.3-1.5 GB, got into commit 0c56fbe and blocked every GitHub push for 9 hours; re-created as 02de4f6).

### 2026-10-28 ~09:30: where R(4,5) <= 25 stands (for the record)
After parity and the Lean-verified degree bounds only d = 8, 10, 12 are needed.

| Stage | Units | Done | Status |
|---|---|---|---|
| d=8 | 30 | 30 | certified (Rust checker) and Lean-verified |
| d=10 | 70,669 | 4,617 (09:25) | running, 0 errors, 245 CPU-h so far, ~230 units/h at 12 workers, ~12 days left on this box |
| d=12 | 37,034 | 0 | not started (`--gray-a 6 --gray-b 8`, ~2,600-2,800 CPU-h, ~7 days) |

So ~4% of the computation is done (by units and by CPU-hours). d=7 and d=9 are certified too but not needed for the theorem.
Lean side: checker, SR rule, batch lemma mode, parity, degree bounds, G6 decoder, clause->unit bridge and `r45_le_25` are proved;
missing: the `checker --assemble` driver (its in-progress version died with the session, nothing on disk), the Lean stage runs
for d=10 and d=12 when they finish, and catalogue completeness stays trusted input. Every solver speed lever is measured out
(IDEAS "Status after 2026-10-28"); the one sure lever is more machines (`--shard`, `scripts/bundle.sh`).

### 2026-10-28 ~11:00: the assembler `checker --assemble` built and verified on d=7; coverage costs for d=10 and d=12
- **Gap closed in Lean** (verified/MonsterVerified/Assemble.lean): the covers map catalogue graphs to generalisations
  only up to a vertex permutation, so the unit clauses refute *relabelled* catalogue graphs. `unitShape_relabel` /
  `stageRefuted_of_relabelled` prove that refuting `(relabel σ a, relabel ρ b)` refutes `(a, b)` (relabel the
  colouring by `assemblePerm 0 [1..d] [d+1..24] σ ρ`; `good_relabel`). `stageOK` is the parallel Bool check
  (hints = generalisation + σ per catalogue graph, untrusted; clause table per unit); `stageRefuted_of_verified`
  (in-process, hypothesis-free) and `stageRefuted_of_record` (recorded clauses) give `StageRefuted cat d`;
  `r45_le_25_of_stages` needs d = 8, 10, 12. Axioms of the stage theorems: the standard three. `sig` got a proved
  `csimp` twin without list building; graph6 bodies are arrays (both executable-only changes).
- **Driver**: `monster assemble-spec` (src/assemble.rs) writes the hints (σ = pi⁻¹ of the cover's `A` line) and the
  spec; `checker --assemble SPEC` (Main.lean) decodes the g6 files, reads hints and clauses, runs `stageOK` in `threads`
  chunks. Batch mode `checker --lemmas LIST --record FILE` now records `path lits` per verified lemma, and
  `unit-lean-stage` passes `--record DIR/verified.rec` (the input of the record form). Bug fixed on the way: `--keep`
  and `--fake` were not registered as boolean flags, so `--keep` had never kept files (it swallowed the next argument).
- **d=7 end to end** (`cargo test --release assemble_d7`, 122 s): the real d=7 stage (8 units, covers c35_7_g6 x
  c44_17_g6, files kept, record written) → record form `s STAGE 7 REFUTED GIVEN THE RECORD` (exit 0) → in-process form
  (the assembler re-verifies the 8 SLRAT files itself) `s STAGE 7 REFUTED: ... stageRefuted_of_verified` (exit 0) → a
  record with one flipped literal `s STAGE 7 NOT REFUTED` (exit 1).
- **Mutations at d=8** (exact unit clauses as a fake record, 179 x 2 pairs, 26 ms): flipped literal, hint that is not
  a permutation, hint pointing at another generalisation, missing unit, two vertices swapped in a hint: all five
  `NOT REFUTED`, exit 1. The unmutated run passes (exit 3 = "covered by unverified clauses", proves nothing).
- **Coverage cost at scale** (fake records = the exact unit clauses, which is what the real stages produce; 14 threads
  on the box running the d=10 solve at load ~27):

| stage | pairs | units | decode | clauses read | coverage check | peak RSS |
|---|---|---|---|---|---|---|
| d=10 | 313 x 130,816 = 40.9 M | 70,669 | 0.7 s | 4.9 s | **229 s wall, 1,328 CPU-s** | 361 MB |
| d=12 | 12 x 1,449,166 = 17.4 M | 37,034 | 2.0 s | 7.0 s | **138 s wall, ~900 CPU-s** | 597 MB |

  So the final assembly (three stages in one spec) is minutes and well under 1 GB; no need for the split check
  (A-part / B-part per literal) that would cut another ~20x.
- **d=8 on the regenerated stage** (`results/leanstage/d8keep`: 30/30 units, 3.0 GB of proofs kept, `verified.rec`
  written by batch mode; specs and outputs in `results/leanstage/assemble/`):
  - record form: `s STAGE 8 REFUTED GIVEN THE RECORD` (theorem `stageRefuted_of_record`), 0.02 s, 12 MB;
  - **in-process form: `s STAGE 8 REFUTED: StageRefuted (catalogueFrom files) 8 by theorem
    MonsterVerified.stageRefuted_of_verified (every lemma verified in this process; no hypothesis beyond the catalogue
    files)`**: 30 lemmas (3.2 GB of SLRAT) re-verified in one process in 910 s, coverage 26 ms, peak RSS 135 MB, exit 0.
  This is the small proof asked for: one verified program, run once, establishes the d=8 stage of the theorem with
  nothing assumed but the two graph6 files it read.

### 2026-10-28 ~11:30: speed pass on the Lean route (what a d=10 Lean stage really costs, and three fixes)
Measured on d=10 units of the running certified stage (`results/overnight/d10_certified/tasks.jsonl`, certified = cube
mode, 12 workers, hint checker) against `monster unit-lean` export (whole-unit solve, LRAT, SLRAT translation), box at load ~27:

| unit (ga,gb) | certified conflicts / secs | whole-unit export conflicts / solve secs / proof |
|---|---|---|
| (0,3951) | 113,168 / 2.3 | 113,067 / 3.4 / 20 MB |
| (0,3459) | 1,437,815 / 67 | 2,433,879 / 153 / 561 MB |
| (0,1797) | 1,983,021 / 136 | 4,083,966 / 351 / 968 MB |

So the whole-unit solve does ~2x the conflicts of the cube strategy on the harder units, and LRAT + writing adds ~25%
per conflict; Lean then costs 0.31 s/MB (20 MB proof: 6.3 s, of which parsing 3.3 s = 53%). Per hard unit the Lean
route was ~4.7x the certified cost (351 + ~300 vs 136 s): ~17,000 CPU-h for d=10. Fixes, all measured:
1. **Cube-and-conquer in the export** (`leanunit::export_unit`, `Options.cube_budget`, default 5,000 like unit mode;
   `--cube-budget` on `unit-lean` / `unit-lean-stage`): the same `glue::cube` (one solver, learned clauses kept,
   core clauses and split resolvents logged with LRAT hints) now drives the export; the proof stays one assumption
   sub-database, the root resolvent is ⊥. Measurement below.
2. **Byte-level fast parser** (`parseLineFast`, Parse.lean; untrusted like `parseLine`, every step is still checked by
   `stepFn`): the hot line kinds are scanned without token lists. 20 MB proof: parse-only 3.36 s → 1.15 s, full lemma
   check 6.15 s → 4.25 s (-31%). `checker --parse FILE` times the parser alone. 39 + 6 tests and the 20 lift mutants pass.
3. **Parallel Lean batches in the stage driver** (`--lean-jobs J`, default = workers; the 4-worker cap is gone): one
   sequential Lean process made the d=8 stage Lean-bound (solve 1,057 CPU-s on 3 workers vs Lean 955 CPU-s on 1).
Not worth building: **proof trimming**. 94.2% of the exported lemmas (106,592 of 113,121 on unit (0,3951)) are in the
cone of the final empty clause, so trimming would save ~6% of Lean time.
- **After the fixes (same units, cube export, new parser):** (0,1797): 1,983,021 conflicts = the certified run's count
  exactly, solve 124 s (certified 136 s wall), proof 482 MB (was 968), Lean 89 s / 84 MB (0.18 s/MB); (0,3459):
  1,437,815 conflicts (= certified), 76 s (certified 67), 332 MB, Lean 59 s. Lean route per hard unit now ~213 s vs
  136 s certified (1.6x, was 4.7x). Projection for d=10 (70,669 units, mean certified 191 s): ~6,100 CPU-h ≈ 16 days
  on this box with solve and Lean overlapped, against ~12 days left for the certified run that keeps no proofs.
  **Decision (11:55 UTC): the certified d=10 run was stopped at 5,050 units (its `tasks.jsonl` stays as a partial
  certified record) and the Lean stage `symsat-d10-lean` launched** (`unit-lean-stage --d 10 --workers 10
  --lean-jobs 8 --batch 6 --resume`, record files per batch in `results/leanstage/d10/rec/`).
- Record robustness: with several Lean processes at once, `unit-lean-stage` gives each batch its own record file
  (`DIR/rec/batch_N.rec`); `assemble-spec --from-record DIR` lists them all (one `record` line each in the spec).

### 2026-10-28 ~12:40: array assignment in the Lean checker (`rupFast`), sharded Lean stages, one-command bootstrap
- **The hot spot was not the clause store** (the database is `Array (Option (List Int))`, O(1) by id) but the
  assignment `Assign := List (Nat × Bool)`, walked linearly for every literal of every hint clause. `rupA` / `rupFast`
  (Rup.lean) keep it as an `Array UInt8` (0/1/2 = unassigned/false/true, grown on demand, first entry wins like
  `alook`); `rup_eq_rupFast : @rup = @rupFast` is proved and tagged `@[csimp]`, so the compiler runs the array form
  while every theorem keeps talking about `rup`. Axioms of `check_sound` unchanged. Measured (same proofs as above):
  20 MB unit 4.25 s → 3.72 s, 482 MB unit 88.7 s → 70.7 s (−15 to −20%; parsing is now ~30% of a check, the rest is
  clause evaluation: boxed `Option` results per literal, `List Int` clause walks). 39 + 6 tests, 20 lift mutants
  pass; the running d=10 stage was switched to this checker at 12:35 (atomic replace of the binary it spawns).
  Lean is now 0.57x the solve CPU per hard d=10 unit (70 s vs 124 s); the Lean route costs 1.4x the old certified
  solve per unit (was 4.7x this morning).
- **`unit-lean-stage --shard I/N`**: this machine takes the units with ga-major index ≡ I (mod N); a shard never
  claims `complete`. Merge: concatenate the shards' `verified.jsonl` into the main stage's file and run the stage
  command with `--resume` (everything skipped → `complete: true`); copy all `rec/*.rec` into one directory for
  `assemble-spec --from-record DIR`.
- **`scripts/bootstrap.sh`**: from a bare Debian/Ubuntu box (x86-64 or aarch64, or Termux through proot-distro
  Ubuntu) to a running Lean shard in one command: apt packages, rustup, elan (toolchain pinned by
  `verified/lean-toolchain`), both repos, `cargo build --release`, `lake build`, then `unit-lean-stage --shard`.
  Tested on this box into a fresh directory with `--no-run`: both binaries built in 3.5 min wall (3 min CPU, 1.2 GB
  peak). Native Termux cannot run Lean (bionic libc); the script says so and prints the proot steps. The bundle
  (`scripts/bundle.sh`, 57 MB) now carries the checker and `run_lean_shard.sh D I N [W] [J]` for x86-64 Linux boxes
  without any toolchain.
- **Scalar literal status tried and rejected** (12:55): `lstatU`/`evalHA` on `UInt8` codes instead of `Option Bool`
  was slower, 4.73 s vs 3.72 s (20 MB) and 79 s vs 71 s (482 MB), on the loaded box; reverted to the array/Option form.

### 2026-10-28 ~13:00: SymSAT 1.0 (public release, MIT)
Public copy at https://github.com/lioncash3k6-ux/SymSAT-1.0: the working tree of `main` as one release commit (code,
Lean project, docs, results, covers; without `context/`, the private conversation exports), `LICENSE` MIT, Cargo
version 1.0.0. Sharding to other machines in one command: `scripts/bootstrap.sh` / `monster bootstrap` (installs Rust and
Lean, clones the public repo and the catalogue repo, builds, starts `unit-lean-stage --shard I/N`), the 57 MB bundle
with the checker for toolchain-free x86-64 boxes, and `monster merge-shards --out DIR SHARD...` to merge the shards'
`verified.jsonl` and record files. The private repo `SymSAT` stays the working repo (full history, chats, snapshots).
