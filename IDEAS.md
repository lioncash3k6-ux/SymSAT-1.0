# Ideas: theory, validity, status

Every idea gets two verdicts: is it **sound** (can it produce a false UNSAT?), and was it **measured**? Ideas come
from the repos (v2–v11, cascade master, Sophyra, the proof repos) and from SAT, proof-complexity and combinatorics
literature. "Measured" numbers are in RESULTS.md.

## Kept

| idea | source / theory | soundness | status |
|---|---|---|---|
| Catalogue gluing over one vertex's neighbourhoods | McKay–Radziszowski 1995 | exact case split; trusts catalogue completeness | core of monster |
| **Minimum-degree route with a flag certificate for the dense case** (2026-10-27): v of minimum red degree δ; δ ≤ 9 by the gluing stages d = 7, 8, 9 (cheap: 71 + 358 + 1,587 units), δ ≥ 10 means every red degree in [10,13], refuted (if at all) by `monster flag --degree 10,13` at K=8 | degree bounds from R(3,5) = 14 and R(4,4) = 18; the flag run is an assumption-form certificate for exactly the case δ ≥ 10 | sound: a case split whose dense half is a certified SDP statement | d=7 done, d=9 running, K=8 flag runs for [10,13] and [11,13] running (CONTINUE.md 5-LATEST+2). Replaces the 145-day d=10 + d=12 stages if the SDP certifies |
| LRAT with antecedent hints for pair/unit certification (`HintChecker`) | LRAT (Cruz-Filipe et al. 2017) | independent linear checker; the solver's hints are untrusted | certification 65x → ~1.1x of solve time |
| Parity degree route (only even d, N odd) | Gauthier–Brown 2024 (arXiv 2404.01761) | handshake lemma | default for odd N |
| Gray-edge generalisations (units) | Gauthier–Brown; repo v10 | glue lemma re-checked per pair, cover untrusted | **best engine so far**: 3,079 conflicts/pair at d=10 vs pair mode's 179,446 |
| Incremental SAT with assumptions, trail reuse | Eén–Sörensson (MiniSat); CaDiCaL trail reuse | assumptions never become axioms | in solver |
| Failed-assumption cores as generalisations | IC3/PDR cube generalisation (Bradley 2011); MUS extraction | core clause is RUP, checked | core cache in stream/unit modes |
| Independent forward RUP checking | DRAT/LRAT practice (Heule, Wetzler) | checker shares no code with the solver | sampled or full certification |
| Witness re-check on full K_N | n/a | brute force | every SAT result |

## Measured negatives (sound, but slower here)

| idea | theory | result |
|---|---|---|
| Stream mode: every edge of one side gray, catalogue graphs as assumptions, core cache | extreme generalisation plus learned-clause transfer | R(3,7): 5.6× slower; R(4,5) d=8: >2× slower; formula 10–40× larger |
| All-gray A × v10 B units | same idea, applied to the small side | R(4,5) d=8: >3× slower than pair mode |
| Degree-window axioms: every vertex's red degree in [7,13] | Resolution cannot count (Haken 1985; Ramsey CNF lower bounds, Krishnamurthy–Moll; Pudlák). Inject counting facts the route already rests on (R(3,5)=14, R(4,4)=18) | sound given the same lemma as the route. d=8: −10% conflicts, +35% time (counter bloat). Unit mode (d=12 sample): 32x slower. Closed |
| Per-pair solving at d=10 | n/a | 7.4 CPU-s/pair, so years for 41M pairs |

From the repo (v7, not re-measured): SBVA bicliques (0.8×), grouped shared learning (2.8–6.3× slower), Chris
age/priority memory policy (no consistent gain), kissat (0.4–0.5×), CaDiCaL option tweaks (none helped).

## Rejected as unsound or unusable

| idea | why |
|---|---|
| Lex "axioms" ¬e(k,w) ∨ e(k+1,w) (R(5,5)-43, R(4,5)-25 proof repos) | The audit shows they make known-SAT formulas UNSAT (K17 R(4,4), K42 R(5,5)). Each SR step checked in isolation with deletion does not compose. |
| "Augmented CNF is UNSAT by BCP" as an R(4,5) proof | no checked derivation of the augmented clauses from the bare CNF (audit) |
| Min-degree counting filters on the parity route | They assume v has minimum degree; invalid on the parity route (repo DEGREE_PARITY.md) |
| Orbit-NS / FI-stability certificates (cascade master) for the gluing route | Sound over F_p for symmetric formulas, but the degree needed (17+ for R(5,5) at cap 10, Phase C1 for R(4,5)) is out of reach, and certificates are mod p only |

## Implemented, being measured

| idea | theory | soundness | first numbers |
|---|---|---|---|
| Learnt-clause vivification (`--vivify`) | Luo et al. 2017; CaDiCaL/Kissat | each shortened clause is RUP, logged, checked in tests | unit (17,698): −7% conflicts, −7% time; 24-unit A/B running |
| Focused/stable mode switching (`--stable`) | Kissat/CaDiCaL stabilisation (Biere–Fleury); target phases (Biere–Fleury 2020 "Chasing target phases") | search heuristic only | unit (17,698): +5% (noise); v11 data says stabilize=0 costs CaDiCaL 1.6× on these units; 24-unit A/B pending |
| Cube-and-conquer inside a unit (`--cube-budget`) | Heule et al. cube-and-conquer; v11 | cube cores and resolvents are LRAT lemmas with hints, hint-checked | **unit-mode default (5k/5k)**: paired d=10 sample secs 0.27 (CI 0.20-0.43); 1,625 units certified in the d=7,8,9 run |
| Own gray-edge cover builder (`monster cover`) | Gauthier–Brown; greedy set cover (Johnson/Lovász ln n bound) | covers are untrusted (glue check) | r44/n14 g6: 4,915 generalisations vs v10's 4,157 |

## Candidates still to try (ranked by expected value)

1. **Cover optimisation by cost, not count.** Choose gray edges and grouping to minimise predicted conflicts/pair rather than unit count.
   v10/v11 found A0B8 (d=12) and A6B6 (d=10) by sampling. A cost model learned from monster's per-unit logs
   (clause count, gray count, pairs) could choose better. Sound: covers are untrusted.
4. **Cardinality via native PB propagation** instead of CNF counters (RoundingSAT-style). The degree axioms lost only
   because of encoding size; a native at-most/at-least propagator has no bloat. Proofs would need VeriPB or
   RUP-expandable reasons. Sound if reasons are logged as clauses.
5. **Symmetry inside units.** Aut(base_A, gray_A) × Aut(base_B, gray_B) acting on cross and gray variables. Satsuma found
   little at d=10 (v11: 0 SR lines) but 2× speed at d=12. Must be SR-logged, never as axioms.
6. **Portfolio of restart policies** per hard unit (glucose vs Luby vs stable mode), choosing by early conflict rate.
   Sound.
7. **Local search (Sophyra / Exoo-style) for the SAT side**, e.g. hunting (4,6)-good colourings beyond 35
   vertices or checking lower bounds. Irrelevant to upper bounds; witnesses are self-certifying.

## External review notes (2026-10-26), with verdicts
| suggestion | verdict |
|---|---|
| Prior art: SEL (SAT 2017), Symmetry Propagation, CosySEL (VMCAI 2023), SAT Modulo Symmetries (CP 2021, TOCL 2024) | Agreed. Novelty is narrower: graph-level canonical pattern store over all of S_N, plus lemmas proved inside F, plus LRAT expansion checked by cake_lpr |
| Replace image expansion by single SR steps with σ as witness | **Not valid as stated.** SR checks the witness against the whole current database; learned lemmas are not σ-closed, so the check fails in general. Deleting lemmas first loses them. Same non-composition trap as the R(5,5) audit. Correct options: our symmetric rule (induction on S_N-invariance of F), or renamed derivations (expansion). Formal verification at scale needs a verified checker with a symmetry rule (cake_lpr HOL4 or the Lean LSR checker), a real project |
| Edge-count bounds E(s,t,n) as certified lemmas (VeriPB cutting planes) | Valid; planned as native PB reasoning. Payoff in full-formula pattern CDCL (on the parity gluing route the counting filters kill 0 pairs) |
| Flag algebras / SDP (Lidický–Pfender) for stronger density lemmas | **Done as `monster flag` (2026-10-26)**: exact finite-N certificates prove R(3,3), R(3,4), R(3,5), R(4,4), R(3,6) tight at K <= 7; not R(3,7) or R(4,5) at K=7 (RESULTS.md). Reference checked: Lidický, Pfender, "Semidefinite Programming and Ramsey Numbers", arXiv 1704.03592, DOI 10.1137/18M1169473; exact values there include R(K4-,K4-,K4-) = 28, R(Q3,Q3) = 13, R(K8,C5) = 29 |
| nauty/Traces/dejavu for canonical labelling | Not needed now: twin pruning took labelling from 61 s to ~0 s; embedding search dominates |
| Target: end-to-end verified R(4,5)=25 from the plain formula (compare Gauthier–Brown HOL4) | Agreed as the defined goal. Path: cube lemmas proved in F, then pattern CDCL derives ⊥ from cube lemmas + images + library (replacing trusted catalogue completeness), symmetric checker, later a verified checker with a symmetry rule. Blocker: per-conflict pattern cost on K25 |

## Reinforcement learning (2026-10-26): where it fits safely
Soundness is never at stake: every claim is re-checked, so a learned policy only changes speed. Candidates, by value:
1. **Pattern admission/eviction bandit.** Reward = images found per unit search time; per-pattern stats already exist
   (`PatternProp::yield_table`). The LBD cap is the strongest knob seen so far (42× fewer conflicts on R(3,5)/K14).
2. **Per-cube parameter profiles** (Thompson sampling over LBD cap, node budget, restart mode, vivify); reward = cube
   time. The ESSENCE bandit idea, applied where it is safe.
3. **Branching policy**: vertex-major vs VSIDS, learned from cube times.
4. **Lemma-library selection**: which rooted lemmas are worth proving for given (s,t,N).
Start with bandits; consider learned networks only if the bandits show signal.

## Research notes (2026-10-26, arXiv)
- **Gauthier & Brown, "A Formal Proof of R(4,5)=25"** (arXiv 2404.01761, ITP 2024): HOL4, MiniSat for the gluing
  lemmas, a generalisation algorithm to reduce lemma count, coverage checked by a custom SAT solver with an
  isomorphism checker. This is the benchmark for our end-to-end goal. Our route differs: full formula plus a symmetry
  rule plus a Lean-verified checker, with no trusted catalogue (target).
- **Proof systems with symmetry** (survey in Gaevoy, "The Power of Small Symmetries", arXiv 2606.25895, MFCS 2026):
  - **global** symmetries (Aut of the original formula, applied to derived clauses; Krishnamurthy 1985,
    Arai–Urquhart 2000): our current image rule.
  - **local** symmetries (symmetries of a subformula): exponentially separated from global. **Our planned "contextual
    import" is a local-symmetry rule** (inside a vertex's blue neighbourhood the R(4,5) sub-formula is (4,4)-symmetric,
    so colour swap applies there).
  - **dynamic** symmetries: superpolynomial lower bounds open.
  - "small" symmetries (acting on few variables) form strict hierarchies and are exponentially stronger than Resolution.
- **Krishnamurthy's symmetry rule gives short proofs of Ramsey-theorem tautologies** by imitating the recursive proof
  (reported by Schweitzer–Seebach, arXiv 2101.05142). Our rooted-lemma library is a computational, verified instance;
  confirm the original citation before quoting.
- **Szeider's homomorphism rule** is strictly stronger than the symmetry rule. Our injective-map import (lemmas proved on
  K_m used in K_N) is a homomorphism-style rule.
- **Open small Ramsey numbers:** R(3,10) ∈ {40, 41} (Angeltveit, arXiv 2401.00392, R(3,10) ≤ 41); R(4,6) unknown;
  43 ≤ R(5,5) ≤ 46 (status per arXiv 2509.03784). Gap-1 target candidates: R(3,10) (40 vs 41).

## Verdicts on external idea pastes (2026-10-26, session 4345886d)
- **Everything as ternary cubes {0,1,*}, consensus, volume bound, relational symbols (=, ≠), grammar compression.**
  Clause = falsifying cube and UNSAT = cover is the standard geometric view; consensus is resolution (inherits its
  lower bounds, incl. pigeonhole). Our v10 gray-edge covers already are ternary strings. The volume bound is Erdős's
  1947 argument: R(4,4)/K18 clause volume is ~96x the space (needs < 1), so it certifies nothing beyond K6.
  Relational/parity symbols target XOR structure that Ramsey clauses do not have (CryptoMiniSat's Gauss covers XOR).
  "Grammar compression of near-identical strings" is what the pattern store already does, stronger (every S_N image,
  with a checked image rule). Kept: bitplane AND/popcount operations, now in the domain-based embedding search.
- **Belnap 4-valued trits; Walsh–Hadamard dual basis; basis switching; signed weights.** Correct math (O'Donnell;
  uncertainty principle |supp f|·|supp f^| ≥ 2^n). Our red/blue bitplanes already are the two planes. A Ramsey clause
  (AND of 6 literals) has all 64 Walsh coefficients nonzero, so a per-region basis choice would always pick cubes here.
  Signed weights where contradictions cancel = algebraic proof systems (Nullstellensatz: dead end on gluing pairs,
  RESULTS.md; symmetric SOS / flag algebras: built later the same day as `monster flag`, see the recovered-ideas table).
- **Symmetric/antisymmetric decomposition, 2-SAT SCCs, orbits, determinant vs permanent.** Correct (isotypic
  decomposition; preorder = equivalence + partial order). Connections that matter: (1) "ask whether an orbit survives,
  break symmetry only by branching" is already our design (symmetric learning, no up-front symmetry-breaking
  predicates, ground rule 1); (2) S_N representation theory (Specht modules) is exactly what block-diagonalises the
  symmetric SOS / flag-algebra SDP, which is where this belongs. Determinant/Pfaffian computation by cancellation is
  Valiant's holographic algorithms; the Cai–Lu–Xia dichotomy theorems map exactly which counting CSPs it captures, and
  general SAT / Ramsey constraints are outside (unless P = NP). "At most one" belongs to native cardinality reasoning
  (next-step 5, VeriPB). No action beyond those two existing items.
- **1D ternary edge array projecting onto the 2D pair structure; switching representations; compressed boundary
  state; F3 vs three states** (fourth paste). Stages "ternary stream" and "pair-space projection" are the engine as it
  is: `evar(i,j) = j(j-1)/2 + i`, per-vertex red/blue bitplanes = rows of the signed matrix A (a Seidel matrix), and
  the anchor filter counts shared neighbours by colour pair. "Proposals checked before use" is ground rule 2. We
  already switch geometries: branching on vertex neighbourhoods (catalogue cubes), propagation on edges, learning on
  S_N orbits. Spectral facts (Hoffman, Lovász theta) bound a given graph's cliques from above, the wrong direction for
  refutation; the checkable form of "change basis, cancel, rule out a family" is symmetric SOS (idea 3 below). A
  compressed boundary state cannot exist exactly: any two edges lie in a common K4, so for s >= 4 every pair of edge
  variables shares a clause and any traversal's boundary is everything unprocessed (3^Θ(n²) states); the working form
  is isomorph-free generation (McKay), i.e. the catalogue route. Three states, not F3, is what we use.

## Ideas from the chats that were never written here (recovered 2026-10-26 from context/chats/)
Status as of 2026-10-26 13:00 UTC. Sources: 2026-10-25_1900_95cc9e5d.md (22:33 "breakthrough ideas", 23:09 BitNet,
23:17 sememe-level, 03:10 "major advancement"), 2026-10-26_0816_1f58dadf.md (10:08 paste).
| idea | source | status |
|---|---|---|
| **Incremental matching across assignments**: keep partial pattern matches alive as edges are assigned and undone (Rete networks, incremental view maintenance / DBSP), or worst-case-optimal joins (Generic Join, Leapfrog Triejoin), since a pattern match is a conjunctive query over red/blue edge relations | 03:10 #1, chosen by the user ("1 and 3") | Two cheap forms measured negative 2026-10-26 (RESULTS.md: exact repeats 0.8–1.2% of scans; global candidate sets prune 0.01% of nodes). The anchored search is already a delta evaluation; a Rete store of partial matches looks too large. Speed now has to come from cheaper deep search or fewer searches (yield throttling, RL #1) |
| **Weisfeiler–Leman refinement / Glasgow "supplemental graphs"**: iterate neighbourhood colour histograms, and filter domains with path-count (length-2 paths) supplemental graphs, before and during backtracking | 23:09 BitNet #2 ("goes into idea 2 now"), 10:08 paste (McCreesh–Prosser) | Measured negative as global candidate sets (0.66% of calls, 0.01% of nodes); inside one search the domain filtering already does it |
| **Batched bit-sliced ternary image evaluation** (T-MAC / bitnet.cpp lookup tables): test thousands of candidate images as one ternary matrix–vector product | 23:09 BitNet #1 | Open |
| **Symmetric SOS / flag-algebra certificates**, exact rational rounding so the certificate is checkable | 22:33 idea 3, chosen by the user ("focus on 1 2 and 3") | **Working (2026-10-26)**: `monster flag`, finite-N flag SDP with exactly checked certificates; tight R(3,5) <= 14 and R(4,4) <= 18 in < 1 s, R(4,5) <= 28 at K=7 (RESULTS.md). Next: K=8, degree constraints, parity and a d=10 case split all measured at K=7 without success (RESULTS.md) |
| **Symmetric cutting planes**: counting facts (degree sums, edge counts, Goodman) derived once and applied at every vertex by symmetry, VeriPB-logged | 03:10 #2 | Open (candidate 4 above is the non-symmetric part) |
| **Aim at an open gap-1 bound**: R(3,10) ∈ {40, 41} (Angeltveit 2024) | 03:10 #4; last research note above | Open; needs the engine items first |
| Portfolio over lemma orders / seeds against heavy tails (Gomes–Selman) | 10:08 paste | Partly answered: `--lib lift` removed the heavy tail on the ladder (RESULTS.md); a portfolio is still cheap insurance for hard cubes |
| Close the library under itself (re-prove each lemma with the others present) | 10:08 paste | Rejected with evidence: the lemmas already come out as their full rooted structures on K25, nothing to shorten (session 1f58dadf, 10:12) |
| Bit-parallel local search for lower bounds | 23:09 BitNet #5 | = candidate 7 above |
| Ternary learned heuristics in the hot loop; F3 bit-sliced elimination | 23:09 BitNet #3, #4 | Low priority (RL section; F3 needs p > n for orbit averaging) |
| Hyperdimensional computing / vector symbolic architectures ("sememe-level representation") | 23:17 | No concrete use found for exact refutation |
- **Holographic algorithms for Ramsey counting** (fifth paste: basis change on the triangle-validity tensor, transfer
  matrices, crossover gadgets). The triangle constraint is the symmetric signature [0,1,1,0] (not-all-equal on 3
  variables). Its support has 6 points, so it is not affine, not product type, and it mixes parities, so it is not a
  standard matchgate signature; the Cai–Lu–Xia dichotomies put #CSP/Holant over such signatures outside the tractable
  classes in general. The K_n triangle network also has treewidth Θ(n²), so transfer-matrix states are exponential
  (the paste itself notes this). The paste's direction C, compressing into symmetry invariants and cancelling there,
  is what works: the flag-algebra SDP (`monster flag`) compresses to densities of small subgraphs and gets its
  "cancellation" from positive semidefiniteness, with exactly checked certificates (tight R(4,4) <= 18 in 0.28 s).
  No further action on the holographic route.
- **Holographic memory** (sixth paste, 2026-10-26 ~23:00: hyperdimensional vectors as a tabu memory, seed-layer SLS,
  spectral objective). The SLS layers are for lower bounds (out of scope). The memory is lossy, so in an exact prover
  it may only steer, never prune or justify; what it approximates ("same up to symmetry") we compute exactly with
  canonical forms; and unit order does not change the total work of a complete refutation unless knowledge transfers
  between units, which measured weak (pattern memory across cubes ~25-30%; stream mode 2-5.6x slower). No action.
  Its exact form ("a fixed-size bit memory of one side, queried by AND/OR") is the feasible-cone engine below.
- **De Loera-Wesley, "Ramsey numbers through the lenses of polynomial ideals and Nullstellensätze"** (arXiv 2209.13859,
  2022, rev. 2025; not about holography). Ramsey as a polynomial system over the algebraic closure of F2; a Builder
  strategy in the restricted online Ramsey game on n vertices gives a Hilbert Nullstellensatz certificate of degree
  R~(r,s;n) - 1 (an upper bound: R(3,3) <= 6 has a degree-5 certificate while R~(3,3;6) = 8). No symmetry reduction;
  the authors call certificates impractical beyond small cases. Consistent with our Nullstellensatz dead end; the
  algebraic route that works here is the symmetry-reduced SOS (`monster flag`). No action.
- **Feasible-cone engine: built and measured negative (2026-10-26 ~23:55; RESULTS.md, "Feasible-cone engine
  prototype").** As a standalone search (forward checking, degree windows, arc consistency) >= 175x slower than CDCL
  on a d=8 pair; as a propagator inside CDCL (`MONSTER_CONEPROP`) -11% conflicts on d=10 pairs and 2-8x slower. Unit
  propagation on the pair CNF already captures most per-vertex cone consistency; the hardness is not local. The
  original proposal, kept for the record:
- **(Proposal) feasible-cone engine for the gluing units.** With A the (3,5,d)-graph on v's red side and
  B the (4,4,24-d)-graph on its blue side, each b in B has a cone R_b (its red neighbours in A). The constraints are
  exactly: unary (A \ R_b holds no blue K4 of A); binary (bb' red: R_b ∩ R_b' holds no red edge of A; bb' blue: the
  common blue neighbours hold no blue triangle of A); ternary (red triangle in B: no common red neighbour; blue
  triangle in B: the common blue neighbours hold no blue edge of A). Domains are bitsets over at most 2^d cones,
  compatibility rows are computed once per A, and propagation is arc consistency by AND/OR. This is the classical
  feasible-cone gluing (Radziszowski-Kreher; Goedgebeur-Radziszowski for R(3,k)). Unit mode today spends ~2.3 s per
  (A,B) pair (1,316 s per d=10 unit of ~580 pairs); d=10 + d=12 are 58.3M pairs (~145 days). At ~10 ms per pair
  (an estimate, not measured) they would take ~10 h on 16 cores. Test first, uncertified: all 358 d=8 pairs and the
  pairs of the 16-unit d=10 sample, verdicts must agree with unit mode; drop it if < 10x faster per pair.
  Certification is the real cost: extension variables for cones (a prefix trie per vertex makes "b has some cone"
  RUP, after which every domain deletion and backtrack is a RUP step), defined once for all pairs, plus a definition
  rule in the Lean checker.
- **"Polynomial routes" paste (seventh paste, 2026-10-26 ~23:45: Erdős–Szekeres and the Campos–Griffiths–Morris–
  Sahasrabudhe book algorithm, derandomised and explicit Ramsey graphs, perfect graphs and theta, closed forms for
  sparse targets, SDP / flags, fixed-parameter structure).** Correct as a survey; for an exact proof of R(4,5) <= 25
  only two points touch upper bounds and both are in use: the "follow the larger colour class" step is the
  neighbourhood split of the gluing route, its book step is SymSAT's rooted book lemmas, and SDP / flags are
  `monster flag`. The asymptotic book algorithm gives (4-ε)^k, nowhere near 25. Derandomisation, explicit Ramsey
  graphs and fixed-parameter (seeded / low-rank / Cayley) searches construct colourings, i.e. lower bounds; theta
  bounds a given graph's cliques from above, the wrong direction for refutation (as recorded above); closed forms
  cover paths, cycles, trees and stars, not K4 vs K5. No action; nothing in it strengthens the cone propagator.

## Ideas from the review pastes of 2026-10-26 ~15:00 (status)
| idea | status |
|---|---|
| Bank d=8 fully certified | **Running** (`symsat-d8-certified`, every task checked) |
| Kill criterion for hybrid on d=10 units (within 2-3x of unit mode or drop it) | **Met: dropped.** 11x and 24x slower on the two common units; unit mode is the d=10 engine |
| Throttle patterns by images per search node (not per call) | Built (`MONSTER_NODE_THROTTLE`); K25: -37% nodes for -15% images at 30k; d=8 ab running |
| Vertex vivification of stored patterns (delete a vertex while still RUP) | Built (`MONSTER_PATVIV`); **0 of 18** K25 patterns shrink under unit propagation. Untried: test each deletion with a bounded solve instead |
| Watched near-miss embeddings (cache two-unassigned images, two watched edges) | Not built. Found images already become database clauses with watched literals; a cached near-miss does not remove the per-literal scan, which still runs for every pattern; recording near-misses needs a two-slack search, which costs more than the current one. Low expected value |
| Order d=10 units by B-side generalisation for transfer | Queued: needs a structured sample (a few B gens x all 17 A gens) in two orders via `--units` files, one worker per side for contiguity |
| Flag-guided cubes (certify a positive minimum density of a class set S, then cube on S) | Queued. Sound in principle (a certified density lower bound is a valid lemma), but cubes that fix one 7-vertex class pin only 21 edges, so each is nearly the whole problem; the likelier use is the global lemma itself as a cut |
| Flag ladder R(3,6), R(3,7) | Done: R(3,6) <= 18 tight at K=7; R(3,7) <= 23 not at K=7 |

## Status after the evening of 2026-10-26 (measured; details in RESULTS.md)
| idea | verdict |
|---|---|
| Library-only patterns (`MONSTER_LIBONLY`) | **Keep for hybrid**: 5.9x faster on the d=8 hybrid sample (time ratio 0.169, CI 0.147-0.207); loses on small full formulas where learned patterns pay; on d=10 units 5.8x slower than unit mode (8 of 16 units, 2.0-13.4x each), so unit mode stays the d=10 engine; R(3,6)/K18 as one formula not solved in 1 h (with or without vertex branching) |
| Lemma mining (`MONSTER_MINE`) | Sound (Lean-checked). Online: 16x on library-free R(3,5)/K14, 50x worse on R(4,4)/K18. Next: offline mining for K25, cached with the library |
| Vertex-major branching (`MONSTER_BRANCH=vertex`) | Portfolio candidate: 36x on R(3,6)/K17, 2.8x per conflict on R(3,6)/K18, far worse on R(4,4)/K17 |
| "CDCL learns local clauses" (premise of sharing learned clauses) | **False at scale**: most learned clauses span all or nearly all vertices on R(3,6)/K18 and K25; 99.9% rejected as patterns. Symmetric lemmas, not shared learned clauses, are the scalable form |
| Minimum-degree case split + flags | Partial: flags refute [12,13] (17.4M pairs), not [11,13] (124.3M pairs) |
| Book axioms as CNF (`glue --book-axioms`) | Negative: -21% conflicts, 21x slower |
| Node throttle by images per search node | Neutral on complete solves |
| Vertex vivification by unit propagation | 0 of 18 K25 patterns shrink; bounded-solve variant untried |
| Small side free at d=10 (`--gray-a 99`) | **Negative**: none of the 4 sample units finished in 23,095 s, past the ~22,400 s per-unit break-even (4,157 units instead of 70,669); stopped 22:47 |
| SR proof format (Heule/Codel; 39-line SR proof of R(4,4) <= 18) for R(4,5) <= 25 | SR witnesses carry substitutions, so WLOG/symmetry steps are one line each | Only compresses symmetry; the catalogues already quotient it (units have trivial groups). Useful for making catalogue completeness a checked step, not for the gluing stages. RESULTS 2026-10-27 ~22:50 |

## Status after 2026-10-28 (speed routes)
Closed with numbers (RESULTS): degree axioms (32x slower in unit mode), hybrid on d=10 (11-24x slower), library-only on d=10
(5.8x), stream / all-gray (2-5.6x), book axioms (21x), cone propagator (2-8x), alternative d=10 covers (noise), K=8 flag SDP
(no certificate). SR with a symmetry witness in place of images: unsound with learned lemmas (above). Still open, unmeasured on
R(4,5) d=10: one-sided / partial cubes (paused; R(3,6) ladder step did not finish), pattern vivification, cheaper embedding,
native cardinality (PB) with a verified checker. The sure lever is machines: `glue --shard I/N` + `scripts/bundle.sh`.

## Counting route (2026-10-28): CLOSED by measurement
Cheap counting kills (vertex windows, degree-flow feasibility, edge-level double counting over common neighbourhoods)
refute 0 of 358 d=8 pairs and 0 of 40,945,408 d=10 pairs (`monster count-kill`, RESULTS "~14:40"). The catalogues
already satisfy every local condition; the hardness is the joint cross-edge search. Do not retry counting-only pruning;
cardinality reasoning inside the search was also measured slower (degree axioms, cone propagator).

## Biclique / SBVA reencoding of units (2026-10-28): CLOSED by measurement
Definition variables for the bipartite cross patterns: -30% conflicts at best, 1.7-9x slower in every variant
(plain, non-decision auxiliaries, binary fast path, blue-only); `glue --biclique` stays as a measurement switch
(RESULTS "~15:20"). A verifiable form (semantic definition variables in the checker's table) was designed, not built.
