# What exactly is verified, and what is trusted

## The theorem
`MonsterVerified.check_sound` (MonsterVerified/Checker.lean):

```lean
theorem check_sound {s t n : Nat} {steps : List Step} (h : check s t n steps = true) :
    ∀ c : Nat → Nat → Bool, ¬ Good s t n c
```
`Good s t n c` (Basic.lean) is stated **directly on colourings**, not on a CNF. For every list `S` of distinct vertices
below `n`: if `|S| = s`, some pair in `S` is blue; if `|S| = t`, some pair in `S` is red. Colours are read on unordered
pairs through `col`. So the conclusion is the Ramsey statement R(s,t) ≤ n itself.

## Is the link from CNF to Ramsey statement trusted? No, it is proved
- The checker **generates the formula itself** from (s,t,n) (`originals`, Checker.lean / Gen.lean). It reads no
  external CNF.
- `genClause_sound` proves that every generated clique clause holds in every good colouring.
- Variable numbering comes from an edge table that is **checked at run time** on every use (`edgeVar` verifies
  `E[v] = (min, max)` and `min < max`). Soundness therefore never depends on how the table was built, or on any
  arithmetic about the numbering.
- Generated sizes (evaluated in Lean): R(4,4)/K18 → 6,120 clauses over 153 variables; R(3,5)/K14 → 2,366; R(4,5)/K25 →
  65,780. These match C(18,4)·2, C(18,2), C(14,3)+C(14,5) and C(25,4)+C(25,5).

## The invariant and the rules
Invariant (`DBSound`): every clause in the database holds in every good colouring.
- **LRAT step** (Rup.lean, `rup_step_sound`). The negated lemma is a partial assignment, and each hint must be unit
  (extending the assignment) or falsified. If a good colouring falsified the lemma, it would agree with the
  assignment, satisfy each (sound) hint, and so force each unit literal; the final falsified hint is then a
  contradiction.
- **Image step** (Image.lean, `image_sound`). Line `id i src p0..p{n-1}` (or `f` for colour swap). The checker verifies
  that `p` is a permutation of {0..n-1} (`permOK`). With `f`, it also verifies `s = t`. The new clause is `p` (with
  colours swapped if `f`) applied to clause `src`, each image variable checked against the edge table. Soundness
  (`good_relabel`): if `c` is good, then `x,y ↦ col c (p x) (p y)` (xor `f`) is good. Every k-set maps to a k-set because
  `p` is injective, and when `f` is set, red s-cliques and blue s-cliques swap, which needs `s = t`. Since `src` holds in
  the relabelled colouring, its image holds in `c`.
- **Sub-instances and the lift step** (Lift.lean, `lift_sound`; Checker.lean, `stepFn_ok`). This is the local-symmetry
  rule. `o s' t' m` opens a sub-instance with its **own** database, initialised with the original clauses of
  F(s',t',m) on the vertices 0..m-1. `s k <line>` runs an LRAT or image step inside sub-instance k. Images there
  permute its m vertices, and colour swap needs `s' = t'`. The invariant covers every sub-database: each clause holds
  in every good colouring of K_m for (s',t'). Line `id l k src v r|b e0..e{m-1} 0` adds to the **main** database the
  clause `e(C) ∨ (some edge v–e_x, x < m, is not of the apex colour)`, where `C` = clause `src` of sub-instance k. The
  checker verifies four things:
  - `e` is injective into {0..n-1} and avoids the apex v (`embOK`), and v < n.
  - `e` names exactly m vertices, so the context covers the whole of K_m and not just the vertices C mentions.
  - (s,t) = (s'+1,t') for a red apex, or (s',t'+1) for a blue one (`liftParams`).
  - `src` is looked up in the sub-database only.

  Soundness (`good_restrict`): if every edge v–e_x has the apex colour, the pulled-back colouring
  `x,y ↦ col c (e x) (e y)` is good for (s',t') on K_m, because a forbidden clique there plus v would be a forbidden
  clique of c. So C holds there, and e(C) holds in c. Otherwise a context literal holds.

  Colour swap is never applied to a main clause through this rule. A sub-instance with s' = t' may swap colours inside
  its own database, which is sound because F(s',s',m) is swap-invariant. A clause learned in the main database can
  depend on constraints outside the neighbourhood, so the two-database split is what makes the local symmetry sound.
- **Acceptance**: the empty clause was added, so by the invariant no good colouring exists (`no_good_of_sound_empty`).

## Axioms and trust
- `#print axioms MonsterVerified.check_sound` gives `propext, Classical.choice, Quot.sound` (Lean's standard
  axioms). No `sorry`, no custom axioms.
- **Theorems for concrete instances** (Theorems.lean: `R34_le_9`, `R35_le_14`, `R44_le_18`) evaluate the checker with
  `native_decide`, so they **additionally trust Lean's compiler and runtime** (auxiliary `native_decide` axioms appear
  in `#print axioms`).
- **Kernel-only theorems** (no compiler trust): `R33_le_6_kernel` (MonsterVerified/KernelR33.lean). A lift proof of
  R(3,3) ≤ 6 (`proofs/lift/R33_lift.slrat`) also checks kernel-only. Proofs are converted to a Lean term by
  `monster slrat2lean` (untrusted; the kernel re-checks every step). A kernel-only R(4,4) ≤ 18 is NOT done: the first
  attempt used 64 GB and was OOM-killed.
- The executable `checker` is compiled from the same `check` function, so it trusts the Lean compiler too.
- The parser (Parse.lean) is untrusted: whatever it produces is checked by `check`.

## Pinned artefacts
`proofs/R44_K18.slrat` (689 lines): sha256 33f716399f39e9937a1e99d2f234d0db5c7dcf017a636c9f1193d911fdfe46ed
(regenerate with `monster full --s 4 --t 4 --n 18 --patterns --lemmas --books --slrat FILE`; solver runs are
deterministic).

## Framing
This checker is specialised to Ramsey formulas (it generates F itself and knows the vertex-permutation and
colour-swap symmetries). It is not a general-purpose verified SAT pipeline. Its advantage is certificate size: the
symmetry rule replaces case splits, so R(4,4) ≤ 18 needs 689 proof lines.

## The assumption rule (Assume.lean; added 2026-10-27 for the gluing route's per-unit proofs)
An assumption sub-database (`a l1 .. lk 0`) holds F(s,t,n) **reduced under** `A = {l1..lk}` (every literal whose
negation is in `A` is removed: `reduceUnder`; the literals must be non-zero), and accepts only LRAT steps
(`u k id lits 0 hints 0`); no image or lift steps, because the assumption is not symmetric. Its invariant is
`SoundUnder`: every clause holds in every good colouring that satisfies all of `A`. Closing (`id a k src 0`) adds
`¬A ∨ C` to the **main** database for a clause `C` of the sub-database (`closeClause`, `close_sound`): a good colouring
that satisfies `A` satisfies `C`; one that does not satisfies some `¬l`. `check_sound` and `checkLemma_sound` keep
the axiom set `[propext, Classical.choice, Quot.sound]`.

For a gluing unit, `monster unit-lean` emits the unit's fixed edges as `A`, the solver's LRAT lines verbatim (GAMMA
variables renamed to K_n edge variables) and one close of the empty clause, so the main database gains `¬A`:
no good colouring of K_n extends the unit. `checker --lemma FILE` (lemma mode, `checkLemma`) runs every step and
reports the last main clause; it does not need an empty clause.

### Deletion and streaming (added later on 2026-10-27)
- `u k d id1 .. idn 0` forgets clauses of assumption sub-database `k` (`deleteAll`: the slots become `none`, ids are
  never reused). Soundness is `deleteAll_sound_under`: the invariant is per retained clause, so forgetting only
  weakens the database. The Lean checker ignores unknown ids; the reference checker rejects them.
- Streaming (Stream.lean): `OKSt s t n` packs a state with its `StOK` proof; its only constructors are `initOK`
  (the originals) and `stepOK` (one `stepFn` step, proof by `stepFn_ok`). `checker --lemma FILE` reads the file
  line by line (`parseLine`, `runStream` in Main.lean), threading an `OKSt`, so only the live databases are held;
  what it reports is sound by `OKSt.clause_sound` (last main clause) or `OKSt.done_sound` (empty clause), whatever
  the IO loop does. Axioms: `[propext, Quot.sound]` for both. The whole-text theorems (`check_sound`,
  `checkLemmaText_sound`) are unchanged.

## Assembly lemmas: parity, degree bounds, the assembled statement (added 2026-10-28; docs/ASSEMBLY.md parts 5a-5c)
Three new modules, none of which touches the checker: `Parity.lean` (imports Basic), `Degree.lean` (imports Lift and
Parity) and `Assembly.lean` (imports Theorems and Degree).
- **Parity (5a).** `redDegree c n v` is the length of `redNbrs c n v = (range n).filter (u ≠ v ∧ col c v u)`.
  `sum_redDegree_even`: the sum of the red degrees over K_n is even (it is the double sum of the symmetric
  edge indicator, which vanishes on the diagonal; `double_sum_even` proves this by induction on `n`, adding the new
  row and column, which are equal). `exists_even_red_degree_odd (hn : n % 2 = 1) : ∃ v < n, redDegree c n v % 2 = 0`
  (a sum of an odd number of odd numbers is odd); `exists_even_red_degree` is the case `n = 25`.
  Axioms: `[propext, Classical.choice, Quot.sound]`.
- **Degree bounds (5b).** `good_induced`: if every vertex of a duplicate-free list `L` is joined to `v` by colour
  `red`, the colouring `relabel L.toArray false c` of K_{|L|} is `(s,t)`-good whenever `c` is `(s+1,t)`-good (red) or
  `(s,t+1)`-good (blue). It is `good_restrict` (Lift.lean) with `embOK` discharged for the list. `red_degree_le_13_of`
  takes `∀ c, ¬ Good 3 5 14 c` as a hypothesis and applies `good_induced` to the first 14 red neighbours;
  `red_degree_ge_7_of` takes `∀ c, ¬ Good 4 4 18 c` and uses the first 18 blue neighbours
  (`redDegree_add_blue`: red degree + blue degree = n − 1). `red_degree_le_13` and `red_degree_ge_7` (Assembly.lean)
  instantiate them with `R35_le_14` and `R44_le_18`, so they inherit those theorems' `native_decide` axioms.
- **The assembled statement (5c).** `Catalogue` is a pair of families `A B : Nat → List (Nat → Nat → Bool)`;
  `CatalogueComplete cat` says that for every `d ∈ Degrees = [8, 10, 12]` every (3,5)-good colouring of K_d agrees on
  K_d, after some `permOK` relabelling, with a listed `A d` entry, and every (4,4)-good colouring of K_{24−d} with a
  listed `B d` entry. `UnitShape d a b c` is the shape of a gluing unit (vertex 0 red to 1..d, blue to d+1..24, `a` on
  1..d, `b` on d+1..24, edges read with `col`), and `UnitsRefuted cat` says no good colouring of K_25 has the shape of
  a listed unit (this is what the per-unit SLRAT lemmas establish, one clause each).
  `r45_le_25 (cat) (hcat : CatalogueComplete cat) (hunits : UnitsRefuted cat) : ∀ c, ¬ Good 4 5 25 c`:
  take `v` of even red degree, so the degree `d` is 8, 10 or 12; the induced colourings on the red and blue
  neighbourhoods are good (`good_induced`), hence listed up to permutations σ, ρ; `assemblePerm v R Bl σ ρ`
  (0 ↦ v, i+1 ↦ R[σ i], d+1+j ↦ Bl[ρ j]) is a `permOK` permutation of K_25 (`assemblePerm_permOK`), so
  `relabel` of `c` through it is good (`good_relabel`) and has `UnitShape d a b`, contradicting `hunits`.
  Axioms of `r45_le_25`: `propext, Classical.choice, Quot.sound` plus the `native_decide` axioms of `R35_le_14` and
  `R44_le_18` (nothing else; the core lemma `assemble` has only the three standard axioms).
  What remains trusted for the final theorem is exactly `CatalogueComplete` (the McKay catalogues) once
  `UnitsRefuted` is discharged by the batch lemma mode of docs/ASSEMBLY.md.

## The SR rule and the two tiers (SR.lean; added 2026-10-28)
`id r lits 0 witness 0 a1 b1 .. ap bp 0 ahints 0 (Did hints 0)* 0` adds `C = lits` to the **SR tier** of the main
database: `C` is substitution-redundant for the substitution σ (witness literals fixed true, var |a| := b negated if
a < 0, identity elsewhere). The checker extends α = ¬C by the unit hints `ahints` (`extend`), then for every clause D
of the main database in id order and for C itself: D|σ is satisfied by σ (a literal maps to true, or a tautology), or a
literal of D|σ is true under α, or the next hint group (id D) derives a conflict from α ∧ ¬(D|σ) by `rup`
(`srClause`, `srClauses`). Run-time side conditions: substitution literals non-zero, and every variable of every D
passes `varOK` (the edge table maps it to a pair and back), so the colouring `substCol E σ c` (pair (a,b) := the
value of σ(edge a b) under c) reads back on D's variables (`litVal_substCol`).
Invariant (`StOK`, six parts): pure main clauses (ids not in `srList`) hold in every good colouring; `done` only when
no good colouring exists; the sub-instance and assumption parts as before; **if a good colouring exists, some good
colouring satisfies the whole main database (both tiers)** (`Satisfiable`); and the originals are in the main
database (`HasOriginals`). The SR step preserves `Satisfiable` (`stepFn_ok`, case `sr`): take the good model c of the
database; if it satisfies C, done; otherwise c agrees with α (`agrees_negAssign`, `extend_agrees`), hence with every
RUP consequence, so c satisfies every D|σ (`srClause_sound`, via `rup_sound`), so `substCol E σ c` satisfies every D
and C (`image_some_sat` / `image_none_sat`), and it is good because it satisfies every original (`good_of_originals`:
a colouring satisfying all clique clauses is good; `subsets_mem` / `subsets_complete` show every k-set is
generated). RUP steps are pure iff all their hints are pure (`getPure`), otherwise SR tier; images and lifts refuse
SR-tier sources (`!decide (src ∈ srList)`); `checkLemma` / `OKSt.last` report only pure clauses; the empty clause in
either tier gives `done` (`done_ok_sat`: a satisfiable-when-good database cannot contain ⊥). Axioms of `check_sound`
and `checkLemma_sound` are still `[propext, Classical.choice, Quot.sound]`. Heule's 39-line SR proof of
R(4,4) ≤ 18 (`monster sr-check ... --slrat FILE` writes the hinted form) checks in 0.9-1.7 s / 28 MB.

## Batch lemma mode (Stream.lean `Verified`, `batch_sound`; added 2026-10-28)
`checker --lemmas LIST [--delete]` verifies the SLRAT files listed in `LIST` (one path per line, each a per-unit proof
as `monster unit-lean` writes them) one after another in one process, all over the (s,t,n) of the first file's
header, streaming: one file's live databases at a time, the originals (`initOK`) computed once and shared. Per file it
prints `s VERIFIED LEMMA path: clause` or `s NOT VERIFIED path`, then `s BATCH (s,t) K_n: k verified lemmas, m
failed` (exit 0 iff m = 0); `--delete` removes each verified file. What the batch accumulates is a
`List (Verified s t n)`: a clause packed with the proof that every good colouring of K_n satisfies it, and the only
constructor of a `Verified` is `OKSt.verified` (a streamed check whose last main clause is pure: SR-tier results are
refused, `OKSt.last_sound`). The driver theorem `batch_sound : ∀ v ∈ L, ∀ c, Good s t n c → ClauseSat (edgeTable n) c
v.clause` therefore holds for whatever list the IO loop builds; axioms `[propext, Quot.sound]`. Measured: three d=7
unit proofs (11-12 MB each) plus one mutant: 3 VERIFIED LEMMA, 1 NOT VERIFIED in 15-18 s, 67 MB peak.

### The concrete catalogue and the unit-clause bridge (added 2026-10-28; G6.lean, Bridge.lean)
- **graph6 (G6.lean).** `decodeG6 line : Option (Nat × (Nat → Nat → Bool))` decodes one McKay graph6 line (n ≤ 62:
  header byte n+63, then the upper triangle in column-major order, six bits per byte, most significant first; pair
  (i, j), i < j, is bit j(j−1)/2 + i, the checker's edge index minus one). An edge is red (`true`), as in
  `src/graph.rs`. Total and executable; malformed lines are dropped by `decodeG6Lines n text`, which only strengthens
  the completeness hypothesis. `catalogueFrom (texts : Nat → String × String) : Catalogue` builds `A d` from
  `r35/n{d}.g6` and `B d` from `r44/n{24−d}.g6`; the files are meant to be read with `IO` at run time, never embedded.
  Checked against the real files (interpreter, 36 s): counts 179 / 313 / 12 (r35 n8, n10, n12), 2 / 640 / 130,816
  (r44 n16, n15, n14) equal McKay's, and every decoded r35 n8–n12 and r44 n15–n16 graph is good for a brute-force
  Bool clique check, which a wrong bit order would break.
- **Bridge (Bridge.lean).** `fixedColour d a b i j : Option Bool` is the colour that `UnitShape d a b` forces on edge
  {i, j} (0–j red for 1 ≤ j ≤ d, blue for d+1 ≤ j ≤ 24, `col a (i−1) (j−1)` inside 1..d, `col b` inside d+1..24);
  `fixedColour_sound`. `litRefutedBy E d a b l` reads the edge of literal `l` from the table `E` (exactly as `varVal`
  does, so nothing about the table is assumed) and checks that the forced colour falsifies `l`
  (`litRefutedBy_sound : ... → UnitShape d a b c → litVal E c l = false`). `clauseRefutes E d a b C` is the check
  on every literal; `unit_refuted_of_clause : (∀ c, Good 4 5 25 c → ClauseSat E c C) → clauseRefutes E d a b C = true →
  ∀ c, Good 4 5 25 c → ¬ UnitShape d a b c`. This covers the exact unit clause (¬ of all fixed edges) and every
  generalised unit (a sub-clause, gray edges free): a sub-clause passes the check for every pair (a, b) that agrees
  with it on the fixed edges. `unitClause_sound` is the plug point from `checkLemmaText` (Lemma.lean).
  Coverage: `catalogueCovered E cat Cs` (linear scan) and `catalogueCoveredIdx E cat Cs idx` (an untrusted index
  hint names the clause for the i-th A-graph and j-th B-graph; no list indexing, so it scales to 17.4 M pairs at
  d = 12) are Bool checks; `unitsRefuted_of_covered` / `unitsRefuted_of_coveredIdx` turn them into `UnitsRefuted cat`,
  and `r45_le_25_of_covered (hcat) (hsound) (hcov) : ∀ c, ¬ Good 4 5 25 c` composes with `r45_le_25`.
  Axioms: the bridge and coverage theorems use `[propext, Quot.sound]`; `r45_le_25_of_covered` inherits the
  native_decide axioms of `R35_le_14` / `R44_le_18` through the degree bounds.
- **Remaining gap** to the final theorem `r45_le_25 (catalogueFrom files) hcat hunits`: a driver (`checker
  --assemble`, Main.lean, other agent) that reads the six g6 files, streams every per-unit lemma file through the
  checker collecting `(C, proof)` pairs (`hsound`), and evaluates `catalogueCoveredIdx` with the unit index; the
  Bool result, like the checker's own verdicts, is trusted through the compiled code (or `decide` for a small
  degree). The only mathematical hypothesis left is `CatalogueComplete (catalogueFrom files)`.

### The assembler `checker --assemble SPEC` (added 2026-10-28; Assemble.lean, Main.lean)
The covers (`results/covers_r45/*.txt`) assign every catalogue graph `X` to a generalisation **up to a vertex
permutation** (`A catidx genid t pi...`, `pi(X)` = the instantiation), so a unit clause refutes `relabel σ false X`
(σ = pi⁻¹), not `X` as listed. `unitShape_relabel` / `stageRefuted_of_relabelled` close the gap: a colouring of shape
`(a, b)` relabelled by `assemblePerm 0 [1..d] [d+1..24] σ ρ` has shape `(relabel σ false a, relabel ρ false b)` and stays
good (`good_relabel`), so refuting the relabelled pair refutes `(a, b)`. `StageRefuted cat d` is the per-degree form of
`UnitsRefuted`; `r45_le_25_of_stages` needs it for `d ∈ Degrees = [8, 10, 12]`.

The executable check `stageOK E d Cs A B hA hB k m` takes the catalogue arrays `A`, `B` (from `decodeG6Lines`), one
untrusted `Hint` (generalisation, σ) per graph, and a clause table `Cs ga gb`. It checks that every hint is a
permutation of the right size and that, for every pair `(i, j)`, `clauseRefutes E d (relabel σ_i false A[i])
(relabel ρ_j false B[j]) (Cs ga_i gb_j)` holds (Bridge.lean); rows are split into `m` chunks of `k` evaluated as
`Task`s (`Task.get (Task.spawn f) = f ()` definitionally, so the parallel definition is the function the theorem
names). `stageOK_sound` / `stageRefuted_of_stageOK` need only soundness of the clauses in the table:
- **in-process form** `stageRefuted_of_verified`: the table holds `Verified 4 5 25` lemmas (Stream.lean), i.e. the
  assembler verified every proof file itself (`proofs LIST` in the spec); the theorem has no hypothesis beyond the
  Bool, so a run printing `s STAGE d REFUTED` establishes `StageRefuted (catalogueFrom files) d` with nothing else
  assumed;
- **record form** `stageRefuted_of_record`: the table holds clauses read from a record written by batch mode
  (`checker --lemmas LIST --record FILE`, one `path lits` line per verified lemma, as `unit-lean-stage` runs it); the
  hypothesis is that every recorded clause was verified by that batch run. This is the form for d = 10 and d = 12,
  whose proofs (tens of TB) cannot exist at once; the trust added is the record file between two runs of the same
  verified program.
`sig` now has an executable twin `sigImpl` (`σ.getD x 0`, no list) connected by the proved `@[csimp]` lemma
`sig_eq_sigImpl`, and graph6 bodies are arrays (`g6Bit`, O(1) per bit); neither changes any statement. Axioms of
`stageRefuted_of_verified` and `stageRefuted_of_record`: `[propext, Classical.choice, Quot.sound]`;
`r45_le_25_of_stages` adds the `native_decide` axioms of `R35_le_14` / `R44_le_18` through the degree bounds.
Checked: the R(4,5) d=7 stage end to end in both forms (`cargo test assemble_d7`), five mutations at d=8 (flipped
literal, non-permutation hint, wrong generalisation, missing unit, swapped vertices) all rejected.
Parsing note (2026-10-28): the streaming modes read proof lines with `parseLineFast` (Parse.lean), a byte-level scanner
for the three hot line kinds that falls back to `parseLine` for the rest. Like `parseLine` it is untrusted: every `Step`
it produces goes through `stepFn`, so a parser bug can only make a valid proof fail, never make an invalid one pass. The
assembler accepts several `record` lines per stage (one record file per Lean batch of `unit-lean-stage`).
`rup` note (2026-10-28): the compiled checker runs `rupFast` (array assignment, Rup.lean) in place of `rup` through the
proved `@[csimp]` equality `rup_eq_rupFast`; the kernel checks that equality, so nothing is trusted about the
replacement (unlike `implemented_by`). Same for `sig` / `sigImpl` (Image.lean).
Executable-only changes of 2026-10-28 ~13:40 (statements untouched, see RESULTS "~13:40"): `OKSt` carries the edge
table with `hE : E = edgeTable n` (the invariant is still stated over `edgeTable n`); `getCFast` replaces `getC` through
the proved `@[csimp] getC_eq_getCFast`; `rupFast` is justified by `rupA_rep` (any array that represents the assignment
list gives the same answer) and `rep_toArr`; the proof text is read by `LineReader` / `parseLineBytes` (untrusted I/O and
parsing, every step still goes through `stepFn`).
