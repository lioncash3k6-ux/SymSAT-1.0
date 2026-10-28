import MonsterVerified.Bridge
import MonsterVerified.G6
import MonsterVerified.Stream

/-!
# Assembling a stage from relabelled catalogue graphs (`checker --assemble`)

The cover files (`results/covers_r45/*.txt`, v10 format) assign every catalogue graph `X` to a generalisation
**up to a vertex permutation** (`A catidx genid t pi...`: `pi(X)` instantiates the generalisation). A unit lemma
(`monster unit-lean-stage`, clause `C` for the pair of generalisations `(ga, gb)`) therefore refutes the *relabelled*
graphs `relabel σ false X` (σ = pi⁻¹), not `X` as listed. This file closes that gap and gives the executable check:

- `unitShape_relabel` / `stageRefuted_of_relabelled`: if, for every listed pair `(a, b)`, some relabelling
  `(relabel σ false a, relabel ρ false b)` is refuted by a sound clause, then `(a, b)` itself is refuted: a colouring
  of shape `(a, b)` relabelled by the K_25 permutation `assemblePerm 0 [1..d] [d+1..24] σ ρ` has the relabelled shape
  and stays good (`good_relabel`).
- `stageOK`: the Bool check over the catalogue arrays `A`, `B` with an (untrusted) hint per graph (its generalisation
  and σ) and a clause table `Cs ga gb`. Rows (A-graphs) are split into chunks evaluated as `Task`s in parallel;
  `Task.get (Task.spawn f) = f ()` definitionally, so the parallel form is the pure function it names.
- `stageOK_sound`, `stageRefuted_of_stageOK`: `stageOK = true` plus soundness of every clause in the table gives
  `StageRefuted cat d`; `stageRefuted_of_verified` is the hypothesis-free form for a table of `Verified` lemmas
  (in-process batch verification), `stageRefuted_of_record` the form for recorded clauses (`--record` of batch mode).
- `r45_le_25_of_stages`: the three stages `d ∈ {8, 10, 12}` give `UnitsRefuted`, hence R(4,5) ≤ 25 under
  `CatalogueComplete`.
-/

namespace MonsterVerified

/-! ## Stages -/

/-- stage `d` is refuted: no good colouring of K_25 has the shape of any listed pair at degree `d` -/
def StageRefuted (cat : Catalogue) (d : Nat) : Prop :=
  ∀ a ∈ cat.A d, ∀ b ∈ cat.B d, ∀ c, Good 4 5 25 c → ¬ UnitShape d a b c

theorem unitsRefuted_of_stages {cat : Catalogue} (h : ∀ d ∈ Degrees, StageRefuted cat d) : UnitsRefuted cat :=
  fun d hd a ha b hb => h d hd a ha b hb

/-- R(4,5) ≤ 25 from catalogue completeness and the three refuted stages -/
theorem r45_le_25_of_stages (cat : Catalogue) (hcat : CatalogueComplete cat)
    (h : ∀ d ∈ Degrees, StageRefuted cat d) : ∀ c, ¬ Good 4 5 25 c :=
  r45_le_25 cat hcat (unitsRefuted_of_stages h)

/-! ## Relabelled pairs -/

theorem getD_range' {s n i : Nat} (hi : i < n) : (List.range' s n).getD i 0 = s + i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp [List.getElem_range']

theorem mem_range'_iff {s n x : Nat} : x ∈ List.range' s n ↔ s ≤ x ∧ x < s + n := by
  rw [List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨x - s, by omega, by omega⟩

/-- a colouring of shape `(a, b)`, relabelled by the assembling permutation built from `σ` and `ρ`, has the shape
`(relabel σ false a, relabel ρ false b)` -/
theorem unitShape_relabel {d : Nat} {a b c : Nat → Nat → Bool} {σ ρ : Array Nat}
    (hσ : permOK σ d = true) (hρ : permOK ρ (24 - d) = true) (hs : UnitShape d a b c) :
    UnitShape d (relabel σ false a) (relabel ρ false b)
      (relabel (assemblePerm 0 (List.range' 1 d) (List.range' (d + 1) (24 - d)) σ ρ) false c) := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hσs := (permOK_spec hσ).1
  have hσi := (permOK_spec hσ).2
  have hρs := (permOK_spec hρ).1
  have hρi := (permOK_spec hρ).2
  have lenR : (List.range' 1 d).length = d := by simp
  have lenB : (List.range' (d + 1) (24 - d)).length = 24 - d := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [col_relabel_false, sig_assemblePerm_zero, sig_assemblePerm_red _ _ _ σ ρ (by rw [lenR]; exact hi),
      getD_range' (hσs i hi), Nat.add_comm]
    exact h1 _ (hσs i hi)
  · intro j hj
    rw [col_relabel_false, sig_assemblePerm_zero, show d + 1 + j = (List.range' 1 d).length + 1 + j by rw [lenR],
      sig_assemblePerm_blue _ _ _ σ ρ (by rw [lenB]; exact hj), getD_range' (hρs j hj)]
    exact h2 _ (hρs j hj)
  · intro x y hxy hy
    rw [col_relabel_false, sig_assemblePerm_red _ _ _ σ ρ (by rw [lenR]; omega),
      sig_assemblePerm_red _ _ _ σ ρ (by rw [lenR]; exact hy), getD_range' (hσs x (by omega)),
      getD_range' (hσs y hy), col_relabel_false, Nat.add_comm 1 (sig σ x), Nat.add_comm 1 (sig σ y)]
    have hne : sig σ x ≠ sig σ y := fun e => by have := hσi x y (by omega) hy e; omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact h3 _ _ hlt (hσs y hy)
    · rw [col_comm c _ _ (by omega), col_comm a _ _ hne]
      exact h3 _ _ hgt (hσs x (by omega))
  · intro x y hxy hy
    rw [col_relabel_false, show d + 1 + x = (List.range' 1 d).length + 1 + x by rw [lenR],
      show d + 1 + y = (List.range' 1 d).length + 1 + y by rw [lenR],
      sig_assemblePerm_blue _ _ _ σ ρ (by rw [lenB]; omega), sig_assemblePerm_blue _ _ _ σ ρ (by rw [lenB]; exact hy),
      getD_range' (hρs x (by omega)), getD_range' (hρs y hy), col_relabel_false]
    have hne : sig ρ x ≠ sig ρ y := fun e => by have := hρi x y (by omega) hy e; omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact h4 _ _ hlt (hρs y hy)
    · rw [col_comm c _ _ (by omega), col_comm b _ _ hne]
      exact h4 _ _ hgt (hρs x (by omega))

/-- refuting a relabelling of every listed pair refutes the stage -/
theorem stageRefuted_of_relabelled {cat : Catalogue} {d : Nat} (hd : d ≤ 24)
    (h : ∀ a ∈ cat.A d, ∀ b ∈ cat.B d, ∃ σ ρ, permOK σ d = true ∧ permOK ρ (24 - d) = true ∧
      ∀ c, Good 4 5 25 c → ¬ UnitShape d (relabel σ false a) (relabel ρ false b) c) :
    StageRefuted cat d := by
  intro a ha b hb c hc hs
  obtain ⟨σ, ρ, hσ, hρ, hn⟩ := h a ha b hb
  have hπ : permOK (assemblePerm 0 (List.range' 1 d) (List.range' (d + 1) (24 - d)) σ ρ) 25 = true :=
    assemblePerm_permOK (by omega)
      (fun x hx => by rw [mem_range'_iff] at hx; omega)
      (fun x hx => by rw [mem_range'_iff] at hx; omega)
      (fun x hx y hy => by rw [mem_range'_iff] at hx hy; omega)
      (List.nodup_range' 1) (List.nodup_range' 1) (by simpa using hσ) (by simpa using hρ) (by simp; omega)
  exact hn _ (good_relabel (f := false) hπ (fun h => by cases h) hc) (unitShape_relabel hσ hρ hs)

/-! ## The executable stage check -/

/-- the (untrusted) hint for one catalogue graph: its generalisation and the relabelling σ (= pi⁻¹ of the cover) -/
structure Hint where
  gen : Nat
  perm : Array Nat

/-- the clause of unit `(ha.gen, hb.gen)` refutes the relabelled pair -/
def pairOK (E : Edges) (d : Nat) (Cs : Nat → Nat → Option (List Int)) (a b : Nat → Nat → Bool) (ha hb : Hint) :
    Bool :=
  match Cs ha.gen hb.gen with
  | some C => clauseRefutes E d (relabel ha.perm false a) (relabel hb.perm false b) C
  | none => false

theorem pairOK_sound {E : Edges} {d : Nat} {Cs : Nat → Nat → Option (List Int)} {a b : Nat → Nat → Bool}
    {ha hb : Hint} (hsound : ∀ ga gb C, Cs ga gb = some C → ∀ c, Good 4 5 25 c → ClauseSat E c C)
    (h : pairOK E d Cs a b ha hb = true) :
    ∀ c, Good 4 5 25 c → ¬ UnitShape d (relabel ha.perm false a) (relabel hb.perm false b) c := by
  unfold pairOK at h
  cases hC : Cs ha.gen hb.gen with
  | none => rw [hC] at h; simp at h
  | some C =>
    rw [hC] at h
    exact unit_refuted_of_clause (hsound _ _ _ hC) h

/-- `f` holds on `i, i+1, ..., i+k-1` (tail recursive: `&&` short-circuits into the recursive call) -/
def allRange (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, i => f i && allRange f k (i + 1)

theorem allRange_spec {f : Nat → Bool} : ∀ {k i : Nat}, allRange f k i = true → ∀ j, i ≤ j → j < i + k → f j = true
  | 0, _, _, _, h1, h2 => by omega
  | k + 1, i, h, j, h1, h2 => by
    simp only [allRange, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact allRange_spec h.2 j hlt (by omega)

/-- row `i`: the `i`-th A-graph against every B-graph -/
def rowOK (E : Edges) (d : Nat) (Cs : Nat → Nat → Option (List Int)) (A B : Array (Nat → Nat → Bool))
    (hA hB : Array Hint) (i : Nat) : Bool :=
  match A[i]?, hA[i]? with
  | some a, some ha =>
    allRange (fun j =>
      match B[j]?, hB[j]? with
      | some b, some hb => pairOK E d Cs a b ha hb
      | _, _ => false) B.size 0
  | _, _ => false

/-- `m` chunks of `k` rows starting at `lo`: `(start, count)` pairs -/
def chunkList (k : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | m + 1, lo => (lo, k) :: chunkList k m (lo + k)

theorem chunkList_cover {k : Nat} : ∀ {m lo : Nat} (i : Nat), lo ≤ i → i < lo + m * k →
    ∃ ch ∈ chunkList k m lo, ch.1 ≤ i ∧ i < ch.1 + ch.2
  | 0, lo, i, h1, h2 => by simp at h2; omega
  | m + 1, lo, i, h1, h2 => by
    by_cases hi : i < lo + k
    · exact ⟨(lo, k), List.mem_cons_self, h1, hi⟩
    · have h2' : i < (lo + k) + m * k := by rw [Nat.add_mul, Nat.one_mul] at h2; omega
      obtain ⟨ch, hch, h3, h4⟩ := chunkList_cover (m := m) (lo := lo + k) i (by omega) h2'
      exact ⟨ch, List.mem_cons_of_mem _ hch, h3, h4⟩

/-- THE STAGE CHECK: every hint is a permutation of the right size, and every row is covered; the rows are split
into `m` chunks of `k` (with `m * k ≥ A.size`), each evaluated by its own `Task` -/
def stageOK (E : Edges) (d : Nat) (Cs : Nat → Nat → Option (List Int)) (A B : Array (Nat → Nat → Bool))
    (hA hB : Array Hint) (k m : Nat) : Bool :=
  decide (A.size ≤ m * k) &&
  hA.all (fun h => permOK h.perm d) && hB.all (fun h => permOK h.perm (24 - d)) &&
  ((chunkList k m 0).map (fun ch =>
      Task.spawn fun _ => allRange (rowOK E d Cs A B hA hB) (min ch.2 (A.size - ch.1)) ch.1)).all Task.get

theorem stageOK_sound {E : Edges} {d : Nat} {Cs : Nat → Nat → Option (List Int)} {A B : Array (Nat → Nat → Bool)}
    {hA hB : Array Hint} {k m : Nat}
    (hsound : ∀ ga gb C, Cs ga gb = some C → ∀ c, Good 4 5 25 c → ClauseSat E c C)
    (h : stageOK E d Cs A B hA hB k m = true) :
    ∀ a ∈ A, ∀ b ∈ B, ∃ σ ρ, permOK σ d = true ∧ permOK ρ (24 - d) = true ∧
      ∀ c, Good 4 5 25 c → ¬ UnitShape d (relabel σ false a) (relabel ρ false b) c := by
  intro a ha b hb
  unfold stageOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map, Array.all_eq_true,
    forall_exists_index, and_imp] at h
  obtain ⟨⟨⟨hsz, hpA⟩, hpB⟩, hall⟩ := h
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hb
  obtain ⟨ch, hch, hlo, hhi⟩ := chunkList_cover (k := k) (m := m) (lo := 0) i (Nat.zero_le _) (by omega)
  have hrow : allRange (rowOK E d Cs A B hA hB) (min ch.2 (A.size - ch.1)) ch.1 = true := hall _ ch hch rfl
  have hri := allRange_spec hrow i hlo (by omega)
  unfold rowOK at hri
  rw [Array.getElem?_eq_getElem hi] at hri
  cases hha : hA[i]? with
  | none => rw [hha] at hri; simp at hri
  | some ha' =>
    rw [hha] at hri
    simp only at hri
    have hrj := allRange_spec hri j (Nat.zero_le _) (by omega)
    rw [Array.getElem?_eq_getElem hj] at hrj
    cases hhb : hB[j]? with
    | none => rw [hhb] at hrj; simp at hrj
    | some hb' =>
      rw [hhb] at hrj
      simp only at hrj
      obtain ⟨hia, ea⟩ := Array.getElem?_eq_some_iff.mp hha
      obtain ⟨hjb, eb⟩ := Array.getElem?_eq_some_iff.mp hhb
      exact ⟨ha'.perm, hb'.perm, ea ▸ hpA i hia, eb ▸ hpB j hjb, pairOK_sound hsound hrj⟩

/-- the stage check on the catalogue's arrays refutes the stage -/
theorem stageRefuted_of_stageOK {cat : Catalogue} {d : Nat} (hd : d ≤ 24) {E : Edges}
    {Cs : Nat → Nat → Option (List Int)} {hA hB : Array Hint} {k m : Nat}
    (hsound : ∀ ga gb C, Cs ga gb = some C → ∀ c, Good 4 5 25 c → ClauseSat E c C)
    (h : stageOK E d Cs (cat.A d).toArray (cat.B d).toArray hA hB k m = true) : StageRefuted cat d :=
  stageRefuted_of_relabelled hd
    (fun a ha b hb => stageOK_sound hsound h a (by simpa using ha) b (by simpa using hb))

/-! ## Clause tables -/

/-- the table of in-process verified lemmas, unit `(ga, gb)` at index `ga * nB + gb` -/
def csOfVerified (V : Array (Option (Verified 4 5 25))) (nB : Nat) (ga gb : Nat) : Option (List Int) :=
  if gb < nB then
    match V[ga * nB + gb]? with
    | some (some v) => some v.clause
    | _ => none
  else none

theorem csOfVerified_sound (V : Array (Option (Verified 4 5 25))) (nB : Nat) :
    ∀ ga gb C, csOfVerified V nB ga gb = some C → ∀ c, Good 4 5 25 c → ClauseSat (edgeTable 25) c C := by
  intro ga gb C h
  unfold csOfVerified at h
  split at h
  · split at h
    · rename_i v _
      simp only [Option.some.injEq] at h
      subst h
      exact v.sound
    · simp at h
  · simp at h

/-- the table of recorded clauses (text written by `checker --lemmas ... --record`), same layout -/
def csOfRecord (R : Array (Option (List Int))) (nB : Nat) (ga gb : Nat) : Option (List Int) :=
  if gb < nB then
    match R[ga * nB + gb]? with
    | some (some C) => some C
    | _ => none
  else none

theorem csOfRecord_sound {E : Edges} (R : Array (Option (List Int))) (nB : Nat)
    (hR : ∀ C, some C ∈ R → ∀ c, Good 4 5 25 c → ClauseSat E c C) :
    ∀ ga gb C, csOfRecord R nB ga gb = some C → ∀ c, Good 4 5 25 c → ClauseSat E c C := by
  intro ga gb C h
  unfold csOfRecord at h
  split at h
  · split at h
    · rename_i C' hget
      simp only [Option.some.injEq] at h
      subst h
      exact hR _ (Array.mem_of_getElem? hget)
    · simp at h
  · simp at h

/-- IN-PROCESS FORM (no hypothesis beyond the Bool): the lemmas were verified in this process -/
theorem stageRefuted_of_verified {cat : Catalogue} {d : Nat} (hd : d ≤ 24) {V : Array (Option (Verified 4 5 25))}
    {nB : Nat} {hA hB : Array Hint} {k m : Nat}
    (h : stageOK (edgeTable 25) d (csOfVerified V nB) (cat.A d).toArray (cat.B d).toArray hA hB k m = true) :
    StageRefuted cat d :=
  stageRefuted_of_stageOK hd (csOfVerified_sound V nB) h

/-- RECORD FORM: the clauses come from a record; the hypothesis is that each one was verified (by batch mode) -/
theorem stageRefuted_of_record {cat : Catalogue} {d : Nat} (hd : d ≤ 24) {R : Array (Option (List Int))}
    {nB : Nat} {hA hB : Array Hint} {k m : Nat}
    (hR : ∀ C, some C ∈ R → ∀ c, Good 4 5 25 c → ClauseSat (edgeTable 25) c C)
    (h : stageOK (edgeTable 25) d (csOfRecord R nB) (cat.A d).toArray (cat.B d).toArray hA hB k m = true) :
    StageRefuted cat d :=
  stageRefuted_of_stageOK hd (csOfRecord_sound R nB hR) h

theorem degrees_le_24 {d : Nat} (hd : d ∈ Degrees) : d ≤ 24 := by
  simp [Degrees] at hd; omega

end MonsterVerified
