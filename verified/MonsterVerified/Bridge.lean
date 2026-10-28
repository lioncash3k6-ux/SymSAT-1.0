import MonsterVerified.Lemma
import MonsterVerified.Assembly

/-!
# The bridge from checked unit clauses to `UnitsRefuted` (assembly part 5c, proof side)

A per-unit lemma file, run through `checkLemma` (Lemma.lean), yields a clause `C` over the edge table that every
(4,5)-good colouring of K_25 satisfies (`checkLemma_sound`). `monster unit-lean` makes `C` the negation of the unit's
fixed edges (root 0 red to the A-vertices 1..d, blue to the B-vertices d+1..24, the non-gray edges inside A and
inside B as in the catalogue graphs; `src/leanunit.rs`). A generalised unit fixes only a subset of these edges
(gray edges are free), so its clause is a sub-clause of the exact one and refutes every pair (a, b) that agrees
with it on the fixed edges.

The check `clauseRefutes E d a b C` reads, for every literal of `C`, its edge from the table and asks whether the
unit shape `UnitShape d a b` forces that edge to the colour that falsifies the literal. Nothing about the table is
assumed: `varVal` reads the same entry. If every literal is falsified by the shape, a colouring satisfying `C` cannot
have the shape (`unit_refuted_of_clause`). Coverage of the whole catalogue (`catalogueCovered`, or the indexed
`catalogueCoveredIdx` for millions of pairs) then gives `UnitsRefuted cat` (`unitsRefuted_of_covered`,
`unitsRefuted_of_coveredIdx`), the second hypothesis of `r45_le_25`.
-/

namespace MonsterVerified

/-- the colour that `UnitShape d a b` forces on the edge {i, j} of K_25, if any -/
def fixedColour (d : Nat) (a b : Nat → Nat → Bool) (i j : Nat) : Option Bool :=
  if i = 0 ∧ 1 ≤ j ∧ j ≤ d then some true
  else if i = 0 ∧ d + 1 ≤ j ∧ j ≤ 24 then some false
  else if 1 ≤ i ∧ i < j ∧ j ≤ d then some (col a (i - 1) (j - 1))
  else if d + 1 ≤ i ∧ i < j ∧ j ≤ 24 then some (col b (i - d - 1) (j - d - 1))
  else none

theorem fixedColour_sound {d : Nat} {a b : Nat → Nat → Bool} {i j : Nat} {w : Bool}
    (h : fixedColour d a b i j = some w) {c : Nat → Nat → Bool} (hs : UnitShape d a b c) : col c i j = w := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold fixedColour at h
  split at h
  · rename_i hc
    obtain ⟨rfl, hj1, hj2⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have := h1 (j - 1) (by omega)
    rwa [show j - 1 + 1 = j by omega] at this
  split at h
  · rename_i hc
    obtain ⟨rfl, hj1, hj2⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have := h2 (j - d - 1) (by omega)
    rwa [show d + 1 + (j - d - 1) = j by omega] at this
  split at h
  · rename_i hc
    obtain ⟨hi, hij, hj⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have := h3 (i - 1) (j - 1) (by omega) (by omega)
    rwa [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega] at this
  split at h
  · rename_i hc
    obtain ⟨hi, hij, hj⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have := h4 (i - d - 1) (j - d - 1) (by omega) (by omega)
    rwa [show d + 1 + (i - d - 1) = i by omega, show d + 1 + (j - d - 1) = j by omega] at this
  simp at h

/-- is literal `l` false in every colouring of shape `(d, a, b)`? (its edge is read from the table `E`) -/
def litRefutedBy (E : Edges) (d : Nat) (a b : Nat → Nat → Bool) (l : Int) : Bool :=
  match E[l.natAbs]? with
  | some (i, j) =>
    match fixedColour d a b i j with
    | some true => decide (l < 0)
    | some false => decide (0 < l)
    | none => false
  | none => false

theorem litRefutedBy_sound {E : Edges} {d : Nat} {a b : Nat → Nat → Bool} {l : Int}
    (h : litRefutedBy E d a b l = true) {c : Nat → Nat → Bool} (hs : UnitShape d a b c) :
    litVal E c l = false := by
  unfold litRefutedBy at h
  cases hE : E[l.natAbs]? with
  | none => rw [hE] at h; simp at h
  | some p =>
    obtain ⟨i, j⟩ := p
    rw [hE] at h
    simp only at h
    have hvv : varVal E c l.natAbs = col c i j := by unfold varVal; rw [hE]
    cases hf : fixedColour d a b i j with
    | none => rw [hf] at h; simp at h
    | some w =>
      rw [hf] at h
      have hw := fixedColour_sound hf hs
      unfold litVal
      rw [hvv, hw]
      cases w <;> simp at h ⊢ <;> omega

/-- every literal of `C` is false under the unit shape: `C` refutes the pair `(a, b)` at degree `d` -/
def clauseRefutes (E : Edges) (d : Nat) (a b : Nat → Nat → Bool) (C : List Int) : Bool :=
  C.all (litRefutedBy E d a b)

/-- THE BRIDGE: a clause that holds in every good colouring and whose literals are all falsified by the unit
shape rules the shape out for good colourings -/
theorem unit_refuted_of_clause {E : Edges} {C : List Int} {d : Nat} {a b : Nat → Nat → Bool}
    (hC : ∀ c, Good 4 5 25 c → ClauseSat E c C) (hr : clauseRefutes E d a b C = true) :
    ∀ c, Good 4 5 25 c → ¬ UnitShape d a b c := by
  intro c hc hs
  obtain ⟨l, hl, hv⟩ := hC c hc
  rw [litRefutedBy_sound (List.all_eq_true.mp hr l hl) hs] at hv
  exact Bool.noConfusion hv

/-- the clause of a lemma file for (4,5,25) holds in every good colouring (the plug point for `checkLemma`) -/
theorem unitClause_sound {text : String} {C : List Int} (h : checkLemmaText text = some (4, 5, 25, C)) :
    ∀ c, Good 4 5 25 c → ClauseSat (edgeTable 25) c C :=
  checkLemmaText_sound h

/-! ## Coverage of the whole catalogue -/

/-- every clause of the list holds in every good colouring of K_25 -/
def SoundClauses (E : Edges) (Cs : List (List Int)) : Prop :=
  ∀ C ∈ Cs, ∀ c, Good 4 5 25 c → ClauseSat E c C

theorem soundClauses_nil (E : Edges) : SoundClauses E [] := fun C h => by simp at h

theorem soundClauses_cons {E : Edges} {C : List Int} {Cs : List (List Int)}
    (hC : ∀ c, Good 4 5 25 c → ClauseSat E c C) (hCs : SoundClauses E Cs) : SoundClauses E (C :: Cs) := by
  intro D hD
  rcases List.mem_cons.mp hD with rfl | hD
  · exact hC
  · exact hCs D hD

/-- some listed clause refutes the pair -/
def coversPair (E : Edges) (d : Nat) (a b : Nat → Nat → Bool) (Cs : List (List Int)) : Bool :=
  Cs.any (clauseRefutes E d a b)

/-- decidable coverage: every listed pair of every degree is refuted by some clause of `Cs d` (linear scan) -/
def catalogueCovered (E : Edges) (cat : Catalogue) (Cs : Nat → List (List Int)) : Bool :=
  Degrees.all fun d => (cat.A d).all fun a => (cat.B d).all fun b => coversPair E d a b (Cs d)

theorem unitsRefuted_of_covered {E : Edges} {cat : Catalogue} {Cs : Nat → List (List Int)}
    (hsound : ∀ d, SoundClauses E (Cs d)) (hcov : catalogueCovered E cat Cs = true) : UnitsRefuted cat := by
  intro d hd a ha b hb
  have h1 := List.all_eq_true.mp hcov d hd
  have h2 := List.all_eq_true.mp h1 a ha
  have h3 := List.all_eq_true.mp h2 b hb
  obtain ⟨C, hC, hr⟩ := List.any_eq_true.mp h3
  exact unit_refuted_of_clause (hsound d C hC) hr

/-- `f i x` for every element `x` of the list, `i` counting from the start value -/
def allIdx (f : Nat → α → Bool) : List α → Nat → Bool
  | [], _ => true
  | x :: xs, i => f i x && allIdx f xs (i + 1)

theorem allIdx_spec {f : Nat → α → Bool} : ∀ {L : List α} {i : Nat}, allIdx f L i = true →
    ∀ x ∈ L, ∃ k, f k x = true
  | [], _, _, x, hx => by simp at hx
  | y :: ys, i, h, x, hx => by
    simp only [allIdx, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨i, h.1⟩
    · exact allIdx_spec h.2 x hx

/-- indexed coverage, for catalogues with millions of pairs: the (untrusted) hint `idx d i j` names the clause of
`Cs d` expected to refute the `i`-th A-graph with the `j`-th B-graph; only that clause is checked -/
def catalogueCoveredIdx (E : Edges) (cat : Catalogue) (Cs : Nat → Array (List Int))
    (idx : Nat → Nat → Nat → Nat) : Bool :=
  Degrees.all fun d =>
    allIdx (fun i a => allIdx (fun j b =>
      match (Cs d)[idx d i j]? with
      | some C => clauseRefutes E d a b C
      | none => false) (cat.B d) 0) (cat.A d) 0

theorem unitsRefuted_of_coveredIdx {E : Edges} {cat : Catalogue} {Cs : Nat → Array (List Int)}
    {idx : Nat → Nat → Nat → Nat} (hsound : ∀ d, ∀ C ∈ Cs d, ∀ c, Good 4 5 25 c → ClauseSat E c C)
    (hcov : catalogueCoveredIdx E cat Cs idx = true) : UnitsRefuted cat := by
  intro d hd a ha b hb
  have h1 := List.all_eq_true.mp hcov d hd
  obtain ⟨i, hi⟩ := allIdx_spec h1 a ha
  obtain ⟨j, hj⟩ := allIdx_spec hi b hb
  cases hC : (Cs d)[idx d i j]? with
  | none => rw [hC] at hj; simp at hj
  | some C =>
    rw [hC] at hj
    exact unit_refuted_of_clause (hsound d C (Array.mem_of_getElem? hC)) hj

/-- the assembled theorem with both hypotheses discharged from data: a complete catalogue and covering clauses -/
theorem r45_le_25_of_covered {E : Edges} {cat : Catalogue} {Cs : Nat → Array (List Int)}
    {idx : Nat → Nat → Nat → Nat} (hcat : CatalogueComplete cat)
    (hsound : ∀ d, ∀ C ∈ Cs d, ∀ c, Good 4 5 25 c → ClauseSat E c C)
    (hcov : catalogueCoveredIdx E cat Cs idx = true) : ∀ c, ¬ Good 4 5 25 c :=
  r45_le_25 cat hcat (unitsRefuted_of_coveredIdx hsound hcov)

end MonsterVerified
