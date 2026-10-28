import MonsterVerified.Theorems
import MonsterVerified.Degree

/-!
# The assembled statement R(4,5) ≤ 25 (assembly parts 5b and 5c; plan in docs/ASSEMBLY.md)

Trusted input: `CatalogueComplete cat` (every (3,5)-good colouring of K_d and every (4,4)-good colouring of K_{24-d},
d ∈ {8, 10, 12}, is a listed one up to a vertex permutation) and `UnitsRefuted cat` (for every listed pair (A, B)
no good colouring of K_25 has vertex 0 red exactly to 1..d, inducing A there, and blue to d+1..24, inducing B
there: the per-unit lemmas checked by the Lean checker). Everything else is proved here:
- `exists_even_red_degree` (Parity.lean): some vertex v of K_25 has even red degree;
- `red_degree_le_13`, `red_degree_ge_7`: the red degree of v is in [7, 13], so it is 8, 10 or 12;
- the red neighbourhood of v carries a (3,5)-good colouring and the blue one a (4,4)-good colouring
  (`good_induced`), so by `CatalogueComplete` they are listed colourings A, B up to permutations σ, ρ;
- the vertex permutation `assemblePerm v R Bl σ ρ` of K_25 (0 ↦ v, i+1 ↦ R[σ i], d+1+j ↦ Bl[ρ j]) turns the
  colouring into one of the shape `UnitShape d A B` (`good_relabel` keeps it good), which `UnitsRefuted` forbids.
-/

namespace MonsterVerified

/-! ## Part 5b: degree bounds in a (4,5)-good colouring of K_25 -/

theorem red_degree_le_13 {c : Nat → Nat → Bool} (hc : Good 4 5 25 c) (v : Nat) (hv : v < 25) :
    redDegree c 25 v ≤ 13 :=
  red_degree_le_13_of R35_le_14 hc v hv

theorem red_degree_ge_7 {c : Nat → Nat → Bool} (hc : Good 4 5 25 c) (v : Nat) (hv : v < 25) :
    7 ≤ redDegree c 25 v :=
  red_degree_ge_7_of R44_le_18 hc v hv

/-! ## Part 5c: the catalogue hypotheses and the assembled theorem -/

/-- a catalogue: for each degree `d`, listed colourings of K_d (red neighbourhoods) and of K_{24-d} (blue ones) -/
structure Catalogue where
  A : Nat → List (Nat → Nat → Bool)
  B : Nat → List (Nat → Nat → Bool)

/-- the degrees the assembly has to cover (even, in [7, 13]) -/
def Degrees : List Nat := [8, 10, 12]

/-- two colourings agree on every edge of K_m -/
def AgreeOn (m : Nat) (c₁ c₂ : Nat → Nat → Bool) : Prop :=
  ∀ x y, x < y → y < m → col c₁ x y = col c₂ x y

/-- catalogue completeness (the trusted input): every (3,5)-good colouring of K_d is, after some vertex
permutation, a listed `A`, and every (4,4)-good colouring of K_{24-d} a listed `B` -/
def CatalogueComplete (cat : Catalogue) : Prop :=
  ∀ d ∈ Degrees,
    (∀ c, Good 3 5 d c → ∃ a ∈ cat.A d, ∃ σ, permOK σ d = true ∧ AgreeOn d (relabel σ false c) a) ∧
    (∀ c, Good 4 4 (24 - d) c → ∃ b ∈ cat.B d, ∃ ρ, permOK ρ (24 - d) = true ∧ AgreeOn (24 - d) (relabel ρ false c) b)

/-- the shape of a gluing unit: vertex 0 red exactly to 1..d, colouring `a` on 1..d, colouring `b` on d+1..24 -/
def UnitShape (d : Nat) (a b c : Nat → Nat → Bool) : Prop :=
  (∀ i, i < d → col c 0 (i + 1) = true) ∧
  (∀ j, j < 24 - d → col c 0 (d + 1 + j) = false) ∧
  (∀ x y, x < y → y < d → col c (x + 1) (y + 1) = col a x y) ∧
  (∀ x y, x < y → y < 24 - d → col c (d + 1 + x) (d + 1 + y) = col b x y)

/-- the per-unit results: no good colouring of K_25 has the shape of a listed unit -/
def UnitsRefuted (cat : Catalogue) : Prop :=
  ∀ d ∈ Degrees, ∀ a ∈ cat.A d, ∀ b ∈ cat.B d, ∀ c, Good 4 5 25 c → ¬ UnitShape d a b c

/-! ### Lists reordered by a permutation -/

theorem getD_mem {L : List Nat} {i : Nat} (h : i < L.length) : L.getD i 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- `L` reordered by `σ`: entry `i` is `L[σ i]` -/
def permuted (L : List Nat) (σ : Array Nat) : List Nat :=
  (List.range L.length).map (fun i => L.getD (sig σ i) 0)

theorem length_permuted (L : List Nat) (σ : Array Nat) : (permuted L σ).length = L.length := by
  simp [permuted]

theorem mem_permuted {L : List Nat} {σ : Array Nat} (hσ : permOK σ L.length = true) {x : Nat}
    (hx : x ∈ permuted L σ) : x ∈ L := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact getD_mem ((permOK_spec hσ).1 i (List.mem_range.mp hi))

theorem nodup_permuted {L : List Nat} (hnd : L.Nodup) {σ : Array Nat} (hσ : permOK σ L.length = true) :
    (permuted L σ).Nodup := by
  apply nodup_map_on _ List.nodup_range
  intro x hx y hy he
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  have hsx := (permOK_spec hσ).1 x hx'
  have hsy := (permOK_spec hσ).1 y hy'
  exact (permOK_spec hσ).2 x y hx' hy' ((List.Nodup.getD_inj hsx hsy hnd).mp he)

theorem getD_permuted {L : List Nat} {σ : Array Nat} {i : Nat} (hi : i < L.length) :
    (permuted L σ).getD i 0 = L.getD (sig σ i) 0 := by
  rw [permuted, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ### The assembling permutation of K_25 -/

/-- the vertex permutation: 0 ↦ v, i+1 ↦ R[σ i] (i < |R|), |R|+1+j ↦ Bl[ρ j] -/
def assemblePerm (v : Nat) (R Bl : List Nat) (σ ρ : Array Nat) : Array Nat :=
  (v :: (permuted R σ ++ permuted Bl ρ)).toArray

theorem sig_assemblePerm_zero (v : Nat) (R Bl : List Nat) (σ ρ : Array Nat) :
    sig (assemblePerm v R Bl σ ρ) 0 = v := by
  rw [assemblePerm, sig_toArray, List.getD_cons_zero]

theorem sig_assemblePerm_red (v : Nat) (R Bl : List Nat) (σ ρ : Array Nat) {i : Nat} (hi : i < R.length) :
    sig (assemblePerm v R Bl σ ρ) (i + 1) = R.getD (sig σ i) 0 := by
  rw [assemblePerm, sig_toArray, List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [length_permuted]; exact hi), ← List.getD_eq_getElem?_getD,
    getD_permuted hi]

theorem sig_assemblePerm_blue (v : Nat) (R Bl : List Nat) (σ ρ : Array Nat) {j : Nat} (hj : j < Bl.length) :
    sig (assemblePerm v R Bl σ ρ) (R.length + 1 + j) = Bl.getD (sig ρ j) 0 := by
  have e : R.length + 1 + j = (R.length + j) + 1 := by omega
  rw [e, assemblePerm, sig_toArray, List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_permuted]; omega), ← List.getD_eq_getElem?_getD,
    length_permuted, Nat.add_sub_cancel_left, getD_permuted hj]

theorem assemblePerm_permOK {n v : Nat} {R Bl : List Nat} {σ ρ : Array Nat} (hv : v < n)
    (hR : ∀ x ∈ R, x < n ∧ x ≠ v) (hB : ∀ x ∈ Bl, x < n ∧ x ≠ v) (hdisj : ∀ x ∈ R, ∀ y ∈ Bl, x ≠ y)
    (hRnd : R.Nodup) (hBnd : Bl.Nodup) (hσ : permOK σ R.length = true) (hρ : permOK ρ Bl.length = true)
    (hn : R.length + Bl.length + 1 = n) : permOK (assemblePerm v R Bl σ ρ) n = true := by
  unfold permOK assemblePerm
  simp only [List.size_toArray, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, List.length_cons, List.length_append, length_permuted]
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · rcases List.mem_append.mp hx with hx | hx
      · exact (hR x (mem_permuted hσ hx)).1
      · exact (hB x (mem_permuted hρ hx)).1
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨nodup_permuted hRnd hσ, nodup_permuted hBnd hρ, ?_⟩⟩
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hR v (mem_permuted hσ hx)).2 rfl
      · exact (hB v (mem_permuted hρ hx)).2 rfl
    · intro x hx y hy
      exact hdisj x (mem_permuted hσ hx) y (mem_permuted hρ hy)

/-! ### The assembly -/

/-- the core of the assembly, for a vertex `v` whose red degree `d` is in `Degrees` -/
theorem assemble (cat : Catalogue) (hcat : CatalogueComplete cat) (hunits : UnitsRefuted cat)
    {c : Nat → Nat → Bool} (hc : Good 4 5 25 c) {v : Nat} (hv : v < 25)
    (hd : (redNbrs c 25 v).length ∈ Degrees) (hdB : (blueNbrs c 25 v).length = 24 - (redNbrs c 25 v).length) :
    False := by
  have hd3 : (redNbrs c 25 v).length = 8 ∨ (redNbrs c 25 v).length = 10 ∨ (redNbrs c 25 v).length = 12 := by
    simpa [Degrees] using hd
  -- the induced colourings on the red and blue neighbourhoods
  have hgA : Good 3 5 (redNbrs c 25 v).length (relabel (redNbrs c 25 v).toArray false c) :=
    good_induced (s := 3) (t := 5) true hv (redNbrs c 25 v) (redNbrs_nodup c 25 v)
      (fun x hx => mem_redNbrs.mp hx) hc
  have hgB : Good 4 4 (24 - (redNbrs c 25 v).length) (relabel (blueNbrs c 25 v).toArray false c) := by
    have := good_induced (s := 4) (t := 4) false hv (blueNbrs c 25 v) (blueNbrs_nodup c 25 v)
      (fun x hx => mem_blueNbrs.mp hx) hc
    rwa [hdB] at this
  -- they are listed, up to permutations σ and ρ
  obtain ⟨a, ha, σ, hσ, hagA⟩ := (hcat _ hd).1 _ hgA
  obtain ⟨b, hb, ρ, hρ, hagB⟩ := (hcat _ hd).2 _ hgB
  rw [← hdB] at hρ hagB
  -- the assembling permutation
  have hπ : permOK (assemblePerm v (redNbrs c 25 v) (blueNbrs c 25 v) σ ρ) 25 = true :=
    assemblePerm_permOK hv (fun x hx => ⟨(mem_redNbrs.mp hx).1, (mem_redNbrs.mp hx).2.1⟩)
      (fun x hx => ⟨(mem_blueNbrs.mp hx).1, (mem_blueNbrs.mp hx).2.1⟩)
      (fun x hx y hy e => by
        have h1 := (mem_redNbrs.mp hx).2.2
        have h2 := (mem_blueNbrs.mp hy).2.2
        rw [e, h2] at h1
        exact Bool.noConfusion h1)
      (redNbrs_nodup c 25 v) (blueNbrs_nodup c 25 v) hσ hρ (by omega)
  have hc' := good_relabel (f := false) hπ (fun h => by cases h) hc
  apply hunits _ hd a ha b hb _ hc'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [col_relabel_false, sig_assemblePerm_zero, sig_assemblePerm_red v _ _ σ ρ hi]
    exact (mem_redNbrs.mp (getD_mem ((permOK_spec hσ).1 i hi))).2.2
  · intro j hj
    rw [col_relabel_false, sig_assemblePerm_zero, sig_assemblePerm_blue v _ _ σ ρ (by omega)]
    exact (mem_blueNbrs.mp (getD_mem ((permOK_spec hρ).1 j (by omega)))).2.2
  · intro x y hxy hy
    rw [col_relabel_false, sig_assemblePerm_red v _ _ σ ρ (by omega), sig_assemblePerm_red v _ _ σ ρ hy,
      ← sig_toArray, ← sig_toArray, ← col_relabel_false, ← col_relabel_false]
    exact hagA x y hxy hy
  · intro x y hxy hy
    rw [col_relabel_false, sig_assemblePerm_blue v _ _ σ ρ (by omega), sig_assemblePerm_blue v _ _ σ ρ (by omega),
      ← sig_toArray, ← sig_toArray, ← col_relabel_false, ← col_relabel_false]
    exact hagB x y hxy (by omega)

/-- R(4,5) ≤ 25, assembled from catalogue completeness and the per-unit refutations -/
theorem r45_le_25 (cat : Catalogue) (hcat : CatalogueComplete cat) (hunits : UnitsRefuted cat) :
    ∀ c, ¬ Good 4 5 25 c := by
  intro c hc
  obtain ⟨v, hv, heven⟩ := exists_even_red_degree c
  have hle := red_degree_le_13 hc v hv
  have hge := red_degree_ge_7 hc v hv
  have hsum := redDegree_add_blue c hv
  have hd : (redNbrs c 25 v).length ∈ Degrees := by
    have h3 : redDegree c 25 v = 8 ∨ redDegree c 25 v = 10 ∨ redDegree c 25 v = 12 := by omega
    unfold redDegree at h3
    rcases h3 with h | h | h <;> rw [h] <;> decide
  exact assemble cat hcat hunits hc hv hd (by unfold redDegree at hsum; omega)

end MonsterVerified
