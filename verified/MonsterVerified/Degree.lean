import MonsterVerified.Lift
import MonsterVerified.Parity

/-!
# Degree bounds (assembly part 5b)

In a (4,5)-good colouring of K_25 every vertex has red degree in [7, 13]:
- 14 red neighbours would carry a (3,5)-good colouring of K_14 (a red triangle there plus the vertex is a red K_4),
  contradicting R(3,5) ≤ 14;
- 18 blue neighbours would carry a (4,4)-good colouring of K_18 (a blue K_4 there plus the vertex is a blue K_5),
  contradicting R(4,4) ≤ 18.
The restriction lemma is `good_restrict` (Lift.lean); `good_induced` packages it for a list of vertices.
The bounds are stated here with the two small Ramsey theorems as hypotheses (so this file does not depend on the
checker); Assembly.lean instantiates them with `R35_le_14` and `R44_le_18`.
-/

namespace MonsterVerified

theorem sig_toArray (L : List Nat) (x : Nat) : sig L.toArray x = L.getD x 0 := by
  simp [sig]

/-- the colour read through a relabelling (no colour swap) is the colour of the image edge -/
theorem col_relabel_false (σ : Array Nat) (c : Nat → Nat → Bool) (x y : Nat) :
    col (relabel σ false c) x y = col c (sig σ x) (sig σ y) := by
  show (if x < y then relabel σ false c x y else relabel σ false c y x) = _
  by_cases h : x < y
  · simp only [h, ite_true, relabel, Bool.xor_false]
  · simp only [h, ite_false, relabel, Bool.xor_false]
    by_cases he : sig σ x = sig σ y
    · rw [he]
    · exact col_comm c _ _ (Ne.symm he)

theorem mem_redNbrs {c : Nat → Nat → Bool} {n v u : Nat} :
    u ∈ redNbrs c n v ↔ u < n ∧ u ≠ v ∧ col c v u = true := by
  simp [redNbrs, List.mem_filter, List.mem_range]

theorem mem_blueNbrs {c : Nat → Nat → Bool} {n v u : Nat} :
    u ∈ blueNbrs c n v ↔ u < n ∧ u ≠ v ∧ col c v u = false := by
  simp [blueNbrs, List.mem_filter, List.mem_range]

theorem redNbrs_nodup (c : Nat → Nat → Bool) (n v : Nat) : (redNbrs c n v).Nodup :=
  List.filter_sublist.nodup List.nodup_range

theorem blueNbrs_nodup (c : Nat → Nat → Bool) (n v : Nat) : (blueNbrs c n v).Nodup :=
  List.filter_sublist.nodup List.nodup_range

theorem sumRange_indicator_ne (v : Nat) :
    ∀ n, sumRange (fun u => if u = v then 0 else 1) n = if v < n then n - 1 else n
  | 0 => by simp [sumRange]
  | n + 1 => by
    simp only [sumRange, sumRange_indicator_ne v n]
    split <;> split <;> split <;> omega

/-- red neighbours plus blue neighbours are all the other vertices -/
theorem redDegree_add_blue (c : Nat → Nat → Bool) {n v : Nat} (hv : v < n) :
    redDegree c n v + (blueNbrs c n v).length = n - 1 := by
  unfold redDegree redNbrs blueNbrs
  rw [length_filter_range, length_filter_range, ← sumRange_add]
  have : sumRange (fun u => (if (u != v && col c v u) = true then 1 else 0)
      + (if (u != v && !col c v u) = true then 1 else 0)) n = sumRange (fun u => if u = v then 0 else 1) n :=
    sumRange_congr n (fun u _ => by by_cases h : u = v <;> cases col c v u <;> simp [h])
  rw [this, sumRange_indicator_ne]; simp [hv]

/-- the colouring induced on a list `L` of vertices all joined to `v` by colour `red`, read on K_{|L|} -/
theorem good_induced {s t n v : Nat} {c : Nat → Nat → Bool} (red : Bool) (hv : v < n) (L : List Nat)
    (hnd : L.Nodup) (hL : ∀ x ∈ L, x < n ∧ x ≠ v ∧ col c v x = red)
    (hc : Good (if red then s + 1 else s) (if red then t else t + 1) n c) :
    Good s t L.length (relabel L.toArray false c) := by
  have he : embOK L.toArray n v = true := by
    unfold embOK
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne]
    exact ⟨fun x hx => ⟨(hL x hx).1, (hL x hx).2.1⟩, hnd⟩
  have hapex : ∀ x, x < L.toArray.size → col c v (sig L.toArray x) = red := by
    intro x hx
    rw [List.size_toArray] at hx
    have hmem : sig L.toArray x ∈ L := by
      rw [sig_toArray, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
      exact List.getElem_mem hx
    exact (hL _ hmem).2.2
  have := good_restrict red he hv hapex hc
  rwa [List.size_toArray] at this

/-- a vertex of a (4,5)-good colouring of K_25 has at most 13 red neighbours, given R(3,5) ≤ 14 -/
theorem red_degree_le_13_of (h35 : ∀ c, ¬ Good 3 5 14 c) {c : Nat → Nat → Bool} (hc : Good 4 5 25 c)
    (v : Nat) (hv : v < 25) : redDegree c 25 v ≤ 13 := by
  apply Classical.byContradiction
  intro hge
  have h14 : 14 ≤ redDegree c 25 v := by omega
  have hlen : ((redNbrs c 25 v).take 14).length = 14 := by
    rw [List.length_take]; unfold redDegree at h14; omega
  have hg := good_induced (s := 3) (t := 5) true hv ((redNbrs c 25 v).take 14)
    ((List.take_sublist _ _).nodup (redNbrs_nodup c 25 v))
    (fun x hx => mem_redNbrs.mp (List.mem_of_mem_take hx)) hc
  rw [hlen] at hg
  exact h35 _ hg

/-- a vertex of a (4,5)-good colouring of K_25 has at least 7 red neighbours, given R(4,4) ≤ 18 -/
theorem red_degree_ge_7_of (h44 : ∀ c, ¬ Good 4 4 18 c) {c : Nat → Nat → Bool} (hc : Good 4 5 25 c)
    (v : Nat) (hv : v < 25) : 7 ≤ redDegree c 25 v := by
  apply Classical.byContradiction
  intro hlt
  have hb : 18 ≤ (blueNbrs c 25 v).length := by have := redDegree_add_blue c hv; omega
  have hlen : ((blueNbrs c 25 v).take 18).length = 18 := by rw [List.length_take]; omega
  have hg := good_induced (s := 4) (t := 4) false hv ((blueNbrs c 25 v).take 18)
    ((List.take_sublist _ _).nodup (blueNbrs_nodup c 25 v))
    (fun x hx => mem_blueNbrs.mp (List.mem_of_mem_take hx)) hc
  rw [hlen] at hg
  exact h44 _ hg

end MonsterVerified
