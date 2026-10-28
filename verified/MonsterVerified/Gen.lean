import MonsterVerified.Basic

namespace MonsterVerified

/-- all `k`-subsets of a list, in lexicographic order (the order monster's `full_clauses` uses) -/
def subsets : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (subsets xs k).map (x :: ·) ++ subsets xs (k + 1)

theorem subsets_spec : ∀ (L : List Nat) (k : Nat) (S : List Nat), S ∈ subsets L k → S.Sublist L ∧ S.length = k
  | _, 0, S, h => by simp [subsets] at h; subst h; exact ⟨List.nil_sublist _, rfl⟩
  | [], _ + 1, S, h => by simp [subsets] at h
  | x :: xs, k + 1, S, h => by
    simp only [subsets, List.mem_append, List.mem_map] at h
    rcases h with ⟨T, hT, rfl⟩ | h
    · obtain ⟨h1, h2⟩ := subsets_spec xs k T hT
      exact ⟨h1.cons₂ x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := subsets_spec xs (k + 1) S h
      exact ⟨h1.cons x, h2⟩

/-- ordered pairs (x before y) of a list -/
def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

theorem pairs_cover : ∀ (S : List Nat) (a b : Nat), a ∈ S → b ∈ S → a ≠ b → (a, b) ∈ pairs S ∨ (b, a) ∈ pairs S
  | [], _, _, ha, _, _ => by simp at ha
  | x :: xs, a, b, ha, hb, hne => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hne
    · exact Or.inl (Or.inl ⟨b, hb, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨a, ha, rfl, rfl⟩)
    · rcases pairs_cover xs a b ha hb hne with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- the variable of the unordered edge {x,y}, read from the table and checked -/
def edgeVar (E : Edges) (x y : Nat) : Option Nat :=
  if E[max x y * (max x y - 1) / 2 + min x y + 1]? = some (min x y, max x y) ∧ min x y < max x y then
    some (max x y * (max x y - 1) / 2 + min x y + 1)
  else none

theorem edgeVar_spec {E : Edges} {x y v : Nat} (h : edgeVar E x y = some v) :
    E[v]? = some (min x y, max x y) ∧ min x y < max x y ∧ 0 < v := by
  unfold edgeVar at h
  by_cases hc : E[max x y * (max x y - 1) / 2 + min x y + 1]? = some (min x y, max x y) ∧ min x y < max x y
  · rw [if_pos hc] at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hc.1, hc.2, by omega⟩
  · rw [if_neg hc] at h
    simp at h

theorem varVal_edgeVar {E : Edges} {x y v : Nat} (c : Nat → Nat → Bool) (h : edgeVar E x y = some v) :
    varVal E c v = col c x y := by
  obtain ⟨h1, h2, _⟩ := edgeVar_spec h
  unfold varVal
  rw [h1]
  simp only
  by_cases hxy : x < y
  · simp [Nat.min_eq_left (Nat.le_of_lt hxy), Nat.max_eq_right (Nat.le_of_lt hxy)]
  · have hyx : y ≤ x := by omega
    have hne : x ≠ y := by
      intro e; subst e; simp at h2
    rw [Nat.min_eq_right hyx, Nat.max_eq_left hyx]
    exact (col_comm c x y hne).symm

/-- Option-valued map; `none` as soon as one element fails -/
def omap (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => match f x, omap f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

theorem omap_mem {f : α → Option β} : ∀ {L : List α} {R : List β} {x : α}, omap f L = some R → x ∈ L →
    ∃ y ∈ R, f x = some y
  | [], _, _, _, hx => by simp at hx
  | a :: as, R, x, h, hx => by
    unfold omap at h
    split at h
    · rename_i y ys hy hys
      simp at h; subst h
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨y, by simp, hy⟩
      · obtain ⟨z, hz, hfz⟩ := omap_mem hys hx
        exact ⟨z, by simp [hz], hfz⟩
    · simp at h

/-- literal for the pair: forbidding a red clique uses ¬x (true when the edge is blue), a blue clique uses x -/
def pairLit (E : Edges) (red : Bool) (p : Nat × Nat) : Option Int :=
  match edgeVar E p.1 p.2 with
  | some v => some (if red then -(v : Int) else (v : Int))
  | none => none

def genClause (E : Edges) (red : Bool) (S : List Nat) : Option (List Int) :=
  omap (pairLit E red) (pairs S)

theorem litVal_pairLit {E : Edges} {red : Bool} {p : Nat × Nat} {l : Int} (c : Nat → Nat → Bool)
    (h : pairLit E red p = some l) : litVal E c l = (if red then !col c p.1 p.2 else col c p.1 p.2) := by
  unfold pairLit at h
  split at h
  · rename_i v hv
    simp at h; subst h
    have hval := varVal_edgeVar c hv
    have hpos := (edgeVar_spec hv).2.2
    have hv0 : v ≠ 0 := by omega
    cases red
    · simp [litVal, hval, hv0]
    · simp [litVal, hval]
  · simp at h

/-- every generated clique clause holds in every good colouring -/
theorem genClause_sound {s t n : Nat} {E : Edges} {red : Bool} {S : List Nat} {C : List Int}
    (hS : IsKSet n (if red then s else t) S) (hC : genClause E red S = some C) : Sound s t n E C := by
  intro c hc
  have key : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ col c a b = !red := by
    cases red
    · obtain ⟨a, ha, b, hb, hab, h⟩ := hc.2 S (by simpa using hS); exact ⟨a, ha, b, hb, hab, by simpa using h⟩
    · obtain ⟨a, ha, b, hb, hab, h⟩ := hc.1 S (by simpa using hS); exact ⟨a, ha, b, hb, hab, by simpa using h⟩
  obtain ⟨a, ha, b, hb, hab, hcol⟩ := key
  have hp : ∃ p ∈ pairs S, col c p.1 p.2 = !red := by
    rcases pairs_cover S a b ha hb hab with h | h
    · exact ⟨(a, b), h, hcol⟩
    · exact ⟨(b, a), h, by rw [← col_comm c a b hab]; exact hcol⟩
  obtain ⟨p, hpS, hpc⟩ := hp
  obtain ⟨l, hl, hfl⟩ := omap_mem hC hpS
  refine ⟨l, hl, ?_⟩
  rw [litVal_pairLit c hfl, hpc]
  cases red <;> simp

/-- the subsets of `range n` are k-sets -/
theorem subsets_range_kset {n k : Nat} {S : List Nat} (h : S ∈ subsets (List.range n) k) : IsKSet n k S := by
  obtain ⟨hsub, hlen⟩ := subsets_spec _ _ _ h
  refine ⟨(List.nodup_range).sublist hsub, ?_, hlen⟩
  intro x hx
  exact List.mem_range.mp (hsub.subset hx)

end MonsterVerified
