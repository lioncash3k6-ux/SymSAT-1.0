import MonsterVerified.Gen
import MonsterVerified.Rup
import MonsterVerified.Assume

/-!
# Substitution redundancy (SR), hinted

A clause `C` is SR with respect to a database `F` under a substitution `σ` (literals to literals or constants) when
`F ∧ ¬C ⊢₁ D|σ` for every `D ∈ F ∪ {C}` (or `D|σ` is satisfied by `σ`). Then `F` satisfiable implies `F ∧ C`
satisfiable: a model `c` falsifying `C` satisfies every `D|σ` (unit propagation is sound), so the colouring
`c ∘ σ` (`substCol`) satisfies every `D` and `C`. Here the propagations are given as LRAT hints: an α list
extending `¬C` by unit hints, then one hint group per clause whose image is neither satisfied by `σ` nor by α.
Clauses added this way are only satisfiability-preserving, so the checker keeps them in a separate tier
(Checker.lean: `srList`), on which no symmetry step may act.
-/

namespace MonsterVerified

/-- the image of a literal under a substitution: a constant or a literal -/
inductive SLit where
  | tt
  | ff
  | lit (l : Int)

structure Subst where
  witness : List Int
  pairs : List (Int × Int)

/-- σ on a variable: a witness literal `w` with `|w| = v` fixes `v` to `w > 0`; a pair `(a, b)` with `|a| = v` maps
`v` to `b` (negated if `a < 0`); identity otherwise -/
def Subst.var (σ : Subst) (v : Nat) : SLit :=
  match σ.witness.find? (fun w => w.natAbs == v) with
  | some w => if w > 0 then .tt else .ff
  | none =>
    match σ.pairs.find? (fun p => p.1.natAbs == v) with
    | some (a, b) => .lit (if a > 0 then b else -b)
    | none => .lit (Int.ofNat v)

def SLit.neg : SLit → SLit
  | .tt => .ff
  | .ff => .tt
  | .lit l => .lit (-l)

def Subst.lit (σ : Subst) (l : Int) : SLit := if l > 0 then σ.var l.natAbs else (σ.var l.natAbs).neg

/-- run-time side condition: no literal 0 in the substitution -/
def substOK (σ : Subst) : Bool := σ.witness.all (fun w => w != 0) && σ.pairs.all (fun p => p.1 != 0 && p.2 != 0)

/-- run-time side condition on a variable: the edge table maps it to a pair and back (so a colouring built on
pairs reads back on this variable) -/
def varOK (E : Edges) (v : Nat) : Bool :=
  match E[v]? with
  | some (i, j) => edgeVar E i j == some v
  | none => false

def SLit.val (E : Edges) (c : Nat → Nat → Bool) : SLit → Bool
  | .tt => true
  | .ff => false
  | .lit l => litVal E c l

/-- the colouring `c ∘ σ`: pair (a, b) takes the value of σ(its variable) under `c` -/
def substCol (E : Edges) (σ : Subst) (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun a b => match edgeVar E a b with
    | some v => (σ.var v).val E c
    | none => false

theorem edgeVar_comm (E : Edges) (a b : Nat) : edgeVar E a b = edgeVar E b a := by
  unfold edgeVar
  rw [Nat.max_comm, Nat.min_comm]

theorem varVal_substCol {E : Edges} {σ : Subst} {c : Nat → Nat → Bool} {v : Nat} (hv : varOK E v = true) :
    varVal E (substCol E σ c) v = (σ.var v).val E c := by
  unfold varOK at hv
  cases hE : E[v]? with
  | none => rw [hE] at hv; simp at hv
  | some p =>
    obtain ⟨i, j⟩ := p
    rw [hE] at hv
    simp only [beq_iff_eq] at hv
    unfold varVal
    rw [hE]
    simp only [col]
    by_cases hij : i < j
    · simp only [hij, ite_true, substCol, hv]
    · simp only [hij, ite_false, substCol, edgeVar_comm E j i, hv]

theorem subst_var_ne_zero {σ : Subst} {v : Nat} {l : Int} (hσ : substOK σ = true) (hv : v ≠ 0)
    (h : σ.var v = .lit l) : l ≠ 0 := by
  unfold substOK at hσ
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hσ
  cases hw : σ.witness.find? (fun w => w.natAbs == v) with
  | some w => simp only [Subst.var, hw] at h; split at h <;> simp at h
  | none =>
    cases hp : σ.pairs.find? (fun p => p.1.natAbs == v) with
    | some p =>
      obtain ⟨a, b⟩ := p
      simp only [Subst.var, hw, hp, SLit.lit.injEq] at h
      have hb := (hσ.2 (a, b) (List.mem_of_find?_eq_some hp)).2
      subst h
      split <;> omega
    | none =>
      simp only [Subst.var, hw, hp, SLit.lit.injEq] at h
      subst h
      intro h0
      exact hv (Int.ofNat.inj h0)

theorem SLit_val_neg {E : Edges} {c : Nat → Nat → Bool} {x : SLit} (hx : ∀ l, x = .lit l → l ≠ 0) :
    x.neg.val E c = !x.val E c := by
  cases x with
  | tt => rfl
  | ff => rfl
  | lit l => simp only [SLit.neg, SLit.val]; exact litVal_neg (hx l rfl)

/-- reading a literal in the substituted colouring = reading its image in the original one -/
theorem litVal_substCol {E : Edges} {σ : Subst} {c : Nat → Nat → Bool} {l : Int} (hσ : substOK σ = true)
    (hl : l ≠ 0) (hv : varOK E l.natAbs = true) : litVal E (substCol E σ c) l = (σ.lit l).val E c := by
  have hne : l.natAbs ≠ 0 := fun h => hl (Int.natAbs_eq_zero.mp h)
  unfold litVal Subst.lit
  rw [varVal_substCol hv]
  by_cases hp : l > 0
  · simp [hp]
  · simp only [hp, ite_false]
    rw [SLit_val_neg (fun l' h => subst_var_ne_zero hσ hne h)]

/-- `D|σ`: `none` if a literal maps to true, else the literal images (false constants dropped) -/
def Subst.image (σ : Subst) : List Int → Option (List Int)
  | [] => some []
  | l :: ls =>
    match σ.lit l with
    | .tt => none
    | .ff => σ.image ls
    | .lit l' => (σ.image ls).map (l' :: ·)

theorem image_none_sat {E : Edges} {σ : Subst} {c : Nat → Nat → Bool} (hσ : substOK σ = true) :
    ∀ {D : List Int}, (∀ l ∈ D, l ≠ 0 ∧ varOK E l.natAbs = true) → σ.image D = none →
      ClauseSat E (substCol E σ c) D
  | [], _, h => by simp [Subst.image] at h
  | l :: ls, hD, h => by
    unfold Subst.image at h
    cases hs : σ.lit l with
    | tt =>
      refine ⟨l, by simp, ?_⟩
      rw [litVal_substCol hσ (hD l (by simp)).1 (hD l (by simp)).2, hs]
      rfl
    | ff =>
      rw [hs] at h
      obtain ⟨m, hm, hv⟩ := image_none_sat hσ (fun x hx => hD x (by simp [hx])) h
      exact ⟨m, by simp [hm], hv⟩
    | lit l' =>
      rw [hs] at h
      simp at h
      obtain ⟨m, hm, hv⟩ := image_none_sat hσ (fun x hx => hD x (by simp [hx])) h
      exact ⟨m, by simp [hm], hv⟩

theorem image_some_sat {E : Edges} {σ : Subst} {c : Nat → Nat → Bool} (hσ : substOK σ = true) :
    ∀ {D R : List Int}, (∀ l ∈ D, l ≠ 0 ∧ varOK E l.natAbs = true) → σ.image D = some R →
      ClauseSat E c R → ClauseSat E (substCol E σ c) D
  | [], R, _, h, hR => by
    simp [Subst.image] at h; subst h
    obtain ⟨m, hm, _⟩ := hR
    simp at hm
  | l :: ls, R, hD, h, hR => by
    unfold Subst.image at h
    cases hs : σ.lit l with
    | tt => rw [hs] at h; simp at h
    | ff =>
      rw [hs] at h
      obtain ⟨m, hm, hv⟩ := image_some_sat hσ (fun x hx => hD x (by simp [hx])) h hR
      exact ⟨m, by simp [hm], hv⟩
    | lit l' =>
      rw [hs] at h
      cases hi : σ.image ls with
      | none => rw [hi] at h; simp at h
      | some R' =>
        rw [hi] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨m, hm, hv⟩ := hR
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · refine ⟨l, by simp, ?_⟩
          rw [litVal_substCol hσ (hD l (by simp)).1 (hD l (by simp)).2, hs]
          exact hv
        · obtain ⟨m', hm', hv'⟩ := image_some_sat hσ (fun x hx => hD x (by simp [hx])) hi ⟨m, hm, hv⟩
          exact ⟨m', by simp [hm'], hv'⟩

/-- extend an assignment by unit hints (the α fixpoint of `¬C`) -/
def extend (get : Nat → Option (List Int)) : Assign → List Nat → Option Assign
  | α, [] => some α
  | α, h :: hs =>
    match get h with
    | none => none
    | some H =>
      match evalH α H with
      | .unit l => extend get (assignTrue α l) hs
      | _ => none

theorem extend_agrees {E : Edges} {c : Nat → Nat → Bool} {get : Nat → Option (List Int)}
    (hget : ∀ h H, get h = some H → ClauseSat E c H) :
    ∀ {α α' : Assign} {hs : List Nat}, Agrees E c α → extend get α hs = some α' → Agrees E c α'
  | _, _, [], ha, h => by simp [extend] at h; subst h; exact ha
  | α, α', h :: hs, ha, he => by
    unfold extend at he
    cases hg : get h with
    | none => rw [hg] at he; simp at he
    | some H =>
      rw [hg] at he
      simp only at he
      cases hv : evalH α H with
      | unit l =>
        rw [hv] at he
        exact extend_agrees hget (agrees_assignTrue ha ((evalH_sound ha H (hget h H hg)).2 l hv)) he
      | sat => rw [hv] at he; simp at he
      | conflict => rw [hv] at he; simp at he
      | many => rw [hv] at he; simp at he

theorem agrees_append {E : Edges} {c : Nat → Nat → Bool} {α β : Assign} (ha : Agrees E c α) (hb : Agrees E c β) :
    Agrees E c (α ++ β) := by
  intro v b hv
  unfold alook at hv
  rw [List.find?_append] at hv
  cases hf : α.find? (fun p => p.1 == v) with
  | some p =>
    rw [hf] at hv
    simp only [Option.some_or, Option.map_some, Option.some.injEq] at hv
    exact ha v b (by unfold alook; rw [hf]; simp [hv])
  | none =>
    rw [hf] at hv
    simp only [Option.none_or] at hv
    exact hb v b hv

theorem taut_sat {E : Edges} {c : Nat → Nat → Bool} {R : List Int} {l : Int} (hl : l ≠ 0) (h1 : l ∈ R)
    (h2 : -l ∈ R) : ClauseSat E c R := by
  cases hv : litVal E c l with
  | true => exact ⟨l, h1, hv⟩
  | false => exact ⟨-l, h2, by rw [litVal_neg hl, hv]; rfl⟩

theorem image_lit_ne_zero {E : Edges} {σ : Subst} (hσ : substOK σ = true) : ∀ {D R : List Int},
    (∀ l ∈ D, l ≠ 0 ∧ varOK E l.natAbs = true) → σ.image D = some R → ∀ l ∈ R, l ≠ 0
  | [], R, _, h, l, hl => by simp [Subst.image] at h; subst h; simp at hl
  | d :: ds, R, hD, h, l, hl => by
    unfold Subst.image at h
    cases hs : σ.lit d with
    | tt => rw [hs] at h; simp at h
    | ff => rw [hs] at h; exact image_lit_ne_zero hσ (fun x hx => hD x (by simp [hx])) h l hl
    | lit l' =>
      rw [hs] at h
      cases hi : σ.image ds with
      | none => rw [hi] at h; simp at h
      | some R' =>
        rw [hi] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · have hd0 : d.natAbs ≠ 0 := by have := (hD d (by simp)).1; omega
          unfold Subst.lit at hs
          split at hs
          · exact subst_var_ne_zero hσ hd0 hs
          · have hn : ∀ l, (σ.var d.natAbs).neg = .lit l → l ≠ 0 := by
              intro l h
              cases hx : σ.var d.natAbs with
              | tt => rw [hx] at h; simp [SLit.neg] at h
              | ff => rw [hx] at h; simp [SLit.neg] at h
              | lit m =>
                rw [hx] at h
                simp only [SLit.neg, SLit.lit.injEq] at h
                have := subst_var_ne_zero hσ hd0 hx
                omega
            exact hn l hs
        · exact image_lit_ne_zero hσ (fun x hx => hD x (by simp [hx])) hi l hl
/-- one clause of the SR check: `D|σ` satisfied by σ, a tautology, satisfied by α, or derived from `α ∧ ¬(D|σ)`
by the next hint group (whose id must be `did`); returns the remaining groups -/
def srClause (get : Nat → Option (List Int)) (E : Edges) (σ : Subst) (α : Assign) (did : Nat) (D : List Int)
    (groups : List (Nat × List Nat)) : Option (List (Nat × List Nat)) :=
  if !(D.all (fun l => l != 0 && varOK E l.natAbs)) then none
  else
    match σ.image D with
    | none => some groups
    | some R =>
      if R.any (fun l => decide (-l ∈ R)) then some groups
      else if R.any (fun l => decide (lstat α l = some true)) then some groups
      else
        match groups with
        | (g, hints) :: rest => if g == did && rup get (negAssign R ++ α) hints then some rest else none
        | [] => none

theorem srClause_sound {E : Edges} {c : Nat → Nat → Bool} {get : Nat → Option (List Int)} {σ : Subst} {α : Assign}
    {did : Nat} {D : List Int} {groups rest : List (Nat × List Nat)} (hσ : substOK σ = true)
    (hget : ∀ h H, get h = some H → ClauseSat E c H) (ha : Agrees E c α)
    (h : srClause get E σ α did D groups = some rest) : ClauseSat E (substCol E σ c) D := by
  unfold srClause at h
  split at h
  · simp at h
  · rename_i hall
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at hall
    have hD : ∀ l ∈ D, l ≠ 0 ∧ varOK E l.natAbs = true := fun l hl => hall l hl
    cases hi : σ.image D with
    | none => exact image_none_sat hσ hD hi
    | some R =>
      rw [hi] at h
      simp only at h
      refine image_some_sat hσ hD hi ?_
      split at h
      · rename_i ht
        simp only [List.any_eq_true, decide_eq_true_eq] at ht
        obtain ⟨l, hl, hnl⟩ := ht
        have hl0 : l ≠ 0 := by
          -- a literal of the image: an image of a literal of D, hence non-zero
          exact image_lit_ne_zero hσ hD hi l hl
        exact taut_sat hl0 hl hnl
      · split at h
        · rename_i hs
          simp only [List.any_eq_true, decide_eq_true_eq] at hs
          obtain ⟨l, hl, hv⟩ := hs
          exact ⟨l, hl, lstat_sound ha hv⟩
        · cases groups with
          | nil => simp at h
          | cons gh rest' =>
            obtain ⟨g, hints⟩ := gh
            simp only at h
            split at h
            · rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              by_cases hsat : ClauseSat E c R
              · exact hsat
              · exfalso
                have hf : ∀ l ∈ R, litVal E c l = false := by
                  intro l hl
                  cases hv : litVal E c l with
                  | false => rfl
                  | true => exact absurd ⟨l, hl, hv⟩ hsat
                exact rup_sound hget _ hints (agrees_append (agrees_negAssign hf) ha) hc.2
            · simp at h

end MonsterVerified
