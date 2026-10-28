import MonsterVerified.Basic

namespace MonsterVerified

/-- partial assignment: list of (variable, value); the first entry for a variable wins -/
abbrev Assign := List (Nat × Bool)

def alook (α : Assign) (v : Nat) : Option Bool := (α.find? (fun p => p.1 == v)).map (·.2)

/-- the assignment agrees with colouring `c` -/
def Agrees (E : Edges) (c : Nat → Nat → Bool) (α : Assign) : Prop :=
  ∀ v b, alook α v = some b → varVal E c v = b

def lstat (α : Assign) (l : Int) : Option Bool :=
  (alook α l.natAbs).map (fun b => if l > 0 then b else !b)

theorem lstat_sound {E : Edges} {c : Nat → Nat → Bool} {α : Assign} {l : Int} {x : Bool}
    (ha : Agrees E c α) (h : lstat α l = some x) : litVal E c l = x := by
  unfold lstat at h
  cases hl : alook α l.natAbs with
  | none => rw [hl] at h; simp at h
  | some b =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hv := ha _ _ hl
    unfold litVal
    by_cases hp : l > 0
    · simp [hp] at h ⊢; rw [hv, h]
    · simp [hp] at h ⊢; rw [hv, h]

inductive HRes where
  | sat
  | conflict
  | unit (l : Int)
  | many

/-- status of a clause under α -/
def evalH (α : Assign) : List Int → HRes
  | [] => .conflict
  | l :: ls =>
    match lstat α l with
    | some true => .sat
    | some false => evalH α ls
    | none =>
      match evalH α ls with
      | .sat => .sat
      | .conflict => .unit l
      | .unit _ => .many
      | .many => .many

/-- if c satisfies H and agrees with α: H is not in conflict, and a unit literal is true under c -/
theorem evalH_sound {E : Edges} {c : Nat → Nat → Bool} {α : Assign} (ha : Agrees E c α) :
    ∀ (H : List Int), ClauseSat E c H →
      evalH α H ≠ .conflict ∧ (∀ l, evalH α H = .unit l → litVal E c l = true)
  | [], hs => by obtain ⟨l, hl, _⟩ := hs; simp at hl
  | l :: ls, hs => by
    obtain ⟨m, hm, hmv⟩ := hs
    simp only [List.mem_cons] at hm
    unfold evalH
    cases hst : lstat α l with
    | some x =>
      cases x with
      | true => simp
      | false =>
        simp only
        have hlf : litVal E c l = false := lstat_sound ha hst
        have hrest : ClauseSat E c ls := by
          rcases hm with rfl | hm
          · rw [hlf] at hmv; simp at hmv
          · exact ⟨m, hm, hmv⟩
        exact evalH_sound ha ls hrest
    | none =>
      simp only
      by_cases hls : ClauseSat E c ls
      · obtain ⟨h1, h2⟩ := evalH_sound ha ls hls
        cases he : evalH α ls with
        | sat => simp
        | conflict => exact absurd he h1
        | unit _ => simp
        | many => simp
      · -- every literal of ls is false under c, so l itself is true
        have hl : litVal E c l = true := by
          rcases hm with rfl | hm
          · exact hmv
          · exact absurd ⟨m, hm, hmv⟩ hls
        cases he : evalH α ls with
        | sat => simp
        | conflict =>
          refine ⟨by simp, ?_⟩
          intro l' h'; simp at h'; subst h'; exact hl
        | unit _ => simp
        | many => simp

/-- extend α by making literal l true -/
def assignTrue (α : Assign) (l : Int) : Assign := (l.natAbs, decide (l > 0)) :: α

theorem agrees_assignTrue {E : Edges} {c : Nat → Nat → Bool} {α : Assign} {l : Int}
    (ha : Agrees E c α) (hl : litVal E c l = true) : Agrees E c (assignTrue α l) := by
  intro v b hv
  unfold alook assignTrue at hv
  simp only [List.find?_cons] at hv
  by_cases he : l.natAbs = v
  · subst he
    simp at hv
    subst hv
    unfold litVal at hl
    by_cases hp : l > 0
    · simp [hp] at hl ⊢; exact hl
    · simp [hp] at hl ⊢; exact hl
  · have : (l.natAbs == v) = false := by simp [he]
    rw [this] at hv
    exact ha v b hv

/-- check a hint chain (LRAT): each hint must be unit (extend α) or falsified (success) -/
def rup (get : Nat → Option (List Int)) : Assign → List Nat → Bool
  | _, [] => false
  | α, h :: hs =>
    match get h with
    | none => false
    | some H =>
      match evalH α H with
      | .conflict => true
      | .unit l => rup get (assignTrue α l) hs
      | _ => false

theorem rup_sound {E : Edges} {c : Nat → Nat → Bool} {get : Nat → Option (List Int)}
    (hget : ∀ h H, get h = some H → ClauseSat E c H) :
    ∀ (α : Assign) (hs : List Nat), Agrees E c α → rup get α hs = true → False
  | _, [], _, h => by simp [rup] at h
  | α, h :: hs, ha, hr => by
    unfold rup at hr
    cases hg : get h with
    | none => rw [hg] at hr; simp at hr
    | some H =>
      rw [hg] at hr
      simp only at hr
      obtain ⟨h1, h2⟩ := evalH_sound ha H (hget h H hg)
      cases he : evalH α H with
      | conflict => exact h1 he
      | unit l =>
        rw [he] at hr
        exact rup_sound hget (assignTrue α l) hs (agrees_assignTrue ha (h2 l he)) hr
      | sat => rw [he] at hr; simp at hr
      | many => rw [he] at hr; simp at hr

/-- the negation of a clause as an assignment -/
def negAssign (C : List Int) : Assign := C.map (fun l => (l.natAbs, !decide (l > 0)))

theorem agrees_negAssign {E : Edges} {c : Nat → Nat → Bool} {C : List Int}
    (hf : ∀ l ∈ C, litVal E c l = false) : Agrees E c (negAssign C) := by
  intro v b hv
  unfold alook negAssign at hv
  cases hfd : List.find? (fun p => p.1 == v) (C.map (fun l => (l.natAbs, !decide (l > 0)))) with
  | none => rw [hfd] at hv; simp at hv
  | some p =>
    rw [hfd] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    have hmem := List.mem_of_find?_eq_some hfd
    have hpv := List.find?_some hfd
    simp only [beq_iff_eq] at hpv
    simp only [List.mem_map] at hmem
    obtain ⟨l, hl, rfl⟩ := hmem
    simp only at hpv hv
    subst hpv; subst hv
    have := hf l hl
    unfold litVal at this
    by_cases hp : l > 0
    · simp [hp] at this ⊢; exact this
    · simp [hp] at this ⊢; exact this

/-- An LRAT step is sound when all hint clauses are sound. -/
theorem rup_step_sound {s t n : Nat} {E : Edges} {get : Nat → Option (List Int)} {C : List Int} {hs : List Nat}
    (hget : ∀ h H, get h = some H → Sound s t n E H) (hr : rup get (negAssign C) hs = true) : Sound s t n E C := by
  intro c hc
  by_cases hsat : ClauseSat E c C
  · exact hsat
  · exfalso
    have hf : ∀ l ∈ C, litVal E c l = false := by
      intro l hl
      cases h : litVal E c l with
      | false => rfl
      | true => exact absurd ⟨l, hl, h⟩ hsat
    exact rup_sound (fun h H hg => hget h H hg c hc) (negAssign C) hs (agrees_negAssign hf) hr

end MonsterVerified

namespace MonsterVerified

/-! ## Executable form of `rup` with an array assignment (proved equal; the compiler uses it through `csimp`)

`alook` walks the association list for every literal of every hint clause: 73% of a lemma check (2026-10-28, after
the fast parser). `rupA` keeps the same assignment as an array of `UInt8` (0 = unassigned, 1 = false, 2 = true),
indexed by variable and grown on demand; `toArr` builds it from the list so that the FIRST entry of a variable wins,
exactly like `alook`. `rup_eq_rupFast` is the kernel-checked equality `@rup = @rupFast`, so every theorem about
`rup` applies to what actually runs. -/

/-- set index `v` to `x`, growing the array with zeros first if needed -/
def setGrow (a : Array UInt8) (v : Nat) (x : UInt8) : Array UInt8 :=
  if v < a.size then a.setIfInBounds v x else (a ++ Array.replicate (v + 1 - a.size) 0).setIfInBounds v x

def alookA (a : Array UInt8) (v : Nat) : Option Bool :=
  match a[v]? with
  | some 1 => some false
  | some 2 => some true
  | _ => none

def encode (b : Bool) : UInt8 := if b then 2 else 1

theorem getElem?_setGrow (a : Array UInt8) (v w : Nat) (x : UInt8) :
    (setGrow a v x)[w]? =
      if v = w then some x else if w < a.size then a[w]? else if w < v + 1 then some 0 else none := by
  unfold setGrow
  by_cases hv : v < a.size
  · simp only [hv, ite_true, Array.getElem?_setIfInBounds]
    by_cases hvw : v = w
    · simp [hvw, hv]
    · simp only [hvw, ite_false]
      by_cases hw : w < a.size
      · simp [hw]
      · have h1 : ¬ w < v + 1 := by omega
        simp [hw, h1, Array.getElem?_eq_none_iff.mpr (by omega : a.size ≤ w)]
  · simp only [hv, ite_false, Array.getElem?_setIfInBounds, Array.size_append, Array.size_replicate]
    by_cases hvw : v = w
    · subst hvw
      have : v < a.size + (v + 1 - a.size) := by omega
      simp [this]
    · simp only [hvw, ite_false, Array.getElem?_append, Array.getElem?_replicate]
      by_cases hw : w < a.size
      · simp [hw]
      · simp only [hw, ite_false]
        by_cases h2 : w < v + 1
        · have : w - a.size < v + 1 - a.size := by omega
          simp [h2, this]
        · have : ¬ w - a.size < v + 1 - a.size := by omega
          simp [h2, this]

theorem alookA_setGrow (a : Array UInt8) (v w : Nat) (b : Bool) :
    alookA (setGrow a v (encode b)) w = if v = w then some b else alookA a w := by
  unfold alookA
  rw [getElem?_setGrow]
  by_cases hvw : v = w
  · simp only [hvw, ite_true]
    cases b <;> rfl
  · simp only [hvw, ite_false]
    by_cases hw : w < a.size
    · simp [hw]
    · rw [Array.getElem?_eq_none_iff.mpr (by omega : a.size ≤ w)]
      simp only [hw, ite_false]
      by_cases h2 : w < v + 1
      · simp only [h2, ite_true]; rfl
      · simp only [h2, ite_false]

/-- the largest variable of an assignment list (so the array is allocated once; growth in `setGrow` then never runs) -/
def maxVar (α : Assign) : Nat := α.foldl (fun m p => max m p.1) 0

theorem alookA_replicate (k v : Nat) : alookA (Array.replicate k 0) v = none := by
  unfold alookA
  rw [Array.getElem?_replicate]
  by_cases h : v < k
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]

/-- the array of an assignment list: allocated once at the largest variable, then filled from the right so that the
FIRST entry of a variable wins, like `alook` -/
def toArr (α : Assign) : Array UInt8 :=
  α.foldr (fun p a => setGrow a p.1 (encode p.2)) (Array.replicate (maxVar α + 1) 0)

/-- `a` represents `α`: the same lookup on every variable -/
def Rep (a : Array UInt8) (α : Assign) : Prop := ∀ w, alookA a w = alook α w

theorem rep_foldr (base : Array UInt8) (hb : ∀ w, alookA base w = none) :
    ∀ (β : Assign), Rep (β.foldr (fun q a => setGrow a q.1 (encode q.2)) base) β
  | [] => fun w => by simp only [List.foldr, alook, List.find?_nil, Option.map_none]; exact hb w
  | q :: β => fun w => by
    show alookA (setGrow (β.foldr (fun q a => setGrow a q.1 (encode q.2)) base) q.1 (encode q.2)) w = alook (q :: β) w
    rw [alookA_setGrow, rep_foldr base hb β w]
    by_cases h : q.1 = w
    · subst h; simp [alook]
    · have hb' : (q.1 == w) = false := by simp [h]
      simp [h, alook, hb']

theorem rep_toArr (α : Assign) : Rep (toArr α) α :=
  rep_foldr _ (fun w => alookA_replicate _ w) α

def lstatA (a : Array UInt8) (l : Int) : Option Bool :=
  (alookA a l.natAbs).map (fun b => if l > 0 then b else !b)

theorem lstatA_rep {a : Array UInt8} {α : Assign} (h : Rep a α) (l : Int) : lstatA a l = lstat α l := by
  unfold lstatA lstat; rw [h]

def evalHA (a : Array UInt8) : List Int → HRes
  | [] => .conflict
  | l :: ls =>
    match lstatA a l with
    | some true => .sat
    | some false => evalHA a ls
    | none =>
      match evalHA a ls with
      | .sat => .sat
      | .conflict => .unit l
      | .unit _ => .many
      | .many => .many

theorem evalHA_rep {a : Array UInt8} {α : Assign} (h : Rep a α) : ∀ (H : List Int), evalHA a H = evalH α H
  | [] => rfl
  | l :: ls => by
    unfold evalHA evalH
    rw [lstatA_rep h, evalHA_rep h ls]

def assignTrueA (a : Array UInt8) (l : Int) : Array UInt8 := setGrow a l.natAbs (encode (decide (l > 0)))

theorem rep_assignTrue {a : Array UInt8} {α : Assign} (h : Rep a α) (l : Int) :
    Rep (assignTrueA a l) (assignTrue α l) := by
  intro w
  unfold assignTrueA assignTrue
  rw [alookA_setGrow]
  by_cases hw : l.natAbs = w
  · subst hw; simp [alook]
  · have hb : (l.natAbs == w) = false := by simp [hw]
    rw [h w]
    simp [hw, alook, hb]

def rupA (get : Nat → Option (List Int)) : Array UInt8 → List Nat → Bool
  | _, [] => false
  | a, h :: hs =>
    match get h with
    | none => false
    | some H =>
      match evalHA a H with
      | .conflict => true
      | .unit l => rupA get (assignTrueA a l) hs
      | _ => false

theorem rupA_rep (get : Nat → Option (List Int)) : ∀ (hs : List Nat) (a : Array UInt8) (α : Assign), Rep a α →
    rupA get a hs = rup get α hs
  | [], _, _, _ => rfl
  | h :: hs, a, α, hr => by
    unfold rupA rup
    cases get h with
    | none => rfl
    | some H =>
      simp only
      rw [evalHA_rep hr]
      cases evalH α H with
      | conflict => rfl
      | unit l => exact rupA_rep get hs _ _ (rep_assignTrue hr l)
      | sat => rfl
      | many => rfl

def rupFast (get : Nat → Option (List Int)) (α : Assign) (hs : List Nat) : Bool := rupA get (toArr α) hs

@[csimp] theorem rup_eq_rupFast : @rup = @rupFast := by
  funext get α hs
  exact (rupA_rep get hs (toArr α) α (rep_toArr α)).symm

end MonsterVerified
