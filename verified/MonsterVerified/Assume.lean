import MonsterVerified.Rup

/-!
# The assumption rule

An assumption sub-database works "under" a list `A` of literals (for the gluing route: the fixed edges of one unit,
each literal asserting an edge colour). Its originals are the clauses of F(s,t,n) with the literals negated by `A`
removed (`reduceUnder`), LRAT steps run inside it unchanged, and it is closed by adding `¬A ∨ C` to the main
database for a clause `C` derived in it (`closeClause`). Soundness: a good colouring that satisfies every literal
of `A` satisfies every clause of the sub-database (`SoundUnder`), hence `C`; one that falsifies some literal of `A`
satisfies `¬A`. No symmetry step is allowed inside (the assumption is not symmetric), only RUP.
-/

namespace MonsterVerified

/-- `c` satisfies every literal of the assumption `A` -/
def Holds (E : Edges) (c : Nat → Nat → Bool) (A : List Int) : Prop := ∀ l ∈ A, litVal E c l = true

/-- a clause holds in every good colouring that satisfies the assumption -/
def SoundUnder (s t n : Nat) (E : Edges) (A C : List Int) : Prop :=
  ∀ c, Good s t n c → Holds E c A → ClauseSat E c C

theorem soundUnder_of_sound {s t n : Nat} {E : Edges} {A C : List Int} (h : Sound s t n E C) :
    SoundUnder s t n E A C :=
  fun c hc _ => h c hc

theorem litVal_neg {E : Edges} {c : Nat → Nat → Bool} {l : Int} (h : l ≠ 0) :
    litVal E c (-l) = !litVal E c l := by
  unfold litVal
  by_cases hp : l > 0
  · simp [hp, Int.natAbs_neg] <;> omega
  · simp [hp, Int.natAbs_neg] <;> omega

/-- the originals reduced under `A`: literals whose negation is assumed are removed -/
def reduceUnder (A C : List Int) : List Int := C.filter (fun l => !decide (-l ∈ A))

theorem reduceUnder_sound {s t n : Nat} {E : Edges} {A C : List Int} (hA : ∀ l ∈ A, l ≠ 0)
    (h : SoundUnder s t n E A C) : SoundUnder s t n E A (reduceUnder A C) := by
  intro c hc hH
  obtain ⟨l, hl, hv⟩ := h c hc hH
  refine ⟨l, ?_, hv⟩
  unfold reduceUnder
  rw [List.mem_filter]
  refine ⟨hl, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  intro hm
  have hne : -l ≠ 0 := hA _ hm
  have h1 := hH _ hm
  rw [litVal_neg (by omega)] at h1
  rw [hv] at h1
  simp at h1

/-- An LRAT step inside the assumption sub-database is sound under the assumption when its hints are. -/
theorem rup_step_sound_under {s t n : Nat} {E : Edges} {A : List Int} {get : Nat → Option (List Int)}
    {C : List Int} {hs : List Nat} (hget : ∀ h H, get h = some H → SoundUnder s t n E A H)
    (hr : rup get (negAssign C) hs = true) : SoundUnder s t n E A C := by
  intro c hc hH
  by_cases hsat : ClauseSat E c C
  · exact hsat
  · exfalso
    have hf : ∀ l ∈ C, litVal E c l = false := by
      intro l hl
      cases h : litVal E c l with
      | false => rfl
      | true => exact absurd ⟨l, hl, h⟩ hsat
    exact rup_sound (fun h H hg => hget h H hg c hc hH) (negAssign C) hs (agrees_negAssign hf) hr

/-- the closing clause `¬A ∨ C` -/
def closeClause (A C : List Int) : List Int := A.map (fun l => -l) ++ C

/-- THE ASSUMPTION RULE: a clause sound under `A` closes to the main clause `¬A ∨ C`. -/
theorem close_sound {s t n : Nat} {E : Edges} {A C : List Int} (hA : ∀ l ∈ A, l ≠ 0)
    (h : SoundUnder s t n E A C) : Sound s t n E (closeClause A C) := by
  intro c hc
  by_cases hall : Holds E c A
  · obtain ⟨l, hl, hv⟩ := h c hc hall
    exact ⟨l, List.mem_append_right _ hl, hv⟩
  · unfold Holds at hall
    obtain ⟨l, hne⟩ := Classical.not_forall.mp hall
    have hl : l ∈ A := Classical.byContradiction fun h => hne (fun h' => absurd h' h)
    have hv : litVal E c l ≠ true := fun e => hne (fun _ => e)
    refine ⟨-l, List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩), ?_⟩
    rw [litVal_neg (hA l hl)]
    cases hx : litVal E c l with
    | true => exact absurd hx hv
    | false => rfl

end MonsterVerified
