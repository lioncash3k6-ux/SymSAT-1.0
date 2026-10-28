import MonsterVerified.Parse

namespace MonsterVerified

/-- Lemma mode: run every step and return the LAST clause of the main database. Unlike `check`, no empty clause is
required: the result is a clause that every good colouring of K_n satisfies (`checkLemma_sound`). Used for the
gluing route's per-unit refutations (`monster unit-lean`), whose final clause says "some fixed edge of this unit has
the other colour", i.e. no good colouring of K_n extends the unit. -/
def checkLemma (s t n : Nat) (steps : List Step) : Option (List Int) :=
  match originals s t n (edgeTable n) with
  | none => none
  | some Cs =>
    match runSteps s t n (edgeTable n) ⟨pushAll #[none] Cs, false, #[], #[], []⟩ steps with
    | some st => if decide ((st.db.size - 1) ∈ st.srList) then none else getC st.db (st.db.size - 1)
    | none => none

/-- If lemma mode returns `C`, every good colouring of K_n satisfies `C` (same invariant as `check_sound`; an
SR-tier last clause is not reported, it is only satisfiability-preserving). -/
theorem checkLemma_sound {s t n : Nat} {steps : List Step} {C : List Int} (h : checkLemma s t n steps = some C) :
    ∀ c, Good s t n c → ClauseSat (edgeTable n) c C := by
  unfold checkLemma at h
  cases ho : originals s t n (edgeTable n) with
  | none => rw [ho] at h; simp at h
  | some Cs =>
    rw [ho] at h
    simp only at h
    cases hr : runSteps s t n (edgeTable n) ⟨pushAll #[none] Cs, false, #[], #[], []⟩ steps with
    | none => rw [hr] at h; simp at h
    | some st =>
      rw [hr] at h
      simp only at h
      split at h
      · simp at h
      · rename_i hp
        exact (runSteps_ok (init_ok ho) hr).1 _ C h (by simpa using hp)

/-- text front end of lemma mode: (s, t, n, final clause) -/
def checkLemmaText (text : String) : Option (Nat × Nat × Nat × List Int) :=
  match parseSLRAT text with
  | some (s, t, n, steps) => (checkLemma s t n steps).map (fun C => (s, t, n, C))
  | none => none

theorem checkLemmaText_sound {text : String} {s t n : Nat} {C : List Int}
    (h : checkLemmaText text = some (s, t, n, C)) : ∀ c, Good s t n c → ClauseSat (edgeTable n) c C := by
  unfold checkLemmaText at h
  cases hq : parseSLRAT text with
  | none => rw [hq] at h; simp at h
  | some x =>
    obtain ⟨s', t', n', steps⟩ := x
    rw [hq] at h
    simp only at h
    cases hc : checkLemma s' t' n' steps with
    | none => rw [hc] at h; simp at h
    | some D =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact checkLemma_sound hc

end MonsterVerified
