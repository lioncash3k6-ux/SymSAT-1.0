import MonsterVerified.Parse

/-!
# Streaming checking: a state that carries its own invariant

`OKSt` pairs a checker state with the proof that it satisfies `StOK`. Its only constructors are `initOK` (the
originals of F(s,t,n)) and `stepOK` (one `stepFn` step, soundness by `stepFn_ok`). An executable that reads a
proof line by line and threads an `OKSt` through `stepOK` therefore never holds the proof text, only the live
databases, and whatever it reports from the final state is sound by `OKSt.clause_sound` / `OKSt.done_sound`,
whatever its IO loop does. The proof fields are erased at run time.
-/

namespace MonsterVerified

structure OKSt (s t n : Nat) where
  st : St
  /-- the edge table, built once (`stepOK` used to rebuild `edgeTable n` on every step; measured 2026-10-28) -/
  E : Edges
  hE : E = edgeTable n
  ok : StOK s t n (edgeTable n) st

def initOK (s t n : Nat) : Option (OKSt s t n) :=
  match ho : originals s t n (edgeTable n) with
  | some Cs => some ⟨⟨pushAll #[none] Cs, false, #[], #[], []⟩, edgeTable n, rfl, init_ok ho⟩
  | none => none

def stepOK {s t n : Nat} (x : OKSt s t n) (step : Step) : Option (OKSt s t n) :=
  match h : stepFn s t n x.E x.st step with
  | some st' => some ⟨st', x.E, x.hE, stepFn_ok x.ok (by rw [x.hE] at h; exact h)⟩
  | none => none

/-- every pure clause of the main database of a reachable state holds in every good colouring -/
theorem OKSt.clause_sound {s t n : Nat} (x : OKSt s t n) {i : Nat} {C : List Int}
    (h : getC x.st.db i = some C) (hp : i ∉ x.st.srList) : ∀ c, Good s t n c → ClauseSat (edgeTable n) c C :=
  x.ok.1 i C h hp

/-- if the empty clause was derived, there is no good colouring: R(s,t) ≤ n -/
theorem OKSt.done_sound {s t n : Nat} (x : OKSt s t n) (h : x.st.done = true) : ∀ c, ¬ Good s t n c :=
  no_good_of_sound_empty (x.ok.2.1 h)

/-- the last clause of the main database (what a lemma-mode proof establishes) -/
def OKSt.last {s t n : Nat} (x : OKSt s t n) : Option (List Int) :=
  if decide ((x.st.db.size - 1) ∈ x.st.srList) then none else getC x.st.db (x.st.db.size - 1)

theorem OKSt.last_sound {s t n : Nat} (x : OKSt s t n) {C : List Int} (h : x.last = some C) :
    ∀ c, Good s t n c → ClauseSat (edgeTable n) c C := by
  unfold OKSt.last at h
  split at h
  · simp at h
  · rename_i hp
    exact x.clause_sound h (by simpa using hp)

end MonsterVerified

namespace MonsterVerified

/-- a clause together with the proof that every good colouring of K_n satisfies it: what batch lemma mode
(`checker --lemmas LIST`) accumulates; the only way to build one is `OKSt.verified`, i.e. a streamed check -/
structure Verified (s t n : Nat) where
  clause : List Int
  sound : ∀ c, Good s t n c → ClauseSat (edgeTable n) c clause

/-- the result of a streamed check: `some v` iff every line checked and the last main clause is pure -/
def OKSt.verified {s t n : Nat} (x : OKSt s t n) : Option (Verified s t n) :=
  match h : x.last with
  | some C => some ⟨C, x.last_sound h⟩
  | none => none

/-- DRIVER THEOREM of batch lemma mode: every clause the batch reports holds in every good colouring of K_n -/
theorem batch_sound {s t n : Nat} (L : List (Verified s t n)) :
    ∀ v ∈ L, ∀ c, Good s t n c → ClauseSat (edgeTable n) c v.clause :=
  fun v _ => v.sound

end MonsterVerified
