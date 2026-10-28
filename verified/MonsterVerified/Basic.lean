/-!
# Ramsey semantics

A 2-colouring of the edges of K_n is any function `c : Nat → Nat → Bool`, read on unordered pairs through `col`
(`true` = red). `Good s t n c` says: no red K_s and no blue K_t among the vertices `0..n-1`.
`∀ c, ¬ Good s t n c` is exactly the statement `R(s,t) ≤ n`.
-/

namespace MonsterVerified

/-- colour of the unordered edge {a,b} -/
def col (c : Nat → Nat → Bool) (a b : Nat) : Bool := if a < b then c a b else c b a

theorem col_comm (c : Nat → Nat → Bool) (a b : Nat) (h : a ≠ b) : col c a b = col c b a := by
  unfold col
  by_cases h1 : a < b
  · have : ¬ b < a := by omega
    simp [h1, this]
  · have : b < a := by omega
    simp [h1, this]

/-- a set of `k` distinct vertices below `n`, given as a duplicate-free list -/
def IsKSet (n k : Nat) (S : List Nat) : Prop :=
  S.Nodup ∧ (∀ x ∈ S, x < n) ∧ S.length = k

/-- no red K_s and no blue K_t -/
def Good (s t n : Nat) (c : Nat → Nat → Bool) : Prop :=
  (∀ S, IsKSet n s S → ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ col c a b = false) ∧
  (∀ S, IsKSet n t S → ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ col c a b = true)

/-- The edge table: `E[v] = (a, b)` with `a < b` names CNF variable `v`. Soundness never assumes anything about how
`E` was built: every use of it is checked at run time. -/
abbrev Edges := Array (Nat × Nat)

def varVal (E : Edges) (c : Nat → Nat → Bool) (v : Nat) : Bool :=
  match E[v]? with
  | some (a, b) => col c a b
  | none => false

def litVal (E : Edges) (c : Nat → Nat → Bool) (l : Int) : Bool :=
  if l > 0 then varVal E c l.natAbs else !varVal E c l.natAbs

def ClauseSat (E : Edges) (c : Nat → Nat → Bool) (C : List Int) : Prop :=
  ∃ l ∈ C, litVal E c l = true

/-- A clause is sound if every good colouring satisfies it. -/
def Sound (s t n : Nat) (E : Edges) (C : List Int) : Prop :=
  ∀ c, Good s t n c → ClauseSat E c C

/-- The empty clause is sound only if there is no good colouring at all. -/
theorem no_good_of_sound_empty {s t n : Nat} {E : Edges} (h : Sound s t n E []) :
    ∀ c, ¬ Good s t n c := by
  intro c hc
  obtain ⟨l, hl, _⟩ := h c hc
  simp at hl

end MonsterVerified
