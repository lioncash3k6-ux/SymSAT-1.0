import MonsterVerified.Basic

/-!
# Parity (assembly part 5a)

`redDegree c n v` is the number of red neighbours of `v` in K_n. The handshake lemma says that the sum of the red
degrees is even (it is twice the number of red edges), so when `n` is odd some vertex has even red degree. This is
the lemma that lets the R(4,5) ≤ 25 assembly restrict the degree of the chosen vertex to {8, 10, 12}.
-/

namespace MonsterVerified

/-- `Σ_{u < n} f u` -/
def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

theorem sumRange_add (f g : Nat → Nat) : ∀ n, sumRange (fun u => f u + g u) n = sumRange f n + sumRange g n
  | 0 => rfl
  | n + 1 => by simp only [sumRange, sumRange_add f g n]; omega

theorem sumRange_congr {f g : Nat → Nat} : ∀ n, (∀ u, u < n → f u = g u) → sumRange f n = sumRange g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumRange]
    rw [sumRange_congr n (fun u hu => h u (by omega)), h n (by omega)]

/-- the red neighbours of `v` among `0..n-1`, in increasing order -/
def redNbrs (c : Nat → Nat → Bool) (n v : Nat) : List Nat :=
  (List.range n).filter (fun u => u != v && col c v u)

/-- the blue neighbours of `v` among `0..n-1`, in increasing order -/
def blueNbrs (c : Nat → Nat → Bool) (n v : Nat) : List Nat :=
  (List.range n).filter (fun u => u != v && !col c v u)

/-- red degree of `v` in K_n: the number of `u < n`, `u ≠ v`, with `col c v u = true` -/
def redDegree (c : Nat → Nat → Bool) (n v : Nat) : Nat := (redNbrs c n v).length

theorem length_filter_range (p : Nat → Bool) : ∀ n,
    ((List.range n).filter p).length = sumRange (fun u => if p u = true then 1 else 0) n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range p n]
    simp only [sumRange, List.filter_cons, List.filter_nil]
    by_cases h : p n = true <;> simp [h]

theorem redDegree_eq_sum (c : Nat → Nat → Bool) (n v : Nat) :
    redDegree c n v = sumRange (fun u => if (u != v && col c v u) = true then 1 else 0) n :=
  length_filter_range _ n

/-- the double sum of a symmetric function that vanishes on the diagonal is even -/
theorem double_sum_even (g : Nat → Nat → Nat) (hsym : ∀ u v, g u v = g v u) (hdiag : ∀ u, g u u = 0) :
    ∀ m, sumRange (fun v => sumRange (fun u => g u v) m) m % 2 = 0
  | 0 => rfl
  | m + 1 => by
    have ih := double_sum_even g hsym hdiag m
    have h1 : sumRange (fun v => sumRange (fun u => g u v) (m + 1)) m
        = sumRange (fun v => sumRange (fun u => g u v) m) m + sumRange (fun v => g m v) m :=
      sumRange_add (fun v => sumRange (fun u => g u v) m) (fun v => g m v) m
    have h2 : sumRange (fun v => g m v) m = sumRange (fun u => g u m) m :=
      sumRange_congr m (fun u _ => hsym m u)
    show (sumRange (fun v => sumRange (fun u => g u v) (m + 1)) m + sumRange (fun u => g u m) (m + 1)) % 2 = 0
    rw [h1, h2]
    show (_ + (sumRange (fun u => g u m) m + g m m)) % 2 = 0
    rw [hdiag]
    omega

/-- handshake: the sum of the red degrees is even -/
theorem sum_redDegree_even (c : Nat → Nat → Bool) (n : Nat) :
    sumRange (fun v => redDegree c n v) n % 2 = 0 := by
  have hs := double_sum_even (fun u v => if (u != v && col c v u) = true then 1 else 0) ?_ ?_ n
  · rw [sumRange_congr n (fun v _ => redDegree_eq_sum c n v)]; exact hs
  · intro u v
    by_cases h : u = v
    · subst h; rfl
    · simp [h, Ne.symm h, col_comm c v u (Ne.symm h)]
  · intro u; simp

theorem sumRange_odd {d : Nat → Nat} : ∀ m, (∀ v, v < m → d v % 2 = 1) → sumRange d m % 2 = m % 2
  | 0, _ => rfl
  | m + 1, h => by
    simp only [sumRange]
    have := sumRange_odd m (fun v hv => h v (by omega))
    have := h m (by omega)
    omega

/-- in K_n with n odd, some vertex has even red degree -/
theorem exists_even_red_degree_odd (c : Nat → Nat → Bool) (n : Nat) (hn : n % 2 = 1) :
    ∃ v < n, redDegree c n v % 2 = 0 := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ v, v < n → redDegree c n v % 2 = 1 := by
    intro v hv
    have : ¬ redDegree c n v % 2 = 0 := fun h => hno ⟨v, hv, h⟩
    omega
  have h1 : sumRange (fun v => redDegree c n v) n % 2 = n % 2 := sumRange_odd n hall
  have h2 := sum_redDegree_even c n
  omega

/-- assembly part 5a: some vertex of K_25 has even red degree -/
theorem exists_even_red_degree (c : Nat → Nat → Bool) : ∃ v < 25, redDegree c 25 v % 2 = 0 :=
  exists_even_red_degree_odd c 25 rfl

end MonsterVerified
