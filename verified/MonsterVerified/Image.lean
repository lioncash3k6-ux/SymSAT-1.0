import MonsterVerified.Gen

namespace MonsterVerified

/-- the permutation as a function -/
def sig (σ : Array Nat) (x : Nat) : Nat := σ.toList.getD x 0

/-- the same function without building the list (the compiler uses it for `sig` through the proved `csimp` lemma:
`sig` is evaluated tens of millions of times by `checker --assemble`) -/
def sigImpl (σ : Array Nat) (x : Nat) : Nat := σ.getD x 0

@[csimp] theorem sig_eq_sigImpl : @sig = @sigImpl := by
  funext σ x
  simp [sig, sigImpl, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

theorem nodup_map_on {f : Nat → Nat} : ∀ {S : List Nat}, (∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) → S.Nodup →
    (S.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: as, hinj, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, nodup_map_on (fun x hx y hy he => hinj x (by simp [hx]) y (by simp [hy]) he) hnd.2⟩
    rintro ⟨b, hb, he⟩
    have := hinj b (by simp [hb]) a (by simp) he
    subst this
    exact hnd.1 hb

/-- run-time check: σ is a permutation of {0..n-1} -/
def permOK (σ : Array Nat) (n : Nat) : Bool :=
  σ.size == n && σ.toList.all (· < n) && decide σ.toList.Nodup

theorem permOK_spec {σ : Array Nat} {n : Nat} (h : permOK σ n = true) :
    (∀ x, x < n → sig σ x < n) ∧ (∀ x y, x < n → y < n → sig σ x = sig σ y → x = y) := by
  unfold permOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hsz, hall⟩, hnd⟩ := h
  have hlen : σ.toList.length = n := by simp [hsz]
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold sig
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hall _ (List.getElem_mem _)
  · intro x y hx hy he
    unfold sig at he
    exact (List.Nodup.getD_inj (by omega) (by omega) hnd).mp he

/-- image of a literal: variable {a,b} ↦ variable {σa, σb}; sign kept, or reversed when `f` (colour swap);
everything checked against the table -/
def imgLit (E : Edges) (σ : Array Nat) (f : Bool) (l : Int) : Option Int :=
  if l = 0 then none else
  match E[l.natAbs]? with
  | some (a, b) =>
    match edgeVar E (sig σ a) (sig σ b) with
    | some v => if a < b then some (if (decide (l > 0)) ^^ f then (v : Int) else -(v : Int)) else none
    | none => none
  | none => none

def imgClause (E : Edges) (σ : Array Nat) (f : Bool) (C : List Int) : Option (List Int) := omap (imgLit E σ f) C

/-- the relabelled (and, if `f`, complemented) colouring -/
def relabel (σ : Array Nat) (f : Bool) (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun x y => col c (sig σ x) (sig σ y) ^^ f

theorem litVal_imgLit {E : Edges} {σ : Array Nat} {f : Bool} {l l' : Int} (c : Nat → Nat → Bool)
    (h : imgLit E σ f l = some l') : litVal E (relabel σ f c) l = litVal E c l' := by
  unfold imgLit at h
  by_cases h0 : l = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  cases hE : E[l.natAbs]? with
  | none => rw [hE] at h; simp at h
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [hE] at h
    simp only at h
    cases hv : edgeVar E (sig σ a) (sig σ b) with
    | none => rw [hv] at h; simp at h
    | some v =>
      rw [hv] at h
      simp only at h
      by_cases hab : a < b
      · simp only [hab, if_true, Option.some.injEq] at h
        subst h
        have hvv := varVal_edgeVar c hv
        have hpos := (edgeVar_spec hv).2.2
        have hv0 : v ≠ 0 := by omega
        have hrel : varVal E (relabel σ f c) l.natAbs = (col c (sig σ a) (sig σ b) ^^ f) := by
          unfold varVal; rw [hE]; simp [col, hab, relabel]
        have hneg : ¬ (0 : Int) < -(v : Int) := by omega
        unfold litVal
        by_cases hp : l > 0 <;> cases f <;> simp [hp, hrel, hvv, hv0, hneg]
      · simp [hab] at h

/-- relabelling a good colouring by a permutation (and complementing it when `f`, allowed only if s = t)
gives a good colouring -/
theorem good_relabel {s t n : Nat} {σ : Array Nat} {f : Bool} {c : Nat → Nat → Bool} (hp : permOK σ n = true)
    (hf : f = true → s = t) (hc : Good s t n c) : Good s t n (relabel σ f c) := by
  obtain ⟨hmap, hinj⟩ := permOK_spec hp
  have kset_map : ∀ k S, IsKSet n k S → IsKSet n k (S.map (sig σ)) := by
    intro k S ⟨hnd, hlt, hlen⟩
    refine ⟨?_, ?_, by simp [hlen]⟩
    · exact nodup_map_on (fun x hx y hy he => hinj x y (hlt x hx) (hlt y hy) he) hnd
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hmap x (hlt x hx)
  have transfer : ∀ k S (want : Bool), IsKSet n k S →
      (∃ a' ∈ S.map (sig σ), ∃ b' ∈ S.map (sig σ), a' ≠ b' ∧ col c a' b' = (want ^^ f)) →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ col (relabel σ f c) a b = want := by
    intro k S want _ ⟨a', ha', b', hb', hne, hcol⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    have hab : a ≠ b := by intro e; subst e; exact hne rfl
    refine ⟨a, ha, b, hb, hab, ?_⟩
    have hsym : col c (sig σ a) (sig σ b) = (want ^^ f) := hcol
    unfold col relabel
    by_cases h : a < b
    · simp only [h, if_true]; rw [hsym]; cases want <;> cases f <;> rfl
    · simp only [h, if_false]; rw [col_comm c _ _ (Ne.symm hne), hsym]; cases want <;> cases f <;> rfl
  cases f with
  | false =>
    exact ⟨fun S hS => transfer s S false hS (by simpa using hc.1 _ (kset_map s S hS)),
           fun S hS => transfer t S true hS (by simpa using hc.2 _ (kset_map t S hS))⟩
  | true =>
    have hst := hf rfl
    subst hst
    exact ⟨fun S hS => transfer s S false hS (by simpa using hc.2 _ (kset_map s S hS)),
           fun S hS => transfer s S true hS (by simpa using hc.1 _ (kset_map s S hS))⟩

/-- THE SYMMETRY RULE (S_n, and S_n × Z_2 when s = t): the image of a sound clause is sound -/
theorem image_sound {s t n : Nat} {E : Edges} {σ : Array Nat} {f : Bool} {C C' : List Int}
    (hp : permOK σ n = true) (hf : f = true → s = t) (hC : Sound s t n E C) (hi : imgClause E σ f C = some C') :
    Sound s t n E C' := by
  intro c hc
  obtain ⟨l, hl, hlv⟩ := hC (relabel σ f c) (good_relabel hp hf hc)
  obtain ⟨l', hl', hfl⟩ := omap_mem hi hl
  exact ⟨l', hl', by rw [← litVal_imgLit c hfl]; exact hlv⟩

end MonsterVerified
