import MonsterVerified.Image

/-!
# Local symmetry as "lift from a sub-instance"

Inside the blue neighbourhood of an apex `v`, an R(s, t+1) colouring restricts to an R(s, t) colouring.
A lemma proved in the sub-instance's own database (where the global rules, including colour swap when s = t,
are already sound) can be lifted into the parent formula under the context "v is blue to every vertex of the
embedded K_m". Colour swap is NOT applied to parent clauses: it is only sound for clauses derived in the
symmetric sub-instance, so provenance is enforced by having two databases.
-/

namespace MonsterVerified

/-- run-time check: τ embeds {0..m-1} (m = τ.size) injectively into {0..n-1} and avoids the apex v -/
def embOK (τ : Array Nat) (n v : Nat) : Bool :=
  τ.toList.all (fun x => x < n && x != v) && decide τ.toList.Nodup

theorem embOK_spec {τ : Array Nat} {n v : Nat} (h : embOK τ n v = true) :
    (∀ x, x < τ.size → sig τ x < n ∧ sig τ x ≠ v) ∧
    (∀ x y, x < τ.size → y < τ.size → sig τ x = sig τ y → x = y) := by
  unfold embOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  obtain ⟨hall, hnd⟩ := h
  have hlen : τ.toList.length = τ.size := by simp
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold sig
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    have h1 := hall _ (List.getElem_mem (by omega : x < τ.toList.length))
    simpa using h1
  · intro x y hx hy he
    unfold sig at he
    exact (List.Nodup.getD_inj (by omega) (by omega) hnd).mp he

/-- restriction to a monochromatic apex neighbourhood:
blue apex: Good s (t+1) n c → Good s t m (c ∘ τ);  red apex: Good (s+1) t n c → Good s t m (c ∘ τ) -/
theorem good_restrict {s t n v : Nat} {τ : Array Nat} {c : Nat → Nat → Bool} (red : Bool)
    (he : embOK τ n v = true) (hv : v < n)
    (hapex : ∀ x, x < τ.size → col c v (sig τ x) = red)
    (hc : Good (if red then s + 1 else s) (if red then t else t + 1) n c) :
    Good s t τ.size (relabel τ false c) := by
  obtain ⟨hmap, hinj⟩ := embOK_spec he
  have kset_map : ∀ k S, IsKSet τ.size k S → IsKSet n k (S.map (sig τ)) := by
    intro k S ⟨hnd, hlt, hlen⟩
    refine ⟨nodup_map_on (fun x hx y hy e => hinj x y (hlt x hx) (hlt y hy) e) hnd, ?_, by simp [hlen]⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (hmap x (hlt x hx)).1
  -- adding the apex to an embedded clique
  have kset_apex : ∀ k S, IsKSet τ.size k S → IsKSet n (k + 1) (v :: S.map (sig τ)) := by
    intro k S hS
    obtain ⟨hnd, hlt, hlen⟩ := kset_map k S hS
    refine ⟨List.nodup_cons.mpr ⟨?_, hnd⟩, ?_, by simp [hlen]⟩
    · intro hm
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
      exact (hmap x (hS.2.1 x hx)).2 hxe
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hv
      · exact hlt y hy
  -- an edge of colour `want` inside the image pulls back
  have pull : ∀ k S (want : Bool), IsKSet τ.size k S →
      (∃ a ∈ v :: S.map (sig τ), ∃ b ∈ v :: S.map (sig τ), a ≠ b ∧ col c a b = want) → want ≠ red →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ col (relabel τ false c) a b = want := by
    intro k S want hS ⟨a', ha', b', hb', hne, hcol⟩ hwr
    have notapex : ∀ x ∈ S, col c v (sig τ x) ≠ want := by
      intro x hx e; exact hwr (e ▸ hapex x (hS.2.1 x hx))
    rcases List.mem_cons.mp ha' with ha2 | ha2
    · subst ha2
      rcases List.mem_cons.mp hb' with hb2 | hb2
      · exact absurd hb2.symm hne
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb2
        exact absurd hcol (notapex y hy)
    rcases List.mem_cons.mp hb' with hb2 | hb2
    · subst hb2
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha2
      exact absurd (by rw [col_comm c _ _ (Ne.symm hne)]; exact hcol) (notapex x hx)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha2
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb2
    have hab : a ≠ b := by intro e; subst e; exact hne rfl
    refine ⟨a, ha, b, hb, hab, ?_⟩
    unfold col relabel
    by_cases h : a < b
    · simp only [h, ite_true, Bool.xor_false]; exact hcol
    · simp only [h, ite_false, Bool.xor_false]; rw [col_comm c _ _ (Ne.symm hne)]; exact hcol
  -- an edge found inside the image alone pulls back directly
  have pull0 : ∀ k S (want : Bool), IsKSet τ.size k S →
      (∃ a ∈ S.map (sig τ), ∃ b ∈ S.map (sig τ), a ≠ b ∧ col c a b = want) →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ col (relabel τ false c) a b = want := by
    intro k S want _ ⟨a', ha', b', hb', hne, hcol⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    have hab : a ≠ b := by intro e; subst e; exact hne rfl
    refine ⟨a, ha, b, hb, hab, ?_⟩
    unfold col relabel
    by_cases h : a < b
    · simp only [h, ite_true, Bool.xor_false]; exact hcol
    · simp only [h, ite_false, Bool.xor_false]; rw [col_comm c _ _ (Ne.symm hne)]; exact hcol
  cases red with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hc
    exact ⟨fun S hS => pull0 s S false hS (hc.1 _ (kset_map s S hS)),
           fun S hS => pull t S true hS (hc.2 _ (kset_apex t S hS)) (by decide)⟩
  | true =>
    simp only [ite_true] at hc
    exact ⟨fun S hS => pull s S false hS (hc.1 _ (kset_apex s S hS)) (by decide),
           fun S hS => pull0 t S true hS (hc.2 _ (kset_map t S hS))⟩

/-- the lifted clause: τ(C) ∨ (some apex edge v–τx is not of colour `red`), over all x < m -/
def liftClause (E : Edges) (τ : Array Nat) (v : Nat) (red : Bool) (C : List Int) : Option (List Int) :=
  match imgClause E τ false C, omap (fun x => pairLit E red (v, sig τ x)) (List.range τ.size) with
  | some A, some B => some (A ++ B)
  | _, _ => none

/-- THE LOCAL-SYMMETRY (LIFT) RULE: a clause sound for the sub-instance on K_m lifts to the parent instance.
For R(4,5) with a blue apex the sub-instance is R(4,4), where colour swap is a global symmetry. -/
theorem lift_sound {s t n v : Nat} {E : Edges} {τ : Array Nat} {red : Bool} {C C' : List Int}
    (he : embOK τ n v = true) (hv : v < n)
    (hC : Sound s t τ.size E C) (hl : liftClause E τ v red C = some C') :
    Sound (if red then s + 1 else s) (if red then t else t + 1) n E C' := by
  intro c hc
  unfold liftClause at hl
  split at hl
  · rename_i A B hA hB
    simp only [Option.some.injEq] at hl
    subst hl
    by_cases hall : ∀ x, x < τ.size → col c v (sig τ x) = red
    · obtain ⟨l, hl, hlv⟩ := hC _ (good_restrict red he hv hall hc)
      obtain ⟨l', hl', hfl⟩ := omap_mem hA hl
      exact ⟨l', List.mem_append_left _ hl', by rw [← litVal_imgLit c hfl]; exact hlv⟩
    · obtain ⟨x, hne⟩ := Classical.not_forall.mp hall
      have hx' : x < τ.size := Classical.byContradiction fun h => hne (fun h' => absurd h' h)
      have hcx : col c v (sig τ x) ≠ red := fun e => hne (fun _ => e)
      obtain ⟨l, hl, hpl⟩ := omap_mem hB (List.mem_range.mpr hx')
      refine ⟨l, List.mem_append_right _ hl, ?_⟩
      unfold pairLit at hpl
      cases hev : edgeVar E v (sig τ x) with
      | none => rw [hev] at hpl; simp at hpl
      | some w =>
        rw [hev] at hpl
        simp only [Option.some.injEq] at hpl
        subst hpl
        have hvv := varVal_edgeVar c hev
        have hw := (edgeVar_spec hev).2.2
        unfold litVal
        cases red <;> simp_all <;> omega
  · simp at hl

end MonsterVerified
