import MonsterVerified.Parse

/-!
# Ramsey upper bounds, machine-checked from monster's pattern-CDCL proofs

Each theorem is obtained by running the verified checker (`check_sound`) on a proof produced by monster
(`monster full --s S --t T --n N --patterns --lemmas --slrat FILE`). `native_decide` evaluates the checker with the
compiled code, so these theorems additionally trust the Lean compiler (axiom `Lean.ofReduceBool`).
-/

namespace MonsterVerified

theorem checkText_sound {text : String} {s t n : Nat}
    (hp : (parseSLRAT text).map (fun x => (x.1, x.2.1, x.2.2.1)) = some (s, t, n)) (h : checkText text = true) :
    ∀ c, ¬ Good s t n c := by
  unfold checkText at h
  cases hq : parseSLRAT text with
  | none => rw [hq] at hp; simp at hp
  | some x =>
    obtain ⟨s', t', n', steps⟩ := x
    rw [hq] at hp h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp h
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact check_sound h

theorem R33_le_6 : ∀ c, ¬ Good 3 3 6 c :=
  checkText_sound (text := include_str "../proofs/R33_K6.slrat") (by native_decide) (by native_decide)

theorem R34_le_9 : ∀ c, ¬ Good 3 4 9 c :=
  checkText_sound (text := include_str "../proofs/R34_K9.slrat") (by native_decide) (by native_decide)

theorem R35_le_14 : ∀ c, ¬ Good 3 5 14 c :=
  checkText_sound (text := include_str "../proofs/R35_K14.slrat") (by native_decide) (by native_decide)

theorem R44_le_18 : ∀ c, ¬ Good 4 4 18 c :=
  checkText_sound (text := include_str "../proofs/R44_K18.slrat") (by native_decide) (by native_decide)

end MonsterVerified
