import MonsterVerified.Rup
import MonsterVerified.Lift
import MonsterVerified.Assume
import MonsterVerified.SR

namespace MonsterVerified

/-- one proof step (SLRAT) -/
inductive Step where
  | add (id : Nat) (lits : List Int) (hints : List Nat)
  | img (id : Nat) (src : Nat) (perm : Array Nat) (flip : Bool)
  /-- open sub-instance number `subs.size`: its own database, starting from the original clauses of F(s,t,m) -/
  | openSub (s t m : Nat)
  /-- an `add` or `img` step inside sub-instance `k` (checked against (s,t,m) of that sub-instance) -/
  | sub (k : Nat) (x : Step)
  /-- main clause `id` := lift of clause `src` of sub-instance `k`, apex `v` of colour `red`, embedding `emb` -/
  | lift (id : Nat) (k : Nat) (src : Nat) (v : Nat) (red : Bool) (emb : Array Nat)
  /-- open assumption sub-database number `asms.size`: F(s,t,n) reduced under the literals `A` (Assume.lean) -/
  | openAsm (A : List Int)
  /-- an LRAT step inside assumption sub-database `k` (no symmetry steps there) -/
  | asm (k : Nat) (id : Nat) (lits : List Int) (hints : List Nat)
  /-- main clause `id` := `¬A ∨ C`, `C` = clause `src` of assumption sub-database `k` -/
  | close (id : Nat) (k : Nat) (src : Nat)
  /-- forget the clauses `ids` of assumption sub-database `k` (the slots become `none`; ids are never reused) -/
  | asmDel (k : Nat) (ids : List Nat)
  /-- substitution redundancy (SR.lean): main clause `id` := `lits`, only satisfiability-preserving (SR tier), under
  the substitution (witness, pairs) with the α hints and one hint group per clause whose image needs propagation -/
  | sr (id : Nat) (lits : List Int) (witness : List Int) (pairs : List (Int × Int)) (ahints : List Nat)
      (groups : List (Nat × List Nat))

/-- the clause database: index = clause id (index 0 unused) -/
abbrev DB := Array (Option (List Int))

def getC (db : DB) (i : Nat) : Option (List Int) := (db[i]?).join

/-- the same lookup without the intermediate `some (some C)` (`Array.getD`); the compiler uses it for `getC` through
the proved `csimp` equality (one allocation less per hint; measured 2026-10-28) -/
def getCFast (db : DB) (i : Nat) : Option (List Int) := db.getD i none

@[csimp] theorem getC_eq_getCFast : @getC = @getCFast := by
  funext db i
  unfold getC getCFast
  rw [Array.getD_eq_getD_getElem?]
  cases db[i]? <;> rfl

def DBSound (s t n : Nat) (E : Edges) (db : DB) : Prop := ∀ i C, getC db i = some C → Sound s t n E C

theorem push_sound {s t n : Nat} {E : Edges} {db : DB} {C : List Int} (hdb : DBSound s t n E db)
    (hC : Sound s t n E C) : DBSound s t n E (db.push (some C)) := by
  intro i D hD
  unfold getC at hD
  rw [Array.getElem?_push] at hD
  by_cases hi : i = db.size
  · simp [hi] at hD; subst hD; exact hC
  · simp [hi] at hD; exact hdb i D (by unfold getC; exact hD)

theorem getC_lt {db : DB} {i : Nat} {C : List Int} (h : getC db i = some C) : i < db.size := by
  refine Nat.lt_of_not_le fun hge => ?_
  unfold getC at h
  rw [Array.getElem?_eq_none_iff.mpr hge] at h
  simp at h

theorem getC_push_of {db : DB} {x : Option (List Int)} {i : Nat} {C : List Int} (h : getC db i = some C) :
    getC (db.push x) i = some C := by
  have hi := getC_lt h
  unfold getC at h ⊢
  rw [Array.getElem?_push]
  simp only [show i ≠ db.size by omega, ite_false]
  exact h

theorem getC_push_self {db : DB} {C : List Int} : getC (db.push (some C)) db.size = some C := by
  unfold getC
  simp [Array.getElem?_push]

/-- a clause of a pushed database is an old one or the new one -/
theorem getC_push_cases {db : DB} {C D : List Int} {i : Nat} (h : getC (db.push (some C)) i = some D) :
    getC db i = some D ∨ D = C := by
  unfold getC at h
  rw [Array.getElem?_push] at h
  by_cases hi : i = db.size
  · simp [hi] at h; exact Or.inr h.symm
  · simp [hi] at h; exact Or.inl (by unfold getC; exact h)

/-- edge table for K_n: E[v] = (i, j), v = j(j-1)/2 + i + 1, i < j < n (correctness is never assumed) -/
def edgeTable (n : Nat) : Edges := Id.run do
  let mut e : Edges := Array.replicate (n * (n - 1) / 2 + 1) (0, 0)
  for j in [1:n] do
    for i in [0:j] do
      e := e.set! (j * (j - 1) / 2 + i + 1) (i, j)
  return e

theorem omap_mem_rev {f : α → Option β} : ∀ {L : List α} {R : List β} {y : β}, omap f L = some R → y ∈ R →
    ∃ x ∈ L, f x = some y
  | [], R, y, h, hy => by simp [omap] at h; subst h; simp at hy
  | a :: as, R, y, h, hy => by
    unfold omap at h
    split at h
    · rename_i b bs hb hbs
      simp at h; subst h
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨a, by simp, hb⟩
      · obtain ⟨x, hx, hfx⟩ := omap_mem_rev hbs hy
        exact ⟨x, by simp [hx], hfx⟩
    · simp at h

/-- the original clauses, in monster's order: red K_s bans, then blue K_t bans -/
def originals (s t n : Nat) (E : Edges) : Option (List (List Int)) :=
  match omap (genClause E true) (subsets (List.range n) s), omap (genClause E false) (subsets (List.range n) t) with
  | some a, some b => some (a ++ b)
  | _, _ => none

theorem originals_sound {s t n : Nat} {E : Edges} {Cs : List (List Int)} (h : originals s t n E = some Cs) :
    ∀ C ∈ Cs, Sound s t n E C := by
  unfold originals at h
  split at h
  · rename_i a b ha hb
    simp at h; subst h
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨S, hS, hg⟩ := omap_mem_rev ha hC
      exact genClause_sound (red := true) (by simpa using subsets_range_kset hS) hg
    · obtain ⟨S, hS, hg⟩ := omap_mem_rev hb hC
      exact genClause_sound (red := false) (by simpa using subsets_range_kset hS) hg
  · simp at h

/-- every k-sublist of L is generated (converse of `subsets_spec`) -/
theorem subsets_mem : ∀ {L S : List Nat} {k : Nat}, S.Sublist L → S.length = k → S ∈ subsets L k
  | _, _, k, .slnil, hl => by subst hl; simp [subsets]
  | a :: l₂, S, k, .cons _ h, hl => by
    cases k with
    | zero =>
      have : S = [] := List.eq_nil_of_length_eq_zero hl
      subst this; simp [subsets]
    | succ k =>
      simp only [subsets, List.mem_append]
      exact Or.inr (subsets_mem h hl)
  | a :: l₂, _, k, .cons₂ _ h, hl => by
    cases k with
    | zero => simp at hl
    | succ k =>
      simp only [subsets, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, subsets_mem h (by simpa using hl), rfl⟩

/-- every k-set of vertices below n is generated, up to order -/
theorem subsets_complete {n k : Nat} {S : List Nat} (h : IsKSet n k S) :
    ∃ S' ∈ subsets (List.range n) k, S'.Nodup ∧ ∀ x, x ∈ S' ↔ x ∈ S := by
  obtain ⟨hnd, hlt, hlen⟩ := h
  have hsub : ((List.range n).filter (fun x => decide (x ∈ S))).Sublist (List.range n) := List.filter_sublist
  have hnd' : ((List.range n).filter (fun x => decide (x ∈ S))).Nodup := (List.nodup_range).sublist hsub
  have hmem : ∀ x, x ∈ (List.range n).filter (fun x => decide (x ∈ S)) ↔ x ∈ S := by
    intro x
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩
  have hperm := (List.perm_ext_iff_of_nodup hnd' hnd).mpr hmem
  exact ⟨_, subsets_mem hsub (by rw [hperm.length_eq, hlen]), hnd', hmem⟩

theorem pairs_spec : ∀ {S : List Nat} {a b : Nat}, S.Nodup → (a, b) ∈ pairs S → a ∈ S ∧ b ∈ S ∧ a ≠ b
  | [], _, _, _, h => by simp [pairs] at h
  | x :: xs, a, b, hnd, h => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    have hnd' := List.nodup_cons.mp hnd
    rcases h with ⟨y, hy, rfl, rfl⟩ | h
    · exact ⟨by simp, by simp [hy], fun e => hnd'.1 (e ▸ hy)⟩
    · obtain ⟨ha, hb, hne⟩ := pairs_spec hnd'.2 h
      exact ⟨by simp [ha], by simp [hb], hne⟩

/-- a colouring that satisfies every original clause is good (the originals are exactly the clique bans) -/
theorem good_of_originals {s t n : Nat} {E : Edges} {Cs : List (List Int)} {c : Nat → Nat → Bool}
    (ho : originals s t n E = some Cs) (hc : ∀ C ∈ Cs, ClauseSat E c C) : Good s t n c := by
  unfold originals at ho
  split at ho
  · rename_i a b ha hb
    simp only [Option.some.injEq] at ho
    subst ho
    have key : ∀ (red : Bool) (k : Nat) (L : List (List Int)),
        omap (genClause E red) (subsets (List.range n) k) = some L → (∀ C ∈ L, ClauseSat E c C) →
        ∀ S, IsKSet n k S → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ col c x y = !red := by
      intro red k L hL hsat S hS
      obtain ⟨S', hS', hnd', hmem⟩ := subsets_complete hS
      obtain ⟨C, hC, hg⟩ := omap_mem hL hS'
      obtain ⟨l, hl, hv⟩ := hsat C hC
      unfold genClause at hg
      obtain ⟨p, hp, hpl⟩ := omap_mem_rev hg hl
      obtain ⟨x, y⟩ := p
      rw [litVal_pairLit c hpl] at hv
      obtain ⟨hx, hy, hne⟩ := pairs_spec hnd' hp
      refine ⟨x, (hmem x).mp hx, y, (hmem y).mp hy, hne, ?_⟩
      cases red <;> simp_all
    refine ⟨?_, ?_⟩
    · intro S hS
      have := key true s a ha (fun C hC => hc C (List.mem_append_left _ hC)) S hS
      simpa using this
    · intro S hS
      have := key false t b hb (fun C hC => hc C (List.mem_append_right _ hC)) S hS
      simpa using this
  · simp at ho

def pushAll (db : DB) : List (List Int) → DB
  | [] => db
  | C :: Cs => pushAll (db.push (some C)) Cs

theorem pushAll_sound {s t n : Nat} {E : Edges} : ∀ {db : DB} {Cs : List (List Int)}, DBSound s t n E db →
    (∀ C ∈ Cs, Sound s t n E C) → DBSound s t n E (pushAll db Cs)
  | _, [], hdb, _ => hdb
  | _, C :: Cs, hdb, hCs => by
    unfold pushAll
    exact pushAll_sound (push_sound hdb (hCs C (by simp))) (fun D hD => hCs D (by simp [hD]))

theorem pushAll_getC_of : ∀ {db : DB} {Cs : List (List Int)} {i : Nat} {C : List Int},
    getC db i = some C → getC (pushAll db Cs) i = some C
  | _, [], _, _, h => h
  | _, C :: Cs, _, _, h => by
    unfold pushAll
    exact pushAll_getC_of (getC_push_of h)

/-- every pushed clause is in the database -/
theorem pushAll_contains : ∀ {db : DB} {Cs : List (List Int)}, ∀ C ∈ Cs, ∃ i, getC (pushAll db Cs) i = some C
  | _, [], _, h => by simp at h
  | db, D :: Cs, C, h => by
    unfold pushAll
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨db.size, pushAll_getC_of getC_push_self⟩
    · exact pushAll_contains C h

/-- a sub-instance: F(s,t,m) on the vertices 0..m-1, with its own clause database -/
structure Sub where
  s : Nat
  t : Nat
  m : Nat
  db : DB

/-- an assumption sub-database: F(s,t,n) reduced under `A`, and everything derived in it by RUP -/
structure Asm where
  A : List Int
  db : DB

def DBSoundUnder (s t n : Nat) (E : Edges) (A : List Int) (db : DB) : Prop :=
  ∀ i C, getC db i = some C → SoundUnder s t n E A C

theorem push_sound_under {s t n : Nat} {E : Edges} {A : List Int} {db : DB} {C : List Int}
    (hdb : DBSoundUnder s t n E A db) (hC : SoundUnder s t n E A C) : DBSoundUnder s t n E A (db.push (some C)) := by
  intro i D hD
  unfold getC at hD
  rw [Array.getElem?_push] at hD
  by_cases hi : i = db.size
  · simp [hi] at hD; subst hD; exact hC
  · simp [hi] at hD; exact hdb i D (by unfold getC; exact hD)

theorem pushAll_sound_under {s t n : Nat} {E : Edges} {A : List Int} : ∀ {db : DB} {Cs : List (List Int)},
    DBSoundUnder s t n E A db → (∀ C ∈ Cs, SoundUnder s t n E A C) → DBSoundUnder s t n E A (pushAll db Cs)
  | _, [], hdb, _ => hdb
  | _, C :: Cs, hdb, hCs => by
    unfold pushAll
    exact pushAll_sound_under (push_sound_under hdb (hCs C (by simp))) (fun D hD => hCs D (by simp [hD]))

theorem empty_db_sound_under {s t n : Nat} {E : Edges} {A : List Int} :
    DBSoundUnder s t n E A (#[none] : DB) := by
  intro i C hC
  unfold getC at hC
  cases i with
  | zero => simp at hC
  | succ k => simp at hC

/-- forgetting a clause (slot := none) only weakens a database -/
theorem delete_sound_under {s t n : Nat} {E : Edges} {A : List Int} {db : DB}
    (hdb : DBSoundUnder s t n E A db) (i : Nat) : DBSoundUnder s t n E A (db.setIfInBounds i none) := by
  intro j C hC
  unfold getC at hC
  rw [Array.getElem?_setIfInBounds] at hC
  split at hC
  · split at hC <;> simp at hC
  · exact hdb j C (by unfold getC; exact hC)

def deleteAll (db : DB) : List Nat → DB
  | [] => db
  | i :: is => deleteAll (db.setIfInBounds i none) is

theorem deleteAll_sound_under {s t n : Nat} {E : Edges} {A : List Int} : ∀ {db : DB} {ids : List Nat},
    DBSoundUnder s t n E A db → DBSoundUnder s t n E A (deleteAll db ids)
  | _, [], hdb => hdb
  | _, i :: is, hdb => by
    unfold deleteAll
    exact deleteAll_sound_under (delete_sound_under hdb i)

/-- checker state: main database, whether the empty clause was derived, the sub-instances, the assumption
sub-databases, and the ids of the SR tier (main clauses that are only satisfiability-preserving) -/
structure St where
  db : DB
  done : Bool
  subs : Array Sub := #[]
  asms : Array Asm := #[]
  srList : List Nat := []

/-- the main database restricted to pure clauses (hints for a pure RUP step) -/
def getPure (db : DB) (sr : List Nat) (i : Nat) : Option (List Int) :=
  if decide (i ∈ sr) then none else getC db i

/-- an `add` or `img` step on one database of F(s,t,n) (sub-instances: no SR tier there); returns the new
database and the added clause -/
def localStep (s t n : Nat) (E : Edges) (db : DB) : Step → Option (DB × List Int)
  | .add id lits hints =>
    if id == db.size && rup (getC db) (negAssign lits) hints then some (db.push (some lits), lits) else none
  | .img id src perm flip =>
    if id == db.size && permOK perm n && (!flip || s == t) then
      match getC db src with
      | some C =>
        match imgClause E perm flip C with
        | some C' => some (db.push (some C'), C')
        | none => none
      | none => none
    else none
  | _ => none

theorem localStep_ok {s t n : Nat} {E : Edges} {db db' : DB} {x : Step} {C : List Int} (hdb : DBSound s t n E db)
    (h : localStep s t n E db x = some (db', C)) : DBSound s t n E db' ∧ Sound s t n E C := by
  cases x with
  | add id lits hints =>
    simp only [localStep] at h
    by_cases hc : (id == db.size && rup (getC db) (negAssign lits) hints) = true
    · rw [if_pos hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hc
      have hs : Sound s t n E lits := rup_step_sound (fun i H hg => hdb i H hg) hc.2
      exact ⟨push_sound hdb hs, hs⟩
    · rw [if_neg hc] at h; simp at h
  | img id src perm flip =>
    simp only [localStep] at h
    by_cases hc : (id == db.size && permOK perm n && (!flip || s == t)) = true
    · rw [if_pos hc] at h
      simp only [Bool.and_eq_true] at hc
      cases hg : getC db src with
      | none => rw [hg] at h; simp at h
      | some D =>
        rw [hg] at h
        simp only at h
        cases hi : imgClause E perm flip D with
        | none => rw [hi] at h; simp at h
        | some D' =>
          rw [hi] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hflip : flip = true → s = t := by
            intro hfl; have := hc.2; subst hfl; simpa using this
          have hs : Sound s t n E D' := image_sound hc.1.2 hflip (hdb src D hg) hi
          exact ⟨push_sound hdb hs, hs⟩
    · rw [if_neg hc] at h; simp at h
  | openSub => simp [localStep] at h
  | sub => simp [localStep] at h
  | lift => simp [localStep] at h
  | openAsm => simp [localStep] at h
  | asm => simp [localStep] at h
  | close => simp [localStep] at h
  | asmDel => simp [localStep] at h
  | sr => simp [localStep] at h

/-- the lift side condition: the parent instance is (s'+1, t') for a red apex, (s', t'+1) for a blue one -/
def liftParams (s t s' t' : Nat) (red : Bool) : Bool :=
  if red then s == s' + 1 && t == t' else s == s' && t == t' + 1

theorem liftParams_spec {s t s' t' : Nat} {red : Bool} (h : liftParams s t s' t' red = true) :
    s = (if red then s' + 1 else s') ∧ t = (if red then t' else t' + 1) := by
  unfold liftParams at h
  cases red <;> simp_all

/-- the SR check over every clause of the main database (ids in order), consuming the hint groups -/
def srClauses (get : Nat → Option (List Int)) (E : Edges) (σ : Subst) (α : Assign) (db : DB) :
    List Nat → List (Nat × List Nat) → Option (List (Nat × List Nat))
  | [], groups => some groups
  | i :: is, groups =>
    match getC db i with
    | none => srClauses get E σ α db is groups
    | some D =>
      match srClause get E σ α i D groups with
      | some rest => srClauses get E σ α db is rest
      | none => none

theorem srClauses_sound {E : Edges} {c : Nat → Nat → Bool} {get : Nat → Option (List Int)} {σ : Subst}
    {α : Assign} {db : DB} (hσ : substOK σ = true) (hget : ∀ h H, get h = some H → ClauseSat E c H)
    (ha : Agrees E c α) : ∀ {is : List Nat} {groups rest : List (Nat × List Nat)},
      srClauses get E σ α db is groups = some rest →
      ∀ i ∈ is, ∀ D, getC db i = some D → ClauseSat E (substCol E σ c) D
  | [], _, _, _, i, hi, _, _ => by simp at hi
  | i :: is, groups, rest, h, j, hj, D, hD => by
    unfold srClauses at h
    simp only [List.mem_cons] at hj
    cases hg : getC db i with
    | none =>
      rw [hg] at h
      rcases hj with rfl | hj
      · rw [hg] at hD; simp at hD
      · exact srClauses_sound hσ hget ha h j hj D hD
    | some D' =>
      rw [hg] at h
      simp only at h
      cases hs : srClause get E σ α i D' groups with
      | none => rw [hs] at h; simp at h
      | some rest' =>
        rw [hs] at h
        rcases hj with rfl | hj
        · rw [hg] at hD
          simp only [Option.some.injEq] at hD
          subst hD
          exact srClause_sound hσ hget ha hs
        · exact srClauses_sound hσ hget ha h j hj D hD

def stepFn (s t n : Nat) (E : Edges) (st : St) : Step → Option St
  | .add id lits hints =>
    if id == st.db.size then
      if rup (getPure st.db st.srList) (negAssign lits) hints then
        some { st with db := st.db.push (some lits), done := st.done || lits.isEmpty }
      else if rup (getC st.db) (negAssign lits) hints then
        -- some hint is in the SR tier: the result is only satisfiability-preserving
        some { st with db := st.db.push (some lits), srList := id :: st.srList, done := st.done || lits.isEmpty }
      else none
    else none
  | .img id src perm flip =>
    if id == st.db.size && permOK perm n && (!flip || s == t) && !decide (src ∈ st.srList) then
      match getC st.db src with
      | some C =>
        match imgClause E perm flip C with
        | some C' => some { st with db := st.db.push (some C'), done := st.done || C'.isEmpty }
        | none => none
      | none => none
    else none
  | .openSub s' t' m =>
    match originals s' t' m E with
    | some Cs => some { st with subs := st.subs.push ⟨s', t', m, pushAll #[none] Cs⟩ }
    | none => none
  | .sub k x =>
    match st.subs[k]? with
    | some sb =>
      match localStep sb.s sb.t sb.m E sb.db x with
      | some (db', _) => some { st with subs := st.subs.setIfInBounds k { sb with db := db' } }
      | none => none
    | none => none
  | .lift id k src v red emb =>
    match st.subs[k]? with
    | some sb =>
      if id == st.db.size && embOK emb n v && decide (v < n) && emb.size == sb.m && liftParams s t sb.s sb.t red then
        match getC sb.db src with
        | some C =>
          match liftClause E emb v red C with
          | some C' => some { st with db := st.db.push (some C'), done := st.done || C'.isEmpty }
          | none => none
        | none => none
      else none
    | none => none
  | .openAsm A =>
    if A.all (fun l => l != 0) then
      match originals s t n E with
      | some Cs => some { st with asms := st.asms.push ⟨A, pushAll #[none] (Cs.map (reduceUnder A))⟩ }
      | none => none
    else none
  | .asm k id lits hints =>
    match st.asms[k]? with
    | some ab =>
      if id == ab.db.size && rup (getC ab.db) (negAssign lits) hints then
        some { st with asms := st.asms.modify k (fun a => { a with db := a.db.push (some lits) }) }
      else none
    | none => none
  | .close id k src =>
    match st.asms[k]? with
    | some ab =>
      if id == st.db.size then
        match getC ab.db src with
        | some C =>
          some { st with db := st.db.push (some (closeClause ab.A C)), done := st.done || (closeClause ab.A C).isEmpty }
        | none => none
      else none
    | none => none
  | .asmDel k ids =>
    match st.asms[k]? with
    | some _ => some { st with asms := st.asms.modify k (fun a => { a with db := deleteAll a.db ids }) }
    | none => none
  | .sr id lits w pairs ahints groups =>
    if id == st.db.size && substOK ⟨w, pairs⟩ then
      match extend (getC st.db) (negAssign lits) ahints with
      | none => none
      | some α =>
        match srClauses (getC st.db) E ⟨w, pairs⟩ α st.db (List.range st.db.size) groups with
        | none => none
        | some rest =>
          match srClause (getC st.db) E ⟨w, pairs⟩ α id lits rest with
          | some [] => some { st with db := st.db.push (some lits), srList := id :: st.srList, done := st.done || lits.isEmpty }
          | _ => none
    else none

/-- the pure clauses of the main database hold in every good colouring -/
def PureSound (s t n : Nat) (E : Edges) (db : DB) (sr : List Nat) : Prop :=
  ∀ i C, getC db i = some C → i ∉ sr → Sound s t n E C

/-- if a good colouring exists, some good colouring satisfies the whole main database (both tiers) -/
def Satisfiable (s t n : Nat) (E : Edges) (db : DB) : Prop :=
  (∃ c, Good s t n c) → ∃ c, Good s t n c ∧ ∀ i C, getC db i = some C → ClauseSat E c C

/-- the originals of F(s,t,n) are in the main database (they are never deleted) -/
def HasOriginals (s t n : Nat) (E : Edges) (db : DB) : Prop :=
  ∃ Cs, originals s t n E = some Cs ∧ ∀ C ∈ Cs, ∃ i, getC db i = some C

/-- invariant: pure main clauses are sound for F(s,t,n); `done` only when there is no good colouring; every
sub-instance clause is sound for its own F(s',t',m); every clause of an assumption sub-database is sound under its
assumption (whose literals are non-zero); the main database is satisfiable by a good colouring whenever one exists;
and the originals are in the main database -/
def StOK (s t n : Nat) (E : Edges) (st : St) : Prop :=
  PureSound s t n E st.db st.srList ∧ (st.done = true → Sound s t n E []) ∧
  (∀ (k : Nat) (sb : Sub), st.subs[k]? = some sb → DBSound sb.s sb.t sb.m E sb.db) ∧
  (∀ (k : Nat) (ab : Asm), st.asms[k]? = some ab → (∀ l ∈ ab.A, l ≠ 0) ∧ DBSoundUnder s t n E ab.A ab.db) ∧
  Satisfiable s t n E st.db ∧ HasOriginals s t n E st.db

theorem pure_push_pure {s t n : Nat} {E : Edges} {db : DB} {sr : List Nat} {C : List Int}
    (h : PureSound s t n E db sr) (hC : Sound s t n E C) : PureSound s t n E (db.push (some C)) sr := by
  intro i D hD hi
  rcases getC_push_cases hD with hD | rfl
  · exact h i D hD hi
  · exact hC

theorem pure_push_sr {s t n : Nat} {E : Edges} {db : DB} {sr : List Nat} {C : List Int}
    (h : PureSound s t n E db sr) : PureSound s t n E (db.push (some C)) (db.size :: sr) := by
  intro i D hD hi
  simp only [List.mem_cons, not_or] at hi
  unfold getC at hD
  rw [Array.getElem?_push] at hD
  simp only [hi.1, ite_false] at hD
  exact h i D (by unfold getC; exact hD) hi.2

theorem sat_push {s t n : Nat} {E : Edges} {db : DB} {C : List Int} (h : Satisfiable s t n E db)
    (hC : ∀ c, Good s t n c → (∀ i D, getC db i = some D → ClauseSat E c D) → ClauseSat E c C) :
    Satisfiable s t n E (db.push (some C)) := by
  intro hex
  obtain ⟨c, hc, hs⟩ := h hex
  refine ⟨c, hc, ?_⟩
  intro i D hD
  rcases getC_push_cases hD with hD | rfl
  · exact hs i D hD
  · exact hC c hc hs

theorem sat_push_sound {s t n : Nat} {E : Edges} {db : DB} {C : List Int} (h : Satisfiable s t n E db)
    (hC : Sound s t n E C) : Satisfiable s t n E (db.push (some C)) :=
  sat_push h (fun c hc _ => hC c hc)

/-- a RUP step whose hints are database clauses (through any `get` that reads the database) keeps satisfiability -/
theorem sat_push_rup {s t n : Nat} {E : Edges} {db : DB} {C : List Int} {get : Nat → Option (List Int)}
    {hints : List Nat} (h : Satisfiable s t n E db) (hget : ∀ i H, get i = some H → getC db i = some H)
    (hr : rup get (negAssign C) hints = true) : Satisfiable s t n E (db.push (some C)) := by
  refine sat_push h ?_
  intro c _ hs
  by_cases hsat : ClauseSat E c C
  · exact hsat
  · exfalso
    have hf : ∀ l ∈ C, litVal E c l = false := by
      intro l hl
      cases hv : litVal E c l with
      | false => rfl
      | true => exact absurd ⟨l, hl, hv⟩ hsat
    exact rup_sound (fun i H hg => hs i H (hget i H hg)) (negAssign C) hints (agrees_negAssign hf) hr

theorem orig_push {s t n : Nat} {E : Edges} {db : DB} {x : Option (List Int)} (h : HasOriginals s t n E db) :
    HasOriginals s t n E (db.push x) := by
  obtain ⟨Cs, ho, hin⟩ := h
  exact ⟨Cs, ho, fun C hC => let ⟨i, hi⟩ := hin C hC; ⟨i, getC_push_of hi⟩⟩

/-- the empty clause in a satisfiable-when-good database: there is no good colouring -/
theorem sound_empty_of_sat {s t n : Nat} {E : Edges} {db : DB} {i : Nat} (h : Satisfiable s t n E db)
    (hb : getC db i = some []) : Sound s t n E [] := by
  intro c hc
  obtain ⟨c', _, hs⟩ := h ⟨c, hc⟩
  obtain ⟨l, hl, _⟩ := hs i [] hb
  simp at hl

theorem done_ok {s t n : Nat} {E : Edges} {d : Bool} {C : List Int} (hd : d = true → Sound s t n E [])
    (hC : Sound s t n E C) : (d || C.isEmpty) = true → Sound s t n E [] := by
  intro h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact hd h
  · have : C = [] := by simpa using h
    subst this; exact hC

/-- `done` after pushing a clause of either tier: the empty clause means no good colouring, by satisfiability -/
theorem done_ok_sat {s t n : Nat} {E : Edges} {d : Bool} {db : DB} {C : List Int}
    (hd : d = true → Sound s t n E []) (h5 : Satisfiable s t n E (db.push (some C))) :
    (d || C.isEmpty) = true → Sound s t n E [] := by
  intro h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact hd h
  · have : C = [] := by simpa using h
    subst this
    exact sound_empty_of_sat h5 (getC_push_self (db := db))

theorem getPure_getC {db : DB} {sr : List Nat} {i : Nat} {H : List Int} (h : getPure db sr i = some H) :
    getC db i = some H ∧ i ∉ sr := by
  unfold getPure at h
  split at h
  · simp at h
  · rename_i hi
    exact ⟨h, by simpa using hi⟩

theorem stepFn_ok {s t n : Nat} {E : Edges} {st st' : St} {x : Step} (hok : StOK s t n E st)
    (h : stepFn s t n E st x = some st') : StOK s t n E st' := by
  obtain ⟨hdb, hdone, hsubs, hasms, hsat, horig⟩ := hok
  -- pushing a sound (pure) clause to the main database keeps every part of the invariant
  have hpush : ∀ {C : List Int}, Sound s t n E C →
      StOK s t n E { st with db := st.db.push (some C), done := st.done || C.isEmpty } := by
    intro C hC
    exact ⟨pure_push_pure hdb hC, done_ok hdone hC, hsubs, hasms, sat_push_sound hsat hC, orig_push horig⟩
  cases x with
  | add id lits hints =>
    simp only [stepFn] at h
    split at h
    · rename_i hid
      simp only [beq_iff_eq] at hid
      split at h
      · rename_i hr
        simp only [Option.some.injEq] at h
        subst h
        have hs : Sound s t n E lits :=
          rup_step_sound (fun i H hg => let ⟨hg', hi⟩ := getPure_getC hg; hdb i H hg' hi) hr
        exact hpush hs
      · split at h
        · rename_i hr
          simp only [Option.some.injEq] at h
          subst h
          subst hid
          have h5 : Satisfiable s t n E (st.db.push (some lits)) := sat_push_rup hsat (fun _ _ hg => hg) hr
          exact ⟨pure_push_sr hdb, done_ok_sat hdone h5, hsubs, hasms, h5, orig_push horig⟩
        · simp at h
    · simp at h
  | img id src perm flip =>
    simp only [stepFn] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      obtain ⟨⟨⟨_, hperm⟩, hflip⟩, hsrc⟩ := hc
      split at h
      · rename_i D hg
        split at h
        · rename_i D' hi
          simp only [Option.some.injEq] at h
          subst h
          have hflip' : flip = true → s = t := by
            intro hfl; subst hfl; simpa using hflip
          exact hpush (image_sound hperm hflip' (hdb src D hg hsrc) hi)
        · simp at h
      · simp at h
    · simp at h
  | openSub s' t' m =>
    simp only [stepFn] at h
    split at h
    · rename_i Cs ho
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hdb, hdone, ?_, hasms, hsat, horig⟩
      intro k sb hk
      simp only [Array.getElem?_push] at hk
      split at hk
      · simp only [Option.some.injEq] at hk
        subst hk
        have hdb0 : DBSound s' t' m E (#[none] : DB) := by
          intro i C hC
          unfold getC at hC
          cases i with
          | zero => simp at hC
          | succ k => simp at hC
        exact pushAll_sound hdb0 (originals_sound ho)
      · exact hsubs k sb hk
    · simp at h
  | sub k y =>
    simp only [stepFn] at h
    split at h
    · rename_i sb hk
      split at h
      · rename_i db' C hl
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨hdb, hdone, ?_, hasms, hsat, horig⟩
        intro j sb' hj
        simp only [Array.getElem?_setIfInBounds] at hj
        split at hj
        · rename_i hkj
          subst hkj
          split at hj
          · simp only [Option.some.injEq] at hj
            subst hj
            exact (localStep_ok (hsubs k sb hk) hl).1
          · simp at hj
        · exact hsubs j sb' hj
      · simp at h
    · simp at h
  | lift id k src v red emb =>
    simp only [stepFn] at h
    split at h
    · rename_i sb hk
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨_, hemb⟩, hv⟩, hm⟩, hpar⟩ := hc
        split at h
        · rename_i C hg
          split at h
          · rename_i C' hl
            simp only [Option.some.injEq] at h
            subst h
            have hCs : Sound sb.s sb.t emb.size E C := hm ▸ hsubs k sb hk src C hg
            have hs := lift_sound hemb hv hCs hl
            obtain ⟨hs1, ht1⟩ := liftParams_spec hpar
            rw [← hs1, ← ht1] at hs
            exact hpush hs
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  | openAsm A =>
    simp only [stepFn] at h
    split at h
    · rename_i hA0
      split at h
      · rename_i Cs ho
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨hdb, hdone, hsubs, ?_, hsat, horig⟩
        intro k ab hk
        simp only [Array.getElem?_push] at hk
        split at hk
        · simp only [Option.some.injEq] at hk
          subst hk
          have hA : ∀ l ∈ A, l ≠ 0 := by
            simp only [List.all_eq_true, bne_iff_ne] at hA0
            exact hA0
          refine ⟨hA, ?_⟩
          refine pushAll_sound_under empty_db_sound_under ?_
          intro C hC
          obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
          exact reduceUnder_sound hA (soundUnder_of_sound (originals_sound ho D hD))
        · exact hasms k ab hk
      · simp at h
    · simp at h
  | asm k id lits hints =>
    simp only [stepFn] at h
    split at h
    · rename_i ab hk
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨hdb, hdone, hsubs, ?_, hsat, horig⟩
        intro j ab' hj
        simp only [Array.getElem?_modify] at hj
        split at hj
        · rename_i hkj
          subst hkj
          rw [hk] at hj
          simp only [Option.map_some, Option.some.injEq] at hj
          subst hj
          obtain ⟨hA, hsd⟩ := hasms k ab hk
          simp only [Bool.and_eq_true] at hc
          exact ⟨hA, push_sound_under hsd (rup_step_sound_under (fun i H hg => hsd i H hg) hc.2)⟩
        · exact hasms j ab' hj
      · simp at h
    · simp at h
  | close id k src =>
    simp only [stepFn] at h
    split at h
    · rename_i ab hk
      split at h
      · rename_i hid
        split at h
        · rename_i C hg
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hA, hsd⟩ := hasms k ab hk
          exact hpush (close_sound hA (hsd src C hg))
        · simp at h
      · simp at h
    · simp at h
  | asmDel k ids =>
    simp only [stepFn] at h
    split at h
    · rename_i ab hk
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hdb, hdone, hsubs, ?_, hsat, horig⟩
      intro j ab' hj
      simp only [Array.getElem?_modify] at hj
      split at hj
      · rename_i hkj
        subst hkj
        rw [hk] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        subst hj
        obtain ⟨hA, hsd⟩ := hasms k ab hk
        exact ⟨hA, deleteAll_sound_under hsd⟩
      · exact hasms j ab' hj
    · simp at h
  | sr id lits w pairs ahints groups =>
    simp only [stepFn] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hid, hσ⟩ := hc
      split at h
      · simp at h
      · rename_i α hα
        split at h
        · simp at h
        · rename_i rest hall
          split at h
          · rename_i hC
            simp only [Option.some.injEq] at h
            subst h
            subst hid
            -- satisfiability: a good model of the database that falsifies C moves through σ
            have h5 : Satisfiable s t n E (st.db.push (some lits)) := by
              intro hex
              obtain ⟨c, hc, hs⟩ := hsat hex
              by_cases hCs : ClauseSat E c lits
              · refine ⟨c, hc, ?_⟩
                intro i D hD
                rcases getC_push_cases hD with hD | rfl
                · exact hs i D hD
                · exact hCs
              · have hf : ∀ l ∈ lits, litVal E c l = false := by
                  intro l hl
                  cases hv : litVal E c l with
                  | false => rfl
                  | true => exact absurd ⟨l, hl, hv⟩ hCs
                have ha : Agrees E c α := extend_agrees (fun i H hg => hs i H hg) (agrees_negAssign hf) hα
                have hD : ∀ i D, getC st.db i = some D → ClauseSat E (substCol E ⟨w, pairs⟩ c) D :=
                  fun i D hD => srClauses_sound hσ hs ha hall i (List.mem_range.mpr (getC_lt hD)) D hD
                have hC' : ClauseSat E (substCol E ⟨w, pairs⟩ c) lits := srClause_sound hσ hs ha hC
                obtain ⟨Cs, ho, hin⟩ := horig
                have hgood : Good s t n (substCol E ⟨w, pairs⟩ c) :=
                  good_of_originals ho (fun C hC => let ⟨i, hi⟩ := hin C hC; hD i C hi)
                refine ⟨substCol E ⟨w, pairs⟩ c, hgood, ?_⟩
                intro i D hD'
                rcases getC_push_cases hD' with hD' | rfl
                · exact hD i D hD'
                · exact hC'
            exact ⟨pure_push_sr hdb, done_ok_sat hdone h5, hsubs, hasms, h5, orig_push horig⟩
          · simp at h
    · simp at h

def runSteps (s t n : Nat) (E : Edges) : St → List Step → Option St
  | st, [] => some st
  | st, x :: xs =>
    match stepFn s t n E st x with
    | some st' => runSteps s t n E st' xs
    | none => none

theorem runSteps_ok {s t n : Nat} {E : Edges} : ∀ {st st' : St} {xs : List Step}, StOK s t n E st →
    runSteps s t n E st xs = some st' → StOK s t n E st'
  | _, _, [], hok, h => by simp [runSteps] at h; subst h; exact hok
  | st, st', x :: xs, hok, h => by
    unfold runSteps at h
    cases hs : stepFn s t n E st x with
    | none => rw [hs] at h; simp at h
    | some st'' => rw [hs] at h; exact runSteps_ok (stepFn_ok hok hs) h

/-- the initial state (the originals of F(s,t,n), nothing derived) satisfies the invariant -/
theorem init_ok {s t n : Nat} {Cs : List (List Int)} (ho : originals s t n (edgeTable n) = some Cs) :
    StOK s t n (edgeTable n) ⟨pushAll #[none] Cs, false, #[], #[], []⟩ := by
  have hdb0 : DBSound s t n (edgeTable n) (#[none] : DB) := by
    intro i C hC
    unfold getC at hC
    cases i with
    | zero => simp at hC
    | succ k => simp at hC
  have hall := pushAll_sound hdb0 (originals_sound ho)
  refine ⟨fun i C hC _ => hall i C hC, by simp, by simp, by simp, ?_, ⟨Cs, ho, pushAll_contains⟩⟩
  intro ⟨c, hc⟩
  exact ⟨c, hc, fun i C hC => hall i C hC c hc⟩

/-- The checker: true iff every step checks and the empty clause is derived (in either tier). -/
def check (s t n : Nat) (steps : List Step) : Bool :=
  match originals s t n (edgeTable n) with
  | none => false
  | some Cs =>
    match runSteps s t n (edgeTable n) ⟨pushAll #[none] Cs, false, #[], #[], []⟩ steps with
    | some st => st.done
    | none => false

/-- MAIN THEOREM: if the checker accepts, no 2-colouring of K_n avoids a red K_s and a blue K_t, i.e. R(s,t) ≤ n. -/
theorem check_sound {s t n : Nat} {steps : List Step} (h : check s t n steps = true) :
    ∀ c : Nat → Nat → Bool, ¬ Good s t n c := by
  unfold check at h
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
      exact no_good_of_sound_empty ((runSteps_ok (init_ok ho) hr).2.1 h)

end MonsterVerified
