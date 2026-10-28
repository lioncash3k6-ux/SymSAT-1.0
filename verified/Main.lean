import MonsterVerified

open MonsterVerified

/-- Stream the proof lines through `stepOK`, one line at a time (the text is never held as a whole; the state carries
its invariant, see Stream.lean). Lines come from a `LineReader` (1 MB chunks, byte slices; Parse.lean) and are parsed
by `parseLineBytes`. `none` on the first line that fails to parse or to check. Tail recursive with the state as an
owned argument: a `let mut` loop shares the state between iterations and every step then copies the live database
(measured: 13x slower). -/
partial def runStream {s t n : Nat} (r : LineReader) (x : OKSt s t n) : IO (Option (OKSt s t n)) := do
  let (line?, r) ← r.next
  match line? with
  | none => return some x
  | some line =>
    match parseLineBytes line with
    | none => return none
    | some none => runStream r x
    | some (some step) =>
      match stepOK x step with
      | some x' => runStream r x'
      | none => return none

/-- open a proof file: the reader positioned after the header, and the header's (s, t, n) -/
def openProof (path : System.FilePath) : IO (Option ((Nat × Nat × Nat) × LineReader)) := do
  let h ← IO.FS.Handle.mk path .read
  let (hdr?, r) ← ({ h := h } : LineReader).next
  match hdr? with
  | none => return none
  | some hdr =>
    match parseHeader (String.fromUTF8! hdr) with
    | some stn => return some (stn, r)
    | none => return none

/-- one file of batch lemma mode: streamed check against F(s,t,n) (the header must match); `none` if the header is
wrong, a line fails, or the last main clause is not pure -/
def checkLemmaFile (s t n : Nat) (x0 : OKSt s t n) (path : System.FilePath) : IO (Option (Verified s t n)) := do
  match ← openProof path with
  | some ((s', t', n'), r) =>
    if s' == s && t' == t && n' == n then
      match ← runStream r x0 with
      | some x => return x.verified
      | none => return none
    else return none
  | none => return none


/-! ## `checker --assemble SPEC` (Assemble.lean) -/

/-- one stage block of a spec file (written by `monster assemble-spec`; every value is untrusted input) -/
structure StageSpec where
  d : Nat := 0
  catA : String := ""
  catB : String := ""
  countA : Option Nat := none
  countB : Option Nat := none
  nA : Nat := 0
  nB : Nat := 0
  hintA : String := ""
  hintB : String := ""
  record : List String := []
  proofs : Option String := none
  fake : Bool := false
  threads : Nat := 1

/-- spec lines: `stage D` opens a block; then `catA PATH`, `catB PATH`, `countA N`, `countB N`, `nA N`, `nB N`,
`hintA PATH`, `hintB PATH`, `record PATH` | `proofs LIST` | `fakerecord PATH`, `threads K` -/
def parseSpec (lines : Array String) : List StageSpec := Id.run do
  let mut out : List StageSpec := []
  let mut cur : Option StageSpec := none
  for l in lines do
    let toks := (l.splitOn " ").filter (· ≠ "")
    match toks with
    | ["stage", v] =>
      if let some s := cur then out := s :: out
      cur := some { d := v.toNat?.getD 0 }
    | [k, v] =>
      if let some s := cur then
        cur := some (match k with
          | "catA" => { s with catA := v }
          | "catB" => { s with catB := v }
          | "countA" => { s with countA := v.toNat? }
          | "countB" => { s with countB := v.toNat? }
          | "nA" => { s with nA := v.toNat?.getD 0 }
          | "nB" => { s with nB := v.toNat?.getD 0 }
          | "hintA" => { s with hintA := v }
          | "hintB" => { s with hintB := v }
          | "record" => { s with record := s.record ++ [v] }
          | "fakerecord" => { s with record := s.record ++ [v], fake := true }
          | "proofs" => { s with proofs := some v }
          | "threads" => { s with threads := v.toNat?.getD 1 }
          | _ => s)
    | _ => pure ()
  if let some s := cur then out := s :: out
  return out.reverse

/-- hint line: `gen σ0 .. σ{n-1}` -/
def parseHint (line : String) : Option Hint := do
  match (line.splitOn " ").filter (· ≠ "") with
  | g :: rest => return { gen := ← g.toNat?, perm := (← rest.mapM String.toNat?).toArray }
  | [] => none

/-- the unit index `ga * nB + gb` of a proof path `.../u{ga}_{gb}.slrat` (or a bare `u{ga}_{gb}`) -/
def unitIndexOfPath (p : String) (nB : Nat) : Option Nat :=
  let base := (((p.splitOn "/").getLast!).splitOn ".slrat").head!
  match base.toList with
  | 'u' :: rest =>
    match (String.ofList rest).splitOn "_" with
    | [a, b] => do
      let ga ← a.toNat?
      let gb ← b.toNat?
      if gb < nB then some (ga * nB + gb) else none
    | _ => none
  | _ => none

def readHints (path : String) : IO (Option (Array Hint)) := do
  let lines ← IO.FS.lines path
  let mut out : Array Hint := Array.mkEmpty lines.size
  for l in lines do
    if l.trimAscii.isEmpty then continue
    match parseHint l with
    | some h => out := out.push h
    | none => IO.println s!"s SPEC ERROR: bad hint line in {path}: {l}"; return none
  return some out

/-- outcome of one stage: `proved` = the Bool check passed on verified / recorded clauses, `timing` = passed on
unverified clauses (fake record), `failed` -/
inductive StageOutcome | proved | timing | failed

def runStage (sp : StageSpec) : IO StageOutcome := do
  let t0 ← IO.monoMsNow
  IO.println s!"c stage d={sp.d}: catalogue {sp.catA} x {sp.catB}, units {sp.nA} x {sp.nB}, threads {sp.threads}"
  let textA ← IO.FS.readFile sp.catA
  let textB ← IO.FS.readFile sp.catB
  let A := (decodeG6Lines sp.d textA).toArray
  let B := (decodeG6Lines (24 - sp.d) textB).toArray
  let t1 ← IO.monoMsNow
  IO.println s!"c decoded {A.size} A-graphs (K_{sp.d}) and {B.size} B-graphs (K_{24 - sp.d}) in {t1 - t0} ms"
  if let some n := sp.countA then
    if n != A.size then IO.println s!"s SPEC ERROR: expected {n} A-graphs"; return .failed
  if let some n := sp.countB then
    if n != B.size then IO.println s!"s SPEC ERROR: expected {n} B-graphs"; return .failed
  let some hA ← readHints sp.hintA | return .failed
  let some hB ← readHints sp.hintB | return .failed
  if hA.size != A.size || hB.size != B.size then
    IO.println s!"s SPEC ERROR: {hA.size} A-hints for {A.size} graphs, {hB.size} B-hints for {B.size} graphs"
    return .failed
  let size := sp.nA * sp.nB
  let threads := max 1 sp.threads
  let k := (A.size + threads - 1) / threads
  let m := threads
  let E := edgeTable 25
  match sp.proofs, sp.record with
  | some list, _ =>
    -- IN-PROCESS: verify every proof file here; the table holds `Verified` lemmas (theorem stageRefuted_of_verified)
    let paths := ((← IO.FS.lines list).toList.map (·.trimAscii.copy)).filter (fun p => !p.isEmpty)
    let some x0 := initOK 4 5 25 | IO.println "s NOT VERIFIED (no formula)"; return .failed
    let mut V : Array (Option (Verified 4 5 25)) := Array.replicate size none
    let mut failed := 0
    for p in paths do
      match unitIndexOfPath p sp.nB with
      | none => IO.println s!"s SPEC ERROR: cannot read the unit index of {p}"; failed := failed + 1
      | some idx =>
        match ← checkLemmaFile 4 5 25 x0 p with
        | some v =>
          IO.println s!"s VERIFIED LEMMA {p}"
          V := V.set! idx (some v)
        | none => IO.println s!"s NOT VERIFIED {p}"; failed := failed + 1
    let t2 ← IO.monoMsNow
    IO.println s!"c {paths.length - failed} lemmas verified in this process, {failed} failed, {t2 - t1} ms"
    let ok := stageOK E sp.d (csOfVerified V sp.nB) A B hA hB k m
    let t3 ← IO.monoMsNow
    IO.println s!"c coverage check: {A.size} x {B.size} pairs in {t3 - t2} ms"
    if ok && failed == 0 then
      IO.println s!"s STAGE {sp.d} REFUTED: StageRefuted (catalogueFrom files) {sp.d} by theorem MonsterVerified.stageRefuted_of_verified (every lemma verified in this process; no hypothesis beyond the catalogue files)"
      return .proved
    else
      IO.println s!"s STAGE {sp.d} NOT REFUTED"
      return .failed
  | none, recs@(_ :: _) =>
    -- RECORD: clauses recorded by `checker --lemmas LIST --record FILE` (theorem stageRefuted_of_record)
    -- one or more record files (unit-lean-stage writes one per Lean batch)
    let mut lines : Array String := #[]
    for r in recs do
      lines := lines ++ (← IO.FS.lines r)
    let recName := if recs.length == 1 then recs.head! else s!"{recs.length} record files ({recs.head!} ...)"
    let mut R : Array (Option (List Int)) := Array.replicate size none
    let mut bad := 0
    let mut n := 0
    for l in lines do
      match (l.splitOn " ").filter (· ≠ "") with
      | p :: lits =>
        match unitIndexOfPath p sp.nB, lits.mapM String.toInt? with
        | some idx, some C => R := R.set! idx (some C); n := n + 1
        | _, _ => bad := bad + 1
      | [] => pure ()
    let t2 ← IO.monoMsNow
    IO.println s!"c record {recName}: {n} clauses read ({bad} unusable lines) in {t2 - t1} ms"
    let ok := stageOK E sp.d (csOfRecord R sp.nB) A B hA hB k m
    let t3 ← IO.monoMsNow
    IO.println s!"c coverage check: {A.size} x {B.size} pairs in {t3 - t2} ms"
    if ok then
      if sp.fake then
        IO.println s!"s STAGE {sp.d} COVERED BY UNVERIFIED CLAUSES (timing run: the record was not written by the checker; proves nothing)"
        return .timing
      IO.println s!"s STAGE {sp.d} REFUTED GIVEN THE RECORD: StageRefuted (catalogueFrom files) {sp.d} by theorem MonsterVerified.stageRefuted_of_record (hypothesis: every clause of {recName} was recorded by checker --lemmas --record)"
      return .proved
    else
      IO.println s!"s STAGE {sp.d} NOT REFUTED"
      return .failed
  | none, [] =>
    IO.println "s SPEC ERROR: a stage needs `proofs LIST` or `record FILE`"
    return .failed

def assembleMain (spec : String) : IO UInt32 := do
  let stages := parseSpec (← IO.FS.lines spec)
  if stages.isEmpty then IO.println "s SPEC ERROR: no stage"; return 2
  let mut proved : List Nat := []
  let mut timing := false
  let mut failed := false
  for sp in stages do
    match ← runStage sp with
    | .proved => proved := sp.d :: proved
    | .timing => timing := true
    | .failed => failed := true
  if Degrees.all (fun d => proved.contains d) then
    IO.println "s R(4,5) <= 25 ASSEMBLED: every stage of Degrees = [8, 10, 12] refuted; theorem MonsterVerified.r45_le_25_of_stages with hypothesis CatalogueComplete (catalogueFrom files) (plus the record hypotheses printed above, if any)"
  else
    IO.println s!"c stages refuted: {proved.reverse}; the theorem r45_le_25_of_stages needs {Degrees}"
  return (if failed then 1 else if timing then 3 else 0)
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match parseSLRAT text with
    | none => IO.println "s PARSE ERROR"; return 1
    | some (s, t, n, steps) =>
      if check s t n steps then
        IO.println s!"s VERIFIED UNSAT: R({s},{t}) <= {n}  (theorem MonsterVerified.check_sound)"
        return 0
      else
        IO.println "s NOT VERIFIED"; return 1
  | ["--lemma", path] =>
    -- lemma mode, streaming: every step must check; the last main clause is reported (no empty clause required)
    match ← openProof path with
    | none => IO.println "s PARSE ERROR (header)"; return 1
    | some ((s, t, n), r) =>
      match initOK s t n with
      | none => IO.println "s NOT VERIFIED (no formula)"; return 1
      | some x0 =>
        match ← runStream r x0 with
        | none => IO.println "s NOT VERIFIED"; return 1
        | some x =>
          if x.st.done then
            IO.println s!"s VERIFIED UNSAT: R({s},{t}) <= {n}  (theorem MonsterVerified.OKSt.done_sound)"
            return 0
          match x.last with
          | some C =>
            IO.println s!"s VERIFIED LEMMA ({s},{t}) K_{n}: every good colouring satisfies {C}  (theorem MonsterVerified.OKSt.clause_sound)"
            return 0
          | none =>
            -- every step checked but the last main clause is SR-tier (satisfiability-preserving only), or there is none
            IO.println s!"s VERIFIED STEPS ({s},{t}) K_{n}: every line checks; the last clause is in the SR tier, not a lemma"
            return 0
  | ["--assemble", spec] => assembleMain spec
  | ["--parse", path] =>
    -- timing aid: read and parse every line (no checking); measures the reader + parser share of a check
    match ← openProof path with
    | none => IO.println "s PARSE ERROR (header)"; return 1
    | some (_, r0) =>
      let mut r := r0
      let mut n := 0
      let mut bad := 0
      repeat
        let (line?, r') ← r.next
        r := r'
        match line? with
        | none => break
        | some line =>
          match parseLineBytes line with
          | some (some _) => n := n + 1
          | some none => pure ()
          | none => bad := bad + 1
      IO.println s!"c parsed {n} steps, {bad} bad lines"
      return 0
  | "--lemmas" :: list :: rest =>
    -- batch lemma mode: one SLRAT path per line of `list`, all over the (s,t,n) of the first file, verified one
    -- after another in this process (one file's live databases at a time); `--delete` removes each verified file
    -- `--record FILE` appends `path lits...` for every verified lemma (read back by `--assemble`, Assemble.lean)
    let delete := rest.contains "--delete"
    let recPath : Option String := match rest.idxOf? "--record" with
      | some i => rest[i + 1]?
      | none => none
    let known := rest.length == (if delete then 1 else 0) + (if recPath.isSome then 2 else 0)
    if !known then
      IO.println "usage: checker --lemmas LIST [--delete] [--record FILE]"
      return 2
    let recH : Option IO.FS.Handle ← match recPath with
      | some p => some <$> IO.FS.Handle.mk p .append
      | none => pure none
    let lines ← IO.FS.lines list
    let paths : List String := (lines.toList.map (fun l => ((l.splitOn "\n")[0]!).trimAscii.copy)).filter (fun p => !p.isEmpty)
    match paths with
    | [] => IO.println "s BATCH: empty list"; return 1
    | first :: _ =>
      let h ← IO.FS.Handle.mk first .read
      let hdr ← h.getLine
      match parseHeader hdr with
      | none => IO.println s!"s PARSE ERROR (header) {first}"; return 1
      | some (s, t, n) =>
        match initOK s t n with
        | none => IO.println "s NOT VERIFIED (no formula)"; return 1
        | some x0 =>
          let mut ok : List (Verified s t n) := []
          let mut failed := 0
          for p in paths do
            match ← checkLemmaFile s t n x0 p with
            | some v =>
              IO.println s!"s VERIFIED LEMMA {p}: {v.clause}"
              ok := v :: ok
              if let some h := recH then
                h.putStrLn (p ++ " " ++ " ".intercalate (v.clause.map toString))
                h.flush
              if delete then IO.FS.removeFile p
            | none =>
              IO.println s!"s NOT VERIFIED {p}"
              failed := failed + 1
          IO.println s!"s BATCH ({s},{t}) K_{n}: {ok.length} verified lemmas (theorem MonsterVerified.batch_sound), {failed} failed"
          return (if failed == 0 then 0 else 1)
  | _ =>
    IO.println "usage: checker proof.slrat | checker --lemma proof.slrat | checker --lemmas LIST [--delete] [--record FILE] | checker --assemble SPEC"
    return 2
