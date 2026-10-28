import MonsterVerified.Checker

namespace MonsterVerified

/-- split a token list at its "0" tokens (a trailing "0" leaves a final empty segment) -/
def splitZero : List String → List (List String)
  | [] => [[]]
  | x :: rest =>
    if x == "0" then [] :: splitZero rest
    else
      match splitZero rest with
      | s :: ss => (x :: s) :: ss
      | [] => [[x]]

def toPairs : List Int → Option (List (Int × Int))
  | [] => some []
  | a :: b :: rest => (toPairs rest).map ((a, b) :: ·)
  | [_] => none

/-- an addition or image line (tokens after any `s k` prefix) -/
def parseLocal (toks : List String) : Option Step := do
  let id ← toks[0]!.toNat?
  if toks.length > 1 && (toks[1]! == "i" || toks[1]! == "f") then
    let src ← toks[2]!.toNat?
    let perm ← (toks.drop 3).dropLast.mapM String.toNat?
    return .img id src perm.toArray (toks[1]! == "f")
  else
    let rest := toks.drop 1
    let z := rest.idxOf "0"
    let lits ← (rest.take z).mapM String.toInt?
    let hints ← ((rest.drop (z + 1)).dropLast).mapM String.toNat?
    return .add id lits hints

/-- the header line `c slrat s t n` -/
def parseHeader (hdr : String) : Option (Nat × Nat × Nat) := do
  let h := ((hdr.splitOn " ").map (fun t => (t.splitOn "\n")[0]!)).filter (· ≠ "")
  if h.length != 5 || h[0]! != "c" || h[1]! != "slrat" then none
  let s ← h[2]!.toNat?
  let t ← h[3]!.toNat?
  let n ← h[4]!.toNat?
  return (s, t, n)

/-- One proof line (a trailing newline is allowed). `none` = parse error, `some none` = nothing to do (blank line or
comment). Parsing is untrusted: whatever it produces is checked by `stepFn`.
Lines: `id lits 0 hints 0`, `id i|f src perm 0`, `o s t m` (open sub-instance), `s k <line>` (step in
sub-instance k), `id l k src v r|b emb 0` (lift clause src of sub-instance k, apex v red/blue),
`a l1 .. lk 0` (open assumption sub-database), `u k id lits 0 hints 0` (LRAT step in assumption sub-database k),
`u k d id1 .. idn 0` (forget clauses of assumption sub-database k),
`id a k src 0` (close: main clause id := ¬A ∨ clause src of assumption sub-database k). -/
def parseLine (line : String) : Option (Option Step) := do
  let toks := ((line.splitOn " ").map (fun t => (t.splitOn "\n")[0]!)).filter (· ≠ "")
  if toks.isEmpty || toks[0]! == "c" then return none
  if toks[0]! == "o" then
    if toks.length != 4 then none
    return some (.openSub (← toks[1]!.toNat?) (← toks[2]!.toNat?) (← toks[3]!.toNat?))
  else if toks[0]! == "s" then
    if toks.length < 3 then none
    return some (.sub (← toks[1]!.toNat?) (← parseLocal (toks.drop 2)))
  else if toks[0]! == "a" then
    if toks.getLast! != "0" then none
    let lits ← ((toks.drop 1).dropLast).mapM String.toInt?
    return some (.openAsm lits)
  else if toks[0]! == "u" then
    if toks.length < 4 then none
    let k ← toks[1]!.toNat?
    if toks[2]! == "d" then
      if toks.getLast! != "0" then none
      let ids ← ((toks.drop 3).dropLast).mapM String.toNat?
      return some (.asmDel k ids)
    match (← parseLocal (toks.drop 2)) with
    | .add id lits hints => return some (.asm k id lits hints)
    | _ => none
  else if toks.length > 1 && toks[1]! == "a" then
    if toks.length != 5 then none
    return some (.close (← toks[0]!.toNat?) (← toks[2]!.toNat?) (← toks[3]!.toNat?))
  else if toks.length > 1 && toks[1]! == "r" then
    -- `id r lits 0 witness 0 a1 b1 .. ap bp 0 ahints 0 (Did hints 0)* 0`
    let id ← toks[0]!.toNat?
    let segs := splitZero (toks.drop 2)
    -- segments: lits, witness, pairs, ahints, groups.., then the empty segment of the final 0 and the end
    if segs.length < 6 || !(segs[segs.length - 1]!).isEmpty || !(segs[segs.length - 2]!).isEmpty then none
    let lits ← segs[0]!.mapM String.toInt?
    let witness ← segs[1]!.mapM String.toInt?
    let flat ← segs[2]!.mapM String.toInt?
    let pairs ← toPairs flat
    let ahints ← segs[3]!.mapM String.toNat?
    let groups ← ((segs.drop 4).dropLast.dropLast).mapM (fun g => do
      match g with
      | [] => none
      | d :: hs => return (← d.toNat?, ← hs.mapM String.toNat?))
    return some (.sr id lits witness pairs ahints groups)
  else if toks.length > 1 && toks[1]! == "l" then
    if toks.length < 7 || (toks[5]! != "r" && toks[5]! != "b") then none
    let emb ← (toks.drop 6).dropLast.mapM String.toNat?
    return some (.lift (← toks[0]!.toNat?) (← toks[2]!.toNat?) (← toks[3]!.toNat?) (← toks[4]!.toNat?)
      (toks[5]! == "r") emb.toArray)
  else
    return some (← parseLocal toks)

/-- Parse SLRAT text into (s, t, n, steps) (whole text; the executable's lemma mode streams line by line instead). -/
def parseSLRAT (text : String) : Option (Nat × Nat × Nat × List Step) := do
  let lines := (text.splitOn "\n").filter (fun l => !l.trimAscii.isEmpty)
  let hdr ← lines.head?
  let (s, t, n) ← parseHeader hdr
  let mut steps : Array Step := #[]
  for line in lines.tail do
    match ← parseLine line with
    | some step => steps := steps.push step
    | none => pure ()
  return (s, t, n, steps.toList)

def checkText (text : String) : Bool :=
  match parseSLRAT text with
  | some (s, t, n, steps) => check s t n steps
  | none => false

end MonsterVerified

namespace MonsterVerified

/-! ## Fast path of the line parser (byte scanning; untrusted like `parseLine`: whatever it produces is checked)

Parsing was 53% of a lemma check (2026-10-28, 20 MB unit proof: 3.3 s of 6.3 s), with `splitOn`, token lists and
`String.toInt?`. The hot kinds (`u k id lits 0 hints 0`, `u k d ids 0`, `id lits 0 hints 0`) are read here byte by
byte; every other kind goes to `parseLine`. -/

partial def skipSpaces (bs : ByteArray) (i : Nat) : Nat :=
  if i < bs.size && (bs[i]! == 32 || bs[i]! == 10 || bs[i]! == 13 || bs[i]! == 9) then skipSpaces bs (i + 1) else i

partial def readDigits (bs : ByteArray) (i : Nat) (acc : Nat) : Nat × Nat :=
  if i < bs.size then
    let c := bs[i]!
    if 48 ≤ c && c ≤ 57 then readDigits bs (i + 1) (acc * 10 + (c.toNat - 48)) else (acc, i)
  else (acc, i)

/-- a signed decimal after optional spaces; `none` without a digit -/
def readInt (bs : ByteArray) (i : Nat) : Option (Int × Nat) :=
  let i := skipSpaces bs i
  if i < bs.size then
    let neg := bs[i]! == 45
    let j := if neg then i + 1 else i
    let (v, k) := readDigits bs j 0
    if k == j then none else some ((if neg then -(v : Int) else (v : Int)), k)
  else none

/-- integers up to and including a `0`; the position after the `0` -/
partial def readUntilZero (bs : ByteArray) (i : Nat) (acc : Array Int) : Option (Array Int × Nat) :=
  match readInt bs i with
  | some (0, k) => some (acc, k)
  | some (v, k) => readUntilZero bs k (acc.push v)
  | none => none

def natsOf (a : Array Int) : Option (List Nat) :=
  if a.all (· ≥ 0) then some (a.toList.map Int.toNat) else none

def parseLineFast (line : String) : Option (Option Step) :=
  let bs := line.toUTF8
  let i := skipSpaces bs 0
  if i ≥ bs.size then some none
  else
    let c := bs[i]!
    let endTok (j : Nat) : Bool := j ≥ bs.size || bs[j]! == 32 || bs[j]! == 10 || bs[j]! == 13
    if c == 99 && endTok (i + 1) then some none                       -- `c` comment
    else if c == 117 && endTok (i + 1) then                           -- `u k ...`
      match readInt bs (i + 1) with
      | some (k, j) =>
        if k < 0 then none else
        let j' := skipSpaces bs j
        if j' < bs.size && bs[j']! == 100 && endTok (j' + 1) then     -- `u k d ids 0`
          match readUntilZero bs (j' + 1) #[] with
          | some (ids, _) => (natsOf ids).map (fun ids => some (.asmDel k.toNat ids))
          | none => none
        else
          match readInt bs j with
          | some (id, j2) =>
            if id < 0 then none else
            match readUntilZero bs j2 #[] with
            | some (lits, j3) =>
              match readUntilZero bs j3 #[] with
              | some (hints, _) => (natsOf hints).map (fun hs => some (.asm k.toNat id.toNat lits.toList hs))
              | none => none
            | none => none
          | none => parseLine line
      | none => parseLine line
    else if 48 ≤ c && c ≤ 57 then                                      -- `id lits 0 hints 0` if token 2 is numeric
      match readInt bs i with
      | some (id, j) =>
        let j' := skipSpaces bs j
        if id ≥ 0 && j' < bs.size && ((48 ≤ bs[j']! && bs[j']! ≤ 57) || bs[j']! == 45) then
          match readUntilZero bs j #[] with
          | some (lits, j3) =>
            match readUntilZero bs j3 #[] with
            | some (hints, _) => (natsOf hints).map (fun hs => some (.add id.toNat lits.toList hs))
            | none => none
          | none => none
        else parseLine line
      | none => parseLine line
    else parseLine line

end MonsterVerified
