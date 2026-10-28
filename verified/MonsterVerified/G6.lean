import MonsterVerified.Assembly

/-!
# graph6 decoding and the concrete catalogue (assembly part 5c, data side)

McKay's catalogues (`r35/n{d}.g6`, `r44/n{24-d}.g6`, one graph per line) are read into colourings
`Nat → Nat → Bool` with the project's convention: an **edge is red** (`true`), a non-edge blue, exactly as
`src/graph.rs` (`from_g6`, "edge always means RED") and `src/catalog.rs` read them. graph6 (n ≤ 62): the first byte
is `n + 63`; then the upper triangle in column-major order (pairs (i, j), i < j, j = 1, 2, ...) is packed six bits
per byte, most significant bit first, each byte offset by 63. Pair (i, j) is bit `j(j-1)/2 + i`, the same index the
checker's edge table uses (minus one), so `g6Colouring body i j` reads it directly.

Everything here is a total, executable definition: no proof depends on the decoder (a line that does not decode is
dropped, which only makes `CatalogueComplete` a stronger, i.e. less likely, hypothesis). The 19 MB `r44/n12.g6` must
not be embedded in a Lean source: a future `checker --assemble` mode reads the files with `IO` and passes their
texts to `catalogueFrom`.
-/

namespace MonsterVerified

/-- the bit of pair index `k` in the packed body (bytes already without the header, as an array: O(1) per bit) -/
def g6Bit (body : Array Nat) (k : Nat) : Bool :=
  match body[k / 6]? with
  | some byte => Nat.testBit (byte - 63) (5 - k % 6)
  | none => false

/-- the colouring of a graph6 body: `i j ↦` bit `j(j-1)/2 + i` (meaningful for `i < j`; `col` orders the pair) -/
def g6Colouring (body : Array Nat) : Nat → Nat → Bool :=
  fun i j => g6Bit body (j * (j - 1) / 2 + i)

/-- decode one graph6 line with n ≤ 62 vertices: `(n, colouring)`; `none` if malformed. Bytes outside 63..126 (CR,
spaces) can never belong to a graph6 line and are dropped first, which replaces trimming. -/
def decodeG6 (line : String) : Option (Nat × (Nat → Nat → Bool)) :=
  match (line.toList.map Char.toNat).filter (fun x => 63 ≤ x && x ≤ 126) with
  | [] => none
  | h :: body =>
    if h < 63 ∨ 125 < h then none
    else
      let n := h - 63
      if body.length = (n * (n - 1) / 2 + 5) / 6 ∧ body.all (fun x => 63 ≤ x && x ≤ 126) then
        some (n, g6Colouring body.toArray)
      else none

/-- the colourings of K_n listed in a graph6 file (one graph per line; other lines are dropped) -/
def decodeG6Lines (n : Nat) (text : String) : List (Nat → Nat → Bool) :=
  (text.splitOn "\n").filterMap fun l =>
    match decodeG6 l with
    | some (m, c) => if m = n then some c else none
    | none => none

/-- the catalogue read from the files: `texts d = (r35/n{d}.g6, r44/n{24-d}.g6)` for `d ∈ Degrees` -/
def catalogueFrom (texts : Nat → String × String) : Catalogue :=
  { A := fun d => decodeG6Lines d (texts d).1, B := fun d => decodeG6Lines (24 - d) (texts d).2 }

/-- the number of graphs decoded from a file (for comparing with McKay's counts at run time) -/
def g6Count (n : Nat) (text : String) : Nat := (decodeG6Lines n text).length

end MonsterVerified
