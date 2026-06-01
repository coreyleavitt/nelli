## Phase 5 — dynamic `seq[T]` via Z3 array theory.
##
## A `seq[T]` is represented as `(len: Z3Int, data: Z3Array[Z3Int, sortOf(T)])`.
## Length is constrained to be non-negative; only indices `0 ≤ i < len`
## are observable through index access.
import std/unittest
import proptest/symex

proc longEnough(s: seq[int]) =
  if s.len > 3:
    symexTarget("long")

suite "symex Phase 5 — seq":
  test "branch on seq length":
    let r = symexFind(longEnough, tLabel("long"))
    check r.status == sxSat
    check r.witness[0].len > 3

  test "concrete-index seq access — s[0] == 42":
    proc headIs42(s: seq[int]) =
      if s.len > 0 and s[0] == 42:
        symexTarget("hd")
    let r = symexFind(headIs42, tLabel("hd"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check r.witness[0][0] == 42

  test "symbolic in-bounds seq index":
    proc someIs42(s: seq[int], i: int) =
      if i >= 0 and i < s.len:
        if s[i] == 42:
          symexTarget("hit")
    let r = symexFind(someIs42, tLabel("hit"))
    check r.status == sxSat
    let i = r.witness[1]
    let s = r.witness[0]
    check i >= 0 and i < s.len
    check s[i] == 42
