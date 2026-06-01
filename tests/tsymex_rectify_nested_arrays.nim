## Rectify #142 — nested static arrays.
import std/unittest
import proptest/symex

proc grid(g: array[2, array[3, int]]) =
  if g[1][2] == 42:
    symexTarget("found")

suite "symex nested arrays #142":
  test "array[2, array[3, int]] indexing works":
    let r = symexFind(grid, tLabel("found"))
    check r.status == sxSat
    check r.witness[0][1][2] == 42
