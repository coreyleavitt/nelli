## Phase 4 — static arrays.
##
## Each `array[N, T]` parameter is represented as N per-element
## SymVals. Concrete-literal indexing returns the matching element;
## symbolic indexing lands in cycle 7+.
import std/unittest
import nelli/symex

proc indexedAt2(arr: array[5, int]) =
  if arr[2] == 42:
    symexTarget("hit-2")

suite "symex Phase 4 — static arrays":
  test "array[5, int] param + literal index":
    let r = symexFind(indexedAt2, tLabel("hit-2"))
    check r.status == sxSat
    check r.witness[0][2] == 42

  test "symbolic in-bounds index — finds a satisfying (i, arr[i])":
    proc symbolicIdx(arr: array[5, int], i: int) =
      if i >= 0 and i < 5:
        if arr[i] == 42:
          symexTarget("found")
    let r = symexFind(symbolicIdx, tLabel("found"))
    check r.status == sxSat
    let i = r.witness[1]
    check i >= 0 and i < 5
    check r.witness[0][i] == 42

  test "array literal as local var + symbolic index":
    proc literalArr(i: int) =
      let arr = [1, 2, 3, 4, 5]
      if i >= 0 and i < 5:
        if arr[i] == 3:
          symexTarget("found-3")
    let r = symexFind(literalArr, tLabel("found-3"))
    check r.status == sxSat
    check r.witness[0] == 2   ## i = 2 → arr[2] = 3
