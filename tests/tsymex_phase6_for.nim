## Phase 6 — for loops over range / array / seq.
##
## For-loops desugar to while loops at parse time. The walker
## handles the resulting while via k-unrolling.
import std/unittest
import proptest/symex

suite "symex Phase 6 — for":
  test "for i in 0..n — range loop reaches target":
    proc sumToFive(n: int) =
      var s = 0
      for i in 0..n:
        s = s + 1
      if s == 4:
        symexTarget("hit")
    let r = symexFind(sumToFive, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "for x in arr — static array iteration":
    proc sumArr(arr: array[3, int]) =
      var s = 0
      for x in arr:
        s = s + x
      if s == 6:
        symexTarget("hit")
    let r = symexFind(sumArr, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0][0] + r.witness[0][1] + r.witness[0][2] == 6

  test "for x in s — seq iteration":
    proc sumSeq(s: seq[int]) =
      var sum = 0
      for x in s:
        sum = sum + x
      if sum == 10 and s.len == 2:
        symexTarget("hit")
    let r = symexFind(sumSeq, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 2
    check r.witness[0][0] + r.witness[0][1] == 10
