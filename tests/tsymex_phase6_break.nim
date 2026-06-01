## Phase 6 — break and continue.
##
## Walker-level loop-frame stack catches break/continue and dispatches
## to the right exit or next-iteration entry.
import std/unittest
import proptest/symex

suite "symex Phase 6 — break / continue":
  test "break exits loop early":
    proc findFirst(s: seq[int]) =
      var found = 0
      var i = 0
      while i < s.len:
        if s[i] == 7:
          found = i + 1
          break
        i = i + 1
      if found == 3:
        symexTarget("found-at-2")
    let r = symexFind(findFirst, tLabel("found-at-2"))
    check r.status == sxSat
    check r.witness[0].len >= 3
    check r.witness[0][2] == 7

  test "continue skips to next iteration":
    proc countEvens(s: seq[int]) =
      var count = 0
      var i = 0
      while i < s.len:
        if (s[i] mod 2) == 1:
          i = i + 1
          continue
        count = count + 1
        i = i + 1
      if count == 2 and s.len == 2:
        symexTarget("two-evens")
    let r = symexFind(countEvens, tLabel("two-evens"))
    check r.status == sxSat
    check r.witness[0].len == 2
    check (r.witness[0][0] mod 2) == 0
    check (r.witness[0][1] mod 2) == 0
