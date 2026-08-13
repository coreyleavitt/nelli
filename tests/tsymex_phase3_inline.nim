## Phase 3 — call resolution via macro-time `getImpl` + walk-time inlining.
##
## Tests in this file exercise the inline-call mechanic without
## recursion: a caller invokes a helper, the walker follows the
## helper's body, and the result composes back into the caller's
## environment.
import std/unittest
import nelli/symex

proc bumpBy1(x: int): int = x + 1

proc f1(x: int) =
  if bumpBy1(x) == 6:
    symexTarget("hit")

proc absVal(x: int): int =
  if x < 0:
    return -x
  return x

proc f2(x: int) =
  if absVal(x) == 7:
    symexTarget("abs-is-7")

suite "symex Phase 3 — inline call resolution":
  test "value-returning helper composes through the caller":
    let r = symexFind(f1, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "helper with internal branches: caller's target reached via callee's branch":
    let r = symexFind(f2, tLabel("abs-is-7"))
    check r.status == sxSat
    # Either x = 7 or x = -7 satisfies absVal(x) == 7.
    check (r.witness[0] == 7 or r.witness[0] == -7)

  test "two call sites of the same helper compose independently":
    proc f4(x: int) =
      let a = bumpBy1(x)
      let b = bumpBy1(x)
      if a + b == 12:
        symexTarget("twin")
    let r = symexFind(f4, tLabel("twin"))
    check r.status == sxSat
    # a = x+1, b = x+1, a+b = 2x+2 == 12 → x = 5.
    check r.witness[0] == 5

  test "target inside a void helper is reached via the caller":
    proc setMark(x: int) =
      if x > 5:
        symexTarget("inside-helper")
    proc f3(x: int) =
      setMark(x)
    let r = symexFind(f3, tLabel("inside-helper"))
    check r.status == sxSat
    check r.witness[0] > 5
