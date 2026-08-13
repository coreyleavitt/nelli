## Phase 2 — `range`-typed parameters tighten path conditions and
## (under `isOptimised`) trigger Z3Int abstraction with an auditable
## proof obligation.
import std/unittest
import nelli/symex

suite "symex Phase 2 — type-derived ranges":
  test "range[0..100] tightens pc — x > 100 is UNSAT":
    proc cannotExceed(x: range[0..100]) =
      if x > 100:
        symexTarget("over")
    let r = symexFind(cannotExceed, tLabel("over"))
    check r.status == sxUnsat

  test "isOptimised promotes range param to Z3Int; audit log records it":
    proc findValue(x: range[0..100]) =
      if x == 42:
        symexTarget("found")
    let r = symexFind(findValue, tLabel("found"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] == 42
    check r.abstractions.len == 1
    check r.abstractions[0].name == "x"
    check r.abstractions[0].interval.lo == 0
    check r.abstractions[0].interval.hi == 100

  test "Natural recognised as `[0..int.high]`":
    proc neverNeg(x: Natural) =
      if x < 0:
        symexTarget("impossible")
    let r = symexFind(neverNeg, tLabel("impossible"))
    check r.status == sxUnsat

  test "Positive recognised as `[1..int.high]`":
    proc neverZeroOrNeg(x: Positive) =
      if x < 1:
        symexTarget("impossible")
    let r = symexFind(neverZeroOrNeg, tLabel("impossible"))
    check r.status == sxUnsat

  test "interval arithmetic composes through let-binding":
    # Both `a` and `b` promote individually; the let-binding `s = a + b`
    # carries the Z3Int representation forward without additional
    # plumbing. The witness must satisfy both range constraints and
    # the sum equation.
    proc compose(a: range[0..100], b: range[0..100]) =
      let s = a + b
      if s == 150:
        symexTarget("hit")
    let r = symexFind(compose, tLabel("hit"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] + r.witness[1] == 150
    check r.witness[0] in 0..100
    check r.witness[1] in 0..100
    check r.abstractions.len == 2
    check r.abstractions[0].name == "a"
    check r.abstractions[1].name == "b"
