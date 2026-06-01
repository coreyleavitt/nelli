## Phase 1 — `symexAssert` + `tAssertionViolation` target.
## Inside symex, an assertion is dual-purpose:
##   * Under a label target, it tightens the path condition with the
##     assertion (subsequent code only sees inputs where it holds).
##   * Under `tAssertionViolation`, it forks: the walker tries to
##     reach `not cond` and reports a witness if SAT.
import std/unittest
import proptest/symex

suite "symex Phase 1 — assertions":
  test "tAssertionViolation finds the falsifying input":
    proc mustBeNonneg(x: int) =
      symexAssert(x >= 0)
    let r = symexFind(mustBeNonneg, tAssertionViolation())
    check r.status == sxSat
    check r.witness[0] < 0

  test "assertion that always holds returns sxUnsat":
    # `x*0 == 0` is always true; no violation is possible.
    proc trivial(x: int) =
      symexAssert(x * 0 == 0)
    let r = symexFind(trivial, tAssertionViolation())
    check r.status == sxUnsat

  test "label target after assertion sees the assertion tighten pc":
    # When searching for a label, the assertion above narrows the
    # input space — the label witness must satisfy the assertion.
    proc afterAssert(x: int) =
      symexAssert(x >= 100)
      if x > 0:
        symexTarget("positive")
    let r = symexFind(afterAssert, tLabel("positive"))
    check r.status == sxSat
    check r.witness[0] >= 100
