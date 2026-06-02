## examples/symex_assert_covered.nim
##
## `assertCoveredBy` — the Phase 7 CI primitive. The contract:
##
##   Given a SUT `fn` with a symex target, and a test function
##   `testFn` that the user claims exercises that target — prove
##   it. Symex finds a satisfying input; we run `testFn` on it
##   under a capture context; if the target didn't fire, we raise.
##
## This is *verification of test adequacy*. It's stronger than
## random PBT alone: random examples may statistically never reach
## a rare branch; symex finds one deterministically, and
## assertCoveredBy then checks your test actually covered it.

import std/[strutils]
import proptest/symex

# The SUT — a tiny dispatch routine with a rarely-reached branch.
proc handle(req: int) =
  if req == 0:        symexTarget("zero")
  elif req mod 13 == 0: symexTarget("magic-13")
  else:                discard

# ---- Happy path: a test function that hits both targets -------------------

proc thoroughTest(req: int) =
  # This test function calls the SUT directly — so whatever input
  # symex finds, the test definitely exercises it. The expected
  # use shape.
  handle(req)

assertCoveredBy(handle, tLabel("zero"),       thoroughTest)
assertCoveredBy(handle, tLabel("magic-13"),   thoroughTest)
echo "assertCoveredBy: thoroughTest covers both targets."

# ---- Failure path: a test function that misses the target -----------------

proc onlyHandlesZero(req: int) =
  # This test only forwards req=0 to the SUT. The magic-13 path is
  # uncovered. symex finds a magic-13 witness, runs `onlyHandlesZero`
  # on it, sees the target wasn't hit, and raises.
  if req == 0:
    handle(req)

var raised = false
try:
  assertCoveredBy(handle, tLabel("magic-13"), onlyHandlesZero)
except AssertionDefect as e:
  raised = true
  doAssert "magic-13" in e.msg
doAssert raised, "expected AssertionDefect when target uncovered"
echo "assertCoveredBy: onlyHandlesZero misses magic-13 — correctly raised."
