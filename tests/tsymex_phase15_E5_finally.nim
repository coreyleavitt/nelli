## Phase 15 — Cluster E, cycle E5: `finally` semantics (both exit paths;
## finally-raises-replaces).
##
## E3 shipped the `try`/`except` core but STUBBED `finally`: the finally block
## was walked on the NORMAL fall-through paths only (raised-path finally was
## explicitly deferred to E5). E5 completes `walk(isTry)` so the finally runs on
## EVERY exit continuation of the try body — normal exits AND raised exits — and
## composes per Nim's documented semantics:
##   - normal-exit  + finally-normal  = normal (original try-body result)
##   - raised-exit   + finally-normal  = RE-RAISED (original exn re-propagated)
##   - any           + finally-RAISED  = finally's exception WINS (replaces the
##                                       in-flight one)
## The `inFlightExn` lifecycle: set while a raised continuation runs its finally
## (so a bare re-raise inside the finally sees it); if the finally completes
## normally on a raised continuation, the original is re-propagated; if the
## finally itself raises, that replaces the in-flight one.
import std/unittest
import proptest/symex
import proptest/smt/[dsl, runtime]

# --- 1. finally runs on the NORMAL exit path --------------------------------
# Pure control flow (no exception). The finally marker is always reachable on
# the normal path; the try body's result is unchanged by the finally.
proc finallyNormal(x: int): int =
  try:
    result = x * 2
  finally:
    symexTarget("finally_normal")

# --- 2. finally-raises REPLACES the in-flight exception ---------------------
# The try body unconditionally raises ValueError. The finally conditionally
# raises IOError when x > 100. Per Nim semantics: when the finally raises, ITS
# exception wins and the original ValueError is dropped; when the finally falls
# through, the original ValueError is re-propagated.
#   x > 100  -> sxRaised{IOError}    (finally's raise replaces ValueError)
#   x <= 100 -> sxRaised{ValueError} (finally falls through, original re-raised)
proc finallyReplaces(x: int): int =
  try:
    raise newException(ValueError, "original")
  finally:
    if x > 100: raise newException(IOError, "overrides")

suite "symex Phase 15 E5 — finally semantics (finally-raises-replaces)":
  # ---- test 1: finally on normal exit ----
  test "E5: finally runs on normal exit (isExact)":
    let r = symexFind(finallyNormal, tLabel("finally_normal"))
    check r.status == sxSat

  test "E5: finally runs on normal exit (isOptimised)":
    let r = symexFind(finallyNormal, tLabel("finally_normal"),
                      optimisedSymexSettings())
    check r.status == sxSat

  # ---- test 2: finally-raises replaces in-flight exception ----
  test "E5: finally raise replaces in-flight exn (IOError wins, x>100)":
    let r = symexFind(finallyReplaces, tRaisedExn("IOError"))
    check r.status == sxRaised
    check r.raisedTypeId == "IOError"
    check r.raisedWitness[0] > 100

  test "E5: finally fall-through re-raises original (ValueError, x<=100)":
    let r = symexFind(finallyReplaces, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] <= 100

  test "E5: finally-replaces — IOError witness (isOptimised)":
    let r = symexFind(finallyReplaces, tRaisedExn("IOError"),
                      optimisedSymexSettings())
    check r.status == sxRaised
    check r.raisedTypeId == "IOError"

  # ---- test 3: finally heap-state visibility — DEFERRED to Cluster R ----
  # RFC §E5 test 3 asserts that BOTH a try-body write (`p[] = 7`) and a
  # pre-raise finally-body write (`q[] = 99`) are visible in the resulting
  # witness, through `p: ptr int` / `q: ptr int` deref-assignments. That is
  # LOGICAL-HEAP (pointer-deref/assignment) semantics — Cluster R. `path.heaps`
  # exists (H1) but is INERT until Cluster R fills it: the engine cannot yet
  # PRODUCE ptr-write witness values, so asserting their visibility would be a
  # faked test. E5 ships the finally CONTROL-FLOW composition (tests 1 & 2) and
  # threads each exit continuation's path state (heaps/heapDepth/allocCounters)
  # into the finally walk structurally — but a ptr-write SUT cannot be modeled
  # until Cluster R lands the deref read/write.
  #
  # DEFERRED to Cluster R: ptr-deref heap writes through finally.
  # (mirrors the S10b → E1 deferral pattern; the finally path-state threading is
  #  in place and will exercise correctly once Cluster R makes `path.heaps` live)
  test "E5: finally heap-write visibility (DEFERRED to Cluster R: ptr-deref)":
    skip()
