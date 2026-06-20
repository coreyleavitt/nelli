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
import std/[unittest, tables, options]
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

  # ---- test 3: finally heap-state visibility — un-deferred at R13 ----
  # RFC §E5 test 3 asserts that BOTH a try-body write (`p[] = 7`) and a
  # pre-raise finally-body write (`q[] = 99`) are visible in the resulting
  # witness, through `p: ptr int` / `q: ptr int` deref-assignments. That is
  # LOGICAL-HEAP (pointer-deref/assignment) semantics — Cluster R. It was
  # DEFERRED to Cluster R because `path.heaps` was INERT until R made it live.
  # Cluster R is now COMPLETE: R4 (heap store `p[] = v`), R8 (`ptr T` heap
  # routing), and R13-B (`ptr T` + try/finally → sxRaised with the heap
  # committed, observed back through a finally guard) compose to support exactly
  # this property. So this is now a PASSING test, not a skip.
  #
  # un-deferred at R13; Cluster R complete.
  #
  # WRINKLE (documented, sound adaptation): the R12 heap-snapshot surfaces a
  # ptr param's committed pointee in the witness ONLY when that cell was READ
  # back via `p[]` (the `currentHeapDerefVals` witness hook fires on `isDeref`,
  # not on a write-only `isDerefWrite`). The RFC's bare write-only SUT (`p[]=7`
  # in try, `q[]=99` in finally, no read-back) therefore commits both stores to
  # `path.heaps` but the witness renders the unobserved pointees as the default
  # zero — the writes are committed to the heap, but not SURFACED. To assert the
  # core property soundly — "the try-body write AND the finally-before-raise
  # write are BOTH committed in the raised witness" — the finally reads both
  # cells back (the R13-B idiom: a `p[]==7` guard) before raising. The guard is
  # satisfiable iff BOTH the try-body store (`p[]=7`, threaded through the
  # raised exit continuation) AND the finally store (`q[]=99`, committed before
  # the raise) landed; the satisfying witness then surfaces p[]==7 and q[]==99.
  # The raise is still the finally's, so the verdict is sxRaised(ValueError).
  proc finallyHeapWrites(p: ptr int, q: ptr int) =
    try:
      p[] = 7
    finally:
      q[] = 99
      if p[] == 7 and q[] == 99:
        raise newException(ValueError, "finally-raised")

  test "E5: finally heap-write visibility (un-deferred at R13: ptr-deref)":
    let r = symexFind(finallyHeapWrites, tRaisedExn("ValueError"))
    # The finally raises after writing q[] = 99, so ValueError propagates out.
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    # The v3 heap-snapshot has one entry per ptr param (p and q).
    check r.heapSnapshot.len == 2
    # Collect each param's committed pointee. If the solver aliased p and q to
    # the same cell, the alias-PRIMARY carries `pointsTo` and the other carries
    # `aliasRef`; resolve aliases so we read the committed value for both names.
    var pointee = initTable[string, string]()
    for e in r.heapSnapshot:
      if e.pointsTo.isSome:
        pointee[e.name] = e.pointsTo.get
    for e in r.heapSnapshot:
      if e.aliasRef.isSome and pointee.hasKey(e.aliasRef.get):
        pointee[e.name] = pointee[e.aliasRef.get]
    # The try-body write `p[] = 7` AND the finally-before-raise write
    # `q[] = 99` are BOTH committed in the raised witness, surfaced by the
    # finally's read-back guard.
    check pointee.hasKey("p")
    check pointee.hasKey("q")
    check pointee["p"] == "7"
    check pointee["q"] == "99"
