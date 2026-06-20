## Phase 15 — Cluster R (FINAL cluster), cycle R13 / sub-track B:
## `ptr T` + `try`/`finally` composition (Feas-H4 fold, deferred from E7).
##
## This is pure CROSS-CLUSTER composition (Ptr × Exceptions). It composes
## EXISTING machinery: E5's finally threading (finally runs on EVERY exit
## continuation of the try body) + R4/R8's ptr deref/store through `path.heaps`.
## It was moved out of E7 because `isDeref` did not exist until R1 — `path.heaps`
## had to become LIVE (Cluster R) before a `ptr T`-typed `p[]` could thread
## through the try/finally exit continuations.
##
## SUT: `proc f(p: ptr int) = (try: p[] = 7; finally: if p[] == 7: raise ...)`.
## The try body stores 7 at `p` on the heap; the finally — which E5 runs on the
## normal exit continuation — derefs the SAME heap cell, observes the 7, and
## raises ValueError. Because the heap state threads through the try/finally exit
## continuation (E5 mechanism) WITH a `ptr T` param, the finally's `p[] == 7`
## condition is satisfied and the result is `sxRaised(ValueError)` with the heap
## committing to `p[] == 7`.
##
## DoD (RFC §R13 sub-track B):
##   1. `sxRaised(ValueError)` (the finally's raise propagates out).
##   2. The heap witness commits to `p[] == 7` (the store threaded through the
##      finally exit continuation — visible in the heapSnapshot pointee).
##
## R13 is ADDITIVE under walker version "10" (no bump; Cluster R bumped at R12).
## See ADR-0010 (logical heap), §F-E (E5 finally), RFC §R13.
import std/unittest
import proptest/symex

# The try body writes 7 to the heap cell `p` points at. E5 runs the finally on
# the normal exit continuation of the try body; the finally derefs the SAME heap
# cell (the store threaded through), sees 7, and raises ValueError — so the
# result is sxRaised(ValueError) with the heap committing to p[] == 7.
proc f(p: ptr int) =
  try:
    p[] = 7
  finally:
    if p[] == 7:
      raise newException(ValueError, "written")

suite "symex Phase 15 R13-B — ptr T + try/finally composition":

  test "R13-B: ptr T + try/finally composition produces sxRaised(ValueError) with witness p[]==7":
    let r = symexFind(f, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    # The heap state threaded through the try/finally exit continuation: the
    # store landed before the finally's deref, so the heap commits to p[] == 7.
    # Surfaced in the v3 heap-snapshot witness (one entry for the ptr param p).
    check r.heapSnapshot.len == 1
    let e = r.heapSnapshot[0]
    check e.name == "p"
    check e.value != "nil"
    check e.pointsTo.isSome
    check e.pointsTo.get == "7"
