## Phase 15 — Cluster R (FINAL cluster), cycle R13 / sub-track A:
## closures capturing `ref T` locals.
##
## This is pure CROSS-CLUSTER composition (Closures × Ref). Before R13 the
## C-cluster closure machinery could only capture PRIMITIVE locals — a `ref T`
## (or `ptr T`) free variable would have been classified `ceUnsupportedCapture`
## (closures couldn't capture refs before the heap existed). R13 lifts that:
## a closure may capture an `svRef`/`svPtr` free variable; its `envRecord`
## (svTuple) entry holds the captured ref's `svRef` SymVal — the SAME Z3 const
## the outer scope holds — and CALLING the closure derefs that captured ref
## through `path.heaps` exactly like any other `svRef` deref (the heap threads
## in via R1b's call-frame mechanism, which closure calls already use).
##
## SUT: a `ref int` local is `new`-allocated, written to 42 on the heap, then a
## closure captures it and — on being called — derefs the captured ref and sees
## the 42. The target is reachable, so the result is `sxSat`.
##
## DoD (RFC §R13 sub-track A):
##   1. `ceUnsupportedCapture` is no longer emitted for a `ref T`-capturing
##      closure (the verdict is a real `sxSat`, NOT `sxUnknown`).
##   2. The captured ref derefs through the heap and observes the write (42).
##
## R13 is ADDITIVE under walker version "10" (no bump; Cluster R bumped at R12).
## See ADR-0009 (closures), ADR-0010 (logical heap), RFC §R13.
import std/unittest
import proptest/symex

# A `ref int` local is new-allocated and written through the heap to 42. The
# closure captures the ref `x` (an svRef free variable); when called it derefs
# the captured ref through `path.heaps` and observes the stored 42, so the
# target is reachable → sxSat. Without R13 the capture is ceUnsupportedCapture
# → sxUnknown.
proc f() =
  var x = new int
  x[] = 42
  let capture = proc() =
    if x[] == 42:
      symexTarget("hit")
  capture()

suite "symex Phase 15 R13-A — closure capturing ref int local observes write through heap":

  test "R13-A: closure capturing ref int local observes write through heap":
    let r = symexFind(f, tLabel("hit"))
    check r.status == sxSat
