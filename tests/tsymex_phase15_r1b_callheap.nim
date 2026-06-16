## Phase 15 — Cluster R (FINAL cluster), cycle R1b: inter-procedural heap
## threading. At each `isCall`/`isGenericCall`/`iekClosureCall` call boundary
## the caller's logical-heap state must thread into the callee and the callee's
## exit heap must merge back out:
##
##   * Call ENTRY: the callee's initial path inherits the CALLER's `path.heaps`,
##     `path.heapDepth`, `path.allocCounters` (instead of R1's fresh-empty
##     default) — so a deref in the callee reads the SAME heap array the caller
##     already constrained.
##   * Call RETURN: the callee's exit `heaps` REPLACE the caller's (callee heap
##     modifications are observed); `allocCounters` merge by `max(caller, callee)`
##     per type key (freshness preserved — post-call caller allocs can't collide
##     with callee-allocated refs); `heapDepth` threads back.
##
## ── TEST RECONCILIATION (no-write approach (a)) ──────────────────────────────
## RFC §R1b's literal SUT does `p[] = 7` (a heap WRITE → `store`), but heap
## WRITES are cycle R4, NOT yet implemented (R1 only did the deref/select READ).
## So the RFC SUT cannot pass at R1b without pulling R4 forward. We instead
## prove threading WITHOUT a write, using the SAME-REF deref consistency that
## R1 already gives us:
##
##   * POSITIVE: the caller deref-constrains `p[] == 7`, then the callee
##     `inner(p)` reads `q[] == 7` on the SAME threaded heap → consistent → sxSat.
##   * NEGATIVE (the actual THREADING PROOF): the caller constrains `p[] == 7`,
##     then `inner2(p)` reads `q[] == 8` on the same threaded heap → the one
##     threaded heap cannot map `p` to both 7 and 8 → sxUnsat. WITHOUT R1b
##     threading the callee would get a FRESH empty heap, `q[]` would be
##     unconstrained, and the conjunction would be sxSat — so the sxUnsat verdict
##     is what PROVES the heap is genuinely threaded across the call boundary.
##
## See ADR-0010 (logical-heap model) and RFC §R1b. R1b is ADDITIVE under walker
## version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

# ── POSITIVE: caller and callee deref the SAME ref into the SAME threaded heap,
#    both expecting 7 → consistent → sxSat. ────────────────────────────────────
proc inner(q: ref int): bool = q[] == 7

proc f(p: ref int) =
  if p[] == 7 and inner(p):
    symexTarget("hit")

# ── NEGATIVE (threading proof): caller constrains heap[p]==7, callee reads
#    heap[p]==8 on the SAME threaded heap → unsat. Unthreaded this would be sat,
#    so sxUnsat proves the heap crosses the call boundary. ──────────────────────
proc inner2(q: ref int): bool = q[] == 8

proc g(p: ref int) =
  if p[] == 7 and inner2(p):
    symexTarget("clash")

suite "symex Phase 15 R1b — inter-procedural heap threading":

  test "R1b: caller deref-constraint observed by callee reading the SAME threaded ref":
    # Threaded heap: heap[p] == 7 set in the caller, read again as 7 in `inner` —
    # consistent. Reaches the target → sxSat.
    let r = symexFind(f, tLabel("hit"))
    check r.status == sxSat

  test "R1b: contradictory caller/callee derefs on the threaded heap are unsat (THREADING PROOF)":
    # heap[p] == 7 (caller) and heap[p] == 8 (callee `inner2`) over the SAME
    # threaded heap is unsatisfiable. WITHOUT R1b threading the callee would see
    # a fresh empty heap and this would be sxSat — so sxUnsat PROVES the heap is
    # threaded across the call boundary.
    let r = symexFind(g, tLabel("clash"))
    check r.status == sxUnsat
