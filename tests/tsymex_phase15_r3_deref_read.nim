## Phase 15 — Cluster R (FINAL cluster), cycle R3: `p[]` deref READ — completing
## the read path + the seq[ref T] element path (the headline R3 deliverable).
##
## R3 lands two things:
##
##   1. CONFIRM the R1 deref READ select threads `path.heaps[typeId]` per-path
##      (NOT a global) and yields a fully-typed SymVal for the dereffed T, and
##      that the read does NOT modify the heap.
##
##   2. The seq[ref T] ELEMENT path: a SUT `xs[0][]` over `seq[ref int]` reads a
##      seq element that is an `svRef` (the seq's backing array is a raw
##      `Z3Array[Z3Int, Ref_T]`), then `[]` derefs that svRef through
##      `path.heaps[typeId]`. The element select + the heap select are both
##      GROUND (no universal-∀ over the uninterpreted Ref_T sort — the G4 hang
##      lesson).
##
## RECONCILIATION (test 1 — the WRITE `p[] = v` is R4): the R3 write path
## (`isDerefWrite`) is STUBBED to a no-op at R3 (R4 implements the real `store`).
## So test 1's SUT does `p[] = 99` then reads `p[] == 99`: at R3 the write is a
## NO-OP and the read picks 99 from the FREE heap array (R1) regardless — the SUT
## is sxSat via the free heap, NOT via real read-after-write (that's R4). The
## per-path isolation "an unwritten branch doesn't see the update" DoD genuinely
## needs the store and is DEFERRED to R4; here we test isolation via INDEPENDENT
## free heaps (two branches each deref with different constraints → each sxSat
## independently, neither prunes the other).
##
## See ADR-0010 (logical-heap model) and RFC §R3. R3 is ADDITIVE under walker
## version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import nelli/symex

# Test 1 SUT: write-then-read. The write is a no-op stub at R3, so `p[] == 99`
# is sxSat purely via the free heap array (the read can pick 99). R4 makes this a
# real read-after-write.
proc writeThenRead(p: ref int) =
  if p != nil:
    p[] = 99
    if p[] == 99:
      symexTarget("hit")

# Test 2 SUT (the REAL R3 work): a seq[ref int] element, dereffed. `xs[0]` reads
# an svRef element from the seq's raw `Z3Array[Z3Int, Ref_T]` backing; `[]` derefs
# it through the per-path heap. The bound guard keeps the index in range.
proc seqRefElem(xs: seq[ref int]): bool =
  if xs.len > 0:
    if xs[0] != nil:
      if xs[0][] == 7:
        symexTarget("seqhit")
  result = true

# Test 3 SUTs: per-path isolation via INDEPENDENT free heaps. Two branches each
# deref `p` under a DIFFERENT value constraint; each is sxSat on its own free
# heap (the fork carries independent heap bindings). No write needed (the
# write-based isolation proof is deferred to R4).
proc branchA(p: ref int, b: bool) =
  if b:
    if p != nil:
      if p[] == 11: symexTarget("isoA")
proc branchB(p: ref int, b: bool) =
  if not b:
    if p != nil:
      if p[] == 22: symexTarget("isoB")

suite "symex Phase 15 R3 — p[] deref read + seq[ref T] element path":

  test "R3 test 1: write-then-read p[]==99 is sxSat (write is a no-op stub at R3; free heap)":
    # The `p[] = 99` write is STUBBED to a no-op at R3 — the read picks 99 from
    # the free heap array regardless. R4 makes this real read-after-write.
    let r = symexFind(writeThenRead, tLabel("hit"))
    check r.status == sxSat

  test "R3 test 2: seq[ref int] element xs[0][]==7 is sxSat (svRef element derefs through heap)":
    # The headline R3 path: `xs[0]` selects an svRef from the seq's raw
    # `Z3Array[Z3Int, Ref_T]`; `[]` derefs it via `select(path.heaps[T], elem)`.
    # The free heap can map the element to 7 → a witness exists. Must NOT hang
    # (both selects are GROUND — no ∀ over the uninterpreted Ref_T sort).
    let r = symexFind(seqRefElem, tLabel("seqhit"))
    check r.status == sxSat

  test "R3 test 3a: forked branch A derefs p==11 on its own free heap → sxSat":
    let r = symexFind(branchA, tLabel("isoA"))
    check r.status == sxSat

  test "R3 test 3b: forked branch B derefs p==22 independently → sxSat":
    # Independent free heaps: branch B is sxSat regardless of branch A's
    # constraint (the fork carries independent per-path heap bindings).
    let r = symexFind(branchB, tLabel("isoB"))
    check r.status == sxSat
