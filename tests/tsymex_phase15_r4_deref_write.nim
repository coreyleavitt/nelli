## Phase 15 — Cluster R (FINAL cluster), cycle R4: `p[] = v` heap WRITE (store).
##
## R4 promotes R3's `isDerefWrite` NO-OP stub to a real GROUND heap store:
##   `path.heaps[typeId] := Z3_mk_store(path.heaps[typeId], p, v)`
## The new heap array is the old one with `p` mapped to `v`; subsequent `select`
## reads on the SAME path see `v`, and reads through an ALIASED ref (same refSym)
## also see it (alias observability falls out of Z3's array theory — same index →
## same value). The store is GROUND (no universal-∀ over the uninterpreted Ref_T
## sort — the G4 MBQI hang lesson); confirmed NOT to hang.
##
## This makes the heap model REAL. Unlike R3 (where `p[] = 99; p[] == 99` was
## sxSat purely via the FREE heap — the write a no-op), R4 proves the write
## propagates via the sxUNSAT cases: the store FIXES the value, so reading a
## DIFFERENT value after the write is now UNSAT (impossible under the free heap,
## where the read could pick anything).
##
## DoD (RFC §R4 + reconciliation §F-R4):
##   1. Real read-after-write: `p[]=99; p[]==99` → sxSat AND the contradiction
##      `p[]=99; p[]==7` → sxUnsat (the store fixes the value — PROVES the write
##      propagates, unlike R3's free-heap pass).
##   2. Alias observability: `let q = p; p[]=5; q[]==5` → sxSat (write through p
##      observed through aliased q); `q[]==6` after `p[]=5` → sxUnsat.
##   3. Per-path isolation via write (DEFERRED from R1b/R3, now proven): write
##      through p on one forked branch; the other (unwritten) branch must NOT see
##      the update — its heap is the pre-write free one.
##
## See ADR-0010 (logical-heap model) and RFC §R4. R4 is ADDITIVE under walker
## version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

# --- DoD 1: real read-after-write ---------------------------------------------
# After `p[] = 99` the store fixes the heap value at `p` to 99. Reading 99 back
# is sxSat (read-your-own-write); reading 7 is sxUnsat (the store proved the
# value can ONLY be 99 — impossible under R3's free heap).
proc rawHit(p: ref int) =
  if p != nil:
    p[] = 99
    if p[] == 99:
      symexTarget("hit")

proc rawContradiction(p: ref int) =
  if p != nil:
    p[] = 99
    if p[] == 7:
      symexTarget("no")

# --- DoD 2: alias observability -----------------------------------------------
# `q = p` aliases the SAME ref const. A write through p stores at that const; a
# read through q selects the SAME index → sees the written value. Same-value
# read is sxSat; different-value read is sxUnsat (alias theory fixes it).
proc aliasObserve(p: ref int) =
  if p != nil:
    let q = p
    p[] = 5
    if q[] == 5:
      symexTarget("alias")

proc aliasContradiction(p: ref int) =
  if p != nil:
    let q = p
    p[] = 5
    if q[] == 6:
      symexTarget("noalias")

# --- DoD 3: per-path isolation via write --------------------------------------
# The write is on the c-true branch only. On c-true the read sees 5 (sxSat via
# the store). On c-false the read is the FREE/unwritten heap value (independently
# satisfiable). The branches are isolated: the unwritten branch's heap is the
# pre-write one. We probe each branch separately.
proc isoWritten(p: ref int, c: bool) =
  if p != nil:
    if c:
      p[] = 5
    if c and p[] == 5:           # c-true: read sees the store
      symexTarget("hitWritten")

proc isoUnwritten(p: ref int, c: bool) =
  if p != nil:
    if c:
      p[] = 5
    if (not c) and p[] == 99:    # c-false: free/unwritten heap — any value sat
      symexTarget("hitUnwritten")

# Isolation contradiction: on the c-true path the read is FIXED to 5 by the
# store, so reading a different value there is sxUnsat — the write did land on
# that branch and only that branch.
proc isoWrittenContradiction(p: ref int, c: bool) =
  if p != nil:
    if c:
      p[] = 5
    if c and p[] == 6:           # c-true: store fixed it to 5 → 6 is impossible
      symexTarget("noWritten")

suite "symex Phase 15 R4 — p[] = v heap store (alias-observable writes)":

  test "R4 test 1a: read-after-write p[]=99; p[]==99 is sxSat (via the store)":
    let r = symexFind(rawHit, tLabel("hit"))
    check r.status == sxSat

  test "R4 test 1b: p[]=99; p[]==7 is sxUnsat — the store FIXES the value (PROVES write propagates)":
    # This is the proof R3 could NOT give: under R3's no-op write the read picks
    # from the free heap and 7 is sat. Under R4's store the value is pinned to 99,
    # so 7 is UNSAT. The unsat verdict is what proves real read-after-write.
    let r = symexFind(rawContradiction, tLabel("no"))
    check r.status == sxUnsat

  test "R4 test 2a: alias write q=p; p[]=5; q[]==5 is sxSat (write through p seen through q)":
    let r = symexFind(aliasObserve, tLabel("alias"))
    check r.status == sxSat

  test "R4 test 2b: alias contradiction q=p; p[]=5; q[]==6 is sxUnsat (same index, fixed value)":
    let r = symexFind(aliasContradiction, tLabel("noalias"))
    check r.status == sxUnsat

  test "R4 test 3a: c-true branch read sees the store (p[]==5) → sxSat":
    let r = symexFind(isoWritten, tLabel("hitWritten"))
    check r.status == sxSat

  test "R4 test 3b: c-false (unwritten) branch reads the free heap → sxSat (isolated)":
    # The unwritten branch never had the store applied; its heap is the pre-write
    # free array, so any value (99) is satisfiable — independent of the c-true
    # branch's store. Proves per-path isolation of the write.
    let r = symexFind(isoUnwritten, tLabel("hitUnwritten"))
    check r.status == sxSat

  test "R4 test 3c: c-true store fixes p[]=5, so p[]==6 there is sxUnsat (write landed on that branch)":
    let r = symexFind(isoWrittenContradiction, tLabel("noWritten"))
    check r.status == sxUnsat
