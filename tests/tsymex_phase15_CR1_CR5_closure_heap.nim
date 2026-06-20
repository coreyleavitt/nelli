## Phase 15 — CR-1 (false UNSAT: closure heap write not merged to caller) and
## CR-5 (spurious aliasing: closure-body `new T` not distinct from caller refs).
##
## CR-1 (runtime.nim ~6144-6154, HIGH): a heap write `p[] = v` INSIDE a closure
## body is never merged back into the caller path.  After the closure body descent
## in `applyClosureGround` the exit paths carry the updated `heaps` array, but the
## stale comment "R4 inert" was wrong — R4 shipped.  The fix mirrors the
## named-proc return-merge (lines 5443-5463): thread `heaps`, `heapDepth`, and
## `allocCounters` (max-merge) from each closure exit path back to the continuing
## caller path.
##
## CR-5 (runtime.nim:6146, MEDIUM): the closure `descentBase` is built WITHOUT
## seeding `liveRefs`, so a `new T` inside the closure body calls `assertFreshness`
## against an EMPTY prior list — it never emits `newRef != callerRef`, letting Z3
## alias a closure-allocated ref with a caller ref.  The fix seeds
## `descentBase.liveRefs` from the caller path's `liveRefs` (exactly as
## `seedCallerHeapThreadvars` already threads `heaps`/`allocCounters`).
##
## RED → GREEN progression:
##   CR-1: before fix, `p[] == 99` after `m()` (which sets `p[] = 99`) is UNSAT
##         (caller heap stale).  After fix it is SAT.
##   CR-5: before fix, `p == q` where `q` is a closure-fresh `new int` and `p` is
##         a caller-fresh `new int` is SAT (Z3 can alias them).  After fix it is
##         UNSAT (the `new T` inside the closure emits `q != p`).
##
## Test naming mirrors the ledger: CR-1-* and CR-5-*.
import std/unittest
import proptest/symex

# ---------------------------------------------------------------------------
# CR-1 SUTs
# ---------------------------------------------------------------------------

# CR-1 test 1 (headline): a closure writes through a captured ref; the caller
# reads the ref AFTER the closure returns.  The write must be visible.
#
#   proc sut(p: ref int) =
#     let m = proc() = p[] = 99      # closure writes through captured ref
#     m()                             # call the closure
#     if p[] == 99:                   # caller reads the heap — must see 99
#       symexTarget("hit")
#
# Without CR-1 fix: caller heap is the PRE-CALL heap (p[] unconstrained from
# the caller's perspective) so p[]==99 is SAT from the free heap but the WRITE
# constraint was never merged → still SAT by coincidence in the free heap.
# The PROOF that the write merged is the contradiction: p[]==7 after m() is
# sxUnsat ONLY when the store propagates (analogous to R4 test 1b).
proc cr1WriteObserve(p: ref int) =
  let m = proc() = p[] = 99
  m()
  if p[] == 99:
    symexTarget("hit")

# CR-1 test 2 (proof by contradiction — mirrors R4 test 1b): after m() sets
# p[]=99, reading 7 is UNSAT iff the store propagated.  Without the fix the
# caller heap is stale (free), so 7 would be sxSat — the merge is what makes
# it sxUnsat.
proc cr1WriteContradiction(p: ref int) =
  let m = proc() = p[] = 99
  m()
  if p[] == 7:
    symexTarget("no")

# CR-1 test 3: a closure writes a different value from what the caller wrote
# before the call.  The write order is: caller sets p[]=5, closure sets p[]=99.
# After the closure call the caller reads p[] — should see 99 (last write wins).
proc cr1OverwriteObserve(p: ref int) =
  p[] = 5
  let m = proc() = p[] = 99
  m()
  if p[] == 99:
    symexTarget("hit")

# CR-1 test 4: the closure writes and the CONTRADICTION: after overwrite, the
# old value 5 is no longer readable (sxUnsat) — proves the closure write
# replaced the caller's earlier write.
proc cr1OverwriteContradiction(p: ref int) =
  p[] = 5
  let m = proc() = p[] = 99
  m()
  if p[] == 5:
    symexTarget("no")

# ---------------------------------------------------------------------------
# CR-5 SUTs
# ---------------------------------------------------------------------------

# CR-5 test 1 (headline): caller allocates `p = new int` (a fresh ref tracked
# in `path.liveRefs`); inside the closure, `q = new int` is also allocated.
# The two MUST be distinct — `p == q` should be UNREACHABLE (sxUnsat).
#
# Without CR-5 fix: `descentBase.liveRefs` is EMPTY (not seeded from caller),
# so `assertFreshness` for `q` doesn't emit `q != p`, and Z3 can alias them →
# the branch `p == q` inside the closure is reachable (false sxSat).
#
# After fix: `descentBase.liveRefs` is seeded from the caller path's `liveRefs`
# (which has `p` after the caller's `new int`), so `assertFreshness` for `q`
# emits `q != p` on the closure descent path → Z3 cannot alias them → sxUnsat.
#
# KEY: `p` must be allocated via `new int` (not a SUT param) so it ends up in
# `path.liveRefs` via `assertFreshness` — SUT params go through `allocateSym`
# which does NOT call `assertFreshness` and so don't populate `liveRefs`.
#
# NOTE: `symexTarget` is inside the closure body, so this test is INDEPENDENT
# of CR-1 (heap write propagation back to caller).
proc cr5ClosureNewDistinct() =
  let p = new int          # caller mints p; assertFreshness adds it to liveRefs
  let m = proc() =
    let q = new int        # closure mints q; assertFreshness should see p in liveRefs
    if p == q:             # p and q must be distinct
      symexTarget("alias") # reachable only if aliasing is permitted
  m()

suite "symex Phase 15 CR-1 + CR-5 — closure heap write merge + liveRefs seeding":

  # ---- CR-1: closure write visible to caller ----

  test "CR-1 test 1: closure write p[]=99 is visible to caller after m() (sxSat)":
    # After the fix the merged caller heap has p[]→99; the target is reachable.
    let r = symexFind(cr1WriteObserve, tLabel("hit"))
    check r.status == sxSat

  test "CR-1 test 2: after m() sets p[]=99, p[]==7 is sxUnsat (write merged — PROOF)":
    # This is the proof that the write propagated: the store pins p[] to 99, so
    # p[]==7 is UNSAT.  Without the merge the caller heap is free and 7 is SAT.
    let r = symexFind(cr1WriteContradiction, tLabel("no"))
    check r.status == sxUnsat

  test "CR-1 test 3: closure overwrite wins — caller reads 99 after p[]=5 then m() sets p[]=99":
    let r = symexFind(cr1OverwriteObserve, tLabel("hit"))
    check r.status == sxSat

  test "CR-1 test 4: after overwrite the old value 5 is gone — p[]==5 sxUnsat (PROOF)":
    let r = symexFind(cr1OverwriteContradiction, tLabel("no"))
    check r.status == sxUnsat

  # ---- CR-5: closure-body new T distinct from caller refs ----

  test "CR-5 test 1: closure-body new T is distinct from caller's new T (p==q inside closure is sxUnsat)":
    # p is minted by the caller's new int (liveRefs-tracked); q is minted
    # inside the lambda body.  With the liveRefs seed fix, assertFreshness for
    # q sees p in the seeded liveRefs and emits q != p → sxUnsat.
    let r = symexFind(cr5ClosureNewDistinct, tLabel("alias"))
    check r.status == sxUnsat
