## Phase 15 — Cluster R (FINAL cluster), cycle R2: `new T` allocation semantics.
## Implements the `of isNew:` walker branch (replacing R1a's structural stub):
##
##   * `freshRef(ctx, sort, typeId, path)` increments `path.allocCounters[typeId]`
##     (per-path; R1b already threads/max-merges it across calls) and derives a
##     FRESH `Ref_T`-sorted Z3 const named `"ref_<typeId>_<n>"` (n = the new
##     counter value) via raw `Z3_mk_const` (the G4 raw-const discipline). The
##     const is bound in the walker env under the `isNew` let-name.
##   * `assertFreshness(ctx, path, newRef, liveRefs)` asserts into `path.pc`:
##       - `newRef != nilConst(Ref_T)` (a freshly allocated ref is never nil);
##       - `newRef != prior` for EVERY prior LIVE ref of this sort on THIS path
##         (the counter-based distinctness guarantee).
##     All GROUND inequalities (no universal-∀ over the uninterpreted ref sort —
##     the G4 MBQI hang lesson). The prior live refs are tracked per-path in
##     `path.liveRefs[typeId]` (deep-copied at every fork — so disjoint forked
##     paths do NOT share them).
##   * CAP: if the count of freshness assertions already on this path would
##     exceed `settings.maxFreshnessAssertions` (default 256; 0 = unlimited), a
##     `heFreshnessCapExceeded` (sevHint) is emitted and the new inequality is
##     SKIPPED — a SOUND over-approximation (Z3 may allow aliasing beyond the
##     cap; never a false UNSAT).
##
## See ADR-0010 (logical-heap model) and RFC §R2. R2 is ADDITIVE under walker
## version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

# A SMALL freshness cap (3) so the cap test can exercise the over-cap path with
# only 5 allocations. `symexFind`'s `settings` is `static`, so this must be a
# `const` (the `withSymexSettings` builder folds at compile time).
const lowFreshCap = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxFreshnessAssertions = 3

# ── Test 1 (the headline DoD): two `new T` allocations are provably distinct.
#    `let p = new int; let q = new int; if p == q` — the two fresh refs carry
#    `p != q` on the path condition, so the `p == q` branch is UNREACHABLE. ──────
proc twoNewsAlias() =
  let p = new int
  let q = new int
  if p == q:
    symexTarget("alias")

# ── Test 2 (disjoint-path counter isolation): two `new T` on DISJOINT forked
#    branches. Each branch independently allocates `ref_int_1` (the counter is
#    snapshotted at the fork, NOT shared) — so neither branch carries a
#    cross-path `ref_int_1 != <other branch's ref>` constraint. We observe this
#    via the SAT-reachable target on EACH branch: a branch-local `new int` whose
#    deref equals a branch-specific value is reachable on both arms (no spurious
#    cross-path contradiction prunes either). ──────────────────────────────────
proc disjointNews(b: bool) =
  if b:
    let p = new int
    if p[] == 1:
      symexTarget("armA")
  else:
    let q = new int
    if q[] == 2:
      symexTarget("armB")

# ── Test 3 (the cap): five `new int` on ONE path under a maxFreshnessAssertions
#    cap of 3. The over-cap allocations stop emitting distinctness inequalities
#    and a `heFreshnessCapExceeded` hint rides the verdict. The path stays SOUND
#    (no crash, no false UNSAT): the target behind a TRUE-by-construction guard
#    is still reachable (sxSat). ────────────────────────────────────────────────
proc manyNews() =
  let a = new int
  let b = new int
  let c = new int
  let d = new int
  let e = new int
  # Use all five so none is dead-code-eliminated; the guard is satisfiable.
  if a[] == 0 or b[] == 0 or c[] == 0 or d[] == 0 or e[] == 0:
    symexTarget("capped")

suite "symex Phase 15 R2 — `new T` allocation (fresh-ref distinctness + cap)":

  test "R2: two new T allocations produce non-equal refs on sat path":
    # `freshRef` mints `ref_int_1` for p and `ref_int_2` for q; `assertFreshness`
    # adds `q != p` (a GROUND inequality) to the path. So `p == q` is provably
    # false → the branch is unreachable → sxUnsat.
    let r = symexFind(twoNewsAlias, tLabel("alias"))
    check r.status == sxUnsat

  test "R2: disjoint forked paths do not share fresh-ref counters (armA reachable)":
    # Arm A allocates its own `ref_int_1` and reads `p[] == 1`; the heap is free,
    # so this is reachable. No constraint from arm B's allocation leaks here.
    let rA = symexFind(disjointNews, tLabel("armA"))
    check rA.status == sxSat

  test "R2: disjoint forked paths do not share fresh-ref counters (armB reachable)":
    # Symmetrically, arm B allocates its own `ref_int_1` (counter RESTARTED from
    # the fork snapshot — NOT continued from arm A) and reads `q[] == 2`.
    let rB = symexFind(disjointNews, tLabel("armB"))
    check rB.status == sxSat

  test "R2: over-cap allocations stay sound (no crash, no false UNSAT)":
    # Cap freshness at 3, then allocate 5 refs on one path. The over-cap allocs
    # skip their distinctness inequalities (a `heFreshnessCapExceeded` hint is
    # emitted), but the path is still sound: the satisfiable target is reachable.
    let r = symexFind(manyNews, tLabel("capped"), lowFreshCap)
    check r.status == sxSat
    # The hint must surface on the verdict (sevHint, never changes the verdict).
    var sawCapHint = false
    for e in r.errors:
      if e.kind == heFreshnessCapExceeded: sawCapHint = true
    check sawCapHint
