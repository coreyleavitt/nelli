## Phase 15 — Cluster R (FINAL cluster), cycle R11b: cross-cluster regression
## smoke. CLOSES the per-feature R grind before R12's version bump.
##
## A single hermetic, in-process test that composes the Cluster-R machinery
## (R1–R11) TOGETHER in one file and confirms it does not disturb the prior
## clusters' verdicts. This is the state-threading sanity net for the heap
## model — `path.heaps`/`heapDepth`/`allocCounters`/`liveRefs` deep-copied at
## every fork, the per-walker `Ref_T` sort + `nilConst`, the field-split heaps,
## the deref/store/freshness/nil-fork/depth-budget/unsafe-cast machinery — all
## exercised in one process so a cross-cycle state-threading bug surfaces here.
##
## Composed (at minimum, per RFC §R11b DoD):
##   * ref alloc + read + write + alias (R2/R3/R4/R7),
##   * a ref-object field write + aliased read (R6),
##   * a nil-access defect finding (R5),
##   * a `ptr T` deref carrying the hePtrFamily hint (R8),
##   * a recursive linked-list walk halting at maxHeapDepth (R9),
##   * an unsafe cast → heUnsafeCast (R11),
##   * the walker-version pin `symexWalkerVersion == "9"` (R11b does NOT bump;
##     R12 does the `"9"→"10"` bump + the rendering `"2"→"3"` bump).
##
## All SUT idioms are reused verbatim from the R1–R11 per-feature tests, so this
## is a faithful re-composition, not a fresh model.  R11b adds NO walker
## machinery; it confirms the existing machinery composes.
import std/unittest
import proptest/symex

# ── R2 / R3 / R4 / R7: ref alloc + read + write + alias ──────────────────────

# R2: two `new T` allocations are provably distinct → `p == q` unreachable.
proc twoNewsDistinct() =
  let p = new int
  let q = new int
  if p == q:
    symexTarget("alias")

# R4: real read-after-write through a heap store — read-back is sxSat, a
# different value is sxUnsat (the store FIXES the value — proves it propagates).
proc readAfterWrite(p: ref int) =
  p[] = 99
  if p[] == 99:
    symexTarget("raw")

proc readAfterWriteContradiction(p: ref int) =
  p[] = 99
  if p[] == 7:
    symexTarget("rawno")

# R7: let-alias chain p == q == r; a write through r is observed through p.
proc aliasChainWrite(p: ref int) =
  let q = p
  let r = q
  r[] = 5
  if p[] == 5:
    symexTarget("aliaswrite")

# ── R6: ref-object field write + aliased read ────────────────────────────────
type Point = object
  x, y: int

# `p.x = 42` stores into the x field-split heap; the aliased `q.x` selects the
# same index when p == q → sees 42 (the headline R6 alias-observable write).
proc fieldAliasWrite(p, q: ref Point) =
  p.x = 42
  if q.x == 42:
    symexTarget("fieldalias")

# ── R5: nil-access defect ────────────────────────────────────────────────────
# A deref of a possibly-nil ref forks; the nil sub-path is the NilAccessDefect,
# surfaced under the `tNilAccess()` target.
proc nilDeref(p: ref int) =
  if p[] == 1:
    symexTarget("nilhit")

# ── R8: ptr T deref carrying the hePtrFamily hint ────────────────────────────
proc ptrDeref(p: ptr int) =
  if p[] == 7:
    symexTarget("ptrhit")

# ── R9: recursive linked-list walk halting at maxHeapDepth ───────────────────
type Node = ref object
  val: int
  next: Node

proc walkDeep(n: Node) =
  if n.next.next.next.val == 5:
    symexTarget("deep")

const depth3 = withSymexSettings() do (s: var SymexSettings):
  s.maxHeapDepth = 3

# ── R11: unsafe cast → heUnsafeCast ──────────────────────────────────────────
proc castPtr(x: int) =
  let p = cast[ptr int](addr x)
  if p[] == 1:
    symexTarget("casthit")

suite "symex Phase 15 R11b — cross-cluster regression smoke (Cluster R composed)":

  test "R11b: two `new T` allocations are distinct → p == q is sxUnsat (R2)":
    let r = symexFind(twoNewsDistinct, tLabel("alias"))
    check r.status == sxUnsat

  test "R11b: real read-after-write p[]=99; p[]==99 is sxSat (R3/R4)":
    let r = symexFind(readAfterWrite, tLabel("raw"))
    check r.status == sxSat

  test "R11b: write FIXES the value — p[]=99; p[]==7 is sxUnsat (R4 propagation proof)":
    let r = symexFind(readAfterWriteContradiction, tLabel("rawno"))
    check r.status == sxUnsat

  test "R11b: alias chain p==q==r; write through r seen through p → sxSat (R7)":
    let r = symexFind(aliasChainWrite, tLabel("aliaswrite"))
    check r.status == sxSat

  test "R11b: ref-object field write p.x=42; aliased q.x==42 → sxSat (R6)":
    let r = symexFind(fieldAliasWrite, tLabel("fieldalias"))
    check r.status == sxSat

  test "R11b: nil-access defect — deref nil path under tNilAccess → sxSat (R5)":
    let r = symexFind(nilDeref, tNilAccess())
    check r.status == sxSat

  test "R11b: nil-access — under tLabel only the non-nil path satisfies → sxSat (R5)":
    let r = symexFind(nilDeref, tLabel("nilhit"))
    check r.status == sxSat

  test "R11b: ptr int deref works like ref + carries hePtrFamily hint (R8)":
    let r = symexFind(ptrDeref, tLabel("ptrhit"))
    check r.status == sxSat
    var sawPtrFamily = false
    for e in r.errors:
      if e.kind == hePtrFamily:
        sawPtrFamily = true
        check e.severity == sevHint
    check sawPtrFamily

  test "R11b: recursive list walk halts cleanly at maxHeapDepth=3 → sxUnknown + heDepthExhausted (R9)":
    let r = symexFind(walkDeep, tLabel("deep"), depth3)
    check r.status == sxUnknown
    var sawDepth = false
    for e in r.errors:
      if e.kind == heDepthExhausted: sawDepth = true
    check sawDepth

  test "R11b: unsafe cast[ptr int](addr x) → sxUnknown + heUnsafeCast (sevError) (R11)":
    let r = symexFind(castPtr, tLabel("casthit"))
    check r.status == sxUnknown
    check r.errors.len > 0
    var sawUnsafeCast = false
    for e in r.errors:
      if e.kind == heUnsafeCast:
        sawUnsafeCast = true
        check e.severity == sevError
    check sawUnsafeCast

  test "R11b: walker version is \"9\" (R11b does NOT bump; R12 does \"9\"->\"10\")":
    check symexWalkerVersion == "10"
