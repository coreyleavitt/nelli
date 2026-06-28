## Phase 15 re-review drain-consolidation tests.
##
## Six finding clusters from the post-CR-1/CR-3 re-review, all rooted in
## `drainClosureExitHeap`/`drainConvFloatToIntBounds` applied ad-hoc in only
## a subset of walk arms.  Root fix: a single `drainPendingLowerEffects(p)`
## helper that drains BOTH sinks + resets ALL associated threadvars.
##
## S-1  HIGH  spurious aliasing: liveRefs union-merge drops equal-length arms
## S-2  HIGH  false UNSAT/SAT: drain missing in isAssert / isWhile arms
## NI-1 MED   stale exit heap across elif: no per-branch threadvar reset
## NI-2 MED   bogus witness: drainConvFloatToIntBounds missing in isDerefWrite
## S-3  MED   heap mutation lost when closure passed as a named-proc arg
## S-4  MED   isReturn retExpr: no seed+drain around lower(retExpr)
##
## RED phase: tests below FAIL (for the right reason) before the fixes.

import std/[unittest, sequtils]
import proptest/symex

# ============================================================================
# S-1: liveRefs union-merge drops equal-length arms → false SAT aliasing
# ============================================================================
#
# Bug: applyClosureGround merges multi-exit-path liveRefs with:
#   if refs.len > merged[tkey].len: merged[tkey] = refs
# When two exit paths carry EQUAL-LENGTH lists (one new T on each arm),
# the second arm's ref is silently dropped.  A caller new T after the closure
# call is only asserted distinct from the KEPT arm's ref, not the dropped one.
# Z3 may then alias the caller ref with the dropped ref → false SAT.
#
# For a minimal reproducible test we need the dropped ref to be REACHABLE
# by the caller, which requires the closure to store it somewhere.  Because
# the engine does not support closure returning ref T, we detect the bug
# indirectly via the freshness-assertion count: BOTH closure refs must end
# up in liveRefs so a later new T emits TWO distinctness inequalities.
#
# FINDING NOTE: constructing a black-box failing test requires the closure
# to export the dropped ref somehow (via captured ref-to-ref or similar),
# which the engine does not yet support.  The tests below verify the CORRECT
# post-fix behaviour (the union is maintained); they do NOT produce a RED
# failure before the fix in the current test infrastructure.  This finding
# is recorded as "confirmed by code inspection; test cannot falsify with
# current API — see implementation audit in runtime.nim:6481-6484."
# The fix (true set-union) is applied unconditionally.

proc s1BranchNewDistinctFromCaller(cond: bool) =
  ## Caller mints callerRef before the closure. Closure branches and mints
  ## exactly one new int per arm (p on arm T, q on arm F). After the closure,
  ## the caller checks that callerRef != the ref minted inside the chosen arm.
  ## NOTE: the closure's locally-minted refs are NOT directly accessible to
  ## the caller (they are local to the body), so this tests the CR-5 seeding
  ## path rather than the S-1 union-merge path.
  let callerRef = new int
  callerRef[] = 77
  let m = proc() =
    if cond:
      let p = new int
      if callerRef == p:
        symexTarget("s1AliasArm1")  # must be sxUnsat: callerRef seeded ≠ p
    else:
      let q = new int
      if callerRef == q:
        symexTarget("s1AliasArm2")  # must be sxUnsat: callerRef seeded ≠ q
  m()

# ============================================================================
# S-2: isAssert and isWhile missing seed + drain
# ============================================================================
#
# Bug A — isAssert: `symexAssert(writeAndReturn())` where writeAndReturn is a
# closure that writes p[]=99 and returns true.  The `isAssert` arm calls
# `lowerBool(p0.env, stmt.acond)` WITHOUT first calling
# `seedCallerHeapThreadvars(p0)` and WITHOUT calling `drainClosureExitHeap`
# after.  The closure body descends with stale/empty heap threadvars and the
# heap write is never propagated back → false UNSAT for `p[]==99` after the
# assert.
#
# Bug B — isWhile: same pattern in the while-guard loop: `seedCallerHeapThreadvars`
# is never called, so a heap-mutating closure used as the while condition loses
# its write.
#
# RED tests: these fail BEFORE the fix.

# S-2 SUT A: symexAssert with a heap-writing closure as the condition.
# symexAssert generates `isAssert` IR (not `isIf` like Nim's builtin assert).
proc s2AssertPredicateClosure(p: ref int) =
  ## symexAssert predicate is a closure that writes p[]=99 and returns true.
  ## After the assert, p[]==99 must be reachable (sxSat).
  ## Without seed+drain in isAssert: closure descends with stale heap
  ## threadvars, write is lost → false UNSAT.
  if p != nil:
    let writeAndReturn = proc(): bool =
      p[] = 99
      return true
    symexAssert(writeAndReturn())
    if p[] == 99:
      symexTarget("s2AssertHit")

proc s2AssertContradiction(p: ref int) =
  ## Proof: after symexAssert(<writes p[]=99>), p[]==7 is sxUnsat.
  ## Without fix: heap stale → 7 is sxSat (false SAT).
  if p != nil:
    let writeAndReturn = proc(): bool =
      p[] = 99
      return true
    symexAssert(writeAndReturn())
    if p[] == 7:
      symexTarget("s2AssertNoHit")

# S-2 SUT B: while guard with a heap-writing closure.
# The while guard is a closure that writes p[]=55 and returns false (so the
# loop body never executes and exits immediately).  After the loop, p[]==55
# must be reachable.
proc s2WhileGuardClosure(p: ref int) =
  ## while cond() executes the guard once; cond writes p[]=55 and returns false.
  ## After the while, p[]==55 must be reachable (sxSat).
  ## Without seed+drain in isWhile: write lost → false UNSAT.
  if p != nil:
    let writeAndExit = proc(): bool =
      p[] = 55
      return false
    while writeAndExit():
      discard
    if p[] == 55:
      symexTarget("s2WhileHit")

proc s2WhileContradiction(p: ref int) =
  ## Proof: after while guard writes p[]=55, p[]==7 is sxUnsat.
  ## Without fix: false SAT.
  if p != nil:
    let writeAndExit = proc(): bool =
      p[] = 55
      return false
    while writeAndExit():
      discard
    if p[] == 7:
      symexTarget("s2WhileNoHit")

# ============================================================================
# NI-1: isIf no per-branch reset → stale exit heap bleeds across elif
# ============================================================================
#
# Bug: `seedCallerHeapThreadvars(p)` is called ONCE before the branch loop;
# closure-exit threadvars are NOT reset per-branch.  Branch 0's exit heap
# (from clo1 writing p[]=11) bleeds into branch 1 (the elif where clo2 runs).
# On the elif-taken path: the exit heap carries BOTH clo1's write (p[]=11)
# AND clo2's write (p[]=22), making p[]==11 falsely SAT on the elif path.
#
# Fix: inside the branch loop, reset exit-heap threadvars and re-seed from
# the CURRENT path cp (post-drain) before each lowerBool call.

proc ni1ElifNoStale(p: ref int) =
  ## clo1 writes p[]=11 and returns false; clo2 writes p[]=22 and returns true.
  ## On the elif path (clo1 false, clo2 true): p[]==22 is sxSat, p[]==11 is sxUnsat.
  if p != nil:
    let clo1 = proc(): bool =
      p[] = 11
      return false
    let clo2 = proc(): bool =
      p[] = 22
      return true
    if clo1():
      symexTarget("ni1IfBranch")     # unreachable (clo1 always returns false)
    elif clo2():
      if p[] == 22:
        symexTarget("ni1ElifHit")    # sxSat: clo2 wrote p[]=22 on this path
      if p[] == 11:
        symexTarget("ni1ElifStale")  # sxUnsat AFTER fix; sxSat BEFORE (stale bleed)

proc ni1ElifContradiction(p: ref int) =
  ## Proof: p[]==11 from clo1 must NOT be visible on the elif path.
  if p != nil:
    let clo1 = proc(): bool =
      p[] = 11
      return false
    let clo2 = proc(): bool =
      p[] = 22
      return true
    if clo1():
      discard
    elif clo2():
      if p[] == 11:
        symexTarget("ni1Contradiction")  # sxUnsat AFTER fix; sxSat BEFORE

# ============================================================================
# NI-2: isDerefWrite missing drainConvFloatToIntBounds → stale/lost domain bounds
# ============================================================================
#
# Bug: `lower(cp.env, stmt.dwValue, some(proto))` inside isDerefWrite may
# deposit float→int domain bounds in `convFloatToIntBoundConds`, but
# `drainConvFloatToIntBounds` is never called.  The bounds are either:
#   (a) silently discarded when the next isIf/isLet resets the sink, OR
#   (b) they cause a sort mismatch (svInt Z3Int stored into a BV64 heap)
#       yielding sxUnsat when the target should be sxSat.
#
# Fix: reset `convFloatToIntBoundConds = @[]` before `lower(stmt.dwValue)`
# and call `drainConvFloatToIntBounds(cp)` after the store (using the
# consolidated `drainPendingLowerEffects` helper).
#
# Also: `isVariantReassignSymbolic` (vrsRhs) and `isIndex` (array index
# with int(f)) have the same missing drain — covered by the uniform audit.

proc ni2DerefWriteFloatConv(x: float, p: ref int) =
  ## p[] = int(x): the float→int domain bound on x must be applied.
  ## The target checks p[] == 3 (sxSat when x=3.0).
  ## Before fix: sort mismatch (svInt into BV64 heap) → sxUnsat (false UNSAT).
  ## After fix: bound applied, store uses BV64-rounded value → sxSat.
  if p != nil:
    p[] = int(x)
    if p[] == 3:
      symexTarget("ni2DerefHit")

proc ni2DerefWriteNanExcluded(x: float, p: ref int) =
  ## NaN float in deref-write: int(NaN) is undefined. After fix the domain
  ## bound excludes NaN → path is sxUnsat when x == NaN (symbolic input).
  ## Before fix: bound not applied → sxUnknown (no domain constraint on x).
  ## After fix: x ∈ [low(int64)..high(int64)] excludes NaN → sxUnsat.
  ## NOTE: `x != x` is the inline IEEE NaN test (avoids a nested proc which
  ## would be isUnsupported and set sawUnknown regardless).
  if p != nil:
    if x != x:    # inline NaN test: only true when x is NaN
      p[] = int(x)
      if p[] == 3:
        symexTarget("ni2NanHit")  # sxUnsat AFTER fix

# ============================================================================
# S-3: isCall arg-lowering: drainClosureExitHeap missing after arg lower
# ============================================================================
#
# Bug: in `isCall`, `seedCallerHeapThreadvars(p)` IS called and
# `drainConvFloatToIntBounds(p)` IS called after arg lowering, but
# `drainClosureExitHeap` is NOT called.  A closure call in an argument
# position that writes through the heap has its mutation silently dropped.
#
# Fix: call `drainClosureExitHeap(p)` (or the consolidated helper) after
# the arg-lowering loop, before building the callee env.
#
# NOTE: `use` is defined at TOP LEVEL (not inside the SUT) to avoid a nested
# `nnkProcDef` statement in the SUT body, which would emit `isUnsupported`
# (nested proc defs in statement position are not in the supported fragment)
# and set `sawUnknown = true` regardless of the fix.

proc s3UseHelper(v: int) =
  ## Top-level helper for S-3 SUT: consumes its int arg and returns.
  discard v

proc s3CallArgClosure(p: ref int) =
  ## Named proc s3UseHelper() called with s3UseHelper(cloWrite()) where
  ## cloWrite writes p[]=99.  After the call, p[]==99 must be sxSat.
  ## Without fix: heap mutation from the closure arg is lost → false UNSAT.
  if p != nil:
    let cloWrite = proc(): int =
      p[] = 99
      return p[]
    s3UseHelper(cloWrite())
    if p[] == 99:
      symexTarget("s3Hit")

proc s3CallArgContradiction(p: ref int) =
  ## Proof: after s3UseHelper(cloWrite()) fixing p[]=99, reading p[]==7 is sxUnsat.
  ## Without fix: stale heap → 7 is sxSat (false SAT).
  if p != nil:
    let cloWrite = proc(): int =
      p[] = 99
      return p[]
    s3UseHelper(cloWrite())
    if p[] == 7:
      symexTarget("s3NoHit")

# ============================================================================
# S-4: isReturn retExpr: no seedCallerHeapThreadvars + no drainClosureExitHeap
# ============================================================================
#
# Bug: in `isReturn`, `lower(p.env, stmt.retExpr)` is called WITHOUT first
# calling `seedCallerHeapThreadvars(p)` (closure in retExpr descends with
# stale/empty caller-heap threadvars) and WITHOUT calling
# `drainClosureExitHeap` after (closure write dropped).
#
# Fix: add `seedCallerHeapThreadvars(p)` before `lower(retExpr)` and
# `drainClosureExitHeap(p)` after (using the consolidated helper).

proc s4ReturnClosure(p: ref int): int =
  ## Returns result of closure that also writes p[]=55.
  if p != nil:
    let writeAndGet = proc(): int =
      p[] = 55
      return p[]
    return writeAndGet()

proc s4Caller(p: ref int) =
  ## Calls s4ReturnClosure; write p[]=55 must be visible after the call.
  ## Without fix: no seed → empty heap threadvars; no drain → write dropped.
  if p != nil:
    let _ = s4ReturnClosure(p)
    if p[] == 55:
      symexTarget("s4Hit")

proc s4CallerContradiction(p: ref int) =
  ## Proof: after s4ReturnClosure sets p[]=55, p[]==7 is sxUnsat.
  ## Without fix: stale heap → 7 is sxSat (false SAT).
  if p != nil:
    let _ = s4ReturnClosure(p)
    if p[] == 7:
      symexTarget("s4NoHit")

# ============================================================================
# Suites
# ============================================================================

suite "symex Phase 15 re-review S-1: liveRefs union-merge":
  ## S-1 cannot be triggered in a black-box test with the current engine API
  ## (closure-body refs are not directly accessible to the caller after return).
  ## The tests below exercise the CR-5 liveRefs seeding path (caller ref seeded
  ## before closure, closure-body new T must be distinct) and will pass both
  ## before AND after the fix — confirming CR-5 is unaffected.
  ## The fix (true set-union in applyClosureGround) is verified by inspection
  ## and by the absence of regression in CR-5 tests.

  test "S-1-arm1: callerRef seeded before closure; arm-T new int is distinct (sxUnsat)":
    let r = symexFind(s1BranchNewDistinctFromCaller, tLabel("s1AliasArm1"))
    check r.status == sxUnsat

  test "S-1-arm2: callerRef seeded before closure; arm-F new int is distinct (sxUnsat)":
    let r = symexFind(s1BranchNewDistinctFromCaller, tLabel("s1AliasArm2"))
    check r.status == sxUnsat

suite "symex Phase 15 re-review S-2a: isAssert missing seed+drain":

  test "S-2a-1: symexAssert predicate closure write p[]=99 visible after assert (sxSat)":
    ## RED test: before fix, isAssert has no seedCallerHeapThreadvars/drainClosureExitHeap
    ## → write lost → sxUnsat or sxUnknown (false). After fix: sxSat.
    let r = symexFind(s2AssertPredicateClosure, tLabel("s2AssertHit"))
    check r.status == sxSat

  test "S-2a-2: symexAssert predicate write proof: p[]==7 after p[]=99 is sxUnsat":
    ## RED test: without fix, heap is stale/free → 7 is sxSat (false SAT).
    ## After fix: write fixed to 99 → 7 is sxUnsat.
    let r = symexFind(s2AssertContradiction, tLabel("s2AssertNoHit"))
    check r.status == sxUnsat

suite "symex Phase 15 re-review S-2b: isWhile missing seed+drain":

  test "S-2b-1: while guard closure write p[]=55 visible after loop (sxSat)":
    ## RED test: isWhile has no seedCallerHeapThreadvars → write lost → false UNSAT.
    ## After fix: sxSat.
    let r = symexFind(s2WhileGuardClosure, tLabel("s2WhileHit"))
    check r.status == sxSat

  test "S-2b-2: while guard write proof: p[]==7 after p[]=55 is NOT sxSat":
    ## RED test: without fix, stale/free heap → p[]==7 is sxSat (false SAT).
    ## After fix: heap correctly has p[]=55 → p[]==7 is UNSAT.
    ## NOTE: sxUnknown is acceptable here because the while-loop unrolling
    ## exhausts the maxLoopUnwind limit (dead truePaths from iter 0 propagate
    ## to iter 1..4), and the "still active after unwind" arm sets sawUnknown.
    ## The RED→GREEN signal is: before fix = sxSat; after fix = NOT sxSat.
    let r = symexFind(s2WhileContradiction, tLabel("s2WhileNoHit"))
    check r.status != sxSat

suite "symex Phase 15 re-review NI-1: per-branch reset in isIf elif":

  test "NI-1-1: elif branch sees clo2 write p[]=22 (sxSat)":
    ## This should already pass (the elif branch's own drain works); verifies
    ## the sxSat signal is correct.
    let r = symexFind(ni1ElifNoStale, tLabel("ni1ElifHit"))
    check r.status == sxSat

  test "NI-1-2: elif branch has no stale clo1 heap (p[]==11 is sxUnsat)":
    ## RED test: without per-branch reset, clo1's exit heap bleeds into the
    ## elif path → p[]==11 is sxSat (false SAT). After fix: sxUnsat.
    let r = symexFind(ni1ElifNoStale, tLabel("ni1ElifStale"))
    check r.status == sxUnsat

  test "NI-1-3: contradiction — p[]==11 on elif path after clo1 (sxUnsat)":
    ## RED test: without fix → sxSat. After fix → sxUnsat.
    let r = symexFind(ni1ElifContradiction, tLabel("ni1Contradiction"))
    check r.status == sxUnsat

suite "symex Phase 15 re-review NI-2: isDerefWrite missing float→int drain":

  test "NI-2-1: p[]=int(x); p[]==3 is sxSat (domain-bound hint retired by R16-2)":
    ## R16-2 replaced the feConvDomainExcluded hint with a real RangeDefect
    ## raise fork. The sat verdict (post-NI-2 fix) remains; hint check removed.
    let r = symexFind(ni2DerefWriteFloatConv, tLabel("ni2DerefHit"))
    check r.status == sxSat

  test "NI-2-2: p[]=int(NaN) path is sxUnsat (domain bound excludes NaN)":
    ## RED test: before fix, sxUnknown (no domain bound → Z3 picks weird values).
    ## After fix: NaN excluded by domain bound → sxUnsat.
    let r = symexFind(ni2DerefWriteNanExcluded, tLabel("ni2NanHit"))
    check r.status == sxUnsat

suite "symex Phase 15 re-review S-3: isCall arg-lowering drainClosureExitHeap":

  test "S-3-1: closure-arg heap write visible after named-proc call (sxSat)":
    ## RED test: without fix, closure-arg heap mutation lost → false UNSAT.
    ## After fix: mutation propagated → sxSat.
    let r = symexFind(s3CallArgClosure, tLabel("s3Hit"))
    check r.status == sxSat

  test "S-3-2: contradiction — after closure-arg write, p[]==7 is sxUnsat":
    ## RED test: without fix, false SAT. After fix: sxUnsat.
    let r = symexFind(s3CallArgContradiction, tLabel("s3NoHit"))
    check r.status == sxUnsat

suite "symex Phase 15 re-review S-4: isReturn retExpr seed+drain":

  test "S-4-1: return-expr closure write p[]=55 visible to outer caller (sxSat)":
    ## RED test: without fix, empty heap threadvars + no drain → false UNSAT.
    ## After fix: seed + drain propagate the write → sxSat.
    let r = symexFind(s4Caller, tLabel("s4Hit"))
    check r.status == sxSat

  test "S-4-2: contradiction — after return-expr closure write, p[]==7 is sxUnsat":
    ## RED test: without fix, false SAT. After fix: sxUnsat.
    let r = symexFind(s4CallerContradiction, tLabel("s4NoHit"))
    check r.status == sxUnsat
