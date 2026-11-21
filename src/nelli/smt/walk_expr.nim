## RFC-0016 INT-34 B6b. Lowering inside a statement and draining its effects
## onto the consuming path: a leaf cut out of `runtime.nim`.
##
## Region R4 of `runtime.nim` (`scripts/int34-deps.py`) lives here whole, in
## the order it had there, less the forward declarations it held for the
## statement walkers above it:
##
##   * the fork-site registry, the defect kinds a raise maps to
##     (`typeIdToDefectKind`) and the depth and recursion bails
##     (`depthMayExtend`, `freshCallRet`, `nativeStackShort`, `depthBail`,
##     `ifArmInfeasible`);
##   * the raise forks and the halts (`raiseSplit`, `haltExcludedDefect`,
##     `crashRaise`, `noteUbAtFork`, `haltUndefined`, `opaqueRaiseForks`,
##     `forkDefect`, `decideUndefined`) and the drains of the pending lowering
##     effects onto the consuming path (`drainPendingLowerEffects`, the
##     `drain*` raise forks, `drainClosureExitHeap`);
##   * lowering inside a statement (`lowerInExpr`, `lowerBoolInExpr`,
##     `lowerLeafInExpr`);
##   * the concrete-branch checks (`concreteBranchOutcome`,
##     `concretelyInfeasible`), the variant and index defect sides, the
##     discriminator writes, the return and jump exits (`completeReturn`,
##     `exitReturn`, `exitJump`), the path join (`joinSV`, `mergeJoinPaths`),
##     the branch and guard followers and the view aliases a binding makes
##     (`bindViewAliases`), and the frontier halts (`haltFrontier`,
##     `capLoopFrontier`).
##
## With it, the run state and the routine of R0 that R4 reads:
## `boundsUnchecked`, `lastDrainedClosureExitPc`, the caller threadvars a
## closure call is lowered against (`currentCallerUb`, `currentCallerTaint`,
## `currentCallerPc`), `closureBodyCallerPc` and `seedCallerHeapThreadvars`,
## which writes them. Each threadvar lives at the lowest layer that reads it:
## the walker above reads and writes them through this module's export, and
## `resetWalkExprState` (called by `resetSymexRunState`) resets every one of
## them that is per-run.
##
## R4 calls one routine above it: `routeRaise` (it walks `finally` bodies, so
## it lives with the statement walker). It is reached through the typed hook
## `walkExprHooks`, which `runtime.nim` fills; nothing here casts a pointer.
##
## Every routine is exported, so `runtime.nim` can call it; `runtime.nim`
## re-exports by name only what it exported before the cut.

import std/tables
import std/options
import std/sets
import std/hashes
import std/algorithm
import std/math
import std/strutils
import z3

from ./buildprofile import buildSemantics, exSetjmp
import ./buildprofile as bprof
import ./types
import ./admission
import ./readonlyaxes
import ./arith_regime
import ./definedness
import ./variant_layout as vl
import ./abstraction
import ./symval
import ./walk_state
import ./walk_types
import ./walk_path
import ./lower_expr
import ./walk_solve
import ./walk_ctx
import ./regex_parser
import ./exn_hierarchy
import ./nativestack
import ./z3check
import ./heap_model
import ./string_lower_support
import ./exits
import ./concolictaxonomy
from std/importutils import privateAccess
privateAccess(RawWitness)     ## its fields stay private to walk_types (see its header)
privateAccess(SatCandidate)   ## `input`, as for `replay_settle.nim`

type
  WalkExprHooks* = object
    ## RFC-0016 INT-34 B6b. The routine this leaf calls that lives above it,
    ## filled by `runtime.nim` when it loads.
    routeRaise*: proc(p: Path, typeId: string, msg: Option[string],
                      w: var WalkCtx): seq[Path] {.nimcall.}
      ## Phase 15 E3. Route a raise of `typeId` on `p` to its handler, its
      ## `finally` bodies walked on the way out (`runtime.nim`).

var walkExprHooks*: WalkExprHooks
  ## Filled once, at `runtime.nim`'s load, before any walk.

proc boundsUnchecked*(): bool =
  ## RFC-0016 PRC-07. The build compiles no `boundChecks`: `s[i]` and `a[i]`
  ## (seq, string, openArray, array) are plain C subscripts, so an index
  ## outside the container is undefined (`index/unchecked`), not an
  ## `IndexDefect`.
  not checkedNow(coBound)

var lastDrainedClosureExitPc* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S7. The exit facts `drainPendingLowerEffects` appended to the
  ## drained path's `defectSurvivorPc` on its most recent call (at its END,
  ## in order). RFC-0005 S8bi: `drainScalarRaiseForks` -- which runs on that
  ## drained path -- strips them and puts each fact back at its place in
  ## evaluation order (`rskClosureExit`), so a raise evaluated before a
  ## closure call does not carry the facts that the call completed.

var currentCallerUb* {.threadvar.}: set[UbKind]
  ## RFC-0016 W1-d3. `currentCallerTaint`'s undefined.
var currentCallerTaint* {.threadvar.}: Taint
  ## RFC-0005 S8cn. The taint of the path a closure call is lowered on: a target
  ## in the body is reached on it (`applyClosureGround`).

var currentCallerPc* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S8cn. The branch conditions of that path. The body descends from an
  ## empty pc, since its axioms guard on its own branches.
var closureBodyCallerPc* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S8cn. What a target in the body being walked must also hold: the
  ## conditions on every calling path out to the routine (`isTargetLabel`).

proc seedCallerHeapThreadvars*(p: Path) {.inline.} =
  ## Phase 15 R1b / CR-5. Mirror a path's logical-heap state (and liveRefs)
  ## into the caller-heap threadvars so a CLOSURE call lowered out of `p.env`
  ## (no `Path` in scope) descends with the caller's threaded heap and
  ## liveRefs (ADR-0010 R1b; CR-5 freshness seeding). Mirrors the
  ## `setInFlightThreadvars` (E8) / `currentWalkCtxPtr` (C2b) idiom.
  ##
  ## CR-9 Stage 6: also calls `seedCallerHeapInWalkCtx` (`walk_path`, since
  ## RFC-0016 INT-34 B3) to mirror the same values into the live WalkCtx
  ## fields when a walk is active, keeping the threadvar path and WalkCtx path
  ## in sync for Groups 3 and 4.
  currentCallerHeaps = p.heaps
  currentCallerHeapDepth = p.heapDepth
  currentCallerAllocCounters = p.allocCounters
  currentCallerLiveRefs = p.liveRefs                     ## Phase 15 CR-5
  currentCallerTaint = p.taint                           ## RFC-0005 S8cn
  currentCallerUb = p.undefined                          ## RFC-0016 W1-d3
  currentCallerPc = p.pc                                 ## RFC-0005 S8cn
  # Reset the exit-heap threadvars so a non-heap-writing closure doesn't
  # carry the PREVIOUS call's exit heap forward to the next call.
  currentClosureDidMutateHeap = false                     ## Phase 15 CR-1
  currentClosureExitHeaps = initTable[string, Z3AnyAst]()
  currentClosureExitAllocCounters = initTable[string, int]()
  currentClosureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()
  currentClosureExitPc = @[]                              ## Phase 16 ADR-0012
  # CR-9 Stage 6 Groups 3+4: mirror into WalkCtx fields (dual-write).
  seedCallerHeapInWalkCtx(p)

# ============================================================================
# Fork-site registry (Phase 15 H1 deep-copy contract — ADR-0010)
# ----------------------------------------------------------------------------
# Every site that creates a CHILD `Path` from a PARENT MUST construct it via
# `forkPath` / `forkPathTainted` (defined above), which deep-copy the
# logical-heap state (`heaps` + `allocCounters` via `deepCopyHeapState`;
# `heapDepth` copies by value). This is the single enforcement point for fork
# isolation so a heap mutation on one branch can never bleed into a
# sibling/parent path. The fresh ROOT path in `runSymex`
# (`let initial = Path(...)`) is one of only TWO raw `Path(` constructions —
# it has no parent and correctly gets empty-default heap fields. The other is
# `applyClosureGround`'s `descentBase` (closure-body descent entry, ~6393):
# also root-like (no parent Path to fork FROM — the closure body descends
# fresh, seeded from the CALLER's threaded heap threadvars rather than a
# parent Path), and — per SND-1b (RFC-chapulin-hardening, walker v39) —
# hardcodes `taint: {}` deliberately (RFC-0005 S1; was `uncertain: false`
# — the descent starts clean; taint is picked back up via `forkPath`/
# `forkPathTainted` calls made BY `walk()` while descending the body, and read
# back off each returned sub-path's `cp.taint` by `applyClosureGround` after
# the descent, to skip axiomatizing any tainted sub-path into the global
# `currentClosureCallAxioms` sink). Pinned by the S1 writer grep-pin.
#
# In H1 the tables are empty on every path (the walker neither reads nor writes
# them); the copies are inert until Cluster R populates the heap. They are
# wired now so E/G/C/R need not re-audit the fork sites. New fork sites added
# by E/G/C/R MUST use `forkPath`/`forkPathTainted` and be added to this
# registry; the R-cluster walker comment block supersedes this one.
#
# R3 hardening (post-H1): `forkPath` takes no taint parameter at all — it
# always PROPAGATES `parent.taint` to the child, which is the correct
# behavior at every site below except the handful marked "deliberate taint,"
# which call `forkPathTainted` instead. Because the taint argument is no
# longer a bare value at the call site, "silently drop the parent's taint" is
# not spellable; RFC-0005 S1 goes further — `forkPathTainted` takes a
# `Degrade` token (only `degrade`/`queueDegrade` mint one from a recorded
# kind), the return merge is `forkPathMerged`, and the shared constructor
# `forkPathTaintPrimitive` is "not for sites" (writer grep-pin). The list below still documents
# fork-site provenance for the heap-copy contract.
#
# Fork sites (line numbers reflect post-H1 state):
#   walk(isIf)                       — true/arm-branch fork
#   walk(isIf)                       — else-branch fork
#   walk(isLet)                      — sequential child (binding)
#   walk(isAssign)                   — sequential child (binding)
#   walk(isWhile)                    — loop-body (cond=true) entry
#   walk(isWhile)                    — loop-exit (cond=false)
#   walk(isWhile)                    — unwind-exhausted uncertain path
#   walk(isIndex) Table              — present-key survivor
#   walk(isIndex) seq                — OOB target solve path
#   walk(isIndex) seq                — in-bounds survivor
#   walk(isIndex) array              — OOB target solve path
#   walk(isIndex) array              — in-bounds survivor
#   walk(isVariantReassign)          — static-tag disc reassign
#   walk(isVariantReassignSymbolic)  — per-arm fork (svVariant)
#   walk(isVariantReassignSymbolic)  — per-arm fork (svMultiVariant)
#   walk(isVariantField)             — out-of-arm (fieldDefect) solve path
#   walk(isVariantField)             — in-arm survivor
#   walk(isReturn)                   — returned-path into call frame
#   walk(isCall) opaque              — fresh-retSym uncertain path
#   walk(isCall) depth-bail          — fresh-retSym uncertain path
#   walk(isCall) recursion-cycle     — fresh-retSym uncertain path
#   walk(isCall) cache-hit           — pcDelta-extended survivor
#   walk(isCall) descent             — callee-frame clone (heap threaded in)
#   walk(isCall) return-merge        — post-call survivor (heap threaded out)
#   walk(isAssert)                   — assertion-violation solve path
#   walk(isAssert)                   — assertion-holds survivor
# (26 fork sites; the single ROOT `Path(` in runSymex is excluded by design.)
# ============================================================================


proc typeIdToDefectKind*(typeId: string): DefectKind =
  ## Phase 15 E6. Map a raised exception type id to its `DefectKind` for the
  ## `defectExclusions` membership test. The standard-library Defect families
  ## map to their dedicated kind; the real Nim out-of-memory type is
  ## `OutOfMemDefect` (both spellings resolve, per the E4 hierarchy
  ## reconciliation). EVERY user-defined Defect subtype maps to `dkOther`, so
  ## user defects can only be excluded all-or-none (documented on `dkOther`).
  case typeId
  of "AssertionDefect":    dkAssertionDefect
  of "IndexDefect":        dkIndexDefect
  of "FieldDefect":        dkFieldDefect
  of "RangeDefect":        dkRangeDefect
  of "OutOfMemDefect", "OutOfMemoryDefect": dkOutOfMemoryDefect
  of "StackOverflowDefect": dkStackOverflowDefect
  of "OverflowDefect":     dkOverflowDefect    ## R16-1 (ADR-0011 F3)
  of "DivByZeroDefect":    dkDivByZeroDefect   ## R16-1 (ADR-0011 F3)
  else:                    dkOther

proc toPublic*(iv: InternalVerdict): RawResult =
  ## Phase 15 E2b. The SINGLE conversion from a private `InternalVerdict` to a
  ## public `RawResult`, called EXACTLY ONCE per finding at the `runSymex`
  ## boundary (Invariant 9 — no `sxRaised` escapes internal raise-flow code; the
  ## walker accumulates `RawResult`s into `w.found` and only the `ivRaised` path
  ## flows through here). E2b only ever maps `ivRaised` (the other arms exist for
  ## the E3+ handler-propagation machinery that consumes `InternalVerdict`).
  case iv.kind
  of ivRaised:
    RawResult(status: sxRaised,
              raisedTypeId: iv.raisedTypeId,
              raisedMsg: iv.raisedMsg,
              isDefect: iv.raisedIsDefect,   ## Phase 15 E6
              raisedWitness: iv.raisedWitness)
  of ivSat:
    RawResult(status: sxSat, witness: iv.satWitness)
  of ivUnsat:
    RawResult(status: sxUnsat)
  of ivUnknown:
    RawResult(status: sxUnknown)

proc evalRaiseMsg*(env: Env, msg: IRExpr): Option[string] =
  ## Phase 15 E2b. Evaluate a `raise newException(T, <msg>)` message expression
  ## to a concrete `Option[string]`. A nil/absent message → `none`. A string
  ## literal (`iekStrLit`) yields its constant value — the common
  ## `newException(T, "literal")` form. Any non-literal message expression has no
  ## single concrete value without a Z3 model on a string sort (deferred to a
  ## later cycle); it conservatively yields `none` so `raisedMsg` is only ever
  ## populated when it is provably exact (Invariant 3 — never a guessed value).
  if msg == nil:
    none(string)
  elif msg.kind == iekStrLit:
    some(msg.sval)
  else:
    none(string)

proc effectiveHeapDepthLimit*(settings: SymexSettings): int =
  ## Phase 15 R9 (ADR-0010, Des-LOW-D1 / M9). Resolve the EFFECTIVE heap-depth
  ## budget. `maxHeapDepth = 0` is the unlimited sentinel (consistent with
  ## `maxFrontierSize = 0`): fall back to `maxCallDepth` if > 0, else a hard cap
  ## of 256. There is NO separate unlimited-mode code path — the deref guard is
  ## simply `if limit > 0 and path.heapDepth >= limit`, and this proc never
  ## returns 0 (the hard cap is the floor), so the guard always fires eventually
  ## (no infinite recursive-deref loop).
  if settings.budget.maxHeapDepth > 0: settings.budget.maxHeapDepth
  elif settings.budget.maxCallDepth > 0: settings.budget.maxCallDepth
  else: 256

# heapDepthExhausted moved to runtime_heap.nim (CR-7-deeper Stage 8+).

proc inRecursiveFrame*(w: WalkCtx): bool =
  ## RFC-0005 S8as. True when the innermost inlined call's callee is also an
  ## outer frame's: the walk is inside a recursion.
  if w.callStack.len < 2: return false
  let top = w.callStack[^1].callee
  for k in 0 ..< w.callStack.high:
    if w.callStack[k].callee == top: return true
  false

const ifSiteProbeMax* = 3
  ## RFC-0005 S8ax. How many times an `if` arm outside a recursion is
  ## checked without the check ever dropping it before the walk stops
  ## checking it (`ifArmInfeasible`).

proc armHeavy*(body: IRStmt): bool =
  ## RFC-0005 S8ax. `body` holds a loop or a call: walking it when no
  ## execution reaches it costs more than the solver call that would have
  ## dropped it. A straight-line arm (assignments, a return, a raise, a
  ## label) is walked in about the time a check takes, so outside a
  ## recursion it is not checked (`ifArmInfeasible`).
  if body == nil: return false
  case body.kind
  of isWhile, isCall: return true
  of isBlock:
    for c in body.stmts:
      if armHeavy(c): return true
  of isIf:
    for b in body.branches:
      if armHeavy(b.body): return true
    return armHeavy(body.elseBody)
  of isTry:
    for h in body.tryHandlers:
      if armHeavy(h.body): return true
    return armHeavy(body.tryBody) or armHeavy(body.tryFinally)
  else: discard
  false

proc armDeclines*(body: IRStmt): bool =
  ## RFC-0005 S8ax. `body` is a block of nothing but a decline marker
  ## (`isUnsupported`), the shape `orderOperands` guards with the condition
  ## under which it applies: walking it records a decline whether or not
  ## any execution reaches it, so the arm is always checked
  ## (`ifArmInfeasible`).
  if body == nil: return false
  case body.kind
  of isUnsupported: true
  of isBlock: body.stmts.len == 1 and armDeclines(body.stmts[0])
  else: false

func hardCallDepth*(settings: SymexSettings): int =
  ## RFC-0005 S8ax. The deepest call stack the walk inlines into:
  ## `maxRecursionDepth`, or `maxCallDepth` when that is set higher (a
  ## caller's explicit depth is never cut).
  max(settings.budget.maxCallDepth, settings.budget.maxRecursionDepth)

proc recursiveCallsOnAPath*(body: IRStmt; names: seq[string]): int =
  ## RFC-0005 S8ax. The most calls to a routine of `names` one execution of
  ## `body` may make: summed along a sequence, the largest over the arms of
  ## an `if` or a `try`, and two (many) for one inside a loop.
  if body == nil: return 0
  case body.kind
  of isCall:
    if body.callee in names: 1 else: 0
  of isBlock:
    var n = 0
    for c in body.stmts: n += recursiveCallsOnAPath(c, names)
    n
  of isIf:
    var n = recursiveCallsOnAPath(body.elseBody, names)
    for b in body.branches: n = max(n, recursiveCallsOnAPath(b.body, names))
    n
  of isTry:
    var h = 0
    for x in body.tryHandlers: h = max(h, recursiveCallsOnAPath(x.body, names))
    recursiveCallsOnAPath(body.tryBody, names) + h +
      recursiveCallsOnAPath(body.tryFinally, names)
  of isWhile:
    if recursiveCallsOnAPath(body.wbody, names) > 0: 2 else: 0
  else: 0

proc depthMayExtend*(w: WalkCtx; live: int): bool =
  ## RFC-0005 S8ax. At or past `maxCallDepth`, inline this call anyway when
  ## the stack is under the hard budget (`hardCallDepth`) and the frontier
  ## is not growing: the walks entered at this depth, these `live` paths
  ## included, number no more than those entered one level up. A recursion
  ## whose arguments decide its depth (`sumTo(n)` with `n` in `0..5`) walks
  ## one feasible path per level and is followed to its base case; one that
  ## fans out (`fib`: a body that may recurse twice on one execution,
  ## `recursiveCallsOnAPath`) declines at `maxCallDepth` as before. So does
  ## every call under an extension that has already reached the hard budget
  ## (`WalkCtx.extHardMark`): its root drops all it walked. Measured (Linux,
  ## Z3 5.1) on `fib(x) == 13`, `x` free: the depth-first frontier test
  ## alone admitted the leftmost chain to the hard budget and walked every
  ## frame on the way back again, 6.1 s at a hard budget of 5, 17.7 s at 8,
  ## killed at 600 s at 24. Every extended level is still bounded by the
  ## hard budget, which bounds the native recursion of `walk` (see the
  ## depth check in `walk`'s `isCall` arm for the measured stack ceiling).
  let d = w.callStack.len
  if d < 1 or d >= hardCallDepth(w.settings): return false
  # Abandoned: a path under this extension's root reached the hard budget,
  # and the root drops all it walked. Walking on would only cost: a fan-out
  # (`fib`) explored depth first enters one walk per level before its
  # siblings, so the frontier test admits its leftmost chain to the hard
  # budget, and every frame on the way back would extend again.
  if w.extHardMark >= 0 and w.depthHardHits > w.extHardMark: return false
  # A body that may recurse twice on one execution (`fib`) fans out: the
  # frontier test, explored depth first, sees one walk per level before the
  # siblings, so it is not extended at all.
  let top = w.callStack[^1].callee
  if top in w.procs:
    var names: seq[string]
    for f in w.callStack: names.add f.callee
    if recursiveCallsOnAPath(w.procs[top].body, names) > 1: return false
  let here = (if d < w.depthWalks.len: w.depthWalks[d] else: 0)
  let above = (if d - 1 < w.depthWalks.len: w.depthWalks[d - 1] else: 0)
  here + live <= above

proc freshCallRet*(stmt: IRStmt; env: Env; z3Name: string;
                  pcOut: var seq[Z3Bool]): SymVal =
  ## RFC-0005 S8be. The fresh return value of a call: one the walk follows
  ## (its `retSym`, bound to the callee's result on each exit) or does not
  ## (`depthBail`, the cycle cut), bounded by the callee's declared type. A
  ## fixed-width `int` was allocated as a bit-vector even where the actuals
  ## are abstracted to the integer sort (`symexAssume` bounds), so the
  ## caller's `k + <fresh>` and its overflow check mixed the sorts
  ## (`bv2int`): `sumTo(n)` under `n in 0..5`, declined at depth 3, took
  ## 146 s (Linux, Z3 5.1); it takes 0.9 s. When an actual reads an
  ## integer-sorted variable, a signed or narrower-than-64-bit `int` return
  ## is allocated in that sort, with the declared type's bounds; otherwise
  ## as before.
  let ty = stmt.retTy
  if ty != nil and ty.kind == itInt and (ty.signed or ty.width < 64):
    var refs: HashSet[string]
    for a in stmt.cargs: collectVarRefs(a, refs)
    var intSorted = false
    for r in refs:
      if env.hasKey(r) and env[r].kind == svInt:
        intSorted = true
        break
    if intSorted:
      result = freshRetSym(ty, z3Name, pcOut, intOffsetPositions = @[0])
      if not ty.hasRange:
        let w = if ty.width in [8, 16, 32, 64]: ty.width else: 64
        let lo = if not ty.signed: 0'i64
                 elif w == 64: low(int64)
                 else: -(1'i64 shl (w - 1))
        let hi = if w == 64: high(int64)
                 elif ty.signed: (1'i64 shl (w - 1)) - 1
                 else: (1'i64 shl w) - 1
        pcOut.add(result.zi >= mkZ3IntLit(lo))
        pcOut.add(result.zi <= mkZ3IntLit(hi))
      return
  freshRetSym(ty, z3Name, pcOut)

const
  nativeStackReserve = 256 * 1024
    ## RFC-0005 S8ca. The native stack a call keeps below it beyond two
    ## levels' cost (`nativeStackShort`): the solves, the lowering and the
    ## bail of the deepest level, and C++ unwinding.
  nativeLevelFloor = 192 * 1024
    ## RFC-0005 S8ca. The least one level is taken to cost, before (or
    ## while) the walk has measured less. Measured on the Linux/podman
    ## debug build (`tsymex_rfc0005_s8ca_stack`): one level of linear
    ## recursion costs about 158 KB on c and 186 KB on cpp, so the first
    ## call, with nothing measured, is covered too.

  nimFrameReserve = 400
    ## RFC-0005 batch 9. The Nim frames a call keeps below it
    ## (`nativeStackShort`): one level is 9 (`walk`, `walkStmt`, `walkBlock`
    ## twice over, `walkCallArm`), and the lowering and the solves of the
    ## deepest level take the rest.

proc levelNeed*(w: WalkCtx): int =
  ## RFC-0005 S8ca. The native stack a call needs left to be inlined.
  nativeStackReserve + 2 * max(w.levelStack, nativeLevelFloor)

proc nativeStackShort*(w: var WalkCtx): int =
  ## RFC-0005 S8ca. The native stack left below this call when it is under
  ## what inlining one more level needs, else -1. `walk` recurses natively
  ## once per inlined call, and `maxCallDepth` counts levels, not bytes: a
  ## cpp level costs more than a c one, and the stack may hold 8 MB (a Linux
  ## main thread), 2 MB (a Nim thread) or 16 MB (a Windows solve's fiber,
  ## `runSymexWithBigStack`), or what is left below a caller's frames.
  ## `tsymex_configdefaults`' crash pin, 50 levels sized on c, ran off an
  ## 8 MB stack on cpp (SIGSEGV), and the default budget's adaptive depth
  ## (`maxRecursionDepth`, 24) ran off a 2 MB thread's on both. One
  ## level's cost is read from the frame pushed one level up (`CallFrame.sp`),
  ## the most so far kept in `WalkCtx.levelStack`; the need is twice that
  ## (at least `nativeLevelFloor`) plus `nativeStackReserve` (`levelNeed`):
  ## about 3 levels on a 1 MB stack, 45 (c) or 39 (cpp) on 8 MB.
  ## RFC-0005 batch 9: a build with stack traces also ends the process at
  ## Nim's call depth limit (`nimFramesLeft`), which a level costing under
  ## 16 MB / 222 reaches before a Windows fiber's stack runs out. That is a
  ## shortage of the same recursion, so the call declines the same way.
  let left = nativeStackLeft()
  if nimFramesLeft() < nimFrameReserve: return left
  if left == high(int): return -1   # not measured on this platform
  if w.callStack.len > 0:
    let top = w.callStack[^1].sp
    let here = nativeStackPointer()
    if top > here: w.levelStack = max(w.levelStack, int(top - here))
  if left < levelNeed(w): left else: -1


proc depthBail*(w: var WalkCtx; stmt: IRStmt; live: seq[Path];
               cut: DepthCut; stackLeft = 0): seq[Path] =
  ## RFC-0005 S8ax. The call-depth decline: each live path continues past
  ## the call with a fresh return value, tainted. `cut` says why (S8ca:
  ## `dcutStack`, with the `stackLeft` bytes it measured).
  ##
  ## (Before S8ax, inline in `walk`'s `isCall` arm.) Bail: continue with a
  ## fresh unconstrained retSym; flag unknown. The surviving paths are marked
  ## uncertain so any target hit on them degrades to sxUnknown (the witness
  ## would otherwise be an unsoundly-Z3-defaulted value).
  ## #161/#163 handoff follow-up: this used to set `sawUnknown` bare — the
  ## run-level Invariant-7 backstop (`runSymexImpl`) then reported an
  ## unclassified `weInternalWalkerFault`, indistinguishable from a real
  ## walker bug. `beBudgetExhausted` (chapulin catalog #5(b)) already names
  ## exactly this shape — "a walk budget ran out with paths still live" —
  ## for `maxLoopUnwind`/`maxFrontierSize`; this call-inlining depth cap is
  ## a sibling of the SAME budget family, so it reuses the kind rather than
  ## adding a near-duplicate. The message names the exhausted budget and its
  ## current value so "raise maxCallDepth" reads as actionable configuration
  ## advice, not a shrug.
  ## RFC-0005 S6a: that reuse is exactly what §3.2's standing rule forbids
  ## once `classOf` reads one word per kind — this bail is not a k-unroll
  ## survivor. It continues with a fresh havoc `retSym` but DROPS the
  ## callee's var-param writes, heap writes and raises (and never lowers the
  ## actuals): a stale env, `dcSubstituted`. Split off as
  ## `beBudgetExhaustedUnmodelled`. Classifying the merged kind by the
  ## frontier prune (`dcOmitted`) would have stripped these survivors' path
  ## taint — a witness through the havoc retSym reported clean sxSat.
  ## RFC-0005 S8an: a path that reaches the bail but that no execution can
  ## take is dropped (by the caller), not bailed: it has no behaviour to
  ## lose.
  let framesShort = cut == dcutStack and nimFramesLeft() < nimFrameReserve
  let why =
    case cut
    of dcutHard:
      "the call stack reached the hard budget (maxRecursionDepth=" &
        $w.settings.budget.maxRecursionDepth & ")"
    of dcutFrontier:
      "the walks at the next depth would outnumber those at this " &
        "one, so the budget was not extended (maxRecursionDepth=" &
        $w.settings.budget.maxRecursionDepth & " bounds an extension)"
    of dcutStack:
      if framesShort:
        "the " & $nimFramesLeft() & " frames left at depth " &
          $w.callStack.len & " before Nim's call depth limit are under the " &
          $nimFrameReserve & " the walk keeps, so the call is not inlined " &
          "whatever the depth budget"
      else:
        "the native stack left (" & $(stackLeft div 1024) & " KB at depth " &
          $w.callStack.len & ") is under what one more level needs (" &
          $(levelNeed(w) div 1024) &
          " KB), so the call is not inlined whatever the depth budget"
  let d = w.degrade(beBudgetExhaustedUnmodelled,
    if cut == dcutStack:
      "call-inlining stopped by the native stack while inlining `" &
        stmt.callee & "` — " & why & "; " &
        (if framesShort:
           "raise -d:nimCallDepthLimit or build without stack traces"
         else:
           "run the analysis on a thread with a larger stack") &
        " to reach deeper (beBudgetExhaustedUnmodelled)"
    else:
      "call-inlining depth budget exhausted (maxCallDepth=" &
         $w.settings.budget.maxCallDepth & ") while inlining `" &
         stmt.callee & "` — " & why & "; raise " &
         "settings.budget.maxCallDepth or maxRecursionDepth if " &
         "this SUT's real call nesting is deeper than the current " &
         "bound (beBudgetExhaustedUnmodelled)", cap = ckCallDepth)
  for p in live:
    var newEnv = p.env
    var pcInit: seq[Z3Bool]
    if stmt.retName.len > 0:
      inc w.synthZ3
      let z3Name = stmt.retName & "_d" & $w.synthZ3
      newEnv[stmt.retName] = freshCallRet(stmt, p.env, z3Name, pcInit)   # S8be
    result.add forkPathTainted(p, p.pc & pcInit, newEnv, d)

proc ifArmInfeasible*(w: var WalkCtx; armPath: Path; last: Z3Bool;
                     site: pointer; body: IRStmt): bool =
  ## RFC-0005 S8as. The `wmExplore` walk forked every `if` arm without a
  ## feasibility check, so a recursion on a symbolic argument walked arms no
  ## execution takes (`fact(1)`'s `k > 1`) down to `maxCallDepth` -- where
  ## S8an's bail dropped them -- and one with two recursive calls (`fib`)
  ## multiplied them at each level: `fib(n)` under `n in 0..5` did not end
  ## in 13 minutes at `maxCallDepth = 4`. Inside a recursive frame an arm
  ## (or else path) whose query is UNSAT is now dropped before it is walked.
  ## `last` is the arm's own conjunct, decided without the solver when it is
  ## a literal. Sound exactly as `loopArmInfeasible` is: an undecided query
  ## keeps the arm.
  ##
  ## RFC-0005 S8ax: outside a recursion the check is ADAPTIVE. Only an arm
  ## that holds a loop or a call is checked (`armHeavy`): a solver call is
  ## dearer than walking a few straight-line statements. And per site
  ## (`site`, the arm's IR node), once a site has been checked
  ## `ifSiteProbeMax` times, it is checked again only while at least one in
  ## four of its checks dropped the arm. Measured (Linux, Z3 5.1, paired
  ## runs, minimum of two; off / this policy / every arm checked):
  ## s8k_bounds 29.4 / 29.6 / 55.7 s, s8p_precision 5.4 / 3.7 / 2.5 s,
  ## s8as_remainder 37.4 / 26.8 / 47.2 s, s8an_remainder 11.7 / 13.9 /
  ## 19.8 s, phase3_recursion 5.1 / 6.0 / 6.9 s. Checking every arm doubled
  ## the string-heavy suites; checking only heavy arms keeps most of the
  ## win where dead arms guard real work. Dropping is sound whichever way
  ## the policy goes (the arm is UNSAT); the policy only decides where the
  ## solver call is spent.
  ##
  ## An arm that only declines (`armDeclines`) is always checked: walked
  ## where no execution reaches it, it voids the verdict for nothing.
  let recursive = inRecursiveFrame(w) or armDeclines(body)
  if not recursive:
    if not armHeavy(body): return false
    let st = w.ifSites.getOrDefault(site)
    if st.checks >= ifSiteProbeMax and st.prunes * 4 < st.checks:
      return false
  inc symexIfArmsChecked
  result = $simplify(last) == "false" or
           pathInfeasible(w.z3, armPath, w.settings)
  if result: inc symexIfArmsPruned
  if not recursive:
    var st = w.ifSites.getOrDefault(site)
    inc st.checks
    if result: inc st.prunes
    w.ifSites[site] = st

proc raiseSplit*(w: WalkCtx; typeId: string): tuple[types: seq[string],
                                                   unknown: seq[string]] =
  ## RFC-0005 S8be. The types an abstract raise of `typeId` (one an opaque
  ## call may raise, known only by its declared or scanned type) is split
  ## into: `typeId` itself, every strict subtype of it that a `try` arm
  ## around the current point names (in this frame or a caller's), and the
  ## search's own `tRaisedExn` filter when it is one. The object raised may
  ## be of any subtype; only those named somewhere can be told apart, and
  ## each is raised on its own fork. `unknown`: arm types the hierarchy does
  ## not know, which may be subtypes too.
  result.types = @[typeId]
  let known = isKnownExnType(typeId, w.statics.exnTable,
                             w.statics.userExnHierarchy)
  template consider(ht: string) =
    if ht != typeId and ht notin result.types:
      if not isKnownExnType(ht, w.statics.exnTable,
                            w.statics.userExnHierarchy):
        if ht notin result.unknown: result.unknown.add ht
      elif known and isSubtypeOf(ht, typeId, w.statics.exnTable,
                                 w.statics.userExnHierarchy):
        result.types.add ht
  template scan(hs: seq[HandlerFrame]) =
    for hf in hs:
      for h in hf.handlers:
        for ht in h.typeIds: consider(ht)
  scan(w.frame.handlerStack)
  for f in w.frameStack: scan(f.handlerStack)
  if w.target.kind == stkRaisedExn and w.target.typeFilter.len > 0:
    consider(w.target.typeFilter)

proc concretelyInfeasible*(ctx: Z3Context, concreteEq: seq[Z3Bool],
                           conds: seq[Z3Bool], settings: SymexSettings): bool
  ## RFC-0016 K10b fwd-decl (defined with the follow-mode helpers below).

# ---- Raise and undefined-behaviour hits (RFC-0016 INT-34 B1: need no walk) ---

proc haltExcludedDefect*(p: Path, typeId: string, w: var WalkCtx) =
  ## RFC-0016 K7b (W-16). A `Defect` raise that reaches the SUT boundary
  ## while its `DefectKind` is in `settings.defectExclusions` ends its path
  ## with no finding (the user excluded it). The omission is now recorded
  ## (`feDefectExcluded`, `dcOmitted`: run `{scIncomplete}`), so a search
  ## the excluded raise could have answered is `sxUnknown`, never a trusted
  ## `sxUnsat`. A path no execution takes, or one a concrete witness's
  ## inputs rule out, is not reached and records nothing.
  if pathInfeasible(w.z3, p, w.settings): return
  if w.mode == wmFollowConcrete and
     concretelyInfeasible(w.z3, w.concreteEq, p.pc & p.defectSurvivorPc,
                          w.settings):
    return
  w.halted(feDefectExcluded,
    "a raise of `" & typeId & "` is excluded by `defectExclusions` (" &
    $typeIdToDefectKind(typeId) & "): the path ends here with no finding, " &
    "so a search it could have answered is not decided")

proc crashRaise*(p: Path, typeId: string, w: var WalkCtx) =
  ## RFC-0005 S8cu. A raise no handler and no `finally` sees: a nil dereference,
  ## which natively is a SIGSEGV (rc 139) that ends the process on the pinned Nim
  ## 2.2.10, by default, with `--panics:on`, `-d:danger`, clang and the cpp
  ## backend, under `except NilAccessDefect`, `except Defect` and a bare
  ## `finally`. `std/segfaults` does not change that with the default goto
  ## exceptions (its handler recurses to the call depth limit, rc 1, or hangs
  ## in a release build), nor with `--exceptions:cpp`; with
  ## `--exceptions:setjmp` it makes the raise catchable and runs the `finally`.
  ## So in a setjmp build a dereference under any `try` declines
  ## (`heNilDerefMayBeCaught`). In every other build the crash leaves each
  ## frame by the channel an escaping raise takes (`escaped`, marked `crash`,
  ## so the caller's drain re-routes it here), since the callee's or closure
  ## body's path holds only its own facts and the drain joins the caller's;
  ## it ends as a finding at the SUT boundary. Before S8cu it was routed as an
  ## ordinary raise: a label in `except NilAccessDefect` was a false sxSat and
  ## `tNilAccess` a false sxUnsat.
  when buildSemantics.exceptions == exSetjmp:
    var guarded = w.frame.handlerStack.len > 0
    for f in w.frameStack:
      if f.handlerStack.len > 0: guarded = true
    if guarded:
      if not pathInfeasible(w.z3, p, w.settings):
        w.halted(heNilDerefMayBeCaught,
          "a nil dereference under a `try` in a build with " &
          "`--exceptions:setjmp`, where `std/segfaults` would make it a " &
          "catchable `" & typeId & "` and run the `finally`: what follows is " &
          "not known -- path degraded to sxUnknown (heNilDerefMayBeCaught)")
      return
  if w.frameStack.len > 0:
    w.frame.exits.escaped.park(EscapedRaise(path: p, typeId: typeId,
                                               msg: none(string), crash: true))
    return
  if w.mode == wmFollowConcrete and
     concretelyInfeasible(w.z3, w.concreteEq, p.pc & p.defectSurvivorPc,
                          w.settings):
    return
  if typeIdToDefectKind(typeId) in w.settings.defectExclusions:
    haltExcludedDefect(p, typeId, w)   ## RFC-0016 K7b (W-16)
    return
  let (st, wit, candErrs, why) = solveTargetHit(w, p)
  case st
  of sxSat:
    let iv = InternalVerdict(kind: ivRaised, raisedTypeId: typeId,
                             raisedMsg: none(string), raisedWitness: wit,
                             raisedIsDefect: true)
    var r = toPublic(iv)
    r.soundness.pathTaint = p.taint
    r.soundness.witnessUndefined = ubOrdinals(p.undefined)
    r.undefinedViaOnly = ubOrdinals(p.undefinedViaOnly)   # W3-z R7
    r.nilDerefOnPath = p.nilDeref
    # RFC-0016 W1-c2: the witness ends the process wherever it runs, so no
    # consumer runs it in the host (`hostRunnable`).
    r.soundness.witnessUnsafe = true
    r.errors.add candErrs
    w.admitSolvedHit(r)
  of sxUnknown:
    w.halted(beSolverUndef,
      "solver returned unknown on a path raising `" & typeId &
           "` (queryRLimit=" & $w.settings.budget.queryRLimit &
           "): " & why & " (beSolverUndef)")
  of sxUnsat, sxRaised: discard

proc noteUbAtFork*(parentTaint: Taint; child: Path; newUb: set[UbKind]) =
  ## RFC-0016 W3-z R1 (finding U3). A `{.noinit.}` read does not halt: it rides
  ## the path as `ub` on a `feGlobalHavoc` degrade, so `haltUndefined`, the only
  ## other hit test, never saw it and `tUndefined` returned a trusted `sxUnsat`
  ## over a reachable indeterminate read. Every fork that newly puts a kind of
  ## the requested set on a path comes here (`forkPathTainted`, `taintInPlace`;
  ## a kind already on the parent was tested where it arrived): the hit is
  ## solved on the child's constraints. The finding's taint is the PARENT's:
  ## the degrade that carries the kind is the finding itself, not a reason to
  ## doubt it, so it does not turn the hit into a replay-only candidate.
  ## Unlike `haltUndefined` the path continues: the read is not a halt.
  ##
  ## RFC-0016 0.10.0 review H2. On the tail walk (`tailGate`) the kinds are
  ## what the run is not shown defined in: a child the pins do not rule out
  ## records them in `WalkCtx.tailUb`, which `verifyTailDefinedKinds` reads.
  ## Before, the tail walk returned here and the read was a trusted `sxSat`.
  if newUb == {} or currentWalkCtxPtr == nil: return
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  if wp[].tailGate:
    if newUb - wp[].tailUb != {} and
       not concretelyInfeasible(wp[].z3, wp[].concreteEq,
                                child.pc & child.defectSurvivorPc,
                                wp[].settings):
      wp[].tailUb.incl newUb
    return
  if wp[].target.kind != stkUndefined or wp[].shouldStop:
    return
  if newUb * wp[].target.ubKinds == {}: return
  if wp[].mode == wmFollowConcrete and
     concretelyInfeasible(wp[].z3, wp[].concreteEq,
                          child.pc & child.defectSurvivorPc, wp[].settings):
    return
  let solveOn = if closureBodyCallerPc.len == 0: child
                else: forkPath(child, closureBodyCallerPc & child.pc, child.env)
  let (st, wit, candErrs, why) = solveTargetHit(wp[], solveOn)
  case st
  of sxSat:
    wp[].admitSolvedHit(RawResult(status: sxSat, witness: wit,
      soundness: Soundness(pathTaint: parentTaint,
                           witnessUndefined: ubOrdinals(child.undefined)),
      nilDerefOnPath: child.nilDeref, errors: candErrs))
  of sxUnknown:
    wp[].halted(beSolverUndef,
      "solver returned unknown on a path reading an indeterminate value: " &
      why & " (beSolverUndef)")
  of sxUnsat, sxRaised: discard

proc haltUndefined*(p: Path, kind: UbKind, cond: Z3Bool, site: string,
                   w: var WalkCtx) =
  ## RFC-0016 W1-d1a (section 9.1 item 2). The undefined side of an op, when
  ## it is not provably unreachable: a TERMINAL path that leaves through the
  ## crash channel's end (no `escaped` parking), never `routeRaise`, whose
  ## handler search would let a bare `except:`, an `except DivByZeroDefect:` or
  ## a `finally` consume it. So: no setjmp arm (nothing recovers an undefined
  ## operation), no `defectExclusions` check (it is not a Defect), and a
  ## `degrade` halt of the op's `UbKind` (`dcOmitted`: run coordinate
  ## `{scIncomplete}`, which keeps `sxUnsat` from being trusted) in place of a
  ## finding. `p` is the path BEFORE the op; `cond` is the undefined side.
  ## In concrete-follow mode a side the witness's inputs rule out is not
  ## reached and records nothing.
  if w.mode == wmFollowConcrete and
     concretelyInfeasible(w.z3, w.concreteEq, p.pc & p.defectSurvivorPc & @[cond],
                          w.settings):
    return
  # RFC-0016 K10a-target (section 9.1 item 5): the side is also a FINDING. Under
  # `tUndefined` a listed kind is the target's hit (a winner, solved on the
  # path with the undefined side's condition); under any other target it is
  # listed on `SymexResult.undefined` (clean paths only, a bounded number).
  # The path ends either way: nothing past the op is modelled.
  let tgt = w.target
  let isHit = tgt.kind == stkUndefined and kind in tgt.ubKinds
  # RFC-0016 K10b: the whole-run gate's second walk reads only the halt, so
  # it lists nothing (the solve for a witness would run unpinned).
  var listIt = tgt.kind != stkUndefined and scSpurious notin p.taint and
               w.undefinedFound.len < maxUndefinedFindings and not w.tailGate
  for u in w.undefinedFound:
    if u.kind == kind and u.site == site: listIt = false   # one per op
  if (isHit and not w.shouldStop) or listIt:
    let atOp = forkPath(p, p.pc & @[cond], p.env)
    let solveOn = if closureBodyCallerPc.len == 0: atOp
                  else: forkPath(atOp, closureBodyCallerPc & atOp.pc, atOp.env)
    let (st, wit, candErrs, why) = solveTargetHit(w, solveOn)
    case st
    of sxSat:
      if isHit:
        w.admitSolvedHit(RawResult(status: sxSat, witness: wit,
          soundness: Soundness(pathTaint: p.taint,
                               witnessUndefined: ubOrdinals(p.undefined + {kind})),
          nilDerefOnPath: p.nilDeref, errors: candErrs))
      else:
        w.undefinedFound.add RawUndefined(kind: kind, site: site, witness: wit)
    of sxUnknown:
      if isHit:
        w.halted(beSolverUndef,
          "solver returned unknown on a path reaching " & $kind & " at " &
          site & ": " & why & " (beSolverUndef)")
    of sxUnsat, sxRaised: discard
  let next =
    if tgt.kind == stkUndefined: ""
    else: "; query `tUndefined()` to ask for an input that reaches it"
  w.halted(kind,
    "undefined behaviour at " & site & " (" & $kind & "): the path ends " &
    "here, what follows is not modelled" & next &
    # RFC-0016 K10c: what the verdict assumes of the C flags nelli cannot see.
    "; " & bprof.assumedAbsentNote())

proc opaqueRaiseForks*(w: var WalkCtx; paths: seq[Path];
                      stmt: IRStmt): seq[Path] =
  ## RFC-0005 S8ax. The raises of an inert opaque call that returned on
  ## `paths` (its writes already havocked). Before S8ax the call never
  ## raised: `try: boom(v) except ValueError: ...` was a false `sxUnsat`,
  ## and a target after a call that always raises a false `sxSat`, both
  ## with nothing recorded.
  ##
  ## * Each type its `raises` list names (`IRStmt.opaqueRaises`) is raised
  ##   on a fork of every path, routed like any raise (`routeRaise`). The
  ##   fork does not know WHEN the call raises, so it is a superset:
  ##   `feOpaqueEffectHavoc` (`dcFreshSymbol`), replayed on a hit. The path
  ##   that returns assumes the call did not raise, a superset too, and
  ##   carries the same kind.
  ## * RFC-0005 S8be: so is each `Defect` type its body may raise
  ##   (`IRStmt.opaqueDefects`, scanned by the parser), which no `raises`
  ##   list names. Before S8be the walk raised none: `IndexDefect` out of an
  ##   opaque call was a false `sxUnsat`, and a `finally` reached only
  ##   through it was never walked (S8ax tainted the path where an arm
  ##   caught Defects, and dropped the rest).
  ## * RFC-0005 S8be: the object raised may be of a subtype of the type
  ##   named. Each strict subtype a `try` arm around the call names, or the
  ##   search's `tRaisedExn` filter names, is raised on a fork of its own
  ##   (`raiseSplit`), so `except SubErr:` sees the raise it catches. Before
  ##   S8be such an arm declined the call (`feOpaqueCallUnmodelled`). An arm
  ##   naming a type the hierarchy does not know still does: it may be a
  ##   subtype the split cannot see.
  # RFC-0016 K10b (section 9.1 item 3): on the whole-run gate's second walk
  # an opaque call whose body may be undefined (`IRStmt.opaqueUndefined`, the
  # parameterised scan's answer) ends every path that concretely reaches it:
  # what the call does is not modelled, so nothing past it is shown defined.
  # The kinds are recorded as the halt's reason; `verifyTailDefined` folds
  # them into the winner's `witnessUndefined`. A path the pins rule out
  # records nothing. The explore walk and the concolic collect never enter.
  if w.tailGate and stmt.opaqueUndefined != {}:
    var reached = false
    for p in paths:
      if not concretelyInfeasible(w.z3, w.concreteEq,
                                  p.pc & p.defectSurvivorPc, w.settings):
        reached = true
    # RFC-0016 W3-z R7: a body that is undefined only through the proc-valued
    # variables it calls through is walked past, as the explore walk does
    # (`noteOpaqueUndefined`); the kinds are reported apart (`tailVia`), and
    # a replay that names the routines the variables held may replace them.
    if reached and stmt.opaqueUndefinedFixed == {}:
      w.tailVia = w.tailVia + stmt.opaqueUndefined
      for k in stmt.opaqueUndefinedVia:
        if k notin w.procValueSites: w.procValueSites.add k
    elif reached:
      var kinds: seq[string]
      for k in stmt.opaqueUndefined: kinds.add $k
      for k in stmt.opaqueUndefined:
        w.halted(k,
          "opaque call `" & stmt.callee & "` after the label: its body may " &
          "be undefined (" & kinds.join(", ") & "), so the run is not shown " &
          "defined past it (RFC-0016 K10b whole-run gate)")
      return @[]
  let raised = stmt.opaqueRaises & stmt.opaqueDefects
  if raised.len == 0: return paths
  let dRet = w.degrade(feOpaqueEffectHavoc,
    "opaque call `" & stmt.callee & "` may raise " &
         raised.join(", ") & ": a path through it is forked for " &
         "each, and the path past it assumes it returned, so a hit on " &
         "either is replayed (feOpaqueEffectHavoc)")
  for p in paths:
    for t in raised:
      let split = raiseSplit(w, t)
      for st in split.types:
        if w.shouldStop: return
        var rp = forkPathTainted(p, p.pc, p.env, dRet)
        if split.unknown.len > 0:
          rp = forkPathTainted(rp, rp.pc, rp.env, w.degrade(
            feOpaqueCallUnmodelled,
            "opaque call `" & stmt.callee & "` may raise " & t &
                 ", and a `try` arm around it names " &
                 split.unknown.join(", ") & ", which the exception " &
                 "hierarchy does not know: it may be a subtype the " &
                 "raise is not split into (feOpaqueCallUnmodelled)"))
        result.add walkExprHooks.routeRaise(rp, st, none(string), w)
    result.add forkPathTainted(p, p.pc, p.env, dRet)


proc degradeUnmodelledReassign*(p: Path, objName: string, kind: SVKind,
                               w: var WalkCtx): Path =
  ## RFC-0005 S8i. A discriminator reassignment (`v.kind = ...`) whose
  ## object is not a modelled variant: its construction was DECLINED
  ## (`isVariantConstructSym`'s recorded decline leaves the destination
  ## unbound, and the parser's A-normalised read of it havocs a scalar
  ## placeholder). Both reassignment arms `doAssert`ed a variant there, so
  ## the recorded decline surfaced as `weInternalWalkerFault`. Now the
  ## reassignment degrades through the same channel: the object is
  ## unbound again (a later read havocs, as the first one did) and the
  ## path carries its own `feUnsupportedOp` token. Not
  ## `feUnsupportedOpHavoc`: the reassignment's branch-change `FieldDefect`
  ## fork (S8f) is dropped here, and a site that drops a raise is
  ## `dcSubstituted` by the §3.2 standing rule -- the kind already lists
  ## "variant reassignment" among its sites.
  let d = w.degrade(feUnsupportedOp,
    "discriminator reassignment of `" & objName & "`, which is not a " &
    "modelled variant (kind " & $kind & "; its construction was declined) " &
    "-- the object is left unmodelled (feUnsupportedOp)")
  var env = p.env
  env.del(objName)
  forkPathTainted(p, p.pc, env, d)

proc forkDefect*(p: Path, defectCond: Z3Bool, typeId: string,
                msg: Option[string], w: var WalkCtx): seq[Path] =
  ## Phase 16 D1a. Unconditionally fork the defect sub-path (constrained by
  ## `defectCond`) and route it through `routeRaise` so a try/except handler
  ## can CATCH it (gating on the *defect condition* not the *target* is what
  ## lets `try: arr[i] except IndexDefect` be modeled). routeRaise checks
  ## satisfiability via trySolve, respects `defectExclusions` (E6), and at the
  ## SUT boundary surfaces sxRaised{isDefect:true, raisedWitness}. Returns its
  ## result (@[] at the boundary; caught continuations exit via the caught
  ## channel). The caller continues the NON-defect path separately.
  let defectPath = forkPath(p, p.pc & @[defectCond], p.env)
  walkExprHooks.routeRaise(defectPath, typeId, msg, w)

proc decideUndefined*(cur: Path; ub: UbKind; cond: Z3Bool; site: string;
                     w: var WalkCtx) =
  ## RFC-0016 W1-d1a / PRC-07. The undefined side `cond` of an op on `cur`,
  ## decided at the op: provably unreachable under `loopPruneRLimit` is
  ## dropped and logged in the current call's prune window (`logPrune`),
  ## anything else ends through `haltUndefined`. Under concolic follow the
  ## flip solve must keep the op defined (`definedFacts`). The caller
  ## continues the defined side itself.
  if guardLiteral(cond) == glFalse: return
  if w.mode == wmFollowConcrete:
    # RFC-0016 K10a-concolic: the flip solve must keep this op defined.
    w.definedFacts.add ConcolicDefinedFact(
      cond: cond, kind: ub, site: site, at: w.branchTrace.len)
  # RFC-0016 INT-58: the side is decided first under the pruning budget,
  # and a side that budget leaves undecided is asked again under the
  # target query's own (`queryRLimit`), as the halt's own solve would be.
  # The side's query is the path's plus one condition, as hard as the
  # target's, and an undecided side ends the path untrusted: under the
  # pruning budget alone a floating-point rounding (`int(round(float(a) /
  # 4.0))`) ran out on every conversion and no unsat past one was trusted.
  var unsat = false
  if guardLiteral(cond) != glTrue:
    let roots = pathRoots(cur, [cond])
    let pruneLimit = loopPruneRLimit(w.settings)
    var st = refuteStatus(w.z3, roots, w.settings, pruneLimit)
    let q = w.settings.budget.queryRLimit
    if st == zsUnknown and (q == 0 or q > pruneLimit):
      st = refuteStatus(w.z3, roots, w.settings, q)
    unsat = st == zsUnsat
  if unsat:
    logPrune(cur, [cond])
  else:
    haltUndefined(cur, ub, cond, site, w)

proc drainConvFloatToIntFresh*(p: Path, w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8g, rerouted by RFC-0016 K10a-float (section 9.1 item 2).
  ## Decide the continuation of an expression that lowered float -> int
  ## conversions on their DOMAIN (the `convFloatToIntBoundConds` sink: each
  ## operand's truncation fits its target type). Nim 2.2.10 emits a plain C
  ## cast and range-checks the CAST value (a tautology), so no check profile
  ## raises, and a NaN, infinite or too-large operand is undefined behaviour:
  ## the `convert/floatToInt` row of the definedness axis (every profile alike).
  ##   * the OUT-OF-DOMAIN side (some conversion's operand is outside) is
  ##     decided at the op, as `drainArithTraps` decides a trap: provably
  ##     unreachable under `loopPruneRLimit` is dropped and logged
  ##     (`logPrune`), anything else ends through `haltUndefined`
  ##     (`ubFloatToIntRange`: a finding under `tUndefined`, listed under
  ##     another target, never a value);
  ##   * the IN-RANGE continuation is `p` with the conjunction of the domains
  ##     in its `pc` -- clean, and exact (the lowered `ite(domain, exact,
  ##     fresh)` can no longer select the fresh arm there).
  ## Before K10a-float the other side continued on a path tainted
  ## `feConvFloatToIntUndefined` with a fresh value; under the time-travel
  ## rule that was not sound for a trusted `sxUnsat` either.
  let conds = w.sinks.convFloatToIntBoundConds
  w.sinks.convFloatToIntBoundConds = @[]
  if conds.len == 0:
    return @[p]
  var inDomain = conds[0].cond
  for i in 1 ..< conds.len: inDomain = inDomain and conds[i].cond
  let cur = forkPath(p, p.pc, p.env)
  let profile = defProfile()
  # One undefined side per conversion, each under its own site: the side
  # of conversion `i` is reached when every earlier one is in range (they
  # evaluate in order and an undefined one ends the path).
  var before: seq[Z3Bool]
  for c in conds:
    let outside = not c.cond
    let convUb = convertDefinedness(c.cls, profile).ubOf
    if convUb.isSome and guardLiteral(outside) != glFalse:
      # Through `decideUndefined` so a concolic replay records the
      # defined-fact the flip solve must keep (RFC-0016 W3-z R4 / U4). The
      # earlier conversions' domains ride in the side's own path, so the
      # fact is this conversion's `outside` alone.
      decideUndefined(forkPath(cur, cur.pc & before, cur.env), convUb.get, outside,
                      (if c.site.len > 0: "float -> int conversion at " & c.site
                       else: "float -> int conversion"), w)
    before.add c.cond
  @[forkPath(cur, cur.pc & @[inDomain], cur.env)]

template genRaiseForkDrain*(procName, field: untyped; gate: static[Option[ArithCheck]];
                            defectType, msg: string;
                            boundSite: string = "") =
  ## R5 dedup. Generates a scalar-raise-fork drain proc of the shape shared by
  ## `drainParseIntRaises`/`drainDivByZeroRaises`/`drainOverflowRaises`/
  ## `drainStrIndexRaises` (was 4 near-identical bodies differing only in the
  ## sink field, an optional settings-gate, the routed defect-type string, and
  ## the message). Each generated proc:
  ##  - reads and resets `w.sinks.field` (the raise-predicate sink accumulated
  ##    by the just-completed `lower`/`lowerBool` call; its only store, which
  ##    the `sync*` deposits fill through `currentLowerSinks`), so a
  ##    subsequent lower() starts clean (idempotent).
  ##  - `gate` is `none(ArithCheck)` for an unconditional drain (parseInt/
  ##    str-index — no opt-out) or `some(acFoo)` for a build-gated drain
  ##    (div-by-zero/overflow). When `gate` is `some` and the build does NOT
  ##    check it (`checked`), or there are no drained predicates, returns
  ##    `@[p]` unchanged — honest-incomplete.
  ##  - otherwise forks each predicate `c` into its own RAISES sub-path
  ##    (`p.pc & @[c]`), routed via E3's `routeRaise(…, defectType, msg, w)`
  ##    (which either transfers it into a surrounding `except` or surfaces a
  ##    public `sxRaised{defectType}` at the SUT boundary, then terminates the
  ##    raise path); the survivor continuation is `p` unchanged, with the
  ##    conjunction of all negated predicates riding in `defectSurvivorPc`
  ##    (ADR-0012: defect-survivor FEASIBILITY facts, not branch selectors —
  ##    asserted by trySolve, inherited by forkPath, excluded from a closure
  ##    return-axiom's implication guard).
  ##
  ## This drain always forks from the POST-lower path `p` directly.
  proc procName(p: Path, w: var WalkCtx): seq[Path] =
    let conds = w.sinks.field
    w.sinks.field = @[]
    # `gate` is a compile-time `static[Option[ArithCheck]]`. `none(ArithCheck)`
    # means "unconditional drain" (parseInt/str-index) — never early-returns on
    # the gate. `some(acFoo)` (div-by-zero/overflow) is build-gated: skip
    # (honest-incomplete) unless that check is enabled.
    if (gate.isSome and not checked(gate.get)) or conds.len == 0:
      return @[p]
    if boundSite.len > 0:
      # RFC-0016 PRC-07: a drain of bound checks. With `boundChecks` off no
      # `IndexDefect` exists: each out-of-container side is an undefined
      # access, decided at the op, and the defined side continues.
      if boundsUnchecked():
        var cur = forkPath(p, p.pc, p.env)
        for c in conds:
          decideUndefined(cur, uncheckedIndexUb(), c, boundSite, w)
          cur = forkPath(cur, cur.pc & @[not c], cur.env)
        return @[cur]
    for c in conds:
      let raisePath = forkPath(p, p.pc & @[c], p.env)
      discard walkExprHooks.routeRaise(raisePath, defectType, some(msg), w)
    var negated: seq[Z3Bool]
    for c in conds:
      negated.add(not c)
    let surv = forkPath(p, p.pc, p.env)
    for n in negated: surv.defectSurvivorPc.add n
    @[surv]

proc drainParseIntRaises*(p: Path, w: var WalkCtx): seq[Path] =
  ## Phase 15 S10b. parseInt raise predicates from `iekStrToInt` —
  ## unconditional (no settings gate). Same read-and-reset / fork /
  ## `defectSurvivorPc` protocol as the `genRaiseForkDrain` family above
  ## (which it was, until RFC-0005 S10), with ONE difference: each lowering
  ## deposits a `ParseIntRaise` pair, and the two halves fork differently.
  ##   * `exact` forks a CLEAN routed `ValueError` raise -- on those inputs
  ##     the model is Nim's `parseInt` (RFC-0005 S8b: sign, digits, range).
  ##   * `lax` (a `_` separator: the value needs `str.replace_all`) forks
  ##     BOTH outcomes on paths tainted through `degrade`
  ##     (`seParseIntLaxSyntax`, `dcFreshSymbol` -> `{scSpurious}`): the
  ##     raise, whose boundary `sxRaised` is a CANDIDATE (`admitSolvedHit`)
  ##     that RFC-0005 S10's replay confirms (`"1_x"` raises for real) or
  ##     refutes (`"1_0"` parses to 10) -- §2.6's replay-gated raise -- and,
  ##     since RFC-0005 S8b, the digits continuation on the lowering's fresh
  ##     `__parseIntLaxValue` (S10 dropped it: the survivor carried `not
  ##     lax`, so a target reachable only through a `_`-string was a false
  ##     `sxUnsat`). The error is recorded ONCE per drain whose `lax` half
  ##     does not simplify to `false` (a literal operand has no lax inputs,
  ##     so it forks and records nothing); a symbolic operand's lax forks are
  ##     taken without a feasibility check, as at every other fork site. Its
  ##     run coordinate `{scSpurious}` is diagnostics-only, so `sxUnsat` is
  ##     unaffected.
  ## The clean survivor carries `not exact` and `not lax`; the tainted lax
  ## survivor carries every `not exact` plus the disjunction of the live
  ## `lax` halves -- together every input on which Nim does not raise.
  let conds = w.sinks.parseIntRaiseConds
  w.sinks.parseIntRaiseConds = @[]
  if conds.len == 0:
    return @[p]
  const msg = "invalid integer: parseInt"
  var laxLive: seq[bool]
  for c in conds: laxLive.add($simplify(c.lax) != "false")
  var laxTok: Degrade
  if true in laxLive:
    laxTok = w.degrade(seParseIntLaxSyntax,
      "parseInt: a `_` digit separator, which Nim's parseInt skips and " &
      "Z3's str.to_int rejects -- both the ValueError raise and the parsed " &
      "value there are over-approximated (seParseIntLaxSyntax; replay-gated " &
      "candidates)")
  var anyLax: Z3Bool
  var anyLaxInit = false
  for i, c in conds:
    let exactPath = forkPath(p, p.pc & @[c.exact], p.env)
    discard walkExprHooks.routeRaise(exactPath, "ValueError", some(msg), w)
    if laxLive[i]:
      let laxPath = forkPathTainted(p, p.pc & @[c.lax], p.env, laxTok)
      discard walkExprHooks.routeRaise(laxPath, "ValueError", some(msg), w)
      if anyLaxInit: anyLax = anyLax or c.lax
      else:
        anyLax = c.lax
        anyLaxInit = true
  let surv = forkPath(p, p.pc, p.env)
  for c in conds:
    surv.defectSurvivorPc.add(not c.exact)
    surv.defectSurvivorPc.add(not c.lax)
  result = @[surv]
  if anyLaxInit:
    # RFC-0005 S8b: the `_`-string continuation, on the fresh lax value.
    let laxSurv = forkPathTainted(p, p.pc, p.env, laxTok)
    for c in conds: laxSurv.defectSurvivorPc.add(not c.exact)
    laxSurv.defectSurvivorPc.add anyLax
    result.add laxSurv

## Phase 16 R16-3. div/mod-by-zero predicates from `lowerArith` (bDiv/bMod on
## svInt or BV operands). Gated by `acDivByZero`: when disabled, honest-
## incomplete (the division result is still usable, matching pre-R16-3
## behavior).
genRaiseForkDrain(drainDivByZeroRaises, divByZeroConds, some(acDivByZero),
                   "DivByZeroDefect", "division by zero")

## Phase 16 R16-4. Signed integer overflow predicates from `lowerArith`
## (bAdd/bSub/bMul on signed BV operands — svInt and unsigned BV produce no
## entries). Gated by `acOverflow`: when disabled, honest-incomplete
## (arithmetic result still usable, matching pre-R16-4 behavior).
genRaiseForkDrain(drainOverflowRaises, overflowConds, some(acOverflow),
                   "OverflowDefect", "integer overflow")

## RFC-chapulin-hardening SND-4 (ADR-0024). String-index (`s[i]`)
## out-of-bounds predicates from `lowerStrArm`'s `iekStrAt` arm — parity with
## the seq/array/Table indexing arms' unconditional `forkDefect` (Phase 16
## D1a), which already model `IndexDefect` for every OTHER container index;
## `s[i]` was the sole gap. Unconditional (no build-check opt-out
## gate) — mirrors the seq/array `isIndex` arm's `forkDefect` call.
genRaiseForkDrain(drainStrIndexRaises, strIndexOobConds, none(ArithCheck),
                   "IndexDefect", "string index out of bounds",
                   "a string index or slice bound outside the string")

## N14 (RFC-chapulin-hardening bucket-2). seq `del(i)` out-of-bounds
## predicates from `lower`'s `iekSeqDel` arm. Unconditional (no
## build-check opt-out gate) — mirrors `drainStrIndexRaises`'s own
## unconditional IndexDefect parity argument (every OTHER container mutation
## site with a bounds check, `isIndexAssign`, forks unconditionally too).
genRaiseForkDrain(drainSeqOobRaises, seqOobConds, none(ArithCheck),
                   "IndexDefect", "index out of bounds",
                   "a seq slice bound or `del` index outside the seq")

## RFC-0005 S8g. `RangeDefect` predicates from a lowering: a `range`
## target's check on a float -> int conversion (`Natural(f)`), a negative
## slice length, `del`'s `Natural` index. Gated by `acRange`, like every
## range check (Nim's `rangeChecks`): when disabled, honest-incomplete.
genRaiseForkDrain(drainRangeRaises, rangeDefectConds, some(acRange),
                   "RangeDefect", "value out of range")

proc drainUninitReads*(p: Path, w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8bv (item 4). Fork the continuation of an expression whose
  ## inline `map` / `filter` / `fold` may have read an unwritten
  ## `newSeqUninit` element (the `uninitReadConds` sink, one condition per
  ## such read): where none did, `p` with the negated disjunction among its
  ## defect-survivor facts -- clean and exact; where one did, `p` with the
  ## disjunction, tainted `uninitReadKind` (the read value is a superset of
  ## what the allocation held). As `drainConvFloatToIntFresh`'s split, the
  ## facts select between two models of one execution, not a program branch.
  let conds = w.sinks.uninitReadConds
  w.sinks.uninitReadConds = @[]
  if conds.len == 0:
    return @[p]
  var anyRead = conds[0]
  for i in 1 ..< conds.len: anyRead = anyRead or conds[i]
  let surv = forkPath(p, p.pc, p.env)
  surv.defectSurvivorPc.add(not anyRead)
  result = @[surv]
  let tok = w.degrade(uninitReadKind, uninitReadMsg)
  let alt = forkPathTainted(p, p.pc, p.env, tok)
  alt.defectSurvivorPc.add anyRead
  result.add alt

proc drainArithTraps*(p: Path, w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8i. Drain the arithmetic-trap sink (see the `arithTrapConds`
  ## threadvar): the continuation `p` gains each trap predicate's negation
  ## and nothing is forked -- a SIGFPE aborts the process, so there is no
  ## raise to route and no execution past it. Ungated: the build's checks model
  ## Nim's runtime checks, and this is the hardware's, which no check setting
  ## removes.
  ##
  ## RFC-0016 W1-d1a (section 9.1 item 2). A deposit marked `ub` is not a
  ## definite hardware outcome but undefined behaviour (the trap's own kind)
  ## and is decided at the op: the undefined side's reachability is asked of
  ## the solver on the path's full query under `loopPruneRLimit`. UNSAT: the
  ## side is dropped and the fact logged in the current call's prune window
  ## (`logPrune`). SAT or UNKNOWN: it ends through `haltUndefined`. The
  ## defined side continues with the negation in its `pc`, not in
  ## `defectSurvivorPc` (which would make a callee uncacheable). The other
  ## deposits (`div` with the checks on, where the `OverflowDefect` fork
  ## already took the side) still confine the survivor through
  ## `defectSurvivorPc`.
  let conds = w.sinks.arithTrapConds
  w.sinks.arithTrapConds = @[]
  if conds.len == 0:
    return @[p]
  var cur = forkPath(p, p.pc, p.env)
  for t in conds:
    if t.raiseName.len > 0:
      # RFC-0016 PRC-07 (float half): Nim's float check, a catchable raise.
      let rp = forkPath(cur, cur.pc & @[t.cond], cur.env)
      discard walkExprHooks.routeRaise(rp, t.raiseName, some(t.site), w)
      cur.defectSurvivorPc.add(not t.cond)
    elif t.ub.isSome:
      decideUndefined(cur, t.ub.get, t.cond, t.site, w)
      let nxt = forkPath(cur, cur.pc & @[not t.cond], cur.env)
      cur = nxt
    else:
      cur.defectSurvivorPc.add(not t.cond)
  @[cur]

proc drainRegexRaises*(p: Path, w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8ay. Route the expression's `RegexError` (see the
  ## `regexRaiseMsgs` threadvar). `re` raises whenever the call runs, so
  ## the raise takes the whole path: it is routed with the FIRST message
  ## (the first rejected pattern evaluated) and there is no continuation.
  ## Ungated: `RegexError` is a `ValueError`, not a runtime check. RFC-0005
  ## S8bb: a stage at the raise's place in evaluation order
  ## (`drainScalarRaiseForks`), so a raise the expression evaluates later
  ## is never forked; the parser lowers only the arguments BEFORE a
  ## rejected pattern (`regexCall`).
  let msgs = w.sinks.regexRaiseMsgs
  w.sinks.regexRaiseMsgs = @[]
  if msgs.len == 0:
    return @[p]
  let rp = forkPath(p, p.pc, p.env)
  discard walkExprHooks.routeRaise(rp, "RegexError", some(msgs[0]), w)
  @[]

proc drainClosureRaises*(p: Path; exitFactsPlaced: bool;
                        w: var WalkCtx): seq[Path] =
  ## RFC-0005 S7. Route the raises that escaped a closure body during the
  ## just-completed `lower`/`lowerBool` (deposited by `applyClosureGround`
  ## into `w.closureRaises`) from the CALLING path `p`, as the `isCall` arm
  ## routes a named callee's escaped raises. Each raise sub-path forks from
  ## the escaped raise's own path (its exit heap and its taint ride out --
  ## the `forkPathMerged` return-merge shape, joined with `p`'s taint), with
  ## `p`'s pc, the body's condition for reaching the raise, `p`'s env and
  ## both sides' defect-survivor facts. The survivor needs no negation here:
  ## the call's exit-coverage fact (`applyClosureGround`) already confines the
  ## caller continuation to the body's value-bearing exits.
  ##
  ## RFC-0005 S8bi: `p` is a survivor of the stages before this call's
  ## raises, in evaluation order (`drainScalarRaiseForks`). It carries the
  ## exit facts of the closure calls that completed earlier and none of this
  ## call's or a later one's, which `drainScalarRaiseForks` stripped from
  ## the drained path and puts back at their `rskClosureExit` stages
  ## (`exitFactsPlaced`). S7 stripped them here instead, from the drained
  ## path, and added the earlier calls' facts back from the raise.
  let raises = w.closureRaises
  w.closureRaises = @[]
  if raises.len == 0:
    return @[p]
  var kept = exact(@[p])
  if not exitFactsPlaced:
    # Not reachable by construction (every raise drain runs on the path
    # `drainPendingLowerEffects` just returned, whose tail is exactly the
    # facts it appended); if it ever is, the raise would be forked under its
    # own negation -- record the walker fault and route the raises anyway
    # rather than drop them silently. RFC-0016 K7a: recorded-but-continued,
    # so the survivor carries the fault's path coordinate.
    kept = continued(@[p], w.degrade(weInternalWalkerFault,
      "closure raise drained on a path whose defect-survivor tail is not " &
      "the last drained closure exit facts (RFC-0005 S7 drainClosureRaises)"))
  for cr in raises:
    let er = cr.raised
    # RFC-0005 S8as: the raising exit's own by-reference writes.
    var renv = p.env
    for (k, v) in cr.writes: renv[k] = v
    var rp = forkPathMerged(er.path, p.pc & er.path.pc, renv, p)
    # RFC-0005 S8bh: the `var` actuals hold what the body had written to
    # them where it raised.
    for o in cr.varOuts: rp.env[o.name] = o.val
    rp.defectSurvivorPc = p.defectSurvivorPc & er.path.defectSurvivorPc
    rp.heapDepth = p.heapDepth
    if er.crash: crashRaise(rp, er.typeId, w)       # RFC-0005 S8cu
    else: discard walkExprHooks.routeRaise(rp, er.typeId, er.msg, w)
    if w.shouldStop: break
  kept.live

proc drainScalarRaiseForks*(p: Path, w: var WalkCtx): seq[Path] =
  ## RFC-0005 S7: routes any closure-body raises (`drainClosureRaises`).
  ## RFC-0005 S8g: forks an expression's float -> int conversions on
  ## their domain (`drainConvFloatToIntFresh`: clean in range, a tainted
  ## fresh value outside).
  ## R16-4 + SND-4 + N14 + S8g: forks the parseInt, div/mod-by-zero,
  ## signed-integer-overflow, string-index-OOB, seq-del-OOB and RangeDefect
  ## raises (RFC-0005 S8i: plus the survivor-only arithmetic-trap drain),
  ## and RFC-0005 S8ay the `RegexError` of a rejected pattern. Each stage
  ## feeds the survivors of the previous stage so every combination of
  ## independent defect conditions is explored.
  ##
  ## RFC-0005 S8bb: the stages run in EVALUATION order. `w.sinks.raiseOrder` logs
  ## the sink of every deposit; the log is cut into runs of consecutive
  ## deposits to one sink, and each run is a stage over exactly its own
  ## deposits. Before S8bb the stages ran in the fixed sink order above
  ## whatever the expression's order: in `int(s.match(re"a**")) +
  ## parseInt(t)` the `ValueError` of `parseInt` was forked although Nim
  ## raises `RegexError` first and never runs it, and in `ord(s[i]) ==
  ## parseInt(t)` the `ValueError` fork lacked the index's survivor fact.
  ## The regex stage has no survivor, so a run after it is never drained.
  ## A deposit the log does not cover (a sink a reset site cleared without
  ## the log) drains after the logged runs, in the fixed order.
  ##
  ## RFC-0005 S8bi: the closure exit facts are a stage too. A closure call's
  ## facts (that each body exit did not raise, and that the body left
  ## through a value-bearing exit) hold only once the call completed, but
  ## `drainPendingLowerEffects` appends them to the drained path, so every
  ## raise this expression evaluated BEFORE the call was forked under them:
  ## in `while ord(s[i]) + f(x) > 0` with `f` raising for `x > 5`, the
  ## `IndexDefect` of `s[i]` was forked only with `x <= 5`, a false `sxUnsat`
  ## for a handler reached with `x > 5`. They are now stripped from the
  ## drained path (`lastDrainedClosureExitPc`, its tail) and put back one
  ## `rskClosureExit` run at a time, at the place the order log gives them.
  ## A path whose tail is not those facts keeps them as they are.
  ##
  ## RFC-0005 S8g: each stage's sink is read ONCE here and reinstated before
  ## the stage runs on EACH survivor. The drains read-and-reset their sink,
  ## so before this a stage that returned two survivors (the parseInt lax
  ## continuation, since S8b) fed the next stage's raises to the FIRST
  ## survivor only: the second continued with no overflow / index / ... fork
  ## at all.
  let closureSnap = w.closureRaises
  let convSnap = w.sinks.convFloatToIntBoundConds
  let parseSnap = w.sinks.parseIntRaiseConds
  let divSnap = w.sinks.divByZeroConds
  let ovfSnap = w.sinks.overflowConds
  let strSnap = w.sinks.strIndexOobConds
  let seqSnap = w.sinks.seqOobConds
  let rangeSnap = w.sinks.rangeDefectConds
  let trapSnap = w.sinks.arithTrapConds
  let uninitSnap = w.sinks.uninitReadConds
  let regexSnap = w.sinks.regexRaiseMsgs
  let order = w.sinks.raiseOrder
  w.sinks.raiseOrder = @[]
  # RFC-0005 S8bi: the closure exit facts, placed by the order log when the
  # drained path ends with exactly them (it does whenever this runs on the
  # path `drainPendingLowerEffects` returned).
  let exitSnap = lastDrainedClosureExitPc
  lastDrainedClosureExitPc = @[]
  var start = p
  var exitFactsPlaced = currentClosureExitPc.len == 0 and
                        p.defectSurvivorPc.len >= exitSnap.len
  if exitFactsPlaced:
    let off = p.defectSurvivorPc.len - exitSnap.len
    for k in 0 ..< exitSnap.len:
      if p.defectSurvivorPc[off + k].raw != exitSnap[k].raw:
        exitFactsPlaced = false
        break
    if exitFactsPlaced and exitSnap.len > 0:
      start = forkPath(p, p.pc, p.env)
      start.defectSurvivorPc.setLen(off)
  # Every sink starts empty: a run reinstates only its own slice, and a
  # run the regex stage cuts off must not leave its deposits behind.
  w.closureRaises = @[]
  w.sinks.convFloatToIntBoundConds = @[]
  w.sinks.parseIntRaiseConds = @[]
  w.sinks.divByZeroConds = @[]
  w.sinks.overflowConds = @[]
  w.sinks.strIndexOobConds = @[]
  w.sinks.seqOobConds = @[]
  w.sinks.rangeDefectConds = @[]
  w.sinks.arithTrapConds = @[]
  w.sinks.uninitReadConds = @[]   # RFC-0005 S8bv
  w.sinks.regexRaiseMsgs = @[]
  var total: array[RaiseSinkKind, int]
  total[rskClosure] = closureSnap.len
  total[rskConvBound] = convSnap.len
  total[rskParseInt] = parseSnap.len
  total[rskDivByZero] = divSnap.len
  total[rskOverflow] = ovfSnap.len
  total[rskArithTrap] = trapSnap.len
  total[rskStrIndex] = strSnap.len
  total[rskSeqOob] = seqSnap.len
  total[rskRange] = rangeSnap.len
  total[rskRegex] = regexSnap.len
  total[rskUninitRead] = uninitSnap.len
  total[rskClosureExit] = (if exitFactsPlaced: exitSnap.len else: 0)
  var used: array[RaiseSinkKind, int]
  var runs: seq[tuple[k: RaiseSinkKind, lo, hi: int]]
  for k in order:
    if used[k] >= total[k]: continue
    if runs.len > 0 and runs[^1].k == k and runs[^1].hi == used[k]:
      inc runs[^1].hi
    else:
      runs.add (k, used[k], used[k] + 1)
    inc used[k]
  for k in RaiseSinkKind:
    if used[k] < total[k]: runs.add (k, used[k], total[k])
  template stage(inp: seq[Path]; sink, snap, lo, hi, drain: untyped): seq[Path] =
    var outp: seq[Path]
    for s in inp:
      w.sinks.sink = snap[lo ..< hi]
      outp.add drain(s, w)
    outp
  var cur = @[start]
  for run in runs:
    if cur.len == 0: break
    let (lo, hi) = (run.lo, run.hi)
    case run.k
    of rskClosure:
      var outp: seq[Path]
      for s in cur:
        w.closureRaises = closureSnap[lo ..< hi]
        outp.add drainClosureRaises(s, exitFactsPlaced, w)
      cur = outp
    of rskClosureExit:
      # RFC-0005 S8bi: the call completed on every survivor; a fork, so a
      # sibling's fact list is never aliased.
      var outp: seq[Path]
      for s in cur:
        var q = forkPath(s, s.pc, s.env)
        for k in lo ..< hi: q.defectSurvivorPc.add exitSnap[k]
        outp.add q
      cur = outp
    of rskConvBound:
      cur = stage(cur, convFloatToIntBoundConds, convSnap, lo, hi,
                  drainConvFloatToIntFresh)
    of rskParseInt:
      cur = stage(cur, parseIntRaiseConds, parseSnap,
                  lo, hi, drainParseIntRaises)
    of rskDivByZero:
      cur = stage(cur, divByZeroConds, divSnap, lo, hi,
                  drainDivByZeroRaises)
    of rskOverflow:
      cur = stage(cur, overflowConds, ovfSnap, lo, hi,
                  drainOverflowRaises)
    of rskArithTrap:
      # RFC-0005 S8i: `lowerArith` deposits a trap after its overflow
      # raise, so a `low(T) div -1` raises `OverflowDefect` (Nim's check
      # runs first) and only its survivor is confined off the trap.
      cur = stage(cur, arithTrapConds, trapSnap, lo, hi,
                  drainArithTraps)
    of rskStrIndex:
      cur = stage(cur, strIndexOobConds, strSnap, lo, hi,
                  drainStrIndexRaises)
    of rskSeqOob:
      cur = stage(cur, seqOobConds, seqSnap, lo, hi,
                  drainSeqOobRaises)
    of rskRange:
      cur = stage(cur, rangeDefectConds, rangeSnap, lo, hi,
                  drainRangeRaises)
    of rskRegex:
      cur = stage(cur, regexRaiseMsgs, regexSnap, lo, hi,
                  drainRegexRaises)
    of rskUninitRead:
      cur = stage(cur, uninitReadConds, uninitSnap, lo, hi,
                  drainUninitReads)
  cur

proc drainClosureExitHeap*(p: Path): Path =
  ## Phase 15 CR-1. Apply the exit heap from the most recent `applyClosureGround`
  ## call back to the caller path `p` (the path that is about to become the
  ## post-call survivor). Mirrors the named-proc return-merge (isCall arm
  ## ~5443-5463): the closure's exit `heaps` replace the caller's; `allocCounters`
  ## are max-merged; `liveRefs` are union-merged so subsequent caller `new T`s
  ## are distinct from closure-allocated refs too.
  ##
  ## Returns a NEW path forked from `p` (via `forkPath` deep-copy) with the
  ## merged heap state. If `currentClosureDidMutateHeap` is false (the closure
  ## wrote nothing / is heap-write-free), returns `p` unchanged (no-op, zero cost).
  ##
  ## Called immediately after `lower()` in `isLet`/`isAssign`/`isIf` walk arms
  ## that seed `seedCallerHeapThreadvars` before the `lower()` call.
  ##
  ## CR-9 Stage 6 Group-4: when a walk is active, read from WalkCtx fields
  ## (`closureDidMutateHeap`, `closureExitHeaps`, etc.) rather than the
  ## threadvars. Falls back to threadvars when `currentWalkCtxPtr == nil`.
  ## NOTE: `drainPendingLowerEffects` resets the exit-heap fields after this
  ## call — do NOT reset here (drainPendingLowerEffects is the single reset site).
  let didMutate = if currentWalkCtxPtr != nil:
    cast[ptr WalkCtx](currentWalkCtxPtr)[].closureDidMutateHeap
  else:
    currentClosureDidMutateHeap
  if not didMutate:
    return p                    # most closures are heap-write-free — fast path
  # Fork from `p` but with the closure's exit heap replacing the caller's.
  # `forkPath` deep-copies heap state from `p` first; then we overwrite the
  # fields that the closure exit merged into.
  let merged = forkPath(p, p.pc, p.env)
  let (exitHeaps, exitAlloc, exitLiveRefs) =
    if currentWalkCtxPtr != nil:
      let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
      (wp[].closureExitHeaps, wp[].closureExitAllocCounters, wp[].closureExitLiveRefs)
    else:
      (currentClosureExitHeaps, currentClosureExitAllocCounters, currentClosureExitLiveRefs)
  merged.heaps = exitHeaps
  merged.heapDepth = p.heapDepth     ## preserve caller depth (closure body may
                                      ## have descended further, but that depth is
                                      ## scoped to the descent — mirrors isCall arm)
  # max-merge allocCounters: post-closure caller allocs must not collide with
  # closure-allocated refs, exactly like the named-proc arm (line ~5459-5462).
  for tkey, closureCount in exitAlloc:
    let callerCount = merged.allocCounters.getOrDefault(tkey, 0)
    if closureCount > callerCount:
      merged.allocCounters[tkey] = closureCount
  # union-merge liveRefs: caller's subsequent `new T` must be distinct from
  # closure-allocated refs. The closure's liveRefs are a SUPERSET of the seeded
  # caller liveRefs (seeded from callerLiveRefs + new refs inside the body).
  # Replace with the closure exit's list — it is already the union.
  for tkey, refs in exitLiveRefs:
    merged.liveRefs[tkey] = refs
  merged

proc liveFrame*(w: WalkCtx; frame: int): bool =
  ## RFC-0005 S8ax. `frame` has not returned: it is the current frame or
  ## one below it.
  if w.frame.frameId == frame: return true
  for f in w.frameStack:
    if f.frameId == frame: return true
  false

proc deadElemRefs*(p: Path; w: WalkCtx): seq[Z3AnyAst] =
  ## RFC-0005 S8be. The element cells (`Path.elemCells`) whose memory Nim
  ## may have freed: one some frame saw its seq resized or assigned whole
  ## (`dead`), or one only returned frames held.
  for e in p.elemCells:
    let r = cast[pointer](e.refAst.raw)
    var dead = false
    var held = false
    for f in p.elemCells:
      if cast[pointer](f.refAst.raw) != r: continue
      if f.dead: dead = true
      elif liveFrame(w, f.frame): held = true
    if dead or not held:
      var seen = false
      for d in result:
        if cast[pointer](d.raw) == r: seen = true
      if not seen: result.add e.refAst

proc danglingCompareTaint*(p: Path; operands: seq[Z3AnyAst]): Path =
  ## RFC-0005 S8ax. `p` after an expression compared the `ptr` values
  ## `operands`: tainted (`feUnsupportedOp`) when one may be the address
  ## cell of a variable whose frame has returned (`Path.addrOwners`). Nim
  ## compares a dead stack slot's address there, which a later frame may
  ## reuse; the walk's cells stay distinct, so the outcome is not Nim's.
  if currentWalkCtxPtr == nil or operands.len == 0: return p
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  var dead: seq[Z3AnyAst]
  for o in p.addrOwners:
    if not liveFrame(wp[], o.frame): dead.add o.refAst
  # RFC-0005 S8be: an element's address whose memory Nim may have freed
  # (`deadElemRefs`) is likewise one a later allocation may reuse.
  dead.add deadElemRefs(p, wp[])
  if dead.len == 0: return p
  let ctx = wp[].z3
  var hits: seq[Z3Bool]
  for a in operands:
    for d in dead:
      hits.add wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, d.raw))
  var anyHit = hits[0]
  for i in 1 ..< hits.len: anyHit = anyHit or hits[i]
  if pathInfeasible(ctx, forkPath(p, p.pc & @[anyHit], p.env), wp[].settings):
    return p
  forkPathTainted(p, p.pc, p.env, wp[].degrade(feUnsupportedOp,
    "RFC-0005 S8ax: a pointer compared here may hold the address of a " &
         "variable whose routine has returned; Nim compares a dead stack " &
         "slot's address, which a later call may reuse (feUnsupportedOp)"))

proc drainPendingLowerEffects*(p: Path): Path =
  ## Phase 15 re-review (S-1/S-2/S-3/S-4/NI-1/NI-2 drain consolidation).
  ## Single choke-point that drains ALL out-of-band `lower()`/`lowerBool()`
  ## effects into path `p` and resets all associated threadvars so no stale
  ## effect leaks to the next `lower()` call:
  ##   (a) RFC-0005 S8g: none. Float→int domain bounds were folded into
  ##       `p.pc` here (a narrowing that dropped every out-of-range input);
  ##       they are now a FORK, `drainScalarRaiseForks`'s
  ##       `drainConvFloatToIntFresh` stage.
  ##   (b) Closure exit-heap state from `currentClosureExitHeaps/AllocCounters/
  ##       LiveRefs` is merged into the path's `heaps/allocCounters/liveRefs`
  ##       (via `drainClosureExitHeap`, conditional on `currentClosureDidMutateHeap`)
  ##       and all four exit-heap threadvars are reset to clean state.
  ##   (d) SND-3 (ADR-0023, walker v58): if the lowering queue is
  ##       non-empty (a lowering site returned a fresh unconstrained symbol
  ##       in-band instead of raising, via `queueDegrade`), fork the path
  ##       joining the taken queue as its `Degrade` token (`takePending`;
  ##       RFC-0005 S1; the run coordinate is derived at drain from the
  ##       recorded `loweringDegradeErrors`).
  ##
  ## USAGE CONVENTION (uniform pattern at every `lower()`/`lowerBool()` call site
  ## inside `walk`):
  ##   seedCallerHeapThreadvars(p)     # seed caller heap + reset exit-heap sink
  ##   convFloatToIntBoundConds = @[]  # reset float-bound sink
  ##   let sv = lower(p.env, expr)     # may deposit float bounds + closure writes
  ##   let p = drainPendingLowerEffects(p)  # drain + reset both sinks
  ##
  ## `seedCallerHeapThreadvars` still seeds the CALLER heap into threadvars
  ## (so a closure body descends with the right heap); this helper handles the
  ## drain and cleanup AFTER. Together they collapse what were two separate
  ## conventions (seed/drain float-bounds and seed/drain closure-exit-heap) into
  ## one auditable pair.
  let p1 = p   ## (a) RFC-0005 S8g: no narrowing (see above)
  var p2 = drainClosureExitHeap(p1)       ## (b) closure exit heap (conditional)
  # (c) Phase 16 ADR-0012: closure exit defect-survivor facts. A closure call
  # lowered during this lower() deposited each body exit path's `not overflow`/
  # `not divByZero`/`not parseIntRaise` negations (branch-guarded) here; thread
  # them onto the CALLER path's `defectSurvivorPc` as hard caller-local facts.
  # Fork before mutating so we never alias a sibling path's constraint list.
  lastDrainedClosureExitPc = currentClosureExitPc   ## RFC-0005 S7
  if currentClosureExitPc.len > 0:
    p2 = forkPath(p2, p2.pc, p2.env)
    for c in currentClosureExitPc: p2.defectSurvivorPc.add c
    currentClosureExitPc = @[]
  # (d) SND-3 (ADR-0023, walker v58). Fork BEFORE mutating (same rationale as
  # (c) above) so we never alias a sibling path's taint. This is the single
  # choke-point that folds an in-band lowering-degrade into the per-path
  # taint. RFC-0005 S1: the pending taint `queueDegrade` joined (one join per
  # recorded `loweringDegradeErrors` entry) becomes this path's `Degrade`
  # token; the RUN coordinate is no longer written here (was the
  # `currentWalkCtxPtr.sawUnknown` write) — it is derived at drain from the
  # very `loweringDegradeErrors` entries `queueDegrade` recorded.
  if not pendingIsEmpty():
    p2 = forkPathTainted(p2, p2.pc, p2.env, asDegrade(takePending()))
  # (e) RFC-0005 S8as: the by-reference writes of the expression's closure
  # calls land on the calling path (`closureEnvWrites`), in call order.
  if closureEnvWrites.len > 0:
    var env2 = p2.env
    for (k, v) in closureEnvWrites: env2[k] = v
    p2 = forkPath(p2, p2.pc, env2)
    closureEnvWrites = @[]
  # (e') RFC-0005 S8bh: the `var` formals' exit values of the closure calls
  # this lower() made, written to the caller variables their actuals name
  # (`applyClosureGround`), in call order. Before S8bh they were dropped: a
  # call through a proc value (`let f = setBoth; f(x, y)`) left `x` and `y`
  # as they were (a false `sxSat`). Fork before mutating, as above.
  if currentWalkCtxPtr != nil:
    let wo = cast[ptr WalkCtx](currentWalkCtxPtr)
    if wo[].closureVarOuts.len > 0:
      var env2 = p2.env
      for o in wo[].closureVarOuts: env2[o.name] = o.val
      p2 = forkPath(p2, p2.pc, env2)
      wo[].closureVarOuts = @[]
  # (f) RFC-0005 S8ax: a `ptr` comparison against a dead frame's cell.
  if pendingPtrCompares.len > 0:
    let operands = pendingPtrCompares
    pendingPtrCompares = @[]
    p2 = danglingCompareTaint(p2, operands)
  loweringReadNames = @[]
  # Reset exit-heap threadvars so a subsequent lower() that contains no closure
  # call does not see the prior call's heaps, and so drainPendingLowerEffects
  # is idempotent (safe to call again without an intervening seed).
  currentClosureDidMutateHeap = false
  currentClosureExitHeaps = initTable[string, Z3AnyAst]()
  currentClosureExitAllocCounters = initTable[string, int]()
  currentClosureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()
  # CR-9 Stage 6 Groups 3+4: also reset WalkCtx fields (idempotent).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].closureDidMutateHeap = false
    wp[].closureExitHeaps = initTable[string, Z3AnyAst]()
    wp[].closureExitAllocCounters = initTable[string, int]()
    wp[].closureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()
  p2

proc claimStrayPendingTaint*() =
  ## RFC-0005 review R1-04. The entry check of every walker lowering:
  ## the lowering queue must be empty when a walk arm starts lowering for
  ## a path, because the drain that follows folds whatever is queued onto
  ## THAT path. A non-empty queue is a deposit an earlier lowering in this
  ## statement left undrained -- possibly for a sibling path (the raw
  ## `lower` over a variant constructor's plain fields, per survivor, left
  ## one path's unwritten-global taint for the next survivor's drain, and
  ## the path that read the global stayed clean). The owner is not known
  ## here, so the taint is kept for the statement (`stmtStrayTaint`), and
  ## `walk` puts it on every path the statement yields; it still lands on
  ## this path through the drain as before.
  ##
  ## RFC-0016 INT-37 (R2-08): every raw `lower` now drains its own queue onto
  ## its own path, so a stray here is a walker fault. The fallback put one
  ## path's decline on its siblings too (an over-taint, never an unsound
  ## verdict), so a debug build stops on it and a release build keeps it.
  when not buildSemantics.release:
    doAssert pendingIsEmpty(),
      "claimStrayPendingTaint: a lowering left pending taint " &
      $peekPending().taint & " with no drain of its own (RFC-0016 R2-08)"
  if not pendingIsEmpty() and currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    let stray = peekPending()
    wp[].stmtStrayTaint = wp[].stmtStrayTaint + stray.taint
    wp[].stmtStrayUb = wp[].stmtStrayUb + stray.ub

proc lowerInExpr*(p: Path, e: IRExpr, w: var WalkCtx,
                 proto = none(SymVal)): (SymVal, Path) =
  ## Phase 15 CR-9 Stage 1. Encapsulates the seed → reset-transient-sinks →
  ## lower → drain pattern so a walk arm cannot forget to drain. Returns the
  ## lowered value and the drained path.
  ##
  ## Reproduces the exact sequence performed by the isLet / isAssign arms:
  ##   parseIntRaiseConds = @[]          # reset parseInt-raise sink
  ##   convFloatToIntBoundConds = @[]    # reset float-bound sink
  ##   seedCallerHeapThreadvars(p)       # seed caller heap + reset exit-heap sink
  ##   let sv = lower(p.env, e, proto)   # may deposit float bounds + closure writes
  ##   let p2 = drainPendingLowerEffects(p)  # drain + reset both sinks
  ##
  ## NOTE: drainParseIntRaises is a FORK (returns seq[Path]) and is intentionally
  ## NOT called here — arms that need the parseInt raise-fork call it on the
  ## returned path p2 after this wrapper returns.
  ##
  ## CR-9 Stage 6: resets the WalkCtx sinks (via w param), the raise sinks'
  ## only store, so each starts clean for each lower() call.
  ## `seedCallerHeapThreadvars` (called below) also calls `seedCallerHeapInWalkCtx`
  ## to reset the exit-heap WalkCtx fields; the remaining sink resets happen here.
  claimStrayPendingTaint()               ## RFC-0005 review R1-04
  w.sinks.parseIntRaiseConds = @[]            # CR-9 Stage 6 Group-2: reset WalkCtx field
  w.sinks.convFloatToIntBoundConds = @[]      # CR-9 Stage 6 Group-1: reset WalkCtx field
  w.sinks.rangeDefectConds = @[]     # RFC-0005 S8g: reset RangeDefect raise sink
  w.sinks.divByZeroConds = @[]                # R16-3: reset div/mod-by-zero raise sink
  w.sinks.overflowConds = @[]                 # R16-4: reset signed-integer overflow raise sink
  w.sinks.strIndexOobConds = @[]              # SND-4: reset string-index OOB raise sink
  w.sinks.seqOobConds = @[]                   # N14: reset seq del-OOB raise sink
  w.sinks.arithTrapConds = @[]                # RFC-0005 S8i: reset arithmetic-trap sink
  w.sinks.uninitReadConds = @[]                ## RFC-0005 S8bv
  w.sinks.regexRaiseMsgs = @[]                # RFC-0005 S8ay: reset RegexError sink
  w.sinks.raiseOrder = @[]                    # RFC-0005 S8bb: reset the order log
  w.closureRaises = @[]                 # RFC-0005 S7: reset closure-raise sink
  seedCallerHeapThreadvars(p)           # also calls seedCallerHeapInWalkCtx(p)
  let sv = lower(p.env, e, proto)
  let p2 = drainPendingLowerEffects(p)
  (sv, p2)

proc lowerBoolInExpr*(p: Path, e: IRExpr, w: var WalkCtx): (Z3Bool, Path) =
  ## Phase 15 CR-9 Stage 1. Same as lowerInExpr but for boolean predicate
  ## positions (calls lowerBool instead of lower). Reproduces the exact
  ## sequence performed by the isAssert arm:
  ##   parseIntRaiseConds = @[]          # reset parseInt-raise sink
  ##   convFloatToIntBoundConds = @[]    # reset float-bound sink
  ##   seedCallerHeapThreadvars(p)       # seed caller heap + reset exit-heap sink
  ##   let b = lowerBool(p.env, e)       # may deposit float bounds + closure writes
  ##   let p2 = drainPendingLowerEffects(p)  # drain + reset both sinks
  ##
  ## CR-9 Stage 6: resets the WalkCtx sinks (via w param), the raise sinks'
  ## only store, so each starts clean for each lowerBool() call.
  claimStrayPendingTaint()               ## RFC-0005 review R1-04
  w.sinks.parseIntRaiseConds = @[]            # CR-9 Stage 6 Group-2: reset WalkCtx field
  w.sinks.convFloatToIntBoundConds = @[]      # CR-9 Stage 6 Group-1: reset WalkCtx field
  w.sinks.rangeDefectConds = @[]     # RFC-0005 S8g: reset RangeDefect raise sink
  w.sinks.divByZeroConds = @[]                # R16-3: reset div/mod-by-zero raise sink
  w.sinks.overflowConds = @[]                 # R16-4: reset signed-integer overflow raise sink
  w.sinks.strIndexOobConds = @[]              # SND-4: reset string-index OOB raise sink
  w.sinks.seqOobConds = @[]                   # N14: reset seq del-OOB raise sink
  w.sinks.arithTrapConds = @[]                # RFC-0005 S8i: reset arithmetic-trap sink
  w.sinks.uninitReadConds = @[]                ## RFC-0005 S8bv
  w.sinks.regexRaiseMsgs = @[]                # RFC-0005 S8ay: reset RegexError sink
  w.sinks.raiseOrder = @[]                    # RFC-0005 S8bb: reset the order log
  w.closureRaises = @[]                 # RFC-0005 S7: reset closure-raise sink
  seedCallerHeapThreadvars(p)           # also calls seedCallerHeapInWalkCtx(p)
  let b = lowerBool(p.env, e)
  let p2 = drainPendingLowerEffects(p)
  (b, p2)

proc lowerLeafInExpr*(p: Path, e: IRExpr): (SymVal, Path) =
  ## Phase 15 CR-9 Stage 3. A container/pointer operand of a deref/index/field
  ## arm that is side-effect-free — no closure call, no float→int conversion —
  ## so no seed/drain is needed. The assert makes any violation loud.
  ##
  ## Admitted kinds and their side-effect status:
  ##   iekVar      — env lookup, trivially pure.
  ##   iekField    — struct field projection, pure.
  ## (RFC-0005 S8c deleted the third admitted kind, `iekStrBytes`, with the
  ## name-only `bytes(s)` model that produced it.)
  ##
  ## RFC-0005 S8bw (item 1): pure, but not decline-free -- a global read
  ## before any write declines in-band (`queueDegrade`). That pending taint
  ## lands on the returned path, `p` forked tainted; it was left for some
  ## later drain, and on the arms that fork no further it leaked to the
  ## walk end (`weInternalWalkerFault`, `gSeq[0] = k`).
  doAssert e.kind in {iekVar, iekField},
    "lowerLeafInExpr: expected side-effect-free container expr; got " & $e.kind &
    " — add seed+drain if parser changes"
  claimStrayPendingTaint()               ## RFC-0005 review R1-04
  let sv = lower(p.env, e)
  if pendingIsEmpty(): return (sv, p)
  (sv, forkPathTainted(p, p.pc, p.env, asDegrade(takePending())))

# nilDerefFork moved to runtime_heap.nim (CR-7-deeper Stage 8+).

# ---- RFC-fuzzer-nextgen G1b: wmFollowConcrete constraint collection --------
#
# The concrete-trace mechanism (RFC §G-concolic step 3): follow the ONE arm
# a concrete replay actually took at every `if`, instead of `wmExplore`'s
# fork-every-arm search. "Which arm was taken" is decided from `w.concreteEq`
# — ground equalities pinning every symbolicated draw to its recorded value —
# via a SCRATCH solver that never touches the live path's `pc` (the draws
# stay free/unpinned so a later G2 flip-solve can still move them).

func concreteBranchRLimit*(settings: SymexSettings): uint =
  ## R7: the rlimit `concreteBranchOutcome` actually uses — the caller's
  ## explicit `settings.budget.queryRLimit` when they set one (a caller who
  ## wants a bigger, or smaller, budget always wins), else
  ## `defaultConcreteBranchRLimit`. Split out as its own pure function so
  ## the "under default settings this site is genuinely bounded, not
  ## silently 0/unlimited" contract is directly unit-testable without
  ## needing to provoke a real Z3 divergence. RFC-0005 S8bu: `queryRLimit`'s
  ## own default (no longer `0`) is not the caller's.
  let q = settings.budget.queryRLimit
  if q != 0 and q != ResourceBudget().queryRLimit: q
  else: defaultConcreteBranchRLimit

var scratchCapped {.threadvar.}: bool
  ## RFC-0016 W3-z R9. A concolic scratch check (`concreteScratchCheck`) spent
  ## its whole rlimit without deciding since the flag was last cleared: the
  ## cap signal `followBranchOutcome` reads so it does not ask the same
  ## branch again at the cap.

proc concreteScratchCheck*(ctx: Z3Context; roots: openArray[Z3Bool];
                          settings: SymexSettings): Z3Status =
  ## RFC-0005 S8by. One of concolic collection's scratch solves
  ## (`concreteBranchOutcome`, `concretelyInfeasible`,
  ## `runConcolicCollectImpl`'s concrete-inputs check): `roots` under
  ## `concreteBranchRLimit(settings)` and `random_seed = 0`, in a context
  ## of its own (`ownContextSolver`, RFC-0005 S8bm), its units added to
  ## `ownContextUnits`. They checked in the walk's context, where what the
  ## context already held moved their search, as S8bm and S8bp measured
  ## for the walker's own: a factoring branch condition took 876,296 units
  ## in one context and 5,854,996 in one that made the query's constants
  ## the other way round (Z3 5.1; 23,956 and 911,593 on 4.13.4), and under
  ## a bound between them it was decided in the first and not in the second
  ## (`tsymex_rfc0005_s8by_remainder`). Now what the context holds moves
  ## neither its spend nor whether it decides within its bound. RFC-0016
  ## S8cj: the process's Z3 memory still does (Z3's QF_NIA portfolio skips
  ## its bit-blasting stage above 100 MB: 72k against 876k / 5.85M units
  ## on this query), so the spend is the query's AND the process's; what a
  ## bound above both figures decides is the query's alone.
  ##
  ## RFC-0016 W3-z R9: in a tail walk the bound is also what the tail's own
  ## budget has left (`workLeftRLimit`), and a check that spent its whole
  ## bound undecided sets `scratchCapped`, so its branch is not asked again.
  let rlimit = workLeftRLimit(concreteBranchRLimit(settings))
  let before = ownContextUnits
  # RFC-0016 S8co: a call on a pinned subject is its value here.
  result = ownContextCheck(ownContextSolver(ctx, foldPinnedPoints(ctx, @roots),
                                            rlimit))
  if result == zsUnknown and uint(max(ownContextUnits - before, 0)) >= rlimit:
    scratchCapped = true

proc definingSlice*(ctx: Z3Context; pins: seq[Z3Bool]; seeds: seq[Z3Bool];
                   conjuncts: seq[Z3Bool]): seq[Z3Bool]

proc foldPinnedRegexCalls*(ctx: Z3Context; pins: seq[Z3Bool];
                          body: var seq[Z3Bool]; cond: var Z3Bool) =
  ## RFC-0016 W4 perf (int4). Each `std/re` call (`regexPointSites`) the
  ## ask reads whose operands the pins fix to literals takes its value from
  ## the automaton (`pointValue`, as `pointCheck`'s pinned round does), and
  ## the assertions that only define it (`defs`) leave the ask. Z3 4.13.4
  ## did not decide those definitions over a ground subject within one
  ## check's bound: `findBounds(s, re"(*UTF)(*ANY).+")` with `s` pinned to
  ## `"abcde"` spent 10.4M units SAT and 19.7M UNSAT, and 8.0M SAT then the
  ## whole 20M undecided (`tsymex_0016_w4perf_tailpools`; the same asks
  ## stay under one check's bound on Z3 5.1). Fail-closed: under the pins `exact`
  ## IS that value (the automaton is PCRE's semantics within the safe
  ## length, past which `pointValue` declines), and the dropped definitions
  ## constrain only the call's own fresh terms, so the folded ask is the
  ## same question or one with fewer constraints. An UNSAT of it is an UNSAT
  ## of the original, and the branch answers rest on an UNSAT.
  if regexPointSites.len == 0: return
  ensureByteDomainKinds()
  let kinds = seqCapKinds()
  var pf, pt: seq[RawZ3Ast]
  for p in pins:
    let t = toAnyAst(p)
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    if args.len != 2 or
       ord(Z3_get_decl_kind(ctx.raw, decl)) != byteDomainKinds.eq: continue
    for (a, b) in [(args[0], args[1]), (args[1], args[0])]:
      if getAstKind(a) != akApp: continue
      let (ad, aargs) = unpackApp(a)
      if aargs.len == 0 and ord(Z3_get_decl_kind(ctx.raw, ad)) == kinds.uninterp and
         (Z3_is_string(ctx.raw, b.raw) or isNumeralAst(ctx, b.raw) or
          Z3_get_bool_value(ctx.raw, b.raw) != Z3_L_UNDEF):
        pf.add a.raw
        pt.add b.raw
        break
  if pf.len == 0: return
  proc subst(r: RawZ3Ast; a, b: seq[RawZ3Ast]): RawZ3Ast =
    var a = a
    var b = b
    ctx.checkErr Z3_substitute(ctx.raw, r, cuint(a.len),
      cast[ptr UncheckedArray[RawZ3Ast]](a[0].addr),
      cast[ptr UncheckedArray[RawZ3Ast]](b[0].addr))
  var ids: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in body: stack.add toAnyAst(r)
  stack.add toAnyAst(cond)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in ids: continue
    ids.incl id
    chargeWalkerTerms(1)
    if getAstKind(t) != akApp: continue
    let (_, args) = unpackApp(t)
    for a in args: stack.add a
  var ef, et: seq[RawZ3Ast]
  var dropped: HashSet[int]
  for st in regexPointSites:
    if astId(ctx, st.exact.raw) notin ids: continue
    let subj = literalStringBytes(simplify(wrap[Z3String](ctx,
                 subst(st.subject.raw, pf, pt))))
    if not subj.ok: continue
    let start = simplify(wrap[Z3Int](ctx, subst(st.start.raw, pf, pt)))
    if not isNumeralAst(ctx, start.raw): continue
    var by = ""
    if st.sp.entry == "replace":
      let b = literalStringBytes(simplify(wrap[Z3String](ctx,
                subst(st.by.raw, pf, pt))))
      if not b.ok: continue
      by = b.s
    let p = pointValue(st, subj.s, by,
                       int(parseBiggestInt(getNumeralString(start))))
    if not p.ok: continue
    ef.add st.exact.raw
    et.add keepRaw(pointLit(st, p))
    for d in st.defs: dropped.incl d
  if ef.len == 0: return
  var kept: seq[Z3Bool]
  for r in body:
    if astId(ctx, r.raw) in dropped: continue
    kept.add wrap[Z3Bool](ctx, subst(r.raw, ef, et))
  body = kept
  cond = wrap[Z3Bool](ctx, subst(cond.raw, ef, et))

proc concreteBranchAsk*(ctx: Z3Context, concreteEq: seq[Z3Bool],
                       cond: Z3Bool, settings: SymexSettings,
                       facts: seq[Z3Bool];
                       slicePools = false): (Z3Status, Z3Status) =
  ## The two scratch solves `concreteBranchOutcome` reads: `cond`, then
  ## `not cond`, each under the pins, the run-wide pools and `facts`.
  ##
  ## RFC-0016 W4 perf: `slicePools` (the tail walk, `followBranchOutcome`)
  ## asks with only the pools that constrain a symbol `facts` and `cond`
  ## reach past the pins (`definingSlice`, the same independence slice the
  ## first ask takes of the `pc`). The pools are run-wide: every regex,
  ## strip and index split the run lowered sits in them, each over the
  ## subject string the pins fix to a ground value. Asked whole, a branch
  ## on `s == "abcde"` carried every `findBounds` definition of the run and
  ## spent its whole 20M-unit bound undecided (`tsymex_rfc0005_s8cf_point_b`:
  ## tails of 60M and 80M units beside explore walks of 111K;
  ## `tsymex_0016_w4perf_tailpools`). Sound: a pool is definitional or
  ## true of every real input, so under the pins, which are the followed
  ## run's input, the pools left out are satisfiable over free symbols
  ## disjoint from the ones the ask keeps; an UNSAT of the sliced ask is an
  ## UNSAT of the whole one (a subset of it), and a SAT model extends.
  var reach = concreteEq
  reach.add facts
  reach.add cond
  let pools =
    if slicePools: definingSlice(ctx, concreteEq, facts & @[cond],
                                 globalRoots(reach))
    else: globalRoots(reach)
  # RFC-0016 W4 perf (int4): a regex call on a pinned subject is its value.
  var body = pools & facts
  var c = cond
  foldPinnedRegexCalls(ctx, concreteEq, body, c)
  # RFC-0005 S8by: each in a context of its own (`concreteScratchCheck`).
  let rTrue = concreteScratchCheck(ctx, concreteEq & body & @[c], settings)
  # RFC-0016 W3-z R9: an undecided first solve decides the answer (`none`)
  # whatever the second says, so the second is not asked.
  if rTrue == zsUnknown: return (zsUnknown, zsUnknown)
  let rFalse = concreteScratchCheck(ctx, concreteEq & body & @[not c],
                                    settings)
  (rTrue, rFalse)

proc concreteBranchOutcome*(ctx: Z3Context, concreteEq: seq[Z3Bool],
                           cond: Z3Bool, settings: SymexSettings,
                           facts: seq[Z3Bool] = @[]): Option[bool] =
  ## Determine whether `cond` (a branch predicate, already lowered against
  ## the current symbolic env) is concretely true or false under
  ## `concreteEq`, WITHOUT asserting `concreteEq` onto any live path.
  ## Two one-shot scratch solves: `cond` under the concrete pins, and
  ## `not cond` under the same pins. Exactly one SAT + one UNSAT means the
  ## pins fully determine `cond`'s truth (the walker-modeled fragment covers
  ## it) — `some(...)` reports which. Both SAT (or both UNSAT, which would
  ## mean the pins are self-contradictory — a bug, not a legitimate case)
  ## means `cond` depends on something the concrete pins don't reach — the
  ## walker-boundary concretization case for CONTROL FLOW — reported as
  ## `none(bool)` so the caller can degrade gracefully instead of guessing.
  ## Takes `ctx`/`concreteEq` by value (not the whole `WalkCtx`) so this can
  ## be called without copying the (large, table-heavy) walk context.
  ##
  ## R7: this runs on EVERY if-decision during EVERY concolic collection,
  ## synchronously on the main fuzz-loop thread with no watchdog — bounded
  ## by `concreteBranchRLimit(settings)` (see its doc for why this site
  ## gets a genuine non-zero DEFAULT, unlike `trySolve`, and why rlimit
  ## rather than G2's wall-clock timeout). `random_seed = 0` matches
  ## `trySolve`'s determinism guarantee. An exhausted rlimit surfaces as
  ## `zsUnknown` on one or both scratch solves, which already falls through
  ## the existing `else: none(bool)` arm below — "cannot determine the
  ## concrete outcome" degrades exactly like the pre-existing
  ## walker-boundary-concretization case, NEVER as a wrong definite
  ## true/false answer: `some(...)` only fires on the "exactly one SAT +
  ## one UNSAT" branch, and `zsUnknown` is neither, so an exhausted bound
  ## can only ever push the result toward `none(bool)`, never flip it
  ## toward an incorrect `some(true)`/`some(false)`.
  ##
  ## RFC-0005 S8i: `facts` (default none) join both solves -- the defect-
  ## survivor facts the condition's own lowering produced, which define a
  ## closure call's result there (its exit facts). `walkIfFollowConcrete`
  ## passes them only after checking the draws satisfy them.
  ##
  ## RFC-0005 S8n: both solves also assert `globalRoots()`, the run-wide
  ## pools every walker query asserts. A closure call's result is a fresh
  ## constant defined by its ground axioms there; without them it was free
  ## under the pins, and an `if` on a closure that returned normally was
  ## always ambiguous. The pools are definitional (or true of every real
  ## input), so they prune no execution the draws describe.
  let (rTrue, rFalse) = concreteBranchAsk(ctx, concreteEq, cond, settings, facts)
  if rTrue == zsSat and rFalse == zsUnsat: some(true)
  elif rTrue == zsUnsat and rFalse == zsSat: some(false)
  else: none(bool)

proc concretelyInfeasible*(ctx: Z3Context, concreteEq: seq[Z3Bool],
                          conds: seq[Z3Bool], settings: SymexSettings): bool =
  ## RFC-0005 S8i. True iff `conds` (a path's `pc` and defect-survivor
  ## facts) is UNSAT under the concrete pins: the replayed execution cannot
  ## be on that path. One scratch solve, bounded like
  ## `concreteBranchOutcome`'s; an exhausted bound is `zsUnknown`, never
  ## `zsUnsat`, so it can only keep a path, never drop one wrongly.
  ## RFC-0005 S8n: with the same `globalRoots()` pools.
  ## RFC-0005 S8by: in a context of its own (`concreteScratchCheck`).
  concreteScratchCheck(ctx, concreteEq & globalRoots(concreteEq & conds) &
                            conds, settings) == zsUnsat

proc fieldsUnchecked*(): bool =
  ## RFC-0016 PRC-07. The build compiles no `fieldChecks`: a variant field is
  ## a plain union member access, so one outside its branch raises no
  ## `FieldDefect`.
  not checkedNow(coField)

proc inactiveFieldSide*(cp: Path; outOfArm: Z3Bool; env: Env; loc: string;
                       w: var WalkCtx; isWrite = false;
                       checkedRead = false): seq[Path] =
  ## RFC-0016 PRC-07. The out-of-branch side `outOfArm` of a variant field
  ## access on `cp` in a `fieldChecks: off` build. On the cpp backend reading a
  ## union member that is not the active one is undefined: decided at the op
  ## and halted (`ubInactiveVariantField`, row `field/inactiveBranch`). A
  ## WRITE (`isWrite`) is not a finding: C++ defines the assignment (the
  ## member becomes active), so it is declined on its own path like the c
  ## backend's, the walker holding no state for a member other than its
  ## discriminator's. On
  ## the c backend C defines it as the overlapping bytes of the active branch;
  ## the caller has already taken the
  ## arms whose bytes the active arm's int/char/bool fields cover
  ## (`variant_layout`, slice A) out of `outOfArm`, and what is left, which
  ## the walker cannot answer (`fieldChecksOffLayout`), is declined, on its own
  ## path only. Returns the declined child (`env`
  ## its environment) for the caller to add to its survivors, or nothing.
  ## RFC-0016 int6-f: `checkedRead` is a CHECKED read (cpp) the discriminator
  ## admits, through a member an unchecked write left inactive: `outOfArm`
  ## is then the inactive-member condition and the side is always decided.
  if guardLiteral(outOfArm) == glFalse: return
  if checkedRead:
    decideUndefined(cp, inactiveFieldUb(), outOfArm,
      opSite("a checked variant field read through a member an " &
             "unchecked write left inactive", loc), w)
    return
  if buildSemantics.backend == beCpp and not isWrite:
    decideUndefined(cp, inactiveFieldUb(),  outOfArm,
      opSite("a variant field accessed outside its branch (a plain union " &
             "member, no check emitted)", loc), w)
    return
  let unsat = guardLiteral(outOfArm) != glTrue and
    refuteStatus(w.z3, pathRoots(cp, [outOfArm]), w.settings,
                 loopPruneRLimit(w.settings)) == zsUnsat
  if unsat:
    logPrune(cp, [outOfArm])
    return
  let (kind, why) = admitDefined(aoField, ocInactiveBytes, dsField).decline
  result.add forkPathTainted(cp, cp.pc & @[outOfArm], env,
    w.degrade(kind.get(feUnsupportedOp),
      (if loc.len > 0: loc & ": " else: "") &
      "a variant field accessed outside its branch with `fieldChecks` off " &
      "(fieldChecksOffLayout): C reads the active branch's overlapping bytes, " &
      "which the walker has no layout for (" & why & ") -- path degraded " &
      "to sxUnknown"))

proc maybeForkDefect*(p: Path, defectCond: Z3Bool, typeId: string,
                     msg: Option[string], w: var WalkCtx) =
  ## RFC-fuzzer-nextgen R14: `wmFollowConcrete` counterpart to the
  ## unconditional `discard forkDefect(...)` call sites in `isIndex`
  ## (OOB seq/array access) and `isVariantField` (out-of-arm field access).
  ##
  ## Those two sites are NOT a `wmExplore`-style fork-every-arm construct —
  ## `forkDefect`'s return value is already discarded by every caller (the
  ## surviving non-defect path is built separately); `forkDefect` exists
  ## purely to (a) let a `try/except` handler catch the defect (via
  ## `routeRaise`'s handler-stack search, recorded on a side channel, not
  ## this call's return value) and (b) probe whether the defect is
  ## reachable at all, for target-witness search. Under `wmFollowConcrete`
  ## (concolic collection), `WalkCtx.target` is always the unreachable
  ## sentinel label (`runConcolicCollectImpl` sets it to
  ## `"__nelli_concolic_unreached__"`), so (b) can never fire — the ONLY
  ## live behavior `forkDefect` retains here is (a), and (a) only matters
  ## when the defect is actually reachable given `w.concreteEq`.
  ##
  ## So: when `concreteBranchOutcome` can determine the defect condition is
  ## concretely FALSE on this replay (`some(false)`), skip the call
  ## entirely — a real `try/except IndexDefect` around this op did not fire
  ## on THIS trace, so there is nothing to route, and the call would only
  ## have burned a `routeRaise`/`trySolve` query for no observable effect.
  ## `some(true)` (the defect DID concretely fire — a handler may need to
  ## catch it) and `none` (ambiguous — walker-boundary concretization, same
  ## conservative default as everywhere else in G1b) both still call
  ## `forkDefect`, unchanged: this is a narrowing, never a soundness
  ## trade-off — the two mode-agnostic call sites are unaffected
  ## (`wmExplore` never calls this proc; it keeps calling `forkDefect`
  ## directly, unconditionally, exactly as before).
  if w.mode == wmFollowConcrete:
    let outcome = concreteBranchOutcome(w.z3, w.concreteEq, defectCond, w.settings)
    if outcome.isSome and not outcome.get():
      return
  discard forkDefect(p, defectCond, typeId, msg, w)

proc indexOobSide*(cp: Path; oob: Z3Bool; unchecked: bool; loc: string;
                  w: var WalkCtx) =
  ## RFC-0016 PRC-07. The out-of-container side `oob` of an index op on `cp`.
  ## A checked access forks `IndexDefect` (`maybeForkDefect`). One Nim emits
  ## with no check -- an array indexed by a value of its own type under
  ## `rangeChecks: off` (`unchecked`, from the parser), or any index under
  ## `boundChecks: off` -- is a plain C subscript, undefined outside the
  ## container: decided at the op and halted (`ubArrayOutOfBounds`), so the
  ## in-range continuation stays exact.
  if unchecked or boundsUnchecked():
    decideUndefined(cp, uncheckedIndexUb(), oob, uncheckedIndexSite(loc), w)
  elif loopArmInfeasible(w.z3, cp, oob, w.settings):
    # W4 perf: the raise side is refuted on the path's own facts by the
    # bounded check a loop guard runs under (`loopArmInfeasible`: a literal
    # side without the solver, otherwise `loopPruneRLimit`), so no real
    # execution of this path raises here and `routeRaise`'s full solve would
    # find it UNSAT. Undecided keeps the arm (the `else`); the drop is logged
    # in the prune window as every such drop is.
    discard
  else:
    maybeForkDefect(cp, oob, "IndexDefect", none(string), w)

proc followConcreteTag*(mode: WalkMode, ctx: Z3Context, concreteEq: seq[Z3Bool],
                       settings: SymexSettings, eq: proc (tagOrd: int64): Z3Bool,
                       candidateTags: seq[int]): Option[int] =
  ## RFC-fuzzer-nextgen R14. `isVariantReassignSymbolic`'s counterpart to
  ## `walkIfFollowConcrete`/`walkWhileFollowConcrete`: which ONE of
  ## `candidateTags` the symbolic-RHS discriminator reassign's RHS
  ## concretely equals (`eq(tag)` is the caller's `rhsSV == tagLiteral`
  ## predicate builder), under `concreteEq` — determined via the same
  ## `concreteBranchOutcome` scratch-solver mechanism. Returns `none(int)`
  ## when not in follow-concrete mode, or when the concrete draws don't
  ## pin a UNIQUE match — the same sound "cannot narrow, fall back to
  ## forking every tag" degrade every other G1b ambiguous case uses (a
  ## real concrete replay always resolves to exactly one tag, so the
  ## ambiguous case should never actually fire in practice). Free-standing
  ## (not nested inside `walk`'s `isVariantReassignSymbolic` arm) because a
  ## closure over `WalkCtx` itself — a `var` object parameter — cannot be
  ## captured in Nim ("would violate memory safety"); this takes exactly
  ## the fields it needs as plain value parameters instead.
  if mode != wmFollowConcrete: return none(int)
  for t in candidateTags:
    if concreteBranchOutcome(ctx, concreteEq, eq(int64(t)), settings) == some(true):
      return some(t)
  none(int)

proc sameBranchCond*(oldDisc: SymVal; newTag: int;
                    branches: seq[seq[int]]): Z3Bool =
  ## RFC-0005 S8f. "The discriminator `oldDisc` selects the same source
  ## branch as `newTag`." Nim checks exactly this on every discriminator
  ## assignment and raises `FieldDefect` ("assignment to discriminant
  ## changes object branch") when it fails -- for a `var` param, a local, a
  ## default-initialised object alike (probed on the pinned toolchain).
  ## `branches` is `vrBranches`: explicit tags grouped by branch; `newTag`
  ## in no group is an `else:` value, whose branch is "no explicit tag".
  for g in branches:
    if newTag in g:
      result = variantDiscEq(oldDisc, int64(g[0]))
      for k in 1 ..< g.len:
        result = result or variantDiscEq(oldDisc, int64(g[k]))
      return
  result = mkBool(true)
  for g in branches:
    for t in g:
      result = result and not variantDiscEq(oldDisc, int64(t))

proc sameBranchSymCond*(oldDisc, newDisc: SymVal;
                       branches: seq[seq[int]]): Z3Bool =
  ## RFC-0005 S8l. `sameBranchCond` for a SYMBOLIC new discriminator: a
  ## discriminator write through a ref (`p.kind = v`, the heap model) stores
  ## an arbitrary value of the discriminator's type, not a parse-time tag.
  ## "Both select the same source branch": some explicit group holds both,
  ## or neither is any explicit tag (both are the `else:` branch's).
  var oldElse = mkBool(true)
  var newElse = mkBool(true)
  var anyGroup = mkBool(false)
  for g in branches:
    var oldIn = mkBool(false)
    var newIn = mkBool(false)
    for t in g:
      oldIn = oldIn or variantDiscEq(oldDisc, int64(t))
      newIn = newIn or variantDiscEq(newDisc, int64(t))
    anyGroup = anyGroup or (oldIn and newIn)
    oldElse = oldElse and not oldIn
    newElse = newElse and not newIn
  anyGroup or (oldElse and newElse)

proc carryBranchFields*(armFields: OrderedTable[int, seq[SymVal]];
                       oldDisc: SymVal; newTag: int;
                       branches: seq[seq[int]]): OrderedTable[int, seq[SymVal]] =
  ## RFC-0005 S8f. A same-branch discriminator assignment keeps the
  ## branch's field storage (`V(kind: kA, a: 5)` then `kind = kC` under
  ## `of kA, kC: a` leaves `a == 5`). The model keeps one field set per TAG,
  ## so the new tag's fields become the OLD tag's: an ite over the branch's
  ## tags on `oldDisc`. A single-tag branch or an else value is unchanged.
  ## May leave a merge-degrade effect pending (`iteSV`): the caller drains.
  result = armFields
  for g in branches:
    if newTag notin g or g.len < 2: continue
    let target = armFields.getOrDefault(newTag)
    var carried: seq[SymVal]
    for j in 0 ..< target.len:
      var v = target[j]
      for t in g:
        if t == newTag: continue
        let src = armFields.getOrDefault(t)
        if j < src.len:
          v = iteSV(variantDiscEq(oldDisc, int64(t)), src[j], v)
      carried.add v
    result[newTag] = carried
    return

proc discFromRhs*(rhs, oldDisc: SymVal): SymVal =
  ## RFC-0005 S8g. The discriminator a symbolic reassignment into the
  ## `else:` arm leaves behind: the RHS value itself, in the old
  ## discriminator's representation (kind, width, signedness).
  case oldDisc.kind
  of svBV8, svBV16, svBV32, svBV64:
    if rhs.kind == oldDisc.kind:
      result = rhs
    else:
      let asInt = SymVal(kind: svInt, zi: toZ3Int(rhs))
      result = svIntToBV(asInt, oldDisc.kind)
    result.signed = oldDisc.signed
  of svInt:
    result = SymVal(kind: svInt, zi: toZ3Int(rhs))
  of svBool:
    # RFC-0005 S8u: a `bool` discriminator (`of true: ...; else: ...`). The
    # RHS of an assignment to it is a `bool`.
    result = rhs
  else:
    raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (allocateSym's itVariant/itMultiVariant arms only ever allocate a BV/Int/Bool discriminator)]
      "discFromRhs: discriminator must be a BV or Z3Int kind (got " &
      $oldDisc.kind & ")")

proc markAmbiguous*(w: var WalkCtx, construct: WalkerConstructKind) =
  ## R28: the ONE site that increments an ambiguous-branch degrade —
  ## `walkIfFollowConcrete`'s `wckIf` and `walkWhileFollowConcrete`'s
  ## `wckWhile` — so the flat `concolicAmbiguousBranches` total and its R28
  ## per-construct breakdown can never drift apart (a single fold, not two
  ## counters hand-kept in sync).
  inc w.concolicAmbiguousBranches
  w.concolicAmbiguousByConstruct.mgetOrPut(construct, 0) += 1

proc declinedIndexEnv*(env: Env; stmt: IRStmt; valTy: IRType): Env =
  ## RFC-0005 S8z. The env of a declined table read `v = t[k]`: `v` bound
  ## to a fresh value of the table's value type on the tainted path. It was
  ## left unbound, so the next read of `v` took the unmodelled-global
  ## stand-in (an int) and `v == "b"` on a `Table[string, string]` hit
  ## `eqBV`'s kind assertion (`weInternalWalkerFault`).
  result = env
  var scratch: seq[Z3Bool]
  result[stmt.ixRetName] = allocateSym(valTy,
    freshDegradeName("__declinedIndexRead"), scratch)

proc declinedVariantEnv*(env: Env; stmt: IRStmt): Env =
  ## RFC-0005 S8ba. `declinedIndexEnv` for a declined symbolic variant
  ## construction: its temporary bound to a fresh value of the variant type.
  result = env
  var scratch: seq[Z3Bool]
  result[stmt.vcsResultVar] = allocateSym(stmt.vcsVariantTy,
    freshDegradeName("__declinedVariant"), scratch)

proc declinedPopEnv*(env: Env; stmt: IRStmt): Env =
  ## RFC-0005 S8ba. `declinedIndexEnv` for a declined `v = s.pop()`: `v`
  ## bound to a fresh value of the element type on the tainted path. Left
  ## unbound, its next read was recorded as an unmodelled global
  ## (`'__sym_pop_N' is read where ...`).
  result = env
  if stmt.spElemTy.isNil: return
  var scratch: seq[Z3Bool]
  result[stmt.spRetName] = allocateSym(stmt.spElemTy,
    freshDegradeName("__declinedPop"), scratch)

proc unbackedElemSurvivor*(p: Path; inPc: seq[Z3Bool]; env: Env;
                          seqSV: SymVal; loc, what: string;
                          w: var WalkCtx): seq[Path] =
  ## RFC-0016 K9c follow-up. The in-bounds side of an element access
  ## (`what`: a read, a store, a `pop`) on a seq whose element type the
  ## model does not back (`isBackedSeqElemTy` false) that is not a
  ## placeholder: a local built from an empty literal
  ## (`var o: seq[seq[T]] = @[]`), or the empty stand-in a declined field
  ## read binds. Its length is exact; its elements have no arrays. The
  ## access's `IndexDefect` side is modelled by the caller. When no
  ## execution reaches the in-bounds side (`inPc` is UNSAT, as it is for an
  ## empty seq) the access always raises and nothing is lost: no survivor.
  ## Otherwise the in-bounds side declines as every other access of such a
  ## seq does (`seNestedSeqUnsupported`, `iekSeqAdd`'s S8bl arm). These
  ## accesses reached raw raises and an `seqElemAt` fallback, filed as
  ## `weInternalWalkerFault`, a walker fault for a known modelling gap.
  if pathInfeasible(w.z3, forkPath(p, inPc, env), w.settings): return @[]
  let locPrefix = if loc.len > 0: loc & ": " else: ""
  let d = w.degrade(seNestedSeqUnsupported, locPrefix & what &
    " of a seq of " & $seqSV.seqElemTy & ", an element type the model " &
    "does not back (seNestedSeqUnsupported)")
  @[forkPathTainted(p, inPc, env, d)]


proc armScalarAfter*(sv: SymVal; zero: bool; declined: var bool): SymVal =
  ## RFC-0005 S8cp (item 2). `sv`'s type's zero, or a fresh value with no range
  ## fact (the bytes need not be in range), for a scalar arm field.
  ## `declined` for anything else (`discWriteOutcomes`).
  var ty: IRType
  case sv.kind
  of svBV8:  ty = tInt(8, sv.signed)
  of svBV16: ty = tInt(16, sv.signed)
  of svBV32: ty = tInt(32, sv.signed)
  of svBV64: ty = tInt(64, sv.signed)
  of svBool: ty = tBool()
  of svFloat32: ty = tFloat32()
  of svFloat64: ty = tFloat64()
  of svString:
    if not zero:
      declined = true
      return sv
    ty = tString()
  else:
    declined = true
    return sv
  if zero: return defaultZero(ty, "__uncheckedArm")
  var scratch: seq[Z3Bool]
  allocateSym(ty, freshDegradeName("__uncheckedArm"), scratch)

proc discWriteOutcomes*(mode: DiscWriteMode;
                       armFields: OrderedTable[int, seq[SymVal]];
                       oldDisc: SymVal; newTag: int;
                       branches: seq[seq[int]];
                       sameValue: Z3Bool;
                       variantTy: IRType = nil;
                       image: seq[Z3BitVec[64]] = @[]): seq[DiscOutcome] =
  ## RFC-0005 S8cp (item 2). What an assignment of the tag `newTag` to a
  ## discriminator leaves in the arm fields (`DiscWriteMode`). Under
  ## `{.cast(uncheckedAssign).}` nothing raises, and the same value changes
  ## nothing. Another value: on an object with a destructor (`dwmZeroing`) Nim
  ## zeroes the memory of this case, of the same branch or not; on any other
  ## object the bytes stay, so the new arm reads the old arm's, unless the object
  ## has a hook, which also zeroes them (`dwmHavoc`). Only the new tag's fields
  ## are reachable until the next assignment, which reads them through its own
  ## old discriminator, so only they change. Natively checked:
  ## `tests/tsymex_rfc0005_s8cp_unchecked.nim`.
  ## May leave a merge-degrade effect pending (`carryBranchFields`): the caller
  ## drains.
  if mode == dwmChecked:
    return @[DiscOutcome(cond: sameBranchCond(oldDisc, newTag, branches),
                         arms: carryBranchFields(armFields, oldDisc, newTag, branches))]
  result.add DiscOutcome(cond: sameValue, arms: armFields,
                         keepImage: image.len > 0)
  var key = -1
  if newTag >= 0:
    for g in branches:
      if newTag in g: key = newTag
  # RFC-0016 PRC-07 slice B (c, `--fieldChecks:off`): the assignment stores
  # the tag alone and the bytes stay (generated C, pinned in
  # `tests/tsymex_0016_fieldoff.nim`), so the new arm's fields are the
  # union image's bytes at their places: exact, no havoc. A field the bytes
  # are no value of (a bool, a range with its checks on) keeps the havoc.
  if mode == dwmHavoc and image.len > 0 and variantTy != nil and key in armFields:
    let lay = vl.variantLayout(variantTy)
    if lay.ok and lay.arms.hasKey(key) and
       lay.arms[key].len == armFields[key].len:
      var carried = DiscOutcome(cond: not sameValue, arms: armFields,
                                keepImage: true)
      var after: seq[SymVal]
      for j, f in lay.arms[key]:
        let nv = bitsPlace(imgReadDef(image, f.off - lay.unionOff, f.size), f,
                           none((vl.Place, SymVal)))
        if nv.isNone: break
        after.add nv.get
      if after.len == lay.arms[key].len:
        carried.arms[key] = after
        result.add carried
        return
  var changed = DiscOutcome(cond: not sameValue, arms: armFields,
                            havoc: mode == dwmHavoc)
  if key in armFields:
    var after: seq[SymVal]
    for f in armFields[key]:
      after.add armScalarAfter(f, mode == dwmZeroing, changed.decline)
    changed.arms[key] = after
  result.add changed

proc discOutcomePath*(p: Path; o: DiscOutcome; w: var WalkCtx): Path =
  ## RFC-0005 S8cp (item 2). The child of `p` that goes the way `o` does.
  if o.decline:
    return forkPathTainted(p, p.pc & @[o.cond], p.env, w.degrade(feUnsupportedOp,
      "an arm field of this type after a discriminator write under " &
      "`{.cast(uncheckedAssign).}` is not modelled (feUnsupportedOp)"))
  result = forkPath(p, p.pc & @[o.cond], p.env)
  if o.havoc:
    taintInPlace(result, w.degrade(feUncheckedDiscBytes,
      "a discriminator written under `{.cast(uncheckedAssign).}`: the new arm " &
      "holds the old bytes or zero, by whether the object has a hook, so a hit " &
      "through it is replayed (feUncheckedDiscBytes)"))

proc unwrittenDisc*(sv: SymVal): string =
  ## RFC-0005 S8bw (item 2). The unwritten part a variant's discriminator
  ## (each axis's, for a multi-variant) mentions, or "": a reassignment
  ## reads it for Nim's branch-change check.
  case sv.kind
  of svVariant: unwrittenIn(sv.vDisc[])
  of svMultiVariant:
    for ax in sv.mvAxes:
      let part = unwrittenIn(ax.disc[])
      if part.len > 0: return part
    ""
  else: ""

proc noinitReturnDegrade*(retVal: SymVal; w: var WalkCtx): Option[Degrade] =
  ## RFC-0016 0.10.0 review H5. A callee returning a `{.noinit.}` `result`
  ## (or a part of it) no path wrote: the caller reads an indeterminate
  ## value. The returning path is tainted with the read (`feGlobalHavoc`,
  ## `ubIndeterminateRead`) and the call's value left free (any value of
  ## the type, which is what it is).
  if unwrittenIn(retVal, simplified = true) != noinitResultPart:
    return none(Degrade)
  some(w.degrade(unwrittenKind(noinitResultPart),
                 unwrittenMsg(noinitResultPart),
                 ub = unwrittenUb(noinitResultPart)))

proc observeRecvPart*(p: Path; part: SymVal; w: var WalkCtx): Option[Degrade] =
  ## RFC-0005 S8cd. A receiver arm reads `part` of its receiver (`recvValue`
  ## observes none of it). An unwritten part taints `p` when its global's
  ## entry value is modelled (`feGlobalHavoc`); any other is returned for the
  ## arm to decline on.
  let unwritten = unwrittenIn(part, simplified = true)
  if unwritten.len == 0: return none(Degrade)
  let d = w.degrade(unwrittenKind(unwritten), unwrittenMsg(unwritten),
                    ub = unwrittenUb(unwritten))
  if unwrittenKind(unwritten) != feGlobalHavoc: return some(d)
  taintInPlace(p, d)
  none(Degrade)

func reassignReadsDisc*(sv: SymVal; branches: seq[seq[int]]): bool =
  ## RFC-0005 S8cd. Whether a discriminator assignment's branch-change check
  ## depends on the old discriminator: not when one branch holds every tag
  ## (one explicit group and no `else`), which no assignment can leave.
  sv.kind != svVariant or branches.len != 1 or sv.vArmFields.hasKey(-1)

proc completeReturn*(p: Path, w: var WalkCtx) =
  ## RFC-0005 S8l. Complete a `return` exit once every `finally` of its frame
  ## has run (`exitReturn`). `result` on `p.env` is the returned value: the
  ## `return <expr>` value, or whatever the body (and the finallys) assigned
  ## before a bare `return`.
  ##   * The SUT's own frame (empty `callStack`): the path joins
  ##     `w.topExits.returnedPaths` (RFC-0005 S8j).
  ##   * A callee: the frame's `retSym` is bound to `result` on the path's pc
  ##     as its LAST conjunct (`applyClosureGround` reads it there) and the
  ##     path joins the frame's `returnedPaths`. A bare `return` in a
  ##     value-returning callee that never assigned `result` binds the return
  ##     type's zero value (Nim zero-initialises `result`), exactly as the
  ##     `isCall` arm's implicit fall-through does (R2); before S8l it left
  ##     `retSym` free on that path. A void callee's path joins unchanged.
  if w.callStack.len == 0:
    w.topExits.returnedPaths.park(p)
    return
  let frameIx = w.callStack.high
  let retSym = w.callStack[frameIx].retSym
  if retCarriesClosure(w.callStack[frameIx].retTy):
    # RFC-0005 S8z: a closure-returning callee has no `retSym` to bind; the
    # path carries its `svClosure` on `result`, which the `isCall` arm hands
    # to the caller as the call's value. RFC-0005 S8be: a tuple holding a
    # closure too (it was `ceUnsupportedHof`).
    if p.env.hasKey("result") and
       closureValueBuilt(p.env["result"], w.callStack[frameIx].retTy):
      w.callStack[frameIx].exits.returnedPaths.park(p)
    else:
      let d = w.degrade(ceUnsupportedHof,
        "a closure-returning callee returns no lambda the walker built " &
        "(an untouched nil proc, or a proc value from elsewhere)")
      w.callStack[frameIx].exits.returnedPaths.park(forkPathTainted(p, p.pc, p.env, d))
    return
  var retVal: SymVal
  if p.env.hasKey("result"):
    retVal = p.env["result"]
  elif w.callStack[frameIx].retTy != nil:
    try:
      retVal = defaultZero(w.callStack[frameIx].retTy,
                           w.callStack[frameIx].retName & ".zerodefault")
    except ValueError:
      # RFC-0005 S6b: `feUnsupportedOpHavoc` -- as the `isCall` arm's
      # untouched-result twin: the free per-call `retSym` ranges over the
      # whole type, zero included.
      let d = w.degrade(feUnsupportedOpHavoc,
        "bare `return` of an untouched composite result (kind " &
             $w.callStack[frameIx].retTy.kind & ") has no sound zero-default (" &
             getCurrentExceptionMsg() & ") — path degraded to sxUnknown " &
             "(feUnsupportedOp)")
      w.callStack[frameIx].exits.returnedPaths.park(forkPathTainted(p, p.pc, p.env, d))
      return
  else:
    w.callStack[frameIx].exits.returnedPaths.park(p)
    return
  # v64 (chapulin catalog #6): a COMPOSITE-typed retSym (svTuple/
  # svArray/…) reaching this binding used to flow into `retBindEq`,
  # whose non-primitive arm RAISES ValueError — an in-walk raise
  # that unwinds through live `seq[Path]` state (the b7258f7/CR-1c
  # C-backend silent-loss hazard). Chapulin observed the same shape
  # both as a hard native crash and as a net-caught
  # `weInternalWalkerFault` — nondeterministic manifestations of
  # this one raise. Repro: DESTRUCTURING a tuple return from a
  # loop-bearing callee that can raise (`let (_, p1) =
  # readCStringTwin(data, 2)`); a `discard`ed call of the same
  # callee never arrives here composite-typed and still proves.
  # Composite binding through this drain is not yet wired (P1
  # wired tuple RETURN PARSING, not the raise-fork return bind) —
  # degrade IN-BAND: classify + taint the returned path
  # (uncertain ⇒ no false sxSat), never raise.
  # v69 (sello #2): svTuple joins the wired set — retBindEq now
  # binds tuples structurally per field. svArray/other composites
  # (and closures returning tuples, bound at the funcApp site)
  # remain in the degrade net.
  # Round-6 A2 (ADR-0029): svVariant joins the wired set —
  # retBindEq's general encoding (discEq + guarded per-arm field
  # eq + plain-field eq) binds a variant-returning callee.
  if retSym.kind notin retBindWiredKinds or
      not retBindKindsAgree(retSym, retVal):  # RFC-0005 S8u
    # NOTE: `w.walkDegradeErrors`, NOT the `loweringDegradeErrors`
    # threadvar — that sink is reset at every `lowerInExpr` wrapper
    # entry, so an entry added HERE (after the wrapper returned)
    # would be wiped by the next lowering before verdict assembly.
    # RFC-0005 S6b: `feUnsupportedOpHavoc` -- `retSym` is this
    # call's own `synthZ3`-numbered symbol (fresh per call) and is
    # left free, `stmt.retExpr` was lowered and its raise forks
    # drained above, and the callee's heap/var effects ride `cp`.
    # A tainted return is never cached. A superset of the value.
    let d = w.degrade(feUnsupportedOpHavoc,
      "composite-typed proc return (kind " & plainEnglishSymValKind(retSym.kind) &
           ") bound through the scalar-raise drain is not yet " &
           "wired — path degraded to sxUnknown (feUnsupportedOp)")
    w.callStack[frameIx].exits.returnedPaths.park(forkPathTainted(
      p, p.pc, p.env, d))
    return
  # Reconcile mixed int reps (e.g. callee returns svInt because
  # of #135 range propagation while retSym was allocated svBV*).
  # CR-9(c) D5: reconcileInt handles the cross-rep case; retBindEq
  # then works on same-kind operands (bv2int was applied if needed).
  if p.env.hasKey("result"):
    let nd = noinitReturnDegrade(retVal, w)
    if nd.isSome:
      w.callStack[frameIx].exits.returnedPaths.park(
        forkPathTainted(p, p.pc, p.env, nd.get))
      return
  if not noteUninitReturn(retSym, retVal, p.pc) and svMentionsUninit(retVal):
    # RFC-0005 S8bq: a seq result is bound with its alias recorded
    # (`noteUninitReturn`). One nested in a composite is not: bound by
    # equality, `retSym` would carry its elements without the
    # `newSeqUninit` base, so a caller's read of an unwritten one would
    # come back clean. `retSym` is left free (a superset of the value),
    # nothing is dropped.
    let d = w.degrade(uninitReadKind, uninitReturnMsg)
    w.callStack[frameIx].exits.returnedPaths.park(forkPathTainted(p, p.pc, p.env, d))
    return
  let (rSym, rVal) = reconcileInt(retSym, retVal)
  # Phase 15 G3: same-kind structural binding (BV-wrap semantics
  # preserved; Z3Int = Z3Int when both are Int after reconcileInt;
  # float uses a NaN-safe structural eq so a NaN-returning callee
  # is not pruned; string binds natively). This is what wires a
  # value-returning generic instantiated at `float64`/`string` to
  # flow its result into the caller.
  let retConstraint = retBindEq(rSym, rVal)
  w.callStack[frameIx].exits.returnedPaths.park(forkPath(
    p, p.pc & @[retConstraint], p.env))

proc exitReturn*(p: Path, w: var WalkCtx) =
  ## RFC-0005 S8l. Send a `return` exit (`result` already bound on `p.env`)
  ## out of the current frame. A `finally` guarding it runs first: the
  ## deepest HandlerFrame with a `finallyBlock` claims the path
  ## (`pendingReturn`), and its `isTry` runs the finally and calls back here
  ## for the next-outer one (innermost first, as Nim unwinds). With none
  ## left, the return completes.
  for i in countdown(w.frame.handlerStack.high, 0):
    if w.frame.handlerStack[i].finallyBlock != nil:
      w.frame.exits.held.pendingReturn.park((depth: i, path: p))
      return
  completeReturn(p, w)

proc exitJump*(p: Path; target: int; isCont: bool; w: var WalkCtx) =
  ## RFC-0005 S8m. Send a `break` (`isCont` false) or `continue` exit to the
  ## loop / labelled-block frame `w.loopStack[target]`. Every `finally` the
  ## jump leaves -- each HandlerFrame of this call frame at or above the
  ## target's `hsDepth` -- runs first, innermost first: the deepest one claims
  ## the path (`pendingJump`), and its `isTry` walks the finally and calls back
  ## here for the next one out. With none left, the path joins the target's
  ## `breakPaths` / `continuePaths`. Before S8m a jump went straight to the
  ## loop and no `finally` (or `defer`) ran on it: a label in a `finally` a
  ## `continue` left was a false `sxUnsat`.
  ##
  ## A jump that leaves a `finally` running on a RAISED exit is
  ## backend-divergent (c re-raises, cpp swallows the exception; probed):
  ## the path halts (`eeFinallyJumpOnRaise`, `dcOmitted`), as S8l's
  ## `return` there does.
  if w.frame.raisedFinallyLoops.len > 0 and
     target < w.frame.raisedFinallyLoops[^1]:
    w.halted(eeFinallyJumpOnRaise,
      "`" & (if isCont: "continue" else: "break") & "` leaving a `finally` " &
      "that runs on a raised exit: the c backend re-raises, cpp does not -- " &
      "path dropped (eeFinallyJumpOnRaise)")
    return
  for i in countdown(w.frame.handlerStack.high, w.loopStack[target].hsDepth):
    if w.frame.handlerStack[i].finallyBlock != nil:
      w.frame.exits.held.pendingJump.park((depth: i, path: p, target: target,
                                         isCont: isCont))
      return
  if isCont: w.loopStack[target].exits.continuePaths.park(p)
  else:      w.loopStack[target].exits.breakPaths.park(p)

proc jumpTarget*(w: WalkCtx; label: string): int =
  ## RFC-0005 S8m. The frame a jump leaves: the innermost loop for "" (a
  ## plain `break` / `continue`), else the innermost labelled block named
  ## `label`. -1 when there is none.
  for i in countdown(w.loopStack.high, 0):
    if w.loopStack[i].label == label: return i
  -1

proc sameSV*(a, b: SymVal): bool =
  ## RFC-0005 S8w. True when `a` and `b` are provably the SAME symbolic
  ## value: same kind, same metadata, and every Z3 term the same AST (Z3
  ## hash-conses terms, so equal raw handles are equal terms). Used by
  ## `mergeJoinPaths` to find the env entries a short-circuit guard's body
  ## left alone. `false` is always safe (the join then either `ite`s the
  ## entry or declines to join); it is returned for any kind not compared
  ## field by field here.
  if a.kind != b.kind: return false
  case a.kind
  of svBV8:  a.signed == b.signed and a.bv8.raw == b.bv8.raw
  of svBV16: a.signed == b.signed and a.bv16.raw == b.bv16.raw
  of svBV32: a.signed == b.signed and a.bv32.raw == b.bv32.raw
  of svBV64: a.signed == b.signed and a.bv64.raw == b.bv64.raw
  of svInt:
    a.zi.raw == b.zi.raw and a.ziWidth == b.ziWidth and
      a.ziSigned == b.ziSigned and a.ziIvl == b.ziIvl
  of svBool: a.bo.raw == b.bo.raw
  of svFloat32: a.fp32.raw == b.fp32.raw
  of svFloat64: a.fp64.raw == b.fp64.raw
  of svString: a.str.raw == b.str.raw
  of svTuple:
    if a.fields.len != b.fields.len or a.fieldNames != b.fieldNames:
      return false
    for i in 0 ..< a.fields.len:
      if not sameSV(a.fields[i], b.fields[i]): return false
    true
  of svArray:
    if a.arrElems.len != b.arrElems.len or a.arrElemTy != b.arrElemTy:
      return false
    for i in 0 ..< a.arrElems.len:
      if not sameSV(a.arrElems[i], b.arrElems[i]): return false
    true
  of svSeq:
    # Handle identity only, as `sameSymVal`'s arm: nothing is lowered or
    # read as a value, and the placeholder flag is itself compared, so a
    # placeholder never matches a backed seq (N27 audit, RFC-0005 S8w).
    a.seqLen.raw == b.seqLen.raw and a.seqDataRaw.raw == b.seqDataRaw.raw and  # [placeholder-audited]
      a.seqDataMore.len == b.seqDataMore.len and   ## RFC-0005 S8bc
      (block:
        var r = true
        for i in 0 ..< a.seqDataMore.len:
          if a.seqDataMore[i].raw != b.seqDataMore[i].raw: r = false
        r) and
      a.seqElemTy == b.seqElemTy and
      a.isUnsupportedFieldPlaceholder == b.isUnsupportedFieldPlaceholder and  # [placeholder-audited]
      a.seqUnsupportedFieldReason == b.seqUnsupportedFieldReason and
      a.seqUnsupportedFieldKind == b.seqUnsupportedFieldKind
  of svTable:
    a.tabDataRaw.raw == b.tabDataRaw.raw and
      a.tabDataMore.len == b.tabDataMore.len and
      (block:
        var same = true
        for i in 0 ..< a.tabDataMore.len:
          if a.tabDataMore[i].raw != b.tabDataMore[i].raw: same = false
        same) and
      a.tabPresentRaw.raw == b.tabPresentRaw.raw and
      a.tabSize.raw == b.tabSize.raw and
      a.tabKeyTy == b.tabKeyTy and a.tabValTy == b.tabValTy
  of svSet:
    a.setMembersRaw.raw == b.setMembersRaw.raw and
      a.setSize.raw == b.setSize.raw and a.setElemTy == b.setElemTy
  of svVariant:
    if a.vDisc.isNil or b.vDisc.isNil or not sameSV(a.vDisc[], b.vDisc[]) or
       a.vDiscName != b.vDiscName or a.vObjectName != b.vObjectName or
       a.vPlainFieldNames != b.vPlainFieldNames or
       a.vPlainFields.len != b.vPlainFields.len or
       a.vArmFields.len != b.vArmFields.len or
       a.vArmFieldNames != b.vArmFieldNames:
      return false
    for i in 0 ..< a.vPlainFields.len:
      if not sameSV(a.vPlainFields[i], b.vPlainFields[i]): return false
    for tag, fs in a.vArmFields:
      if not b.vArmFields.hasKey(tag): return false
      let gs = b.vArmFields[tag]
      if fs.len != gs.len: return false
      for i in 0 ..< fs.len:
        if not sameSV(fs[i], gs[i]): return false
    true
  of svUninterpRef:
    a.uninterpAst.raw == b.uninterpAst.raw and a.sortName == b.sortName and
      a.typeTag == b.typeTag
  of svDistinct:
    a.distinctAst.raw == b.distinctAst.raw and
      a.distinctName == b.distinctName and
      not a.distinctBaseSym.isNil and not b.distinctBaseSym.isNil and
      sameSV(a.distinctBaseSym[], b.distinctBaseSym[])
  of svRef:
    a.refAst.raw == b.refAst.raw and a.refPointee == b.refPointee
  of svPtr:
    a.ptrAst.raw == b.ptrAst.raw and a.ptrFamily == b.ptrFamily and
      a.ptrPointee == b.ptrPointee
  of svBitSet:   ## RFC-0005 S8bq
    a.bsRaw.raw == b.bsRaw.raw and a.bsElemTy == b.bsElemTy
  of svMultiVariant, svClosure:
    false

proc sameZ3Seq*(a, b: seq[Z3Bool]): bool =
  ## RFC-0005 S8w. Element-wise identical path-condition prefixes.
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if a[i].raw != b[i].raw: return false
  true

proc hasZ3Prefix*(s, prefix: seq[Z3Bool]): bool =
  if s.len < prefix.len: return false
  for i in 0 ..< prefix.len:
    if s[i].raw != prefix[i].raw: return false
  true

proc heapMetaExtends*(a, skip: Path): bool =
  ## RFC-0005 S8w (S8aa: the heap arrays themselves may differ; S8ac: the
  ## body may allocate). A survivor's logical-heap bookkeeping EXTENDS the
  ## skip path's: the same heap arrays by pointee type, the same nil-edge
  ## flag, and for every type its fresh-ref counter at least the skip
  ## path's and its live refs the skip path's followed by the refs the
  ## body minted (`freshRef`/`assertFreshness`). The body's allocations
  ## need no bookkeeping of the skip path's own: a fresh ref's facts
  ## (`!= nil`, `!=` each prior) sit in the survivor's own path condition,
  ## so the join holds them as `cond => R`, and on the skip side the ref is
  ## a constant nothing there reads. `heapDepth` is not compared: it counts
  ## the dereferences walked on the path (a budget, `heapDepthExhausted`),
  ## not program state, and the join keeps the larger count, which only
  ## ever halts a path sooner.
  if a.nilDeref != skip.nilDeref or a.heaps.len != skip.heaps.len or
     a.freshnessAssertCount < skip.freshnessAssertCount:
    return false
  for k in skip.heaps.keys:
    if not a.heaps.hasKey(k): return false
  for k, n in skip.allocCounters:
    if a.allocCounters.getOrDefault(k, 0) < n: return false
  for k, v in skip.liveRefs:
    if not a.liveRefs.hasKey(k): return false
    let u = a.liveRefs[k]
    if u.len < v.len: return false
    for i in 0 ..< v.len:
      if u[i].raw != v[i].raw: return false
  true

proc joinHeapMeta*(merged: Path, arms: seq[Path]) =
  ## RFC-0005 S8ac. The joined path's bookkeeping from the skip path's
  ## (`merged`, forked from it) and each survivor's extension of it
  ## (`heapMetaExtends`): every counter the largest, so a later `new T`
  ## on the joined path mints a name no survivor used; every live ref any
  ## survivor minted, so that `new T` is asserted distinct from each (on a
  ## side where the ref was never minted it is an unconstrained constant,
  ## and the inequality restricts nothing that side reads). Two survivors
  ## of one body mint the same NAME for their first allocation of a type
  ## (both count up from the skip path's counter); it is one constant,
  ## constrained by each survivor's facts under that survivor's own `G_i`.
  for a in arms:
    for k, n in a.allocCounters:
      if n > merged.allocCounters.getOrDefault(k, 0):
        merged.allocCounters[k] = n
    for k, v in a.liveRefs:
      var cur = merged.liveRefs.getOrDefault(k, @[])
      for r in v:
        var seen = false
        for c in cur:
          if c.raw == r.raw: seen = true; break
        if not seen: cur.add r
      merged.liveRefs[k] = cur
    merged.freshnessAssertCount = max(merged.freshnessAssertCount,
                                      a.freshnessAssertCount)

proc joinSV*(sel: Z3Bool, t, e: SymVal): Option[SymVal] =
  ## RFC-0005 S8w/S8aa. `ite(sel, t, e)` for two values of ONE program
  ## variable on the two sides of a short-circuit join, or `none` when the
  ## ite would not be exact. Identical values are kept as they are. A
  ## scalar is an `ite` of its term (a stamped Int of one width and sign
  ## keeps the hull of both intervals). S8aa adds the store shapes, where
  ## the value IS its terms, so the `ite` of the terms is the `ite` of the
  ## value: a string (one Z3 string), a seq of one element type (its
  ## length and its data array; a placeholder is never merged), a `ref` /
  ## `ptr` to one pointee (the address), and a tuple / array whose elements
  ## all join. S8ac adds a table (data, presence, counter), a set
  ## (members, counter), a distinct value (its constant and its base), an
  ## object variant with the same arms (discriminator and every field) and
  ## an opaque ref. A multi-axis variant and a closure decline.
  if sameSV(t, e): return some(t)
  if t.kind != e.kind: return none(SymVal)
  case t.kind
  of svBool, svFloat32, svFloat64:
    some(iteSV(sel, t, e))
  of svBV8, svBV16, svBV32, svBV64:
    if t.signed == e.signed: some(iteSV(sel, t, e)) else: none(SymVal)
  of svInt:
    if t.ziWidth != e.ziWidth or t.ziSigned != e.ziSigned:
      return none(SymVal)
    var m = iteSV(sel, t, e)
    m.ziIvl = if t.ziIvl.isSome and e.ziIvl.isSome:
                some(interval(min(t.ziIvl.get.lo, e.ziIvl.get.lo),
                              max(t.ziIvl.get.hi, e.ziIvl.get.hi)))
              else: none(Interval)
    some(m)
  of svString:
    some(SymVal(kind: svString, str: ite(sel, t.str, e.str)))
  of svSeq:
    if t.isUnsupportedFieldPlaceholder or e.isUnsupportedFieldPlaceholder or  # [placeholder-audited]
       t.seqElemTy != e.seqElemTy:
      return none(SymVal)
    let ctx = t.seqDataRaw.ctx  # [placeholder-audited]
    # Wrapped (inc_ref'd) at once: a raw handle is not owned, and the next
    # API call may reclaim it. RFC-0005 S8bc: every data array of a tree
    # element (the element types are equal, so the arrays agree).
    let ta = seqArrs(t)
    let ea = seqArrs(e)
    if ta.len != ea.len: return none(SymVal)
    var arrs: seq[Z3AnyAst]
    for i in 0 ..< ta.len:
      arrs.add wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw, ta[i].raw, ea[i].raw))
    some(mkSeqSV(ite(sel, t.seqLen, e.seqLen), arrs, t.seqElemTy))  # [placeholder-audited]
  of svRef:
    if t.refPointee != e.refPointee: none(SymVal)
    else: some(iteSV(sel, t, e))
  of svPtr:
    if t.ptrPointee != e.ptrPointee or t.ptrFamily != e.ptrFamily:
      none(SymVal)
    else: some(iteSV(sel, t, e))
  of svBitSet:   ## RFC-0005 S8bq: one bit-vector, of one domain
    if bitSetDomain(t.bsElemTy) != bitSetDomain(e.bsElemTy): none(SymVal)
    else: some(iteSV(sel, t, e))
  of svTuple:
    if t.fields.len != e.fields.len or t.fieldNames != e.fieldNames:
      return none(SymVal)
    var fs: seq[SymVal]
    for i in 0 ..< t.fields.len:
      let f = joinSV(sel, t.fields[i], e.fields[i])
      if f.isNone: return none(SymVal)
      fs.add f.get
    some(SymVal(kind: svTuple, fields: fs, fieldNames: t.fieldNames))
  of svArray:
    if t.arrElems.len != e.arrElems.len or t.arrElemTy != e.arrElemTy:
      return none(SymVal)
    var es: seq[SymVal]
    for i in 0 ..< t.arrElems.len:
      let x = joinSV(sel, t.arrElems[i], e.arrElems[i])
      if x.isNone: return none(SymVal)
      es.add x.get
    some(SymVal(kind: svArray, arrElems: es, arrElemTy: t.arrElemTy))
  of svTable:
    # RFC-0005 S8ac. A table IS its data and presence arrays and its
    # cardinality counter (#144), so the `ite` of the three is the `ite` of
    # the table.
    if t.tabKeyTy != e.tabKeyTy or t.tabValTy != e.tabValTy or
       t.tabDataMore.len != e.tabDataMore.len:   ## RFC-0005 S8at
      return none(SymVal)
    let ctx = t.tabDataRaw.ctx
    let data = wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw,
                              t.tabDataRaw.raw, e.tabDataRaw.raw))
    let present = wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw,
                                 t.tabPresentRaw.raw, e.tabPresentRaw.raw))
    var more: seq[Z3AnyAst]   ## RFC-0005 S8at
    for i in 0 ..< t.tabDataMore.len:
      more.add wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw,
                              t.tabDataMore[i].raw, e.tabDataMore[i].raw))
    some(SymVal(kind: svTable, tabDataRaw: data, tabDataMore: more,
                tabPresentRaw: present,
                tabSize: ite(sel, t.tabSize, e.tabSize),
                tabKeyTy: t.tabKeyTy, tabValTy: t.tabValTy))
  of svSet:
    # RFC-0005 S8ac. A set IS its membership array and its counter.
    if t.setElemTy != e.setElemTy: return none(SymVal)
    let ctx = t.setMembersRaw.ctx
    let members = wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw,
                                 t.setMembersRaw.raw, e.setMembersRaw.raw))
    some(SymVal(kind: svSet, setMembersRaw: members,
                setSize: ite(sel, t.setSize, e.setSize),
                setElemTy: t.setElemTy))
  of svDistinct:
    # RFC-0005 S8ac. A distinct value is its opaque constant and the base
    # value G4's eject pin ties it to (`eject(d) == base`). The `ite` of
    # both keeps the pin by congruence: `eject(ite(s, d1, d2))` is
    # `ite(s, eject(d1), eject(d2))`, i.e. `ite(s, b1, b2)`, the joined
    # base.
    if t.distinctName != e.distinctName or t.distinctBaseSym.isNil or
       e.distinctBaseSym.isNil:
      return none(SymVal)
    let b = joinSV(sel, t.distinctBaseSym[], e.distinctBaseSym[])
    if b.isNone: return none(SymVal)
    let ctx = t.distinctAst.ctx
    var bs = new SymVal
    bs[] = b.get
    some(SymVal(kind: svDistinct,
                distinctAst: wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw,
                              t.distinctAst.raw, e.distinctAst.raw)),
                distinctName: t.distinctName, distinctBaseSym: bs))
  of svVariant:
    # RFC-0005 S8ac. One object variant with the same arms: its
    # discriminator and every field (plain, and each arm's, live or not)
    # join. A field of an arm the joined discriminator does not select is
    # never read as a value (the field access checks the discriminator
    # first), so its `ite` is harmless.
    if t.vDisc.isNil or e.vDisc.isNil or t.vDiscName != e.vDiscName or
       t.vObjectName != e.vObjectName or
       t.vPlainFieldNames != e.vPlainFieldNames or
       t.vPlainFields.len != e.vPlainFields.len or
       t.vArmFields.len != e.vArmFields.len or
       t.vArmFieldNames != e.vArmFieldNames:
      return none(SymVal)
    let d = joinSV(sel, t.vDisc[], e.vDisc[])
    if d.isNone: return none(SymVal)
    var plain: seq[SymVal]
    for i in 0 ..< t.vPlainFields.len:
      let f = joinSV(sel, t.vPlainFields[i], e.vPlainFields[i])
      if f.isNone: return none(SymVal)
      plain.add f.get
    var arms: OrderedTable[int, seq[SymVal]]
    for tag, fs in t.vArmFields:
      if not e.vArmFields.hasKey(tag): return none(SymVal)
      let gs = e.vArmFields[tag]
      if fs.len != gs.len: return none(SymVal)
      var js: seq[SymVal]
      for i in 0 ..< fs.len:
        let f = joinSV(sel, fs[i], gs[i])
        if f.isNone: return none(SymVal)
        js.add f.get
      arms[tag] = js
    var dr = new SymVal
    dr[] = d.get
    # RFC-0016 PRC-07 slice B: the images merge cell by cell (one is missing:
    # none), the active members as discriminators do.
    var img: seq[Z3BitVec[64]]
    if t.vImage.len > 0 and t.vImage.len == e.vImage.len:
      for i in 0 ..< t.vImage.len: img.add ite(sel, t.vImage[i], e.vImage[i])
    var act: ref SymVal
    if t.vActive != nil and e.vActive != nil:
      let ja = joinSV(sel, t.vActive[], e.vActive[])
      if ja.isSome: act = activeOf(ja.get)
    some(SymVal(kind: svVariant, vDisc: dr, vDiscName: t.vDiscName,
                vObjectName: t.vObjectName, vArmFields: arms,
                vArmFieldNames: t.vArmFieldNames, vPlainFields: plain,
                vPlainFieldNames: t.vPlainFieldNames,
                vImage: img, vActive: act))
  of svUninterpRef:
    # RFC-0005 S8ac. An opaque ref (an exception object) is its constant.
    if t.sortName != e.sortName or t.typeTag != e.typeTag:
      return none(SymVal)
    let ctx = t.uninterpAst.ctx
    some(SymVal(kind: svUninterpRef, sortName: t.sortName, typeTag: t.typeTag,
                uninterpAst: wrap[Z3AnyAst](ctx, checkedIte(ctx, sel.raw,
                             t.uninterpAst.raw, e.uninterpAst.raw))))
  of svMultiVariant, svClosure:
    # RFC-0005 S8ac: declined. A multi-axis variant's axes and a closure's
    # site-bound function symbol have no one term to select; the paths
    # stay apart (the pre-S8w walk), which is exact.
    none(SymVal)

proc conjTail*(s: seq[Z3Bool], start: int): Option[Z3Bool] =
  ## RFC-0005 S8aa. The conjunction of `s[start .. ^1]`, `none` when empty.
  if s.len <= start: return none(Z3Bool)
  var c = s[start]
  for i in start + 1 ..< s.len: c = c and s[i]
  some(c)

proc mergeJoinPaths*(base: Path, cond: Z3Bool, armOut: seq[Path],
                    skip: Path): seq[Path] =
  ## RFC-0005 S8w. The join of an `IRStmt.ifJoin` guard (a short-circuit
  ## chain's `if sc: <next operand>`, `lowerShortCircuitParts`): the body's
  ## survivors `a_1 .. a_n` (forked from `base` with `cond`) and the skip
  ## path (`base` with `not cond`) become ONE path. Each survivor's own
  ## later branch conditions are `R_i` and its own defect-survivor facts
  ## `D_i`. With one survivor (S8w):
  ##   pc   = base.pc   & [cond => R]
  ##   dspc = base.dspc & [cond => D]
  ##   env  = a's env, each entry the skip path holds differently
  ##          `ite(cond, a's, skip's)`
  ## which is exactly `base and ((cond and R and D) or not cond)`, the
  ## disjunction of the two paths: `cond` separates them, so the `ite`
  ## picks each one's value. RFC-0005 S8aa: with several survivors (a
  ## callee's two returns, a nested `if` in the operand), the survivors are
  ## separated by their own `G_i = R_i and D_i` -- the walker forks every
  ## branch on a predicate and its negation, so at most one holds -- and
  ##   pc   = base.pc   & [cond => (R_1 or ... or R_n)]
  ##   dspc = base.dspc & [cond => (G_1 or ... or G_n)]
  ##   env  = ite(cond, ite(G_1, a_1's, ite(G_2, a_2's, ... a_n's)), skip's)
  ## (the last survivor needs no selector: under `cond` one `G_i` holds).
  ## The two facts together are `cond => (G_1 or ... or G_n)`; `pc` keeps
  ## only branch conditions, as everywhere (ADR-0012). The reads the body
  ## hoisted were already forked (and their raises routed) on each
  ## survivor, under `cond`; only the continuation is shared.
  ##
  ## An entry joins through `joinSV`: scalars, and since S8aa strings, seqs,
  ## refs and tuples / arrays of them. A heap array the body wrote (a
  ## `ref` field store) joins the same way, `ite` over the arrays, when the
  ## heap bookkeeping extends the skip path's (`heapMetaExtends`; since
  ## S8ac the body may allocate, `joinHeapMeta`).
  ##
  ## Declined (the paths are returned as they are, as before S8w) when the
  ## join would not be exact: a survivor's taint differs from the skip
  ## path's, the bookkeeping does not extend the skip path's
  ## (`heapMetaExtends`), a prefix was rewritten,
  ## an entry does not join (`joinSV`), or an entry is bound on some
  ## survivors and not others. Entries only the body bound (its
  ## temporaries) are kept as the body bound them: nothing on the skip side
  ## reads them.
  if armOut.len == 0:
    return @[skip]
  let decline = armOut & @[skip]
  if not sameZ3Seq(skip.defectSurvivorPc, base.defectSurvivorPc):
    return decline
  for a in armOut:
    if a.taint != skip.taint or a.undefined != skip.undefined or
       not heapMetaExtends(a, skip) or
       not hasZ3Prefix(a.pc, base.pc) or a.pc.len <= base.pc.len or
       a.pc[base.pc.len].raw != cond.raw or
       not hasZ3Prefix(a.defectSurvivorPc, base.defectSurvivorPc):
      return decline
  let n = armOut.len
  var rs, gs: seq[Option[Z3Bool]]
  for a in armOut:
    let r = conjTail(a.pc, base.pc.len + 1)
    let d = conjTail(a.defectSurvivorPc, base.defectSurvivorPc.len)
    rs.add r
    gs.add(if r.isSome and d.isSome: some(r.get and d.get)
           elif r.isSome: r
           else: d)
  # Several survivors are separated only by their own `G_i`: a survivor
  # with none (an unconditional one) cannot be told apart, so decline.
  if n > 1:
    for g in gs:
      if g.isNone: return decline
  proc armValue(vals: seq[SymVal]): Option[SymVal] =
    # ite(G_1, v_1, ite(G_2, v_2, ... v_n)).
    var acc = some(vals[n - 1])
    for i in countdown(n - 2, 0):
      acc = joinSV(gs[i].get, vals[i], acc.get)
      if acc.isNone: return acc
    acc
  var env: Env
  for k in armOut[0].env.keys:
    var vals: seq[SymVal]
    for a in armOut:
      if not a.env.hasKey(k): return decline
      vals.add a.env[k]
    let armV = armValue(vals)
    if armV.isNone: return decline
    if not skip.env.hasKey(k):
      env[k] = armV.get
      continue
    let e = skip.env[k]
    let av = armV.get
    if av.kind == svBool and e.kind == svBool and not sameSV(av, e) and
       (e.bo.raw == cond.raw or (not e.bo).raw == cond.raw):
      # RFC-0005 S8w2: the chain's own guard temporary. On the skip side
      # it IS the guard's operand -- `cond` itself for an `and` chain (so
      # false there), `not cond` for an `or` chain (so true there) -- and
      # `ite(cond, v, e)` is exactly `cond and v`, resp. `e or v`. Built
      # as the connective, the target query is the conjunction (the
      # disjunction) the chain means, the shape the pre-S8w walk lowered:
      # the `ite` form is equivalent but not the same query, and Z3 4.13.4
      # answered it with a different (valid, longer) model.
      env[k] =
        if e.bo.raw == cond.raw: SymVal(kind: svBool, bo: cond and av.bo)
        else: SymVal(kind: svBool, bo: e.bo or av.bo)
      continue
    let j = joinSV(cond, av, e)
    if j.isNone: return decline
    env[k] = j.get
  for a in armOut:
    if a.env.len != armOut[0].env.len: return decline
  for k in skip.env.keys:
    if not armOut[0].env.hasKey(k): return decline
  # Heap arrays, in sorted key order (a build-independent term order, as
  # the return merge's heap `ite`).
  var hkeys: seq[string]
  for k in skip.heaps.keys: hkeys.add k
  sort(hkeys)
  var joined = skip.heaps
  for k in hkeys:
    var acc = armOut[n - 1].heaps[k]
    var changed = acc.raw != skip.heaps[k].raw
    for i in countdown(n - 2, 0):
      let h = armOut[i].heaps[k]
      if h.raw == acc.raw: continue
      acc = wrap[Z3AnyAst](h.ctx, checkedIte(h.ctx, gs[i].get.raw, h.raw, acc.raw))
      changed = true
    if changed and acc.raw != skip.heaps[k].raw:
      joined[k] = wrap[Z3AnyAst](acc.ctx, checkedIte(acc.ctx, cond.raw, acc.raw,
                                                     skip.heaps[k].raw))
  var pc = base.pc
  var facts: Option[Z3Bool]
  if n == 1:
    if rs[0].isSome: pc.add cond.implies(rs[0].get)
    facts = conjTail(armOut[0].defectSurvivorPc, base.defectSurvivorPc.len)
  else:
    var anyR = rs[0]
    for i in 1 ..< n:
      if anyR.isNone or rs[i].isNone: anyR = none(Z3Bool); break
      anyR = some(anyR.get or rs[i].get)
    if anyR.isSome: pc.add cond.implies(anyR.get)
    var anyG = gs[0].get
    for i in 1 ..< n: anyG = anyG or gs[i].get
    facts = some(anyG)
  let merged = forkPath(skip, pc, env)
  merged.heaps = joined
  joinHeapMeta(merged, armOut)
  for a in armOut: merged.heapDepth = max(merged.heapDepth, a.heapDepth)
  if facts.isSome:
    merged.defectSurvivorPc = base.defectSurvivorPc & @[cond.implies(facts.get)]
  @[merged]

var uninterpDeclKind {.threadvar.}: int
  ## RFC-0016 W3-z int4x. `Z3_get_decl_kind` of an uninterpreted symbol (a
  ## constant or a function), plus one; 0 until first read.

proc uninterpSymbols*(ctx: Z3Context; root: Z3Bool): HashSet[int] =
  ## RFC-0016 W3-z int4x. The uninterpreted symbols `root` mentions -- its
  ## free constants and uninterpreted functions, each by its declaration's
  ## id. Bound variables (a quantifier's, a lambda's) are not symbols.
  if uninterpDeclKind == 0:
    let pc = probeContext()
    let c = mkIntVar(pc, "__int4x_uninterp_probe")
    uninterpDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, c.raw)))) + 1
  var seen: HashSet[int]
  var stack = @[root.raw]
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    case Z3_get_ast_kind(ctx.raw, t)
    of Z3_APP_AST:
      let app = Z3_to_app(ctx.raw, t)
      let decl = Z3_get_app_decl(ctx.raw, app)
      if ord(Z3_get_decl_kind(ctx.raw, decl)) + 1 == uninterpDeclKind:
        result.incl astId(ctx, Z3_func_decl_to_ast(ctx.raw, decl))
      for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
        stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
    of Z3_QUANTIFIER_AST:
      stack.add Z3_get_quantifier_body(ctx.raw, t)
    else: discard

proc definingSlice*(ctx: Z3Context; pins: seq[Z3Bool]; seeds: seq[Z3Bool];
                   conjuncts: seq[Z3Bool]): seq[Z3Bool] =
  ## RFC-0016 W3-z int4x. The conjuncts of `conjuncts` (a path's `pc` and
  ## defect-survivor facts) that constrain the symbols `seeds` (a branch
  ## condition and its facts) mention which the pins leave free, closed
  ## transitively: one that shares such a symbol with the seeds or with a
  ## conjunct already taken is taken, and its own free symbols join the
  ## reach. A symbol a pin fixes to a ground value (`x == v`, the pin's only
  ## symbol) does not connect: under the pins it is that value. In order.
  ##
  ## This is the constraint-independence slice of a symbolic executor's
  ## query cache (KLEE's independent-constraint set). The conjuncts it leaves
  ## out share no free symbol with the condition, so on a path the pins do
  ## not contradict, `pins & slice & cond` is satisfiable iff
  ## `pins & conjuncts & cond` is: a model of the first extends by a model
  ## of the rest, over disjoint free symbols. It is also a subset of the
  ## `pc`, which the followed execution satisfies, so an answer it decides
  ## holds of that execution whatever the rest says.
  var pinned: HashSet[int]
  for p in pins:
    let syms = uninterpSymbols(ctx, p)
    if syms.len == 1:
      for s in syms: pinned.incl s
  var reach: HashSet[int]
  for s in seeds:
    for x in uninterpSymbols(ctx, s):
      if x notin pinned: reach.incl x
  if reach.len == 0: return
  var free = newSeq[HashSet[int]](conjuncts.len)
  for i, c in conjuncts:
    for x in uninterpSymbols(ctx, c):
      if x notin pinned: free[i].incl x
  var taken = newSeq[bool](conjuncts.len)
  var grew = true
  while grew:
    grew = false
    for i in 0 ..< conjuncts.len:
      if taken[i] or free[i].len == 0 or disjoint(free[i], reach): continue
      taken[i] = true
      reach.incl free[i]
      grew = true
  for i, c in conjuncts:
    if taken[i]: result.add c


proc followBranchOutcome*(w: var WalkCtx; dp: Path; cond: Z3Bool;
                         facts: seq[Z3Bool];
                         construct: WalkerConstructKind): FollowOutcome =
  ## RFC-0016 K10b. The concrete outcome of `cond` for a follow-mode branch,
  ## or none when the pins do not decide it. The fuzzer's replay pins every
  ## draw, so `concreteEq` alone decides a branch there. The tail gate's pins
  ## cover only the parameters, and a branch on a routine's result (`$tailCol(a)`
  ## branches on the call's fresh result constant) is decided by the path's
  ## own `pc`, where the taken arms and the result's binding sit. A branch the
  ## pins and the closure facts leave open is asked again under the `pc`
  ## (true of the followed execution, so it prunes nothing the pins describe).
  ## Only then: the `pc` of a path that built a string or a heap joins Int and
  ## bit-vector terms a solve may not close, so the first ask stays cheap.
  ## Without the second ask the branch read as undecided and the walk went on
  ## without the arm's bindings: a later read of a name the arm binds was the
  ## unbound-name stand-in, an `eqBV` kind assertion (`weInternalWalkerFault`).
  ##
  ## RFC-0016 W3-z R9: a first ask whose check spent its whole bound
  ## undecided (`scratchCapped`) is not asked again under the `pc`: the same
  ## query with more terms in it, at the same bound.
  ##
  ## RFC-0016 W3-z int4x: on the tail walk the first ask also carries the
  ## part of the `pc` that defines the condition's free symbols
  ## (`definingSlice`). A symbol the pins leave free -- a grown string
  ## `__setLenStr` = `s ++ pad`, an opaque call's result -- was free in it
  ## though the `pc` defines it, so the ask was about any string at all, not
  ## the run's: `t[0] == 'q'` over a free `t` spent the whole 20M-unit bound
  ## undecided (about 268 s under Z3 5.1) three times in one
  ## `tsymex_rfc0005_s8bx_setlenstr` run, and the capped first ask then kept
  ## the second ask, which decides it at once, from being made. Pinned
  ## symbols alone, the slice is empty and the first ask is what it was.
  ## Only the tail walk reads the `pc` here (K10b): the fuzzer's replay pins
  ## every draw. Fail-closed: the slice is a subset of the `pc`, which the
  ## followed execution satisfies, so `some(...)` from it is that
  ## execution's outcome. A slice that is the whole `pc` makes the second
  ## ask a repeat of the first, so it is not made.
  ##
  ## RFC-0016 W3-z int6: on the tail walk, both sides UNSAT is `foOffRun`.
  ## The asks carry a subset of the path's `pc` and facts, so the pins
  ## contradict the path itself: it is an arm an earlier open fork walked
  ## that the run did not take. It was read as open, so every later branch
  ## on it forked both ways again, each arm as dead as the path: a
  ## `tsymex_rfc0005_s8cn_views_f` tail walk asked 1,967 branches, 1,324 of
  ## them both-UNSAT, and took 65 s where the explore walk took seconds.
  ## The caller drops the path, as `concretelyInfeasible` drops one whose new
  ## facts the pins contradict. Only definite UNSATs say so (an undecided
  ## ask is `foOpen`), so no path the run can take is dropped. The fuzzer's
  ## replay pins every draw, where both-UNSAT is a bug, not a dead arm: it
  ## stays `foOpen` there, and degrades as before.
  scratchCapped = false
  let wholePc = dp.pc & dp.defectSurvivorPc
  let defs =
    if w.tailGate: definingSlice(w.z3, w.concreteEq, facts & @[cond], wholePc)
    else: newSeq[Z3Bool]()
  proc read(st: (Z3Status, Z3Status); tail: bool): FollowOutcome =
    if st[0] == zsSat and st[1] == zsUnsat: foTrue
    elif st[0] == zsUnsat and st[1] == zsSat: foFalse
    elif tail and st[0] == zsUnsat and st[1] == zsUnsat: foOffRun
    else: foOpen
  result = read(concreteBranchAsk(w.z3, w.concreteEq, cond, w.settings,
                                  defs & facts, w.tailGate), w.tailGate)
  if result == foOpen and w.tailGate and not scratchCapped and
     defs.len < wholePc.len:
    result = read(concreteBranchAsk(w.z3, w.concreteEq, cond, w.settings,
                                    wholePc & facts, w.tailGate), w.tailGate)
  if result == foOpen:
    markAmbiguous(w, construct)
    # Section 9.1 item 3: an undecided side counts as undefined, so the tail
    # walk (`tailGate`) forks both arms at the caller and walks each; nothing
    # an arm does is skipped. An arm whose `pc` the pins contradict is not
    # the run, and its undefined sides read `concretelyInfeasible` at the op.

proc followGuard*(w: var WalkCtx; dp: Path; cond: Z3Bool; factBase: int;
                 construct: WalkerConstructKind): FollowOutcome =
  ## RFC-0016 review R8-3. The outcome of one continuation of a guard a
  ## follow-mode walk evaluated (`walkIfFollowConcrete`,
  ## `walkWhileFollowConcrete`), decided under the facts its lowering and
  ## drain added to `dp.defectSurvivorPc` past `factBase` (a closure call's
  ## exit facts, a drained raise's negation). They must hold on the replay and
  ## they define a closure call's result in `cond`, so the pins read the guard
  ## with them. A continuation whose new facts the pins contradict is not
  ## this trace: `foOffRun`, as a path the pins contradict on the tail walk
  ## (`followBranchOutcome`), and the caller drops it. Otherwise
  ## `followBranchOutcome`.
  let newFacts =
    if dp.defectSurvivorPc.len > factBase:
      dp.defectSurvivorPc[factBase .. ^1]
    else: newSeq[Z3Bool]()
  if newFacts.len > 0 and
     concretelyInfeasible(w.z3, w.concreteEq, newFacts, w.settings):
    return foOffRun
  followBranchOutcome(w, dp, cond, newFacts, construct)

proc recvValue*(p: Path; name: string; w: var WalkCtx): (SymVal, Path) =
  ## RFC-0005 batch 6. The value of the receiver `name` a statement arm
  ## updates in place (`xs[i] = v`, `xs.pop()`, `o.kind = k`), and the path
  ## to continue on. A bound name is read from `Env`. An unbound one is read
  ## as `lower` reads the name (`iekVar`): a module-level variable the walk
  ## has not written yet is its ENTRY value (S8as `entryValueOf`, the path
  ## tainted `feGlobalHavoc`), and anything else declines in-band. The arms
  ## read `Env` directly before, so a global receiver not yet written
  ## raised `KeyError` (the path was dropped: a false `sxUnsat`) or skipped
  ## the statement (its `FieldDefect` was never forked).
  ##
  ## RFC-0005 S8cd: the receiver is read as one, not observed. An untouched
  ## unwritten part (a field the statement does not reach, an element it
  ## overwrites) does not taint the path; each arm observes the parts it
  ## reads (`observeRecvPart`, `unwrittenDisc`). And a global of a known type
  ## is read at that type (`vGlobalTy`, as a parsed read carries).
  if p.env.hasKey(name): return (p.env[name], p)
  let recv = mkVar(name)
  if w.statics.globals.hasKey(name):
    recv.vGlobalTy = w.statics.globals[name].ty
  lowerAsReceiver = true
  lowerInExpr(p, recv, w)

const viewGrownPrefix* = "__viewGrown#"
  ## RFC-0005 S8cn. On a callee's path, the condition that a key was added to
  ## the Table of a `slot` entry: a write to the view past it may be lost to a
  ## rehash, by a capacity that is not modelled.
const viewGonePrefix* = "__viewGone#"
  ## RFC-0005 S8cn. Set on a callee's path where the key of a `slot` entry was
  ## removed and the slot is empty (`syncAddrCells`).

func irFieldPath*(e: IRExpr): string =
  ## RFC-0005 S8cn. `e` as a location path (`t`, `o.tab`), or "".
  if e == nil: return ""
  case e.kind
  of iekVar: e.vname
  of iekField:
    let r = irFieldPath(e.obj)
    if r.len == 0: "" else: r & "." & e.fieldName
  else: ""

func exprLocRoot*(e: IRExpr): string =
  ## RFC-0005 S8cn. The variable the location `e` is a path into, or "".
  if e == nil: return ""
  case e.kind
  of iekVar: e.vname
  of iekField: exprLocRoot(e.obj)
  of iekIndex: exprLocRoot(e.arr)
  else: ""

proc bindsViewWholeShape*(s: IRStmt; names: var seq[string];
                         sh: var WriteShape): bool =
  ## RFC-0005 S8cn. `s` holds the memory of one of `names` in a way the walk
  ## takes for a copy. A local bound to a whole seq, Table or string: Nim's
  ## cursor inference (ARC/ORC) shares the memory when the local is never
  ## mutated (`let c = t`), and copies when it is, so whether a write through
  ## the other formal is seen through the local depends on what the compiler
  ## proved. A loop over one: `items` and `values` yield `lent`, so the loop
  ## variable reads the element live.
  if s == nil: return false
  case s.kind
  of isBlock:
    for c in s.stmts:
      if bindsViewWholeShape(c, names, sh): return true
  of isIf:
    for b in s.branches:
      if bindsViewWholeShape(b.body, names, sh): return true
    return bindsViewWholeShape(s.elseBody, names, sh)
  of isWhile:
    return bindsViewWholeShape(s.wbody, names, sh)
  of isTry:
    if bindsViewWholeShape(s.tryBody, names, sh): return true
    for h in s.tryHandlers:
      if bindsViewWholeShape(h.body, names, sh): return true
    return bindsViewWholeShape(s.tryFinally, names, sh)
  of isLet:
    # A synthetic `let` is the walk's own (a `var` actual's temporary).
    if s.lty == nil or s.lname.startsWith("__sym_"): return false
    if s.lty.kind in {itInt, itBool, itFloat32, itFloat64}:
      # A scalar binding holds no memory of the container. The route lets it
      # through; the table says which decline this shape's verdict carries.
      sh = wsScalarRead
      return routeDeclines(rrViewWhole, sh)
    if s.lvalue != nil and s.lvalue.kind == iekTupleLit:
      sh = wsTupleCopy   # a constructor copies what it is given
      return routeDeclines(rrViewWhole, sh)
    if exprLocRoot(s.lvalue) in names:
      sh = wsVarCopy
      return routeDeclines(rrViewWhole, sh)
    return false
  of isIndex:
    if exprLocRoot(s.ixArr) in names:
      if s.ixRetName.startsWith("__sym_fs_"):   # the `for` lowering
        sh = wsLentLoop
        return routeDeclines(rrViewWhole, sh)
      if s.ixElemTy != nil and
         s.ixElemTy.kind notin {itInt, itBool, itFloat32, itFloat64}:
        names.add s.ixRetName
  of isTabKeys:
    if exprLocRoot(s.tkRecv) in names:
      sh = wsLentLoop
      return routeDeclines(rrViewWhole, sh)
  # RFC-0016 K6c (W-10). No `else`: a statement kind is listed here as one that
  # binds no view of a container's memory, so a kind added to `IRStmtKind` does
  # not compile until its author decides (the fail-open `else: discard` this
  # replaced let a new binder through as "holds nothing").
  of isAssign, isBreak, isContinue, isReturn, isAssert, isAssume,
     isCall, isVariantField, isVariantReassign, isVariantReassignSymbolic,
     isVariantConstructSym, isIndexAssign, isSeqPop, isTargetLabel, isRaise,
     isDeref, isNew, isDerefWrite, isUnsupported, isUnsafeCast, isSetLen,
     isUndefined:
    discard
  false

proc bindViewAliases*(stmt: IRStmt; sig: ProcSig; callerEnv: Env;
                     w: var WalkCtx): string =
  ## RFC-0005 S8bx (item 3). Record the call's `cViewAliases` in the callee's
  ## frame (just pushed), as `slot` address entries (`AddrCellEntry`,
  ## `syncAddrCells`). Returns why the call declines, or "": the view's
  ## formal is by value and not a scalar (Nim may pass it by address, so it
  ## would see the table's writes: not modelled), or the key is unbound.
  ## A by-value scalar view is a copy, and nothing relates it to the table.
  ## A call made inside such a callee that passes both formals on carries
  ## the pair into its own callee (Nim passes the one location on).
  ## RFC-0005 S8cn: the entry's `path` is the field path from the Table's
  ## formal to the Table, when an object holding it came. A call made on a
  ## slot the key has left declines (`viewGonePrefix`: the callee would need
  ## that state, and nothing passes it).
  var pairs: seq[tuple[viewArg, tabArg: int; key: SymVal; path: seq[string]]]
  for a in stmt.cViewAliases:
    if a.viewArg >= sig.params.len or a.tabArg >= sig.params.len or
       not callerEnv.hasKey(a.keyName):
      return "and the walk does not bind the two"
    pairs.add (viewArg: a.viewArg, tabArg: a.tabArg,
               key: callerEnv[a.keyName],
               path: (if a.tabField.len > 0: a.tabField.split('.')
                      else: newSeq[string]()))
  if w.frameStack.len > 0:
    for a in w.frameStack[^1].addrCells:
      if a.slot.len == 0: continue
      var vi, ti = -1
      var path = a.path
      for i, arg in stmt.cargs:
        if arg.kind == iekVar and arg.vname == a.local: vi = i
        elif irFieldPath(arg) == a.slot:
          ti = i
        elif a.path.len > 0:
          # The holder's Table passed on: a field `var` actual comes through
          # a temporary (`cVarLocs`).
          for l in stmt.cVarLocs:
            if l.mode == "var" and l.root == a.slot and l.path == a.path and
               arg.kind == iekVar and arg.vname == l.temp:
              ti = i
              path = @[]
          if irFieldPath(arg) == a.slot & "." & a.path.join("."):
            ti = i
            path = @[]
      if vi >= 0 and ti >= 0 and vi < sig.params.len and ti < sig.params.len:
        if callerEnv.hasKey(viewGonePrefix & a.local):
          return "on a slot its key has left"
        pairs.add (viewArg: vi, tabArg: ti, key: a.ixs[0], path: path)
  for a in pairs:
    let vf = sig.params[a.viewArg]
    if not vf.isVar:
      if vf.ty.kind in {itInt, itBool, itFloat32, itFloat64}: continue
      return "the view by value (not modelled for a " & $vf.ty.kind & ")"
    var held = @[vf.name, sig.params[a.tabArg].name]
    var heldShape = wsUnlisted
    if bindsViewWholeShape(sig.body, held, heldShape):
      return "a local or a `for` holding the whole of one (Nim may share its " &
             "memory or copy it, by what its cursor inference proved) [" &
             admitShape(rrViewWhole, heldShape).decline[1] & "]"
    w.frame.addrCells.add (local: vf.name, cell: "", ty: vf.ty, path: a.path,
                           ixs: @[a.key], bound: true, view: false,
                           slot: sig.params[a.tabArg].name)
  ""

proc haltFrontier*(w: var WalkCtx; pruned: int; where: string) =
  ## The one `ckFrontier` site: `maxFrontierSize` dropped `pruned` live paths,
  ## after a statement (`walkBlock`) or inside a k-unroll (`capLoopFrontier`).
  w.halted(beBudgetExhaustedPrune,
    "path-frontier cap (maxFrontierSize=" &
         $w.settings.budget.maxFrontierSize & ") pruned " & $pruned &
         " live path(s)" & where & " — their verdicts are unexplored " &
         "(beBudgetExhaustedPrune)",
    cap = ckFrontier)

proc capLoopFrontier*(paths: var seq[Path]; w: var WalkCtx) =
  ## RFC-0016 K7 (CRH-01). `walkBlock` prunes `maxFrontierSize` only after a
  ## statement, and one unrolled loop multiplies its live set inside it. Holds
  ## a k-unroll's active and exit sets to the same nonzero cap: certain paths
  ## kept before tainted ones, the overflow HALTED as `ckFrontier`
  ## (`beBudgetExhaustedPrune`), so the run is `sxUnknown`.
  let limit = w.settings.budget.maxFrontierSize
  if limit <= 0 or paths.len <= limit: return
  var kept: seq[Path]
  for p in paths:
    if p.taint == {} and kept.len < limit: kept.add p
  for p in paths:
    if p.taint != {} and kept.len < limit: kept.add p
  haltFrontier(w, paths.len - kept.len, " of a while-loop k-unroll")
  paths = kept

proc resetWalkExprState*() =
  ## RFC-0016 INT-34 B6b. The per-run resets `resetSymexRunState` made for
  ## this module's threadvars, in their order there. `scratchCapped` is set
  ## and cleared per concrete-branch ask; `uninterpDeclKind` caches the
  ## linked Z3's decl kind for the thread: neither is per-run.
  closureBodyCallerPc = @[]              ## RFC-0005 S8cn
  currentCallerTaint = {}                ## RFC-0005 S8cn
  currentCallerUb = {}                   ## RFC-0016 W1-d3
  currentCallerPc = @[]                  ## RFC-0005 S8cn
  lastDrainedClosureExitPc = @[]         ## RFC-0005 S7

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(
    lastDrainedClosureExitPc, currentCallerUb, currentCallerTaint,
    currentCallerPc, closureBodyCallerPc, scratchCapped, uninterpDeclKind)

registerThreadStateRelease(releaseThreadState)
