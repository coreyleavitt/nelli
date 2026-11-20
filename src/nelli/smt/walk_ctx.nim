## RFC-0016 INT-34 B6a. The walk context's verbs: a leaf cut out of
## `runtime.nim`.
##
## Region R3 of `runtime.nim` (`scripts/int34-deps.py`) lives here whole, in
## the order it had there:
##
##   * the degrade funnel and the path verdicts a statement arm returns
##     (`degrade`, `halted`, `exact`, `surviving`, `continued`,
##     `selfTainted`, `carriedDegrade`, `asDegrade`, `closureDegrade`), the
##     root path (`initialWalkPath`) and the walk-end leak pin
##     (`stampLoweringPendingLeak`);
##   * the pending lowering effects a closure descent sets aside and puts
##     back (`takePendingLowerEffects`, `restorePendingLowerEffects`) and the
##     in-flight raise threadvars (`setInFlightThreadvars`);
##   * the frames (`exitPath`, `initLoopFrame`, `initCallFrame`,
##     `initCallFrameCtx`, `pushFrame`, `popFrame`) and the stop test
##     (`shouldStop`);
##   * the target solve and the verdict (`solveTargetHit`, `admitSolvedHit`,
##     `toCandidate`, `decideVerdict`, `rfc0005RawStatus`, `symValHash`);
##   * the opaque-call heap havoc (`havocOpaqueHeaps`, `havocOpaqueWrites`),
##     the outer bindings and cells a call carries (`threadOuterBindings`,
##     `inheritAddrCells`, `carryElemCells`, `settleAddrCells`, ...) and the
##     call-summary cache keys (`argShapeKey`, `cacheArgsSame`,
##     `exitKeepsOuter`, `pruneFactsHold`, ...).
##
## With it, the run state of R0 that R3 reads: `heapDepthErrors`,
## `newFieldZeroErrors`, the caller-heap threadvars a closure descent starts
## from (`currentCallerHeaps`, `currentCallerHeapDepth`,
## `currentCallerAllocCounters`, `currentCallerLiveRefs`), the closure-exit
## ones it hands back (`currentClosureExitHeaps`,
## `currentClosureExitAllocCounters`, `currentClosureExitLiveRefs`,
## `currentClosureDidMutateHeap`, `currentClosureExitPc`) and
## `currentClosureCallErrors`. Each threadvar lives at the lowest layer that
## reads it: the walker above reads and writes them through this module's
## export, and `resetWalkCtxState` (called by `resetSymexRunState`) resets
## every one of them that is per-run.
##
## R3 calls nothing above it, so this leaf declares no hooks.
##
## Every routine is exported, so `runtime.nim` can call it; `runtime.nim`
## re-exports by name only what it exported before the cut.

import std/tables
import std/options
import std/hashes
import std/math
import std/strutils
import z3

import ./types
import ./symval
import ./walk_state
import ./walk_types
import ./walk_path
import ./lower_expr
import ./walk_solve
import ./heap_model
import ./exits
from std/importutils import privateAccess
privateAccess(RawWitness)     ## its fields stay private to walk_types (see its header)
privateAccess(SatCandidate)   ## `input`, as for `replay_settle.nim`

var heapDepthErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 R9 (ADR-0010). Accumulator for `heDepthExhausted` (sevError),
  ## recorded when a deref/deref-write on a path would push `path.heapDepth` to
  ## the EFFECTIVE heap-depth limit (`maxHeapDepth`, else `maxCallDepth`, else
  ## 256). The exhausting path is HALTED (it returns no survivor → contributes
  ## `sxUnknown` via `w.sawUnknown`); shallower paths continue. The error rides
  ## every verdict branch via `exnWarnings` (dedup'd by message) so a degraded
  ## `sxUnknown` carries the classified kind (Invariant 3). Reset at
  ## `runSymexImpl` entry. A SUT whose every deref stays UNDER the cap drains
  ## NOTHING — exactly the R2 `freshnessCapHints` / R8 `ptrFamilyHints` idiom.

var newFieldZeroErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Cluster H Step C (ADR-0022). Accumulator for `heNewFieldZeroUnsupported`
  ## (sevError), recorded when the universal `isNew` zero-write
  ## (`runtime_heap.nim`) finds a freshly-allocated object FIELD whose type has
  ## no clean zero encoding this cycle (`zeroIRExprForType` returned `nil`).
  ## The path is tainted `uncertain = true` and `w.sawUnknown` is set (SND-1,
  ## mirroring `isUnsupported`) rather than halted outright, so a shallower/
  ## unrelated finding on the SAME run can still surface — but this path's own
  ## verdict is forced to `sxUnknown`. Reset at `runSymexImpl` entry; drained
  ## (dedup'd) into `RawResult.errors` on every verdict branch — exactly the R9
  ## `heapDepthErrors` idiom.

var currentCallerHeaps* {.threadvar.}: Table[string, Z3AnyAst]
  ## Phase 15 R1b (ADR-0010). The CALLER path's logical-heap arrays, threaded
  ## into a CLOSURE-call descent. The `isCall`/`isGenericCall` arms thread the
  ## caller heap structurally (the callee path is `forkPath`'d from the caller,
  ## carrying `p.heaps` in via `deepCopyHeapState`), but a `iekClosureCall` is
  ## lowered inside `lower` (a pure env→SymVal evaluator with NO `Path` in
  ## scope — the same constraint that forced `currentWalkCtxPtr`). So the walk
  ## arm that is about to lower an expression seeds this threadvar from the
  ## current path's `heaps`, and `applyClosureGround` builds the closure
  ## `descentBase` from it instead of R1's fresh-empty default — so a deref in
  ## the closure body reads the SAME threaded heap. Reset at `runSymexImpl`
  ## entry and (re)seeded per path before expression lowering.
  ## NOTE: closure-body heap WRITES (the return-merge BACK out of a closure
  ## descent) are inert until R4 (closures cannot mutate the heap yet); R1b
  ## threads the READ direction (entry) for the closure arm.

var currentCallerHeapDepth* {.threadvar.}: int
  ## Phase 15 R1b. Companion to `currentCallerHeaps`: the caller path's
  ## `heapDepth`, threaded into the closure descent's `descentBase`.

var currentCallerAllocCounters* {.threadvar.}: Table[string, int]
  ## Phase 15 R1b. Companion to `currentCallerHeaps`: the caller path's
  ## `allocCounters`, threaded into the closure descent's `descentBase` so
  ## allocations inside the closure body (R2+) start above the caller's
  ## freshness counters.

var currentCallerLiveRefs* {.threadvar.}: Table[string, seq[Z3AnyAst]]
  ## Phase 15 CR-5. Companion to `currentCallerHeaps`: the caller path's
  ## `liveRefs`, seeded into the closure `descentBase` so `assertFreshness`
  ## for a `new T` inside the closure body emits `newRef != callerRef`
  ## distinctness inequalities against every prior live ref the caller
  ## already minted. Without this seed, the closure descent sees an empty
  ## `liveRefs` and Z3 can alias a closure-body `new T` with a caller ref
  ## (CR-5 spurious aliasing witness). Reset at `runSymexImpl` entry.

# ---- Phase 15 CR-1: post-closure heap state threadvars ----------------------
# Complement to the `currentCallerHeap*` entry threadvars (R1b): these carry
# the EXIT heap from a closure body descent BACK to the calling walk arm.
# `applyClosureGround` writes them after merging the closure's exit paths;
# `drainClosureExitHeap` in `walk` applies them to the survivor path. This
# mirrors the named-proc return-merge (isCall arm ~5443-5463) for the closure
# arm — the same `max(caller, callee)` allocCounter merge and direct heap
# replacement. Reset at `runSymexImpl` entry and at each `applyClosureGround`
# entry (so a non-heap-writing closure leaves the drain a no-op).

var currentClosureExitHeaps* {.threadvar.}: Table[string, Z3AnyAst]
  ## Phase 15 CR-1. The merged logical-heap arrays from the closure body's
  ## exit paths. Written by `applyClosureGround` when the body produced at
  ## least one exit path; empty when the closure produced no exit paths (the
  ## body diverged or was fully-stubbed).

var currentClosureExitAllocCounters* {.threadvar.}: Table[string, int]
  ## Phase 15 CR-1. The per-type alloc counter from the closure body's exit
  ## heap (max-merged over all exit paths, exactly like the named-proc arm).

var currentClosureExitLiveRefs* {.threadvar.}: Table[string, seq[Z3AnyAst]]
  ## Phase 15 CR-1. The per-type live-ref list from the closure body's exit
  ## heap (union-merged over all exit paths so subsequent caller `new T`s
  ## are distinct from every closure-allocated ref too).

var currentClosureDidMutateHeap* {.threadvar.}: bool
  ## Phase 15 CR-1. True iff `applyClosureGround` merged at least one
  ## closure exit path back; the drain proc skips the update when false so
  ## a heap-write-free closure call is a no-op on the caller path's heaps.

var currentClosureExitPc* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 ADR-0012. Caller-LOCAL defect-survivor facts produced by a closure
  ## body descent (`applyClosureGround`): each exit path's `not overflow`/`not
  ## divByZero`/`not parseIntRaise` negations, guarded by that path's branch
  ## conditions (`implies(branchConds_i, neg)`). Mirrors the closure-exit-HEAP
  ## channel (`currentClosureExitHeaps`): written by `applyClosureGround`, drained
  ## by `drainPendingLowerEffects` onto the caller path's `defectSurvivorPc`, reset
  ## by `seedCallerHeapThreadvars` before each lower() and at `runSymexImpl` entry.
  ## CRUCIAL (anti-masking): this is NOT `currentClosureCallAxioms` — those drain
  ## into every trySolve globally; a GLOBAL `not overflow` would make the in-body
  ## OverflowDefect raise path UNSAT and mask the defect. These facts are local to
  ## the caller continuation only.

var currentClosureCallErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 C2b. Classified closure-call failures accumulated during lowering
  ## (`ceClosureUnknownCallee`, `ceInlineBudgetExceeded`) — `lower` has no
  ## WalkCtx to push onto `w.sawUnknown`/findings, so they ride this sink and are
  ## drained into the finding's errors (and force `sxUnknown`) at the SUT
  ## boundary. Reset at `runSymexImpl` entry. (The `unknownExnWarnings` idiom.)

proc degrade*(w: var WalkCtx; kind: SymexErrorKind; msg: string;
             sink = dsWalk; scope = walkSite();
             ub: set[UbKind] = {}; cap = ckNone): Degrade =
  ## RFC-0005 S1 (§2.2 "One funnel performs all three acts"). THE way a
  ## walk-level degrade site (one with `w: var WalkCtx` in scope) records a
  ## classified degrade and obtains its `Degrade` token:
  ##   1. records `SymexErrorInfo(kind, sevError, msg)` into the site's
  ##      existing sink (`sink`, default `dsWalk` = `w.walkDegradeErrors`) —
  ##      the drain-time derivation of `w.runTaint` reads it, so the RUN act
  ##      is performed by recording, never by a separate write;
  ##   2. returns `Degrade(path: pathTaint(classOf(kind)))` for the PATH act:
  ##      `forkPathTainted(p, pc, env, d)` per survivor, `taintInPlace(p, d)`
  ##      for a mutation-shaped site, or `discard` at a HALT site (a halted
  ##      path needs no carrier — its contribution is run-global).
  ## One kind mention drives both acts, so recording and classification
  ## cannot disagree. Minimum ceremony for a new degrade: tail-append the
  ## enum member, add its `classOf` arm (the compiler forces it), call this.
  ##
  ## `sink` preserves the pre-RFC sink each site already used (the sinks are
  ## drained separately and deduped per sink at verdict assembly, so moving a
  ## site between sinks would change `RawResult.errors`). The dual-store sinks
  ## write their threadvar fallback AND the live `WalkCtx` field, exactly as
  ## the hand-written sites did. No-`w` lowering sites use the sibling
  ## `queueDegrade` instead.
  ##
  ## RFC-0005 S6b: `dsUnknownExn` is the one sink that records at
  ## `sevWarning` (the `eeUnknownExnType` severity consumers already see);
  ## its run coordinate still counts through `taintsRun`'s carve-out.
  ##
  ## RFC-0005 S8: `scope` defaults to `dskWalkSite` (the record exists
  ## because a path reached this site). The two walk arms that reach a
  ## PARSE-time anchor pass it instead -- `isUnsupported`/`isUnsafeCast`
  ## (`siteAnchored(marker)`) and the missing-callee arm (`calleeKeyed`) --
  ## so the parse record and its reach record join on the same anchor.
  ## RFC-0016 K7a: a cap cut names its setting in the recorded message, so
  ## two caps sharing one error kind still tell the user which knob to raise.
  let shown = if cap == ckNone: msg else: msg & " (cap: " & capSetting(cap) & ")"
  let info = SymexErrorInfo(kind: kind, severity: severity(kind), msg: shown,
                            scope: scope)
  case sink
  of dsWalk:
    w.walkDegradeErrors.add info
  of dsHeapDepth:
    heapDepthErrors.add info            # threadvar: kept for compatibility
    w.heapDepthErrors.add info          # CR-9 Stage 5: LIVE WalkCtx field
  of dsNewFieldZero:
    newFieldZeroErrors.add info         # threadvar: fallback
    w.newFieldZeroErrors.add info       # CR-9-style LIVE WalkCtx field
  of dsClosure:
    currentClosureCallErrors.add info   # threadvar: fallback
    w.sinks.closureCallErrors.add info        # CR-9 Stage 5: LIVE WalkCtx field
  of dsUnknownExn:
    unknownExnWarnings.add info         # threadvar: fallback
    w.unknownExnWarnings.add info       # CR-9 Stage 5: LIVE WalkCtx field
  Degrade(path: pathTaint(classOf(kind)), ub: ub)

proc halted*(w: var WalkCtx; kind: SymexErrorKind; msg: string;
            scope = walkSite(); sink = dsWalk; cap = ckNone): Survivors
           {.discardable.} =
  ## RFC-0016 K7a. A HALT: records the classified degrade and returns no
  ## paths. A halted path needs no carrier (its contribution is run-global),
  ## so this holds the one sanctioned discard of a `Degrade` token; a halt
  ## site never writes `discard w.degrade(...)`. Discardable because a void
  ## routing proc has nothing to return the empty `Survivors` to.
  discard w.degrade(kind, msg, sink, scope, cap = cap)
  Survivors(live: @[])

func exact*(ps: seq[Path]): Survivors =
  ## RFC-0016 K7a. The walker's word that `ps` leave untainted; no token.
  Survivors(live: ps)

proc surviving*(ps: seq[Path]; d: Degrade): Survivors =
  ## RFC-0016 K7a. A fold of `forkPathTainted`: each of `ps` forks onto its
  ## own env carrying `d`'s path coordinate.
  result = Survivors(live: @[])
  for p in ps: result.live.add forkPathTainted(p, p.pc, p.env, d)

proc continued*(ps: seq[Path]; d: Degrade): Survivors =
  ## RFC-0016 K7a. A fold of `taintInPlace`: the degrade was recorded and
  ## `ps` go on, each now carrying `d`'s path coordinate.
  for p in ps: p.taintInPlace d
  Survivors(live: ps)

proc selfTainted*(ps: seq[Path]): Survivors =
  ## RFC-0016 K7c. `ps` leave carrying their own taint: each was forked with
  ## `forkPathTainted` onto a recorded degrade (the variant constructor's
  ## declined arms, which bind the result to a fresh value on the tainted
  ## path). The invariant is that EVERY path in `ps` is tainted; nothing
  ## untainted goes through here (that is `exact`). A debug build asserts it.
  for p in ps:
    assert p.taint != {}, "selfTainted: an untainted path"
  Survivors(live: ps)

proc carriedDegrade*(taint: Taint; ub: set[UbKind] = {}): Degrade =
  ## RFC-0005 S8cn. A closure body's start: taint its caller's path already
  ## holds and its call's pending decline, each recorded where it arose.
  Degrade(path: taint, ub: ub)

proc asDegrade*(q: PendingDegrade): Degrade =
  ## RFC-0005 S1. The lowering-sink half of the token discipline: the token of
  ## the lowering queue `takePending` took (each join already paired with a
  ## recorded `loweringDegradeErrors` entry, or with the closure sink's).
  ## Used by the drains that fold the queue onto the path it was queued for:
  ## `drainPendingLowerEffects`, `lowerLeafInExpr` and, before the walk,
  ## `initialWalkPath`. (Was `takeLoweringPendingDegrade`, which also took the
  ## queue; RFC-0016 INT-34 gave the queue one owner, `symval`.)
  Degrade(path: q.taint, ub: q.ub)

proc initialWalkPath*(pc: seq[Z3Bool]; env: Env): Path =
  ## RFC-0005 review R3 (leak fix), R4. THE constructor of a walk driver's
  ## initial path (`runSymexImpl`, `runConcolicCollectImpl`): the parameters'
  ## path condition and bindings, joined with what the parameter set-up
  ## queued before the walk began, so no driver can start a walk without
  ## that drain. Setting up the parameters allocates their symbols, and an
  ## allocation that declines (`allocDegrade`, a `proc`-typed parameter has
  ## no lambda the walker built) queues its taint with no drain of its own. That taint
  ## belongs to the initial path, the one the allocation was made for, and
  ## so to every path the walk derives from it. It must be drained here:
  ## the top-level `walk` sets a queue it finds on entry aside as its
  ## caller's (R2 SD1) and puts it back on return, and the driver has no
  ## drain after it, so the walk-end leak pin fired on a taint that had
  ## in fact reached every path.
  let initial = Path(pc: pc, env: env)
  if pendingIsEmpty(): initial
  else: forkPathTainted(initial, initial.pc, initial.env,
                        asDegrade(takePending()))

proc closureDegrade*(kind: SymexErrorKind; msg: string) =
  ## RFC-0005 S7 (§2.5 precondition for S9). THE way a closure / HOF site
  ## records a decline. These sites run inside `lower` (a closure call or a
  ## HOF is an EXPRESSION), so they cannot fork the consuming path; before S7
  ## they wrote only the closure sink, which the blanket closure veto read
  ## -- and nothing reached the PATH, so deleting the veto (S9, done) would
  ## have turned every hit through a stand-in value into a clean `sxSat`. One kind
  ## mention performs both acts, exactly as `queueDegrade` does for the
  ## lowering sink:
  ##   1. records the classified `sevError` into the closure sink (threadvar
  ##      fallback + the LIVE `WalkCtx.closureCallErrors` field, which the
  ##      drain-time run coordinate reads);
  ##   2. queues `pathTaint(classOf(kind))` (`queueDegrade`), which
  ##      `drainPendingLowerEffects` folds onto the path that consumes the
  ##      lowered value.
  ## A closure-sink decline outside `lower` would use `w.degrade(…,
  ## dsClosure)`; none exists (pinned by the S7 test).
  let info = SymexErrorInfo(kind: kind, severity: severity(kind), msg: msg,
                            scope: walkSite())   # RFC-0005 S8
  currentClosureCallErrors.add info   # threadvar: fallback
  syncClosureCallError(info)          # LIVE WalkCtx field (no-op outside a walk)
  queueDegrade(pathTaint(classOf(kind)))

proc stampLoweringPendingLeak*(w: var WalkCtx) =
  ## RFC-0005 S1 (§2.2 last paragraph) — the pending-taint LEAK PIN. Called
  ## once, right after the top-level `walk` returns, by BOTH walk drivers
  ## (`runSymexImpl`; `runConcolicCollectImpl` since S1c). The lowering queue
  ## must be empty there: every `queueDegrade` join is meant to be folded onto
  ## a path by `drainPendingLowerEffects`; a non-empty residue means a
  ## lowering degrade was recorded but its PATH taint landed nowhere (the
  ## "lost entirely" hazard `runtime_heap.nim`'s N42 note documents — a lost
  ## `{scSpurious}` would leave a havoc value on a clean path). The Invariant-7
  ## backstop is extended to it: stamp a classified `weInternalWalkerFault`
  ## (so telemetry sees the leak) and reset the residue so it cannot bleed
  ## into the next run on this thread.
  if not pendingIsEmpty():
    let leaked = takePending()
    w.halted(weInternalWalkerFault,
      "lowering pending taint " & $leaked.taint & " leaked at walk " &
      "end — a lowering degrade's path taint was never drained onto a path " &
      "(RFC-0005 S1 leak pin; weInternalWalkerFault)")

# ---- RFC-0005 S1: exported test hooks (H1 pattern) --------------------------
# `Path`/`WalkCtx`/`Degrade` are not exported past the runtime unit (they live
# in `walk_types.nim`, which `runtime.nim` does not re-export), so — exactly as
# `h1PathHasHeapFields`/`h1ForkIsolation` above — `tests/tsymex_rfc0005_s1_
# lattice.nim` drives the REAL templates/procs through these hooks and checks
# what they observed. They exist solely for that test and have no role in the
# walker; each saves and restores every threadvar sink it touches.


proc kindsOf*(errs: openArray[SymexErrorInfo]): seq[SymexErrorKind] =
  for e in errs: result.add e.kind

proc rfc0005S1CarrierProbe*(): Rfc0005S1CarrierProbe =
  ## Drives the S1 carrier + funnel on synthetic `Path`s and a scratch
  ## `WalkCtx`: `forkPath` propagation, `forkPathTainted`'s join (and that
  ## the parent is untouched), `degrade` into each of the four sinks (and
  ## that it writes no run coordinate), `taintInPlace`, the return-merge
  ## union, and the lowering funnel (`queueDegrade` → pending →
  ## `takePending`).
  let savedHeapDepth = heapDepthErrors
  let savedNewFieldZero = newFieldZeroErrors
  let savedClosure = currentClosureCallErrors
  let savedLowering = loweringDegradeErrors
  let savedPending = setAsidePending()
  heapDepthErrors = @[]
  newFieldZeroErrors = @[]
  currentClosureCallErrors = @[]
  loweringDegradeErrors = @[]
  var p {.used.} = Path()
  result.hasTaintField = compiles(p.taint)
  result.hasNoUncertainField = not compiles(p.uncertain)
  let spur: Taint = {scSpurious}
  let parent = Path(pc: @[], env: initOrderedTable[string, SymVal](),
                    taint: spur)
  result.forkPathPropagated = forkPath(parent, parent.pc, parent.env).taint
  var w: WalkCtx
  let d = w.degrade(feUnsupportedOp, "rfc0005 S1 probe (walk sink)")
  result.tokenPath = d.path
  result.walkSinkKinds = kindsOf(w.walkDegradeErrors)
  for e in w.walkDegradeErrors: result.walkSinkSeverities.add e.severity
  let child = forkPathTainted(parent, parent.pc, parent.env, d)
  result.forkTaintedJoined = child.taint
  result.forkTaintedParentUntouched = parent.taint
  w.halted(heDepthExhausted, "rfc0005 S1 probe (heap depth)", sink = dsHeapDepth)
  let dz = w.degrade(heNewFieldZeroUnsupported, "rfc0005 S1 probe (new zero)",
                     dsNewFieldZero)
  w.halted(ceInlineBudgetExceeded, "rfc0005 S1 probe (closure)", sink = dsClosure)
  result.heapDepthSinkKinds = kindsOf(w.heapDepthErrors)
  result.newFieldZeroSinkKinds = kindsOf(w.newFieldZeroErrors)
  result.closureSinkKinds = kindsOf(w.sinks.closureCallErrors)
  result.closureThreadvarKinds = kindsOf(currentClosureCallErrors)
  result.runTaintBeforeDrain = w.runTaint
  let inPlace = Path(pc: @[], env: initOrderedTable[string, SymVal](),
                     taint: spur)
  taintInPlace(inPlace, dz)
  result.taintInPlaceJoined = inPlace.taint
  let cleanCallee = Path(pc: @[], env: initOrderedTable[string, SymVal]())
  result.returnMergeJoined =
    forkPathMerged(cleanCallee, cleanCallee.pc, cleanCallee.env, parent).taint
  result.returnMergeCleanStaysClean =
    forkPathMerged(cleanCallee, cleanCallee.pc, cleanCallee.env, cleanCallee).taint
  queueDegrade(seUnsupportedStringOp, "rfc0005 S1 probe (lowering)")
  result.lowerPendingAfter = peekPending().taint
  result.loweringSinkKinds = kindsOf(loweringDegradeErrors)
  result.lowerDrainedPath = asDegrade(takePending()).path
  result.lowerPendingAfterDrain = peekPending().taint
  heapDepthErrors = savedHeapDepth
  newFieldZeroErrors = savedNewFieldZero
  currentClosureCallErrors = savedClosure
  # RFC-0016 W1-d3: the same carriers for `undefined`.
  let ubParent = Path(pc: @[], env: initOrderedTable[string, SymVal](),
                      taint: spur, undefined: {UbKind(ubIndeterminateRead)})
  result.undefForkPropagated =
    forkPath(ubParent, ubParent.pc, ubParent.env).undefined
  let dub = w.degrade(feGlobalHavoc, "rfc0016 W1-d3 probe (undefined)",
                      ub = {UbKind(ubSignedOverflow)})
  result.undefTokenFromKind = dub.ub
  result.undefForkTaintedJoined =
    forkPathTainted(ubParent, ubParent.pc, ubParent.env, dub).undefined
  result.undefForkTaintedParentUntouched = ubParent.undefined
  let ubInPlace = Path(pc: @[], env: initOrderedTable[string, SymVal](),
                       taint: spur, undefined: {UbKind(ubUnsignedDivZero)})
  taintInPlace(ubInPlace, dub)
  result.undefInPlaceJoined = ubInPlace.undefined
  let ubCallee = Path(pc: @[], env: initOrderedTable[string, SymVal](),
                      undefined: {UbKind(ubIntMinModMinusOne)})
  result.undefReturnMergeJoined =
    forkPathMerged(ubCallee, ubCallee.pc, ubCallee.env, ubParent).undefined
  result.undefReturnMergeCleanStaysClean =
    forkPathMerged(cleanCallee, cleanCallee.pc, cleanCallee.env,
                   cleanCallee).undefined
  queueDegrade(feGlobalHavoc, "rfc0016 W1-d3 probe (lowering undefined)",
               {UbKind(ubIndeterminateRead)})
  result.undefLowerDrained = asDegrade(takePending()).ub
  result.undefLowerPendingAfterDrain = peekPending().ub
  loweringDegradeErrors = savedLowering
  restorePending(savedPending)

proc rfc0005S1LeakPinProbe*(): Rfc0005S1LeakPinProbe =
  ## Drives `stampLoweringPendingLeak` twice on a scratch `WalkCtx`: once with
  ## a clean pending taint (must stamp nothing) and once with a residue left
  ## by a `queueDegrade` that no `drainPendingLowerEffects` consumed (must
  ## stamp one `weInternalWalkerFault` sevError and reset the residue).
  let savedLowering = loweringDegradeErrors
  let savedPending = setAsidePending()
  loweringDegradeErrors = @[]
  var clean: WalkCtx
  stampLoweringPendingLeak(clean)
  result.cleanStampedKinds = kindsOf(clean.walkDegradeErrors)
  var leaky: WalkCtx
  queueDegrade(seUnsupportedStringOp, "rfc0005 S1 leak probe")
  stampLoweringPendingLeak(leaky)
  result.leakStampedKinds = kindsOf(leaky.walkDegradeErrors)
  for e in leaky.walkDegradeErrors: result.leakStampedSeverities.add e.severity
  result.pendingAfterStamp = peekPending().taint
  loweringDegradeErrors = savedLowering
  restorePending(savedPending)


proc takePendingLowerEffects*(w: var WalkCtx): PendingLowerEffects =
  ## RFC-0005 S7. See `PendingLowerEffects`. The WalkCtx fields are the LIVE
  ## store during a walk (the raise sinks' only store; the closure threadvars
  ## mirror their own), so they are what is saved; every store is cleared. The caller-heap seed is saved, not
  ## cleared -- the descent reads it.
  result = PendingLowerEffects(
    queue: setAsidePending(),
    parseInt: w.sinks.parseIntRaiseConds, divByZero: w.sinks.divByZeroConds,
    overflow: w.sinks.overflowConds, strIndexOob: w.sinks.strIndexOobConds,
    seqOob: w.sinks.seqOobConds, convBound: w.sinks.convFloatToIntBoundConds,
    rangeDefect: w.sinks.rangeDefectConds, arithTrap: w.sinks.arithTrapConds,
    uninitRead: w.sinks.uninitReadConds,
    regexRaise: w.sinks.regexRaiseMsgs, raiseOrder: w.sinks.raiseOrder,
    closureRaises: w.closureRaises, closureVarOuts: w.closureVarOuts,
    exitPc: currentClosureExitPc, didMutate: w.closureDidMutateHeap,
    exitHeaps: w.closureExitHeaps, exitAlloc: w.closureExitAllocCounters,
    exitLiveRefs: w.closureExitLiveRefs, callerHeaps: w.callerHeaps,
    callerHeapDepth: w.callerHeapDepth, callerAlloc: w.callerAllocCounters,
    callerLiveRefs: w.callerLiveRefs,
    envWrites: closureEnvWrites, readNames: loweringReadNames)
  closureEnvWrites = @[]
  loweringReadNames = @[]
  w.sinks.parseIntRaiseConds = @[]
  w.sinks.divByZeroConds = @[]
  w.sinks.overflowConds = @[]
  w.sinks.strIndexOobConds = @[]
  w.sinks.seqOobConds = @[]
  w.sinks.convFloatToIntBoundConds = @[]
  w.sinks.rangeDefectConds = @[]
  w.sinks.arithTrapConds = @[]
  w.sinks.uninitReadConds = @[]   # RFC-0005 S8bv
  w.sinks.regexRaiseMsgs = @[]
  w.sinks.raiseOrder = @[]
  w.closureRaises = @[]
  w.closureVarOuts = @[]        ## RFC-0005 S8bh
  currentClosureExitPc = @[]
  w.closureDidMutateHeap = false; currentClosureDidMutateHeap = false

proc restorePendingLowerEffects*(w: var WalkCtx; s: PendingLowerEffects) =
  ## RFC-0005 S7. Inverse of `takePendingLowerEffects`: reinstates the calling
  ## expression's pending effects in every store, discarding whatever the
  ## descent's own statement arms left behind (they drained their own).
  restorePending(s.queue)
  w.sinks.parseIntRaiseConds = s.parseInt
  w.sinks.divByZeroConds = s.divByZero
  w.sinks.overflowConds = s.overflow
  w.sinks.strIndexOobConds = s.strIndexOob
  w.sinks.seqOobConds = s.seqOob
  w.sinks.convFloatToIntBoundConds = s.convBound
  w.sinks.rangeDefectConds = s.rangeDefect
  w.sinks.arithTrapConds = s.arithTrap
  w.sinks.uninitReadConds = s.uninitRead
  w.sinks.regexRaiseMsgs = s.regexRaise
  w.sinks.raiseOrder = s.raiseOrder
  w.closureRaises = s.closureRaises
  w.closureVarOuts = s.closureVarOuts   ## RFC-0005 S8bh
  currentClosureExitPc = s.exitPc
  w.closureDidMutateHeap = s.didMutate; currentClosureDidMutateHeap = s.didMutate
  w.closureExitHeaps = s.exitHeaps; currentClosureExitHeaps = s.exitHeaps
  w.closureExitAllocCounters = s.exitAlloc
  currentClosureExitAllocCounters = s.exitAlloc
  w.closureExitLiveRefs = s.exitLiveRefs; currentClosureExitLiveRefs = s.exitLiveRefs
  w.callerHeaps = s.callerHeaps; currentCallerHeaps = s.callerHeaps
  w.callerHeapDepth = s.callerHeapDepth; currentCallerHeapDepth = s.callerHeapDepth
  w.callerAllocCounters = s.callerAlloc; currentCallerAllocCounters = s.callerAlloc
  w.callerLiveRefs = s.callerLiveRefs; currentCallerLiveRefs = s.callerLiveRefs
  closureEnvWrites = s.envWrites       ## RFC-0005 S8as
  loweringReadNames = s.readNames      ## RFC-0005 S8as


func globalsTable*(gs: seq[IRGlobal]): Table[string, IRGlobal] =
  ## RFC-0005 S8as.
  for g in gs: result[g.name] = g


proc setInFlightThreadvars*(inFlight: Option[ExnRecord]) {.inline.} =
  ## Phase 15 E8. Mirror the structural `w.frame.inFlightExn` into the
  ## lower-time threadvars (`currentInFlightTypeId` / `currentInFlightMsg`) that
  ## the no-arg `getCurrentException()` / `getCurrentExceptionMsg()` intrinsics
  ## read in `lower` (a pure Env→SymVal function with no WalkCtx access). Called
  ## at every site that sets/restores `w.frame.inFlightExn` (handler-body entry
  ## and the finally raised-exit walk), keeping the two views in lockstep.
  if inFlight.isSome:
    currentInFlightTypeId = some(inFlight.get.typeId)
    currentInFlightMsg = inFlight.get.msg
  else:
    currentInFlightTypeId = none(string)
    currentInFlightMsg = none(string)

proc currentFrameId*(): int =
  ## RFC-0005 S9 (a `lowerHooks` field, read by `runtime_closures.nim`). The live walk's
  ## `CallFrameCtx.frameId`; -1 outside a walk (a probe), which no walk frame
  ## ever equals.
  if currentWalkCtxPtr == nil: -1
  else: cast[ptr WalkCtx](currentWalkCtxPtr)[].frame.frameId

proc registerCapCell*(local: string; v: SymVal) =
  ## RFC-0005 S8ax (a `lowerHooks` field, read by `runtime_closures.nim`). A closure built
  ## in the current frame captures the local `local` by reference: from now
  ## on the frame keeps it in its env cell too (`capCellName`, bound to `v`,
  ## the local's value, through `closureEnvWrites`). Outside a walk (a
  ## probe) nothing is kept, and an application elsewhere declines.
  if currentWalkCtxPtr == nil: return
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  let cell = capCellName(wp[].frame.frameId, local)
  if (local: local, cell: cell) notin wp[].frame.capCells:
    wp[].frame.capCells.add (local: local, cell: cell)
  closureEnvWrites.add (cell, v)

proc varFormalPtrRisk*(w: WalkCtx; formals: seq[IRParam]; args: seq[IRExpr];
                      codes: seq[int]):
    tuple[risk: seq[IRParam]; safe: seq[string]] =
  ## RFC-0005 S8bn (item 3). The call's `var` formals split by whether a
  ## `ptr` of unknown origin may address their actual (`CallFrame.
  ## ptrRiskFormals`): an actual coded 1 (`IRStmt.cVarPtrSafe`) may not, nor
  ## one coded 2 (the caller's own formal passed on) that is safe in the
  ## caller's frame (the top of `callStack`; at the SUT's own frame it is a
  ## `var` parameter of the SUT, which may be one). Any other actual, and
  ## every formal of a call carrying no codes, may.
  for i, f in formals:
    if not f.isVar: continue
    let c = if i < codes.len: codes[i] else: 0
    var safe = c == 1
    if c == 2 and i < args.len and args[i].kind == iekVar and
       w.callStack.len > 0:
      safe = args[i].vname in w.callStack[^1].ptrSafeFormals
    if safe: result.safe.add f.name
    else: result.risk.add f

# RFC-0005 review R5: the hooks `exits.nim`'s group walks reach an entry's
# path and handler depth through.
proc exitPath*(p: var Path): var Path = p
proc exitPath*(e: var HeldPath): var Path = e.path
proc exitPath*(e: var HeldRaise): var Path = e.path
proc exitPath*(e: var HeldJump): var Path = e.path
proc exitPath*(e: var EscapedRaise): var Path = e.path
func depthOf*(e: HeldPath): int = e.depth
func depthOf*(e: HeldRaise): int = e.depth
func depthOf*(e: HeldJump): int = e.depth

proc initLoopFrame*(clock: ExitClock; hsDepth = 0;
                   label = ""): LoopFrame {.inline.} =
  ## RFC-0016 INT-35 (R6-04). The one way to make a loop (or labelled block)
  ## frame: its exit group is bound to the walk's clock here, so no frame can
  ## carry a zero-valued group that fails only at its first `park`.
  LoopFrame(exits: clock.newExits(LoopExits), hsDepth: hsDepth, label: label)

proc initCallFrame*(clock: ExitClock; callee = ""; retSym = default(SymVal);
                   retName = ""; retTy: IRType = nil;
                   ptrRiskFormals: seq[IRParam] = @[];
                   ptrSafeFormals: seq[string] = @[];
                   sp: uint = 0): CallFrame {.inline.} =
  ## RFC-0016 INT-35 (R6-04). The one way to make an inline-call frame, its
  ## exit group bound to the walk's clock.
  CallFrame(exits: clock.newExits(CallExits), callee: callee, retSym: retSym,
            retName: retName, retTy: retTy, ptrRiskFormals: ptrRiskFormals,
            ptrSafeFormals: ptrSafeFormals, sp: sp)

proc initCallFrameCtx*(clock: ExitClock; frameId = 0): CallFrameCtx {.inline.} =
  ## RFC-0016 INT-35 (R6-04). The one way to make a call descent's exception
  ## context, its exit group bound to the walk's clock.
  CallFrameCtx(frameId: frameId, exits: clock.newExits(FrameExits))

proc pushFrame*(w: var WalkCtx) {.inline.} =
  ## Phase 15 E1. Save the current call frame's exception context and install a
  ## fresh, empty one for the callee being descended into. The handler stack is
  ## per-frame: a `try` opened inside the callee is NOT visible to the caller
  ## after the callee returns (popFrame restores the caller's frame verbatim).
  ## Structural in E1 (handlerStack/inFlightExn are always empty until E2b+);
  ## wired now so E3/E5 need not re-audit the call-descent arms.
  w.frameStack.add w.frame
  inc w.frameIdCounter                        ## RFC-0005 S9
  w.frame = initCallFrameCtx(w.exitClock, frameId = w.frameIdCounter)

proc popFrame*(w: var WalkCtx) {.inline.} =
  ## Phase 15 E1. Restore the caller's call frame saved by `pushFrame`.
  if w.frameStack.len > 0:
    w.frame = w.frameStack[^1]
    w.frameStack.setLen(w.frameStack.len - 1)

proc shouldStop*(w: WalkCtx): bool {.inline.} =
  ## Phase 16 ADR-0012. Halt once the finding that ANSWERS THE TARGET exists.
  ## stkLabel: only an sxSat answers "is the label reachable?" — an incidental
  ## sxRaised (defect found on a sibling path) must NOT stop exploration, or the
  ## label's sxSat is never computed. All raise-flavoured targets: an sxRaised IS
  ## the terminal answer (unchanged).
  if walkWorkExhausted: return true   ## RFC-0016 K7: out of solver work
  if walkStalled: return true         ## RFC-0016 INT-57: the stall backstop
  if tailWorkExhausted: return true   ## RFC-0016 W3-z R9: the tail's budget
  for r in w.found:
    if r.status == sxSat: return true
    if r.status == sxRaised and w.target.kind != stkLabel: return true
  false

const defaultConcreteBranchRLimit* = 20_000_000'u
  ## R7: the genuine, non-zero default `concreteBranchOutcome` falls back to
  ## when the caller's `settings.budget.queryRLimit` is `0` (i.e. expressed
  ## no preference — the codebase-wide "0 = unbounded" convention every
  ## other `ResourceBudget` field also uses, so this substitution happens
  ## only at that one sentinel value, never silently overriding a caller who
  ## explicitly asked for a smaller — or larger — budget).
  ##
  ## `trySolve` is allowed to default to unbounded (`0`) because it runs
  ## inside a user-invoked symex query: the user chose to run a solver and
  ## can set a budget if they want one. `concreteBranchOutcome` has no such
  ## user in the loop — it runs on the FUZZ LOOP's hot path, synchronously,
  ## on the main thread, on every if-decision of every concolic collection,
  ## with no watchdog. A hang there wedges the whole campaign silently
  ## (the dt-bounded.sh header documents a real 24+ minute mixed-theory
  ## hang from exactly this class of unbounded query). That asymmetry is
  ## why this site needs a real default where `trySolve` doesn't.
  ##
  ## rlimit (a deterministic Z3 logical-step count), not G2's wall-clock
  ## `timeout`: this call sits in the general-walk layer `trySolve`
  ## occupies, not G2's bounded-relaxation-attempt loop, and — unlike a G2
  ## flip-solve, whose only output is a throwaway candidate Track E
  ## re-verifies concretely regardless — this call's outcome directly
  ## shapes which arm `walkIfFollowConcrete` follows, i.e. the search
  ## trajectory itself. A wall-clock timeout is reproducible in the
  ## SAT/UNSAT case (Z3 always finds those given enough time) but the
  ## TIMING of a timeout is machine/load-dependent, so the same seed could
  ## resolve a branch on a fast/idle machine and degrade to `ambiguousBranches`
  ## on a slow/loaded one — different collected constraints, different
  ## corpus growth, from the identical campaign. `rlimit` counts logical
  ## steps, not wall-clock time, so it reproduces identically across
  ## machines for a fixed Z3 build (the same property `trySolve` already
  ## relies on — see `docs/symex/RFC-unsat-caching.md`'s "Wall-clock
  ## timeouts aren't [deterministic]... Z3 exposes rlimit"). A fuzzer whose
  ## intermediate search steps depend on machine speed is a much bigger
  ## reproducibility problem than a throwaway flip-solve candidate is, so
  ## rlimit is the right instrument here even though G2 chose timeout for
  ## its own (differently-shaped) problem.
  ##
  ## Value: `20_000_000` is not an arbitrary round number — it's the one
  ## rlimit magnitude this codebase has already validated empirically.
  ## `tests/tsymex_r4_strip.nim` bisected a real adversarial query (nested
  ## `strip` idempotence decomposition) that ran UNBOUNDED for measured
  ## 3+ hours, and confirmed `queryRLimit: 20_000_000` bounds it to a fast,
  ## deterministic `sxUnknown`. `concreteBranchOutcome`'s own queries are
  ## far simpler by construction (a fully concrete-pinned comparison, no
  ## free variables) and should resolve in a tiny fraction of that budget
  ## under normal conditions — so this ceiling gives enormous headroom
  ## against a false/premature `none(bool)` degrade on ordinary campaigns,
  ## while still being a genuine, finite, deterministic backstop against
  ## the exact class of mixed-theory divergence dt-bounded.sh exists to
  ## catch. Reusing this proven value (vs. inventing an untested one) means
  ## its termination behavior is already known-good on this Z3 build,
  ## rather than a fresh guess this fix would be the first to rely on.
  ##
  ## RFC-0005 S1c: the same asymmetry now holds INSIDE `trySolve`'s own
  ## layer. A tainted target-hit path (`solveTargetHit`) was never solved
  ## before S1c, and its pc can carry a degraded lowering's mixed-theory
  ## residue (N36's `iekStrInOptionRegion` shape spun Z3 unbounded) -- the
  ## user never chose to run THAT query, so `taintedSolveRLimit` falls back
  ## to this same ceiling. Declared here, ahead of `solveTargetHit`, for
  ## that reason (Nim declaration order).

func taintedSolveRLimit*(settings: SymexSettings): uint =
  ## RFC-0005 S1c. The Z3 `rlimit` a TAINTED target-hit path is solved under
  ## (`solveTargetHit`): the caller's explicit `queryRLimit` when set (a
  ## caller's budget always wins), else `defaultConcreteBranchRLimit` -- the
  ## same validated finite backstop, for the same mixed-theory divergence
  ## class, that R7's `concreteBranchRLimit` applies. Pure, so the "never
  ## unbounded under default settings" contract is unit-testable without
  ## provoking a real divergence (`tsymex_rfc0005_s1c_verdict`). RFC-0005
  ## S8bu: `queryRLimit`'s own default (no longer `0`) is not the caller's.
  let q = settings.budget.queryRLimit
  if q != 0 and q != ResourceBudget().queryRLimit: q
  else: defaultConcreteBranchRLimit

func budgetOutFloor*(settings: SymexSettings): int =
  ## RFC-0005 S8y. What a target-hit solve spends when it runs out: the
  ## smaller of its `queryRLimit` and `seqQueryRLimit` (`checkCapped`'s
  ## model search spends exactly the smaller one before giving up), 0 when
  ## both are unbounded.
  let q = settings.budget.queryRLimit
  let sq = settings.budget.seqQueryRLimit
  if q == 0: int(sq)
  elif sq == 0: int(q)
  else: int(min(q, sq))

proc groundedLike*(sym, val: SymVal): SymVal =
  ## RFC-0005 S8bl (item 2). `sym` with each scalar leaf replaced by `val`'s
  ## when Z3's rewriter folds that to a literal of the same kind (an Int or
  ## 64-bit numeral, a string literal), through tuples; `sym`'s own leaf
  ## otherwise. Sound wherever the path asserts `sym == val`.
  result = sym
  if sym.kind != val.kind: return
  case sym.kind
  of svInt:
    let ctx = sym.zi.ctx
    let f = ctx.checkErr Z3_simplify(ctx.raw, val.zi.raw)
    if Z3_is_numeral_ast(ctx.raw, f): result.zi = wrap[Z3Int](ctx, f)
  of svBV64:
    let ctx = sym.bv64.ctx
    let f = ctx.checkErr Z3_simplify(ctx.raw, val.bv64.raw)
    if Z3_is_numeral_ast(ctx.raw, f): result.bv64 = wrap[Z3BitVec[64]](ctx, f)
  of svString:
    let ctx = sym.str.ctx
    let f = ctx.checkErr Z3_simplify(ctx.raw, val.str.raw)
    if Z3_is_string(ctx.raw, f): result.str = wrap[Z3String](ctx, f)
  of svTuple:
    if sym.fields.len != val.fields.len: return
    for i in 0 ..< sym.fields.len:
      result.fields[i] = groundedLike(sym.fields[i], val.fields[i])
  else: discard

func assumedStringPin*(e: IRExpr): tuple[name, lit: string] =
  ## RFC-0005 S8bl (item 2). `(s, lit)` for an assumed `s == lit` (or
  ## `lit == s`) of a variable and a string literal; `("", "")` otherwise.
  if e == nil or e.kind != iekBinop or e.bop != bEq: return
  if e.lhs.kind == iekVar and e.rhs.kind == iekStrLit:
    return (e.lhs.vname, e.rhs.sval)
  if e.rhs.kind == iekVar and e.lhs.kind == iekStrLit:
    return (e.rhs.vname, e.lhs.sval)


func classifyTargetSolve*(st: SymexStatusKind; spent, floor: int):
    TargetSolveCost =
  ## RFC-0005 S8ag. `floor` is `budgetOutFloor`; 0 (unbounded) is never
  ## costly. An UNSAT is never costly here: it is no candidate, and its
  ## depth bounds nothing.
  if floor <= 0: tscCheap
  elif st == sxUnknown and spent >= floor: tscBudgetOut
  elif st == sxSat and spent >= floor div 2: tscSlowSat
  else: tscCheap

func atLeastAsDeep*(p: Path; depth: openArray[tuple[loop: int, iters: int]]):
    bool =
  ## RFC-0005 S8y. `p` has entered the body of each loop in `depth` at least
  ## as many times as `depth` records (and `depth` names a loop at all).
  if depth.len == 0: return false
  for (loop, n) in depth:
    var ok = false
    for e in p.loopIters:
      if e.loop == loop and e.iters >= n:
        ok = true
        break
    if not ok: return false
  true

proc solveTargetHit*(w: var WalkCtx; p: Path):
    tuple[status: SymexStatusKind, witness: RawWitness,
          candidateErrs: seq[SymexErrorInfo], undefWhy: string] =
  ## RFC-0005 S1c (§2.3). THE solve for a path that reached the search target
  ## -- `isTargetLabel`'s label hit and `routeRaise`'s SUT-boundary raise --
  ## run on EVERY such path, tainted or not. Before S1c both sites refused to
  ## solve a tainted path; an unsolved path that reaches the target is itself
  ## an omission (§0.1), so the refusal forced a kindless ⊤ run mark and made
  ## rule 5 (`sxUnsat` on `scIncomplete notin runTaint`) unshippable. Now the
  ## only unsolved outcome is a solver unknown, which the caller records as
  ## `beSolverUndef` (classified, so it derives the run coordinate).
  ##
  ## Witness extraction may record `extractionErrors` (sevError/sevHint), and
  ## that sink is surfaced on the WINNER branch only. A candidate is not a
  ## winner, so its extraction errors are moved off the shared sink into
  ## `candidateErrs` (they ride the candidate's own `RawResult.errors`) --
  ## otherwise a clean witness found later would inherit diagnostics about a
  ## model it never used.
  ##
  ## A TAINTED path's query is solved under `taintedSolveRLimit` -- never
  ## unbounded. Its pc carries whatever a degraded lowering left behind
  ## (the N36 `iekStrInOptionRegion` BV-bound decline's residue spins Z3's
  ## `check` forever under the default `queryRLimit = 0`), and before S1c
  ## that query was never issued, so an unbounded solve here would be a NEW
  ## non-termination, not a pre-existing one. The bound's `zsUnknown` is the
  ## honest `beSolverUndef` the caller records. A clean path's query is
  ## exactly the pre-S1c one and keeps the caller's budget unchanged.
  ##
  ## RFC-0005 S8y. A tainted hit that runs out of budget records its loop
  ## depths (`Path.loopIters`) in `w.budgetOutDepths`, and a later tainted
  ## hit at least as deep in every one of those loops is NOT solved: it
  ## comes back `sxUnknown`, which the caller records as the same
  ## `beSolverUndef` a solver unknown is, so it voids `sxUnsat` exactly as
  ## spending the budget would have. The hits are a walk's deeper unrolls of
  ## one loop, whose queries only grow: `tsymex_r6_n36_raise_degrade`'s
  ## pair loop spent its whole 20M budget on each five-iteration hit, twice
  ## per test, the break on a fifth empty key and the unroll-bound survivor
  ## (and on a four-iteration one too once the walk's context held S8r's or
  ## S8v's extra terms). What is given up is a candidate, never a winner (a
  ## tainted SAT only feeds S10's replay), and a CLEAN hit is always
  ## solved: its SAT would be a finding.
  ##
  ## RFC-0005 S8ag. A tainted hit that finds a model only after spending
  ## half its budget (`slowSat`: step 1 ran out, step 3 found one) records
  ## its depths the same way. With the one-character `str.indexof` split
  ## the pair loop's exit hits find models instead of running out, so the
  ## costly hits are SATs, and the budget-out bound alone no longer
  ## stopped a walk solving every deeper one.
  let isCandidate = scSpurious in p.taint
  let exStart = extractionErrors.len
  let exLiveStart = w.sinks.extractionErrors.len
  var solveSettings = w.settings
  if p.taint != {}:
    solveSettings.budget.queryRLimit = taintedSolveRLimit(w.settings)
    for depth in w.budgetOutDepths:
      if p.atLeastAsDeep(depth):
        inc symexTargetSolveStats.declined
        var iters: seq[int]
        for e in depth: iters.add e.iters
        return (status: sxUnknown, witness: RawWitness(), candidateErrs: @[],
                undefWhy: "not solved (RFC-0005 S8y): an earlier tainted " &
                  "path reached the target after " & $iters &
                  " loop iterations and ran out of its solver budget (or, " &
                  "RFC-0005 S8ag, found a model only after half of it), " &
                  "and this tainted path is at least as deep in each of " &
                  "those loops")
  # RFC-0005 S8y: what the solve spent. RFC-0005 S8bp: every search it
  # runs is in a context of its own (`checkCapped`), so that is what
  # `ownContextUnits` grew by (S8y read the walk context's counter, and
  # S8bm added step 1's own context to it).
  let spentBefore = ownContextUnits
  let (st, wit, why) = trySolve(w.z3, p, w.params, solveSettings, w.initialEnv)
  let spent = ownContextUnits - spentBefore
  symexTargetSolveStats.units += spent
  case classifyTargetSolve(st, spent, budgetOutFloor(solveSettings))
  of tscBudgetOut:
    inc symexTargetSolveStats.budgetOut
    if p.taint != {} and p.loopIters.len > 0:
      w.budgetOutDepths.add p.loopIters
  of tscSlowSat:
    # RFC-0005 S8ag: a tainted SAT found only after half the budget --
    # `checkCapped`'s capped step 1 ran out and the uncapped step 3 found
    # a model -- spent 10M of a 20M budget and more, and is no budget-out.
    # Before, nothing bounded how many such hits a walk solved: S8y's
    # decline took only budget-outs. It records its depths the same way,
    # so a later tainted hit at least as deep is declined, classified, and
    # voids `sxUnsat` as the solve would have; what is given up is a
    # further candidate for S10's replay beside the one this hit found.
    # A clean hit's slow SAT bounds nothing: its SAT is a finding.
    if p.taint != {}:
      inc symexTargetSolveStats.slowSat
      if p.loopIters.len > 0:
        w.budgetOutDepths.add p.loopIters
  of tscCheap: discard
  var errs: seq[SymexErrorInfo]
  w.hitExtraction.setLen(0)
  if isCandidate:
    for i in exLiveStart ..< w.sinks.extractionErrors.len:
      errs.add w.sinks.extractionErrors[i]
    extractionErrors.setLen(exStart)
    w.sinks.extractionErrors.setLen(exLiveStart)
  else:
    # RFC-0016 INT-32 (R1-33): a clean hit's own extraction failures stay on
    # the sink (the run reports them) and are ALSO this hit's, so a winner is
    # lossy by its own witness only, never by a sibling hit's.
    for i in exLiveStart ..< w.sinks.extractionErrors.len:
      if w.sinks.extractionErrors[i].kind == feExtractionFailed:
        w.hitExtraction.add w.sinks.extractionErrors[i]
  (status: st, witness: wit, candidateErrs: errs, undefWhy: why)

proc admitSolvedHit*(w: var WalkCtx; r: RawResult) =
  ## RFC-0005 S1c (§2.3 "Candidate lifecycle"). Files a SOLVED finding by the
  ## taint of the path that produced it (`r.soundness.pathTaint`, recorded at the hit):
  ## a clean one into `w.found` (a winner; may halt the walk via
  ## `shouldStop`), an `scSpurious`-tainted one into `w.candidates` (never
  ## halts, never wins by itself -- only S10's replay can promote it; it
  ## still blocks `sxUnsat`, `decideVerdict` rule 4). `path.scIncomplete`
  ## alone is inert (§2.1): an omission cannot invent a model.
  if scSpurious in r.soundness.pathTaint:
    w.candidates.add r
  else:
    var r = r
    r.witnessExtraction = w.hitExtraction   # RFC-0016 INT-32
    w.found.add r

func toCandidate*(r: RawResult): SatCandidate =
  ## RFC-0005 S10. Re-types a pooled candidate for the `runSymex` boundary
  ## (`RawResult.candidates`): the witness moves into the private `input`
  ## field, so past this point the model is not spellable as a `sxSat`.
  case r.status
  of sxSat:
    SatCandidate(status: sxSat, pathTaint: r.soundness.pathTaint, errors: r.errors,
                 witnessUndefined: r.soundness.witnessUndefined,
                 witnessUndefinedViaOnly: r.undefinedViaOnly,   # W3-z R7
                 witnessUnsafe: r.soundness.witnessUnsafe,
                 nilDerefOnPath: r.nilDerefOnPath, input: r.witness)
  of sxRaised:
    SatCandidate(status: sxRaised, pathTaint: r.soundness.pathTaint, errors: r.errors,
                 witnessUndefined: r.soundness.witnessUndefined,
                 witnessUndefinedViaOnly: r.undefinedViaOnly,   # W3-z R7
                 witnessUnsafe: r.soundness.witnessUnsafe,
                 nilDerefOnPath: r.nilDerefOnPath,
                 raisedTypeId: r.raisedTypeId, isDefect: r.isDefect,
                 raisedMsg: r.raisedMsg, input: r.raisedWitness)
  of sxUnsat, sxUnknown:
    # `admitSolvedHit` is only ever handed a solved SAT / raise.
    raiseAssert "RFC-0005 S10: a candidate is always a solved sxSat/sxRaised"

func toCandidates*(pool: openArray[RawResult]): seq[SatCandidate] =
  for r in pool: result.add toCandidate(r)


func decideVerdict*(found, candidates: openArray[RawResult]; runTaint: Taint;
                    reachUnknown: bool): VerdictDecision =
  ## RFC-0005 §2.3 -- THE verdict rule, an ordered decision procedure with
  ## disjoint guards (first matching rule wins). Pure: `runSymexImpl` feeds it
  ## the walk's pools and the drained run coordinate, and a test can drive
  ## every rule directly with any `Taint` -- including ones no kind produces
  ## until S4-S6 reclassify a funnel (all-⊤ makes rule 4 indistinguishable
  ## from rule 5 through `symexFind` today).
  ##
  ##   1. a clean `sxSat` in `found` -> `sxSat` (first in discovery order)
  ##   2. a clean `sxRaised` in `found` -> `sxRaised` (a reachable raise is an
  ##      existence claim: it obeys the SAT rule verbatim)
  ##   3. a candidate whose replay returns `roConfirmed` -> `sxSat`/`sxRaised`
  ##      -- RFC-0005 S10's rule: replay is macro code (§4.2 plumbing), so
  ##      it cannot sit in this runtime function; S10 applies it to
  ##      `RawResult.candidates` on the `sxUnknown` this procedure returns
  ##      under rule 4 (RFC-0016 W4 perf: the replays run inside the run,
  ##      through the macro's `CandidateReplay`; the settle follows it).
  ##   4. any solved SAT anywhere -- a candidate, or a `found` entry the rules
  ##      above did not accept -- terminally blocks `sxUnsat`: the enlarged
  ##      program DOES reach the target. -> `sxUnknown`
  ##   5. nothing solved SAT and `scIncomplete notin runTaint` -> `sxUnsat`
  ##   6. otherwise -> `sxUnknown`
  ##
  ## `reachUnknown` (RFC-0005 S9, §2.5 point 4): some admitted decline has
  ## no anchor (`dskUnplaced`), so whether it was reached -- and so whether a
  ## clean finding or an empty pool can be trusted -- is undecidable. It
  ## suppresses rules 1-2 and blocks rule 5. S9 deleted the two blanket
  ## vetoes (`capForcedUnknown`/`closureForcedUnknown`) this parameter used
  ## to carry; it now fires only on bucket 4, which the S8 pin keeps empty.
  if not reachUnknown:
    for i, f in found:                                         # rule 1
      if f.status == sxSat and scSpurious notin f.soundness.pathTaint:
        return VerdictDecision(status: sxSat, winnerIdx: i)
    for i, f in found:                                         # rule 2
      if f.status == sxRaised and scSpurious notin f.soundness.pathTaint:
        return VerdictDecision(status: sxRaised, winnerIdx: i)
  if reachUnknown or found.len > 0 or candidates.len > 0:      # rule 4
    return VerdictDecision(status: sxUnknown, winnerIdx: -1)
  if scIncomplete notin runTaint:                              # rule 5
    return VerdictDecision(status: sxUnsat, winnerIdx: -1)
  VerdictDecision(status: sxUnknown, winnerIdx: -1)            # rule 6

var rfc0005RawStatus* {.threadvar.}: SymexStatusKind
  ## RFC-0005 S9 (was S7's `rfc0005UnvetoedStatus`, which observed the
  ## verdict WITHOUT the two blanket vetoes; S9 deleted them). The status the
  ## most recent `runSymexImpl` decided (`decideVerdict`), BEFORE an entry
  ## macro's replay settles its candidates (S10) -- so a test can tell a
  ## clean `sxSat` from a confirmed candidate. Written only by `runSymexImpl`
  ## (not reset by the concolic driver).

proc symValHash*(sv: SymVal): uint =
  ## Hash of a SymVal's Z3 representation for use as a call-cache key.
  case sv.kind
  of svUninterpRef: astHash(sv.uninterpAst)
  of svFloat32: astHash(sv.fp32)
  of svFloat64: astHash(sv.fp64)
  of svDistinct: astHash(sv.distinctAst) xor symValHash(sv.distinctBaseSym[])  ## G4
  of svClosure:   ## Phase 15 C1: site key + env hash (nominal-for-site, D7).
    var h = uint(sv.closureSite.siteHash) xor (uint(sv.closureSite.declOrder) shl 1)
    if sv.closureEnv != nil: h = h xor symValHash(sv.closureEnv[])
    h
  of svRef:   ## Phase 15 R1a: the Ref_T const ast (never reached in R1a stub).
    astHash(sv.refAst)
  of svPtr:   ## Phase 15 R1a: the ptr const ast.
    astHash(sv.ptrAst) xor (if sv.ptrFamily: 1'u else: 0'u)
  of svBitSet: astHash(sv.bsRaw)   ## RFC-0005 S8bq
  of svBool: astHash(sv.bo)
  of svInt:  astHash(sv.zi)
  of svString: astHash(sv.str)
  of svSeq:
    var h = astHash(sv.seqLen) xor astHash(sv.seqDataRaw) # [placeholder-audited]
    for m in sv.seqDataMore: h = h xor astHash(m)   ## RFC-0005 S8bc
    h
  of svTable:
    var h = astHash(sv.tabDataRaw) xor astHash(sv.tabPresentRaw)
    for m in sv.tabDataMore: h = h xor astHash(m)   ## RFC-0005 S8at
    h
  of svSet:
    astHash(sv.setMembersRaw)
  of svTuple:
    var h: uint = 0
    for f in sv.fields:
      h = (h shl 1) xor symValHash(f)
    h
  of svArray:
    var h: uint = 0
    for e in sv.arrElems:
      h = (h shl 1) xor symValHash(e)
    h
  of svBV8:  astHash(sv.bv8)
  of svBV16: astHash(sv.bv16)
  of svBV32: astHash(sv.bv32)
  of svBV64: astHash(sv.bv64)
  of svVariant:
    var h = symValHash(sv.vDisc[])
    for tagOrdinal, fields in sv.vArmFields.pairs:
      h = (h shl 1) xor uint(tagOrdinal)
      for f in fields:
        h = (h shl 1) xor symValHash(f)
    h
  of svMultiVariant:
    var h: uint = 0
    for ax in sv.mvAxes:
      h = (h shl 1) xor symValHash(ax.disc[])
      for tagOrdinal, fields in ax.armFields.pairs:
        h = (h shl 1) xor uint(tagOrdinal)
        for f in fields:
          h = (h shl 1) xor symValHash(f)
    h

proc heapUnchanged*(a, b: Path): bool =
  ## RFC-0005 S8u. `a`'s logical heap is `b`'s: the same per-type allocation
  ## counters and the same heap array handle per sort (a store makes a new
  ## handle). The call cache admits a callee only when its return path
  ## leaves the caller's heap as it found it.
  if a.allocCounters != b.allocCounters: return false
  if a.heaps.len != b.heaps.len: return false
  for k, h in a.heaps:
    if not b.heaps.hasKey(k) or b.heaps[k].raw != h.raw: return false
  true

const heapEpochPrefix* = "@hv:"
  ## RFC-0005 S8ax. An `allocCounters` key `@hv:<typeId>` (or `@hv:*`) counts
  ## the opaque calls on the path that havocked that pointee's heaps (every
  ## heap). `@` begins no type id, so it never collides with a `new` counter.

func heapKeyOfId*(k, id: string): bool =
  ## RFC-0005 S8ax. Heap key `k` belongs to pointee type id `id`: the
  ## scalar heap itself, or one of its field / discriminator / leaf heaps
  ## (`<id>__...`).
  k == id or k.startsWith(id & "__")

proc heapInputName*(p: Path; k: string): string =
  ## RFC-0005 S8ax. The name of the heap array `k` is read from when `p`
  ## has not touched it: the free input constant `heap_<k>`, or, once an
  ## opaque call on `p` havocked `k`'s pointee (`heapEpochPrefix`), a
  ## constant of its own for that havoc, so the read no longer sees the
  ## input heap. One name per havoc count, so every read between two havocs
  ## agrees. The `@` keeps it out of `heapKeyShapes` (`mkHeapArrayVar`).
  var n = 0
  for ck, c in p.allocCounters:
    if ck.startsWith(heapEpochPrefix):
      let id = ck[heapEpochPrefix.len .. ^1]
      if id == "*" or heapKeyOfId(k, id): n += c
  if n == 0: "heap_" & k else: "heap_" & k & "@ep" & $n

proc havocOpaqueHeaps*(w: var WalkCtx; p: Path; stmt: IRStmt): bool =
  ## RFC-0005 S8ax. An inert opaque call returned on `p`: every heap cell
  ## its summary reaches (`IRStmt.opaqueHeapTys`, or every heap for
  ## `opaqueHeapAll`) holds fresh contents. A heap the path holds is
  ## replaced by a fresh constant of its sort; one it has not touched yet is
  ## read from a constant of its own from here on (`heapInputName`). True
  ## when anything was havocked.
  enumHolesMade = true   # RFC-0016 INT-84: the callee may store a hole
  var ids: seq[string]
  for t in stmt.opaqueHeapTys:
    let pointee = if t.kind == itRef: t.refPointeeTy else: t.ptrPointeeTy
    let id = refPointeeTypeId(pointee)
    if id notin ids: ids.add id
  if not stmt.opaqueHeapAll and ids.len == 0: return false
  let ctx = requireCurrentContext()
  var keys: seq[string]
  for k in p.heaps.keys: keys.add k
  for k in keys:
    var hit = stmt.opaqueHeapAll
    for id in ids:
      if heapKeyOfId(k, id): hit = true
    if not hit: continue
    let old = p.heaps[k]
    let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, old.raw)
    # RFC-0016 PRC-07 (ref variants): the indeterminate-byte mask of a case
    # object's union image (`<id>__@msk<i>`) is determinate after the call,
    # as a value variant's havoc (`allocateSym`: a parameter's bytes are all
    # determinate) and a `{.noinit.}` local rebound by `havocOpaqueWrites`
    # are. The data heaps take fresh contents; a mask of fresh constants
    # would let a read of a byte the callee wrote observe "indeterminate"
    # (`ubIndeterminateRead`), where the path is already tainted and a
    # witness through it replayed.
    if "__@msk" in k:
      let dom = ctx.checkErr Z3_get_array_sort_domain(ctx.raw, arrSort)
      heapPut(p, k, wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const_array(
        ctx.raw, dom, mkBitVec[64](0'i64).raw)), hwStore)
      continue
    inc w.synthZ3
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
      ("heap_" & k & "@hv" & $w.synthZ3).cstring)
    heapPut(p, k,
            wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                        arrSort)), hwStore)
  if stmt.opaqueHeapAll: ids = @["*"]
  for id in ids:
    let ck = heapEpochPrefix & id
    p.allocCounters[ck] = p.allocCounters.getOrDefault(ck, 0) + 1
  true

proc havocOpaqueWrites*(w: var WalkCtx; p: Path; stmt: IRStmt) =
  ## RFC-0005 S8as. An inert opaque call returned on `p`: rebind every name
  ## its effect summary lists (`IRStmt.opaqueHavoc`; `havocAllGlobals` is
  ## every writable global of the program) to a fresh value of its type.
  ## The call may or may not have written each one, and a fresh value is
  ## every value it can hold either way, so nothing real is excluded and the
  ## path carries `feGlobalHavoc` (`dcFreshSymbol`): an UNSAT stands, a SAT
  ## is replayed. A global the walk has not bound yet is bound here too: its
  ## entry value (`entryValueOf`) is what it held BEFORE the call.
  ##
  ## RFC-0005 S8ax: a name whose type reaches heap cells is rebound too (a
  ## fresh `ref` is any address, nil included), and the cells it reaches
  ## take fresh contents (`havocOpaqueHeaps`, `feOpaqueEffectHavoc`). S8as
  ## kept such a call non-inert, and declined one under `havocAllGlobals`.
  enumHolesMade = true   # RFC-0016 INT-84: the callee may write a hole
  var names: seq[string]
  for nm in stmt.opaqueHavoc:
    if nm == "*":
      for g in w.statics.globals.values:
        if g.isVar and g.name notin names: names.add g.name
    elif nm notin names:
      names.add nm
  # RFC-0005 S8be: a call that may run a closure (`opaqueHeapAll`: a
  # routine reaches it through an argument, a global or a capture) may
  # write every variable a live closure captures by reference, which lives
  # in its env cell (`capCellName`); the frame's own copy takes the cell's
  # value after the call (`walk`). Before S8be the cells kept their values:
  # a target after the closure ran was a false `sxUnsat`, nothing recorded.
  if stmt.opaqueHeapAll:
    for k in p.env.keys:
      if k.startsWith(globalEnvPrefix & "@cap") and k notin names:
        names.add k
  var rebound: seq[string]
  for nm in names:
    var ty: IRType = nil
    if p.env.hasKey(nm): ty = tyOf(p.env[nm])
    elif w.statics.globals.hasKey(nm): ty = w.statics.globals[nm].ty
    else: continue        # never read by the walked code
    var facts: seq[Z3Bool]
    p.env[nm] = allocateSym(ty, freshDegradeName("__opaqueHavoc_" &
                                                 displayName(nm)), facts)
    for f in facts: p.pc.add f
    rebound.add displayName(nm)
  if rebound.len > 0:
    taintInPlace(p, w.degrade(feGlobalHavoc,
      "opaque call `" & stmt.callee & "` may write " & rebound.join(", ") &
           " (its effect summary): each holds a fresh value of its type " &
           "after the call, so a hit through it is replayed (feGlobalHavoc)"))
  if havocOpaqueHeaps(w, p, stmt):
    taintInPlace(p, w.degrade(feOpaqueEffectHavoc,
      "opaque call `" & stmt.callee & "` may write the heap cells its " &
           "arguments, globals and captures reach" &
           (if stmt.opaqueHeapAll: " (any cell: it may cast, run inline " &
              "assembly, dispatch or call foreign code)" else: "") &
           ": each holds fresh contents after the call, so a hit through " &
           "one is replayed (feOpaqueEffectHavoc)"))

func guardedOuterNames*(roots, captures: seq[string]): seq[string] =
  ## RFC-0005 S8an. The roots of a call's `var`/`addr` actuals that the
  ## callee could also reach directly: a module-level global, or one of its
  ## captures (`IRStmt.cGuardRoots`, `ProcSig.captures`).
  for g in roots:
    if (isGlobalEnvName(g) or g in captures) and g notin result:
      result.add g

proc threadOuterBindings*(calleeEnv: var Env; callerEnv: Env;
                         captures, guarded: seq[string]): bool =
  ## RFC-0005 S8an. Copy the caller's globals and the callee's captures
  ## into the callee's env (a withheld name stays out). True when the call
  ## shares any state outside its arguments with its caller.
  for k, v in callerEnv:
    if isGlobalEnvName(k) and k notin guarded:
      calleeEnv[k] = v
      result = true
  for c in captures:
    result = true
    if c notin guarded and callerEnv.hasKey(c) and not calleeEnv.hasKey(c):
      calleeEnv[c] = callerEnv[c]

proc carryOuterBindings*(dst: var Env; exitEnv: Env;
                        captures, guarded: seq[string]) =
  ## RFC-0005 S8an. On a callee exit, its globals and captures -- the
  ## caller's own locations -- are carried back into the caller's env.
  for k, v in exitEnv:
    if isGlobalEnvName(k) and k notin guarded: dst[k] = v
  for c in captures:
    if c notin guarded and exitEnv.hasKey(c): dst[c] = exitEnv[c]

func varLocCellName*(formal: string): string =
  ## RFC-0005 S8bs. The env name of a `bound` entry's pointer
  ## (`AddrCellEntry`): not `addrCellName(formal)`, which `addr formal`
  ## allocates as the formal's own cell.
  addrCellName(formal) & "#loc"

proc inheritAddrCells*(calleeEnv: var Env; callerEnv: Env;
                      callerCells: seq[AddrCellEntry];
                      varArgs: seq[(string, string)];
                      captures, guarded: seq[string]): seq[AddrCellEntry] =
  ## RFC-0005 S8ax. The address cells a callee frame starts with: each
  ## address-taken caller variable it reaches by name -- a capture it is
  ## threaded (`threadOuterBindings`), or the caller variable a `var` formal
  ## is (#140's `varArgs`, under the formal's name) -- with the pointer
  ## bound in `calleeEnv`. The callee's statements then keep that name and
  ## the cell equal, so a write through the formal is seen through a
  ## pointer the callee also holds, in program order.
  for c in callerCells:
    if not callerEnv.hasKey(c.cell): continue
    if c.local in captures and c.local notin guarded:
      calleeEnv[c.cell] = callerEnv[c.cell]
      result.add c
    # RFC-0016 S8ch: a module-level variable's cell, threaded as the variable
    # is (`threadOuterBindings`): the callee reaches both by name.
    if not c.bound and isModuleGlobalEnvName(c.local) and
       c.local notin guarded and calleeEnv.hasKey(c.local):
      calleeEnv[c.cell] = callerEnv[c.cell]
      result.add c
    for (formal, callerName) in varArgs:
      if callerName == c.local:
        # RFC-0005 S8bs: a formal bound into a cell passes the binding on.
        let cell = if c.bound: varLocCellName(formal) else: addrCellName(formal)
        calleeEnv[cell] = callerEnv[c.cell]
        result.add (local: formal, cell: cell, ty: c.ty, path: c.path,
                    ixs: c.ixs, bound: c.bound, view: c.view, slot: "")

proc inheritElemCells*(calleePath: Path; callerFrame, calleeFrame: int;
                      varArgs: seq[(string, string)];
                      captures, guarded: seq[string]) =
  ## RFC-0005 S8be. As `inheritAddrCells`, for element cells: a seq of the
  ## caller with element cells that the callee reaches by name -- a
  ## capture, or the caller variable a `var` formal is -- has them in the
  ## callee's frame too, under the name the callee knows it by, so the
  ## callee's statements keep its elements and their cells equal.
  let n = calleePath.elemCells.len
  for k in 0 ..< n:
    let e = calleePath.elemCells[k]
    if e.frame != callerFrame or e.dead: continue
    if e.root in captures and e.root notin guarded:
      var c = e
      c.frame = calleeFrame
      calleePath.elemCells.add c
    for (formal, callerName) in varArgs:
      if callerName == e.root:
        var c = e
        c.frame = calleeFrame
        c.root = formal
        calleePath.elemCells.add c

proc carryElemCells*(p: Path; callerFrame, calleeFrame: int;
                    varArgs: seq[(string, string)];
                    captures, guarded: seq[string]) =
  ## RFC-0005 S8be. On a callee exit, its view of each element cell of a
  ## seq the caller owns (a `var` formal's caller variable, a capture)
  ## becomes the caller's: a cell the caller already had takes the
  ## callee's `dead`; one the callee took (`addr s[i]` of its `var`
  ## formal) is the caller's from now on. Its view of a seq of its own
  ## stays, owned by a returned frame (`deadElemRefs`).
  var kept: seq[ElemCell]
  for e in p.elemCells:
    if e.frame != calleeFrame:
      kept.add e
      continue
    var to = ""
    if e.root in captures and e.root notin guarded: to = e.root
    for (formal, callerName) in varArgs:
      if formal == e.root: to = callerName
    if to.len == 0:
      kept.add e
      continue
    var had = false
    for c in kept.mitems:
      if c.frame == callerFrame and c.root == to and
         cast[pointer](c.refAst.raw) == cast[pointer](e.refAst.raw):
        had = true
        if e.dead: c.dead = true
    if not had:
      var c = e
      c.frame = callerFrame
      c.root = to
      kept.add c
  # A caller cell the callee's view saw die, listed after it.
  for c in kept.mitems:
    if c.frame != callerFrame or c.dead: continue
    for e in p.elemCells:
      if e.frame == calleeFrame and e.dead and
         cast[pointer](c.refAst.raw) == cast[pointer](e.refAst.raw):
        c.dead = true
  p.elemCells = kept


proc carryAddrCells*(dst: var Env; exitEnv: Env; calleeCells: seq[AddrCellEntry];
                    varArgs: seq[(string, string)]; sig: ProcSig;
                    guarded: seq[string]; w: var WalkCtx): AddrCarry =
  ## RFC-0005 S8ax. On a callee exit (`w.frame` is the caller's again), each
  ## address cell of a variable the caller owns -- a `var` formal's caller
  ## variable, a capture -- becomes (or stays) the caller's cell for it:
  ## `getP(x: var int): ptr int = addr x` returns the address of the
  ## caller's `x`. `moved` are those cells (`settleAddrCells` gives them to
  ## the caller's frame); `lost` are cells of a `var` formal bound to
  ## something with no cell (a field, an element; RFC-0016 S8ch: a
  ## module-level variable has one, `addrCellName`).
  ## A cell of the callee's own variable stays the callee's: it dangles now
  ## (`danglingFork`).
  for c in calleeCells:
    if not exitEnv.hasKey(c.cell) or exitEnv[c.cell].kind != svPtr: continue
    # RFC-0005 S8bs: a `bound` entry is the caller's own cell, at a path:
    # the caller keeps it, and the formal's `#140` write-back carries the
    # value.
    if c.bound: continue
    var to = ""
    for (formal, callerName) in varArgs:
      if formal == c.local: to = callerName
    if to.len == 0 and c.local in sig.captures and c.local notin guarded:
      to = c.local
    # RFC-0016 S8ch: a module-level variable's cell is the caller's too
    # (`carryOuterBindings` carried the pointer under the global's name).
    if to.len == 0 and isModuleGlobalEnvName(c.local) and
       c.local notin guarded:
      to = c.local
    var isVarFormal = false
    for f in sig.params:
      if f.name == c.local and f.isVar: isVarFormal = true
    # A parser temporary (`__sym_varArg_<n>`, the copy a field or element
    # actual is passed through) is not the location: the cell is lost.
    if to.len > 0 and (isModuleGlobalEnvName(to) or
                       not isGlobalEnvName(to) and not to.startsWith("__")):
      dst[addrCellName(to)] = exitEnv[c.cell]
      var known = false
      for k in w.frame.addrCells:
        if k.local == to and not k.bound: known = true
      if not known:
        w.frame.addrCells.add (local: to, cell: addrCellName(to), ty: c.ty,
                               path: @[], ixs: @[], bound: false, view: false, slot: "")
      if isModuleGlobalEnvName(to): result.unowned.add exitEnv[c.cell].ptrAst
      else: result.moved.add exitEnv[c.cell].ptrAst
    elif isVarFormal or to.len > 0:
      result.lost.add displayName(c.local)

proc settleAddrCells*(p: Path; carried: AddrCarry; w: var WalkCtx): Path =
  ## RFC-0005 S8ax. `p` (a callee exit's caller path) with the moved cells
  ## owned by the caller's frame, and tainted for any lost one
  ## (`feUnsupportedOp`: the pointer outlives the call, but nothing keeps
  ## the location it names equal to it).
  for r in carried.moved:
    for o in p.addrOwners.mitems:
      if cast[pointer](o.refAst.raw) == cast[pointer](r.raw):
        o.frame = w.frame.frameId
  for r in carried.unowned:   ## RFC-0016 S8ch
    var kept: seq[tuple[refAst: Z3AnyAst; frame: int]]
    for o in p.addrOwners:
      if cast[pointer](o.refAst.raw) != cast[pointer](r.raw): kept.add o
    p.addrOwners = kept
  if carried.lost.len > 0:
    taintInPlace(p, w.degrade(feUnsupportedOp,
      "RFC-0005 S8ax: the address of the `var` formal(s) " &
           carried.lost.join(", ") & " was taken, and the formal is bound " &
           "to a field or an element, which has no " &
           "address cell the walk keeps equal to it (feUnsupportedOp)"))
  p

func touchedGuard*(exitEnv: Env; guarded: seq[string]): string =
  ## RFC-0005 S8an. The first withheld name the callee bound (wrote), or "".
  for g in guarded:
    if exitEnv.hasKey(g): return g
  ""

proc guardDegrade*(w: var WalkCtx; callee, name: string): Degrade =
  ## RFC-0005 S8an. `callee` wrote `name` directly while `name` was also
  ## one of its `var`/`addr` actuals. Nim's two writes land on one location
  ## in program order; the copy-out of the argument would overwrite the
  ## direct write. `dcSubstituted` (the exit value is not Nim's).
  w.degrade(feUnsupportedOp,
    "`" & displayName(name) & "` is reached by `" & callee & "` both " &
         "through a `var`/`addr` argument and directly; the walk passes " &
         "the argument by copy-in/copy-out, so the direct write is not " &
         "modelled (feUnsupportedOp)")

proc argShapeKey*(callee: string, args: seq[SymVal]): string =
  ## (callee, argShapeHash) → a string key. Hash combination is XOR
  ## with bit rotation — collisions are merely cache misses, never
  ## correctness bugs.
  var h: uint = 0
  for a in args:
    h = (h shl 1) xor symValHash(a)
  callee & "#" & $h

const callCacheBucketMax* = 8
  ## RFC-0005 S8ax. The summaries kept per `argShapeKey`: one per distinct
  ## actual list or pruned context a call was walked in. A bound on the
  ## re-checks a lookup can cost, not on soundness (a full bucket walks).
const callCacheExitsMax* = 16
  ## RFC-0005 S8ax. The exit paths a cached summary may replay.

proc cacheArgsSame*(a, b: seq[SymVal]): bool =
  ## RFC-0005 S8ax. The two actual lists are the same terms, handle for
  ## handle (`sameSymVal`), with an Int's signedness stamp too (it decides
  ## the callee's overflow obligations). `false` on any doubt: a miss.
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if not sameSymVal(a[i], b[i]): return false
    if a[i].kind == svInt and a[i].ziSigned != b[i].ziSigned: return false
  true

proc outerState*(env: Env; captures: seq[string]):
    seq[tuple[name: string, val: SymVal]] =
  ## RFC-0005 S8be. The globals and capture cells bound in `env`, and the
  ## `captures` it binds, in the env's order (`CallCacheEntry.outer`).
  for k, v in env:
    if isGlobalEnvName(k) or k in captures: result.add (k, v)

proc cacheOuterSame*(a, b: seq[tuple[name: string, val: SymVal]]): bool =
  ## RFC-0005 S8be. The same names bound to the same terms, handle for
  ## handle. Order is not assumed.
  if a.len != b.len: return false
  for (nm, v) in a:
    var found = false
    for (nm2, v2) in b:
      if nm2 == nm:
        found = sameSymVal(v, v2)
        break
    if not found: return false
  true

proc exitKeepsOuter*(exitEnv: Env; outerIn: seq[tuple[name: string,
                    val: SymVal]]; captures: seq[string]): bool =
  ## RFC-0005 S8be. A callee exit left every global, capture cell and
  ## capture as it was entered with, and bound no global it was not (a
  ## first read binds its entry value, which the caller must see).
  for (nm, v) in outerIn:
    if not exitEnv.hasKey(nm) or not sameSymVal(exitEnv[nm], v): return false
  for k in exitEnv.keys:
    if isGlobalEnvName(k) or k in captures:
      var known = false
      for (nm, _) in outerIn:
        if nm == k:
          known = true
          break
      if not known: return false
  true

proc factsPrefixSame*(full, prefix: seq[Z3Bool]): bool =
  ## RFC-0005 S8ax. `prefix` is a prefix of `full`, handle for handle.
  if full.len < prefix.len: return false
  for i in 0 ..< prefix.len:
    if cast[pointer](full[i].raw) != cast[pointer](prefix[i].raw): return false
  true

proc pruneFactsSince*(mark: int; p: Path; facts: var seq[seq[Z3Bool]]): bool =
  ## RFC-0005 S8ax. The drops logged since `mark` (`ctxPruneLog`), each as
  ## the facts it added beyond `p`'s (the caller's path at the call): the
  ## callee's own path facts and defect-survivor facts, then the arm. False
  ## when a drop's path does not extend `p` (a merge rebuilt its facts):
  ## its dependence on the context is then not separable, and the call is
  ## not cached.
  for i in mark ..< ctxPruneLog.len:
    let f = ctxPruneLog[i]
    if not factsPrefixSame(f.pc, p.pc) or
       not factsPrefixSame(f.dsp, p.defectSurvivorPc):
      return false
    facts.add f.pc[p.pc.len ..< f.pc.len] &
              f.dsp[p.defectSurvivorPc.len ..< f.dsp.len] & f.extra
  true

proc pruneFactsHold*(ctx: Z3Context; p: Path; facts: seq[seq[Z3Bool]];
                    settings: SymexSettings): bool =
  ## RFC-0005 S8ax. Every drop a cached summary's walk decided is decided
  ## the same way under `p`, the replaying caller's path: its facts are
  ## UNSAT with `p`'s (the same bounded check, `loopPruneRLimit`). An
  ## undecided check is `false` (the call is walked). Each check that holds
  ## is itself a drop decided against `p`'s context, logged for an
  ## enclosing call's summary (`logPrune`).
  for d in facts:
    if refuteStatus(ctx, pathRoots(p, d), settings,
                    loopPruneRLimit(settings)) != zsUnsat:
      return false
  for d in facts: logPrune(p, d)
  true

# ---- the per-run reset ----------------------------------------------------

proc resetWalkCtxState*() =
  ## RFC-0016 INT-34 B6a. The per-run reset of every threadvar of this module,
  ## called by `resetSymexRunState` (the statements it held for them, in their
  ## order there).
  rfc0005RawStatus = sxUnknown  ## RFC-0005 S7: an aborted walk decides nothing
  heapDepthErrors = @[]                  ## Phase 15 R9: reset heap-depth-error sink
  newFieldZeroErrors = @[]               ## Cluster H Step C: reset isNew-zero-write sink
  currentClosureExitPc = @[]             ## Phase 16 ADR-0012: reset exit-pc channel
  currentClosureCallErrors = @[]         ## Phase 15 C2b: reset closure-call errors
  currentCallerHeaps = initTable[string, Z3AnyAst]()  ## Phase 15 R1b
  currentCallerHeapDepth = 0                          ## Phase 15 R1b
  currentCallerAllocCounters = initTable[string, int]()  ## Phase 15 R1b
  currentCallerLiveRefs = initTable[string, seq[Z3AnyAst]]()  ## Phase 15 CR-5
  currentClosureExitHeaps = initTable[string, Z3AnyAst]()     ## Phase 15 CR-1
  currentClosureExitAllocCounters = initTable[string, int]()  ## Phase 15 CR-1
  currentClosureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()  ## Phase 15 CR-1
  currentClosureDidMutateHeap = false                         ## Phase 15 CR-1

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(
    heapDepthErrors, newFieldZeroErrors, currentCallerHeaps,
    currentCallerHeapDepth, currentCallerAllocCounters,
    currentCallerLiveRefs, currentClosureExitHeaps,
    currentClosureExitAllocCounters, currentClosureExitLiveRefs,
    currentClosureDidMutateHeap, currentClosureExitPc,
    currentClosureCallErrors, rfc0005RawStatus)

registerThreadStateRelease(releaseThreadState)
