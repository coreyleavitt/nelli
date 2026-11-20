## Phase-2 IR interpreter.
##
## The IR is type-erased after parsing; the runtime determines the
## width of each integer subexpression by probing the env or
## inheriting from the surrounding context (let RHS = let LHS type;
## comparison operands = the matching variable's type).
##
## Storage: `SymVal` is a sum over the Z3 families we need
##
##   { Z3Bool, Z3BitVec[8|16|32|64], Z3Int }
##
## with a `signed: bool` field inside each BV variant case (Nim's `int*`/`uint*`
## distinguish signedness at the operator layer, not the bit-pattern).
## `Z3Int` lands as a SymVal variant for Phase-2 cycles 5+ when the
## abstraction layer promotes range-typed integers; the parser/runtime
## here ship with the variant present and the structural plumbing in
## place, so cycle 5 only adds the promotion logic, not new families.

import std/tables
import ./walk_log
export walk_log.walkUnitsLogEnv
import std/options
from std/typetraits import nil   ## RFC-0005 S8ar: `readCellField`'s distinct arm
import std/sets
import std/hashes
import std/algorithm   ## N46 audit (RFC-chapulin-hardening bucket-2): sort() for
                        ## deterministic Table-key iteration order at Z3 term-
                        ## building sites (mergeClosureExitHeap's ITE loop)
import std/math   ## Phase 15 F2: classify() for float-literal NaN/Inf/-0.0 lowering
import std/monotimes   ## RFC-0016 INT-57: the stall backstop deadline
import std/strutils   ## Phase 15 S5: parseInt on a concrete seqLen numeral; split
import z3

from ./buildprofile import buildSemantics, exSetjmp   ## RFC-0016 W1-c1b
import ./buildprofile as bprof   ## RFC-0016 K5a: the host half, the segment, the row
import ./types
import ./admission
import ./arith_regime   ## RFC-0016 review D1 S4: the one owner of the arithmetic regime
import ./definedness   ## RFC-0016 K10a-axis: the definedness axis
import ./variant_layout as vl   ## RFC-0016 PRC-07 slice A: a variant's C layout
import ./abstraction
import ./symval   ## RFC-0016 review D3c-1: the value core (SymVal, Env, the Symex*Error family)
import ./walk_state   ## RFC-0016 review D3c-2: the per-run walk state, the sinks and the hooks
import ./walk_types   ## RFC-0016 INT-34 B2: Path, the frames, WalkCtx, the Raw* results
from std/importutils import privateAccess
privateAccess(RawWitness)     ## its fields stay private to walk_types (see its header)
privateAccess(SatCandidate)   ## `input`, as for `replay_settle.nim`
export walk_types.RawDiagnostic, walk_types.RawUndefined,
       walk_types.SatCandidate, walk_types.CandidateReplay,
       walk_types.RawResult, walk_types.ConcolicBranchRecord,
       walk_types.ConcolicDefinedFact, walk_types.Rfc0005S1CarrierProbe,
       walk_types.Rfc0005S1LeakPinProbe, walk_types.TargetSolveCost,
       walk_types.VerdictDecision
# Exactly the names `runtime.nim` exported before the move, so
# `import nelli/symex` (through `dsl.nim`'s `export runtime`) sees the same
# surface (`scripts/int34-public-names.sh` diffs it).
import ./walk_path   ## RFC-0016 INT-34 B3: making and forking paths (region R0's procedures)
export walk_path.h1PathHasHeapFields, walk_path.h1ForkIsolation,
       walk_path.seedCallerHeapInWalkCtx, walk_path.isFollowConcreteWalk,
       walk_path.svWithRaw, walk_path.c1ClosurePoCApply
# Exactly the routines `runtime.nim` exported before the move, as above.
import ./lower_expr   ## RFC-0016 INT-34 B4: lowering an expression (region R1, and the R0 state it reads)
export lower_expr.obligationLog, lower_expr.sliceViewCounter,
       lower_expr.variantLitFreshCounter,
       lower_expr.variantConstructSymFreshCounter, lower_expr.walkerWorkUnits,
       lower_expr.walkerTermUnits, lower_expr.walkerContextUnits,
       lower_expr.arrayAccessTooWide, lower_expr.bsCard,
       lower_expr.reconcileFloat, lower_expr.symbolicPositions,
       lower_expr.termDepth, lower_expr.termTooDeep
# Exactly the names `runtime.nim` exported before the move, as above.
import ./walk_solve   ## RFC-0016 INT-34 B5: solving a path (region R2, and the R0 state it reads)
export walk_solve.currentVariantHeaps, walk_solve.heapWitnessNominalRegistry,
       walk_solve.currentClosureCallAxioms, walk_solve.extractionErrors,
       walk_solve.unknownExnWarnings, walk_solve.maxWitnessSeqLen,
       walk_solve.ptrTargetCode, walk_solve.ptrAimPrefix,
       walk_solve.symexTargetSolveStats, walk_solve.ownContextUnits,
       walk_solve.symexZ3CallCount, walk_solve.seqLenBoundFacts,
       walk_solve.fpIntervalRefutes, walk_solve.seqRangeFacts,
       walk_solve.dropImpliedByteDomains, walk_solve.deepTermsLeftAlone,
       walk_solve.mergeMemberships, walk_solve.stallBackstopMs,
       walk_solve.querySolver, walk_solve.divRangeFacts,
       walk_solve.factsFirstRLimit, walk_solve.bvOffsetLinks,
       walk_solve.bvIntInverseFacts, walk_solve.bvViewRangeFacts,
       walk_solve.cardFreeAbstraction, walk_solve.recFactsRLimit,
       walk_solve.defaultLoopPruneRLimit, walk_solve.loopPruneRLimit,
       walk_solve.symexIfArmsPruned, walk_solve.symexIfArmsChecked,
       walk_solve.symexLoopIterations, walk_solve.limitWorldRLimit
when defined(symexQueryStats):
  export walk_solve.SymexQueryStat, walk_solve.symexQueryStats,
         walk_solve.symexQueryStatsPaused, walk_solve.symexFactsFirstOff,
         walk_solve.SymexStepStat, walk_solve.symexStepStats,
         walk_solve.symexPerturbConsts, walk_solve.symexQueryStatsSummary,
         walk_solve.symexQueryStatsTotals, walk_solve.symexEqsSplits
# Exactly the names `runtime.nim` exported before the move, as above.
import ./walk_ctx   ## RFC-0016 INT-34 B6a: the walk context's verbs (region R3, and the R0 state it reads)
export walk_ctx.heapDepthErrors, walk_ctx.newFieldZeroErrors,
       walk_ctx.currentCallerHeaps, walk_ctx.currentCallerHeapDepth,
       walk_ctx.currentCallerAllocCounters, walk_ctx.currentCallerLiveRefs,
       walk_ctx.currentClosureExitHeaps,
       walk_ctx.currentClosureExitAllocCounters,
       walk_ctx.currentClosureExitLiveRefs,
       walk_ctx.currentClosureDidMutateHeap, walk_ctx.currentClosureExitPc,
       walk_ctx.currentClosureCallErrors, walk_ctx.rfc0005S1CarrierProbe,
       walk_ctx.rfc0005S1LeakPinProbe, walk_ctx.defaultConcreteBranchRLimit,
       walk_ctx.taintedSolveRLimit, walk_ctx.classifyTargetSolve,
       walk_ctx.decideVerdict, walk_ctx.rfc0005RawStatus
# Exactly the names `runtime.nim` exported before the move, as above.
import ./walk_expr   ## RFC-0016 INT-34 B6b: lowering inside a statement and its drains (region R4, and the R0 state it reads)
export walk_expr.seedCallerHeapThreadvars, walk_expr.typeIdToDefectKind,
       walk_expr.concretelyInfeasible, walk_expr.concreteBranchRLimit,
       walk_expr.concreteBranchOutcome
# Exactly the names `runtime.nim` exported before the move, as above.
import ./runtime_heap   ## RFC-0016 INT-34 B7: the heap arm (`walkHeapArm`, the R0 hint sinks it writes)
export runtime_heap.freshnessCapHints, runtime_heap.ptrFamilyHints,
       runtime_heap.freshRef, runtime_heap.freshFrameRef,
       runtime_heap.ptrPreKey, runtime_heap.assertFreshness,
       runtime_heap.keepStrBuf
# Exactly the names `runtime.nim` exported before the move, as above.
import ./pcre_select   ## RFC-0005 S8bb: the priority run (`replace`)
import ./pcre_engine   ## RFC-0005 S8bt: the engine of unanchored calls
import ./exn_hierarchy   ## Phase 15 E4: exnTypeTable / isSubtypeOf / isDefect
import ../choice   ## RFC-fuzzer-nextgen G1b: ChoiceNode — the concrete draw trace
import ../int128   ## RFC-fuzzer-nextgen G1b: toInt64(ChoiceInt) for draw bounds/values
import ./ptraim   ## RFC-0005 S8bw (item 3): ptrAimByName
import ./nativestack   ## RFC-0005 S8ca: `nativeStackShort`
import ./stdlib_rows   ## RFC-0016 K4c: the facet cells a decline names
import ./z3check   ## RFC-0016 review D3c-6: the sort-checked Z3 term builders
import ./heap_model   ## RFC-0016 review D3c-6: the heap algebra (replaces the forward-declaration block)
export z3check.checkedStore, z3check.checkedSelect, z3check.checkedIte,
       z3check.checkedEq, z3check.termWalkMaxDepth
export heap_model.distinctBijectivityHints, heap_model.distinctSortNames,
       heap_model.ContainerCardRegistry, heap_model.containerCard,
       heap_model.discriminatorDomain, heap_model.axisDiscriminatorDomain,
       heap_model.currentBorrowReboxCounter, heap_model.bvTermToZ3Int,
       heap_model.refPointeeTypeId, heap_model.allocRefSort,
       heap_model.fieldHeapKey, heap_model.inheritTagKey,
       heap_model.heapChainDepth, heap_model.heapDerefsPerPathCap,
       heap_model.heapDerefDecline, heap_model.sortOfTuple
import ./string_lower_support   ## RFC-0016 review D3c-7: index splits, `splitNeedle`, `literalStringBytes`
import ./runtime_strings   ## RFC-0016 review D3c-7: Cluster S, `lowerStrArm`
import ./runtime_closures   ## RFC-0016 review D3c-5: Cluster C, `lowerClosureArm`
import ../thread_state   ## RFC-0016 S8ck-r: the per-thread state release registry
import ./exits   ## RFC-0005 review R4: the exit channels (`park`, `claimAt`)
import ./concolictaxonomy   ## RFC-fuzzer-nextgen G2/R28/R29b: the concolic
  ## yield taxonomy (`ConcolicFlipOutcome`/`ConcolicYieldCounters`/etc.) now
  ## lives in this Z3-free leaf module so `fuzz.nim` can share it directly
  ## instead of hand-mirroring — see that module's doc comment. Re-exported
  ## so this module's own public surface (and everything that transitively
  ## imports it — `smt/dsl.nim`, `symex.nim`) is unchanged.
export concolictaxonomy

export tables, sets   ## for `Table` / `HashSet` in witness types

# Once-per-process banner for `isLoose` mode. ADR-0001 calls this out
# as a deliberate footgun; the banner is the documented warning.
var isLooseBannerEmitted = false

proc emitIsLooseBanner() =
  if not isLooseBannerEmitted:
    stderr.writeLine "nelli/symex: WARNING — `isLoose` integer semantics " &
                     "is UNSOUND (Z3Int everywhere, no BV floor). May produce " &
                     "witnesses that overflow at runtime. See ADR-0001."
    isLooseBannerEmitted = true

# ---- SymVal -----------------------------------------------------------------

# ---- Path and its heap-state records: in ./walk_types (RFC-0016 INT-34 B2),
# with the frame types and `WalkCtx` (the value core is in ./symval)

# ---- Forking a path (`forkPath*`, `taintInPlace`), the literal protos, the
# container-cell readers and the `WalkCtx` readers: in ./walk_path (RFC-0016
# INT-34 B3). What stays in this region is the run state they do not read,
# and the routines that do.

# `freshnessCapHints` and `ptrFamilyHints` live in ./runtime_heap (RFC-0016
# INT-34 B7): the heap arm writes them.

# ---- RFC-0005 S8m: sort-checked Z3 term construction ------------------------
#
# A Z3 API error (a BV stored into a Bool array, an `ite` over two sorts) is
# raised by nim-z3's `checkErr` as a `Z3Error`. On the C backend that raise,
# unwinding through the walker's live `walkBlock` frames, is LOST (the
# goto-exception hazard `degradeStrArm`'s doc describes): the store returned
# as if it had not happened, `runSymexCaught`'s `Z3Error` arm never ran, and
# the run reported a silent `sxUnsat` with no error at all. Reproduced at
# a58dc08 by removing S8l's bool-discriminator fold: `BoolV(on: true, t: x)`
# was `sxUnsat []` on c and `sxUnknown [ekZ3Error]` on cpp.
#
# Two guards. (1) The raw constructors the walker builds from values of
# independently derived sorts -- array store and select, `ite`, `=` -- check
# the sorts first (`checked*`). A mismatch is a walker fault: it is recorded
# as `weInternalWalkerFault` through the lowering sink (the calling path is
# tainted when it drains, or the walk-end leak pin records it), and a fresh
# term of the expected sort stands in, so nothing raises. (2) The error
# handler every symex context installs (`nelliZ3ErrorHandler`) counts every
# Z3 API error of the run, whether or not its raise survived; `runSymex`
# turns any verdict of a run that saw one into `sxUnknown` + `ekZ3Error`.

var z3ApiErrorCount* {.threadvar.}: int
  ## RFC-0005 S8m. Z3 API errors raised in this thread's current run (reset
  ## by `resetSymexRunState`), counted by `nelliZ3ErrorHandler`.
var z3ApiFirstError* {.threadvar.}: string
  ## RFC-0005 S8m. The first such error's code, for the recorded message.

proc nelliZ3ErrorHandler(c: RawZ3Context, e: Z3ErrorCode) {.cdecl.} =
  ## RFC-0005 S8m. Replaces nim-z3's no-op handler on every context
  ## `resetSymexRunState` makes. Z3 has already set the error code, so
  ## `checkErr` still raises after the call returns; this only counts it,
  ## so a raise the C backend loses still reaches `runSymex`.
  if z3ApiErrorCount == 0: z3ApiFirstError = $e
  inc z3ApiErrorCount

# ---- RFC-0005 S8ce: a raise survives every destroy on its way out -----------
#
# The mechanism behind every "goto-exception hazard" note in this file (N31,
# N36, ADR-0023, S8m). Nim 2.2.10's C code generator (goto exceptions) runs a
# destructor on the raise path with the error flag still set, unless it takes
# that destructor as able to raise: a call's result temporary (`T = f(); if
# (*nimErr_) { =destroy(T); goto exit; }`, `walkBlock`'s `seq[Path]`) and a
# local at its scope's merge label alike. nim-z3's hooks wrapped their bodies
# in `try: ... except CatchableError: discard`, and a `try` entered with the
# flag set takes the IN-FLIGHT exception as its own: its first checked call
# jumps to its handler, which clears the flag and pops it. The frame returned
# as if nothing was raised, and the walk went on to a false verdict. C++
# exceptions are native and were unaffected.
#
# S8ce fixes the hooks at the root (nim-z3 `rfc-0005-s8ce`: raise-free by
# construction, no `try`, `quirky`), so every raise in the walk, witness
# extraction's and an own-context solve's among them, reaches
# `runSymexCaught` on both backends. This module has no lifecycle hook of its
# own. The in-band sinks those notes describe predate the fix and remain the
# walker's way to report a decline; they are no longer the only sound one.
# They stay (S8ck item 6, re-read at S8ck-r against nim-z3 d86efda): raise-free
# hooks make a raise SURVIVE, they do not make one cheap. A raise ends the
# whole run at `runSymexCaught` as `sxUnknown` (the boundary-abort class),
# because the walker has no unwind discipline to resume after one (no
# try/finally around `arithFrames` and the other per-run stacks; every escape
# ends the run, which re-seeds them). An in-band degrade (`queueDegrade`,
# `degradeStrArm`) instead taints only the path that met it
# (`drainPendingLowerEffects` (d)), and every other path still decides. So
# the sinks are kept for precision, and Nim 2.2.10 still loses a raise in any
# destructor that enters a `try` (UPS-01), which nim-z3's raise-free hooks do
# not cover.

# ---- Phase 15 Cluster R (R1): per-walker ref-sort + nil-const cache -----------
#
# Each distinct `ref T`/`ptr T` pointee type gets ONE fresh uninterpreted sort
# `Ref_<typeId>` (`mkUninterpretedSort`) shared across every path — the sort is
# per-WALKER, not per-path (ADR-0010). Like G4's distinct sorts and C2a's
# closure funcSyms, the sort is allocated where there is no `WalkCtx`
# (`allocateSym(itRef)`, a pure type→SymVal allocator, allocates the param's
# `Ref_T` const), so the cache lives in threadvars reset at `runSymexImpl`
# entry and is mirrored into `WalkerStatics.refSorts`/`.nilConsts` after the
# walk for post-run inspection. The `nil_<typeId>` const rides alongside.

# CR-9 Stage 4: `currentWalkCtxPtr` moved here (from the C2b cluster) so that
# `allocRefSort` and `assertFreshness` — defined before `WalkCtx` — can test
# the nil-guard and delegate to `syncRefSortEntry` (forward-decl below). The
# variable is `pointer` (not `ptr WalkCtx`) so no WalkCtx forward-reference is
# needed; callers cast it after WalkCtx is in scope.
# ----------------------------------------------------------------------------
# CR-1c carrier-boundary table (round-6 mechanical-debt slice, item 5)
# ----------------------------------------------------------------------------
# RFC-chapulin-hardening.md's CR-1c (~539-547) proposed retiring the file's
# ~18 near-identical `object of CatchableError` raise carriers into ONE
# generic `SymexClassifiedDegradeError{kind}` and named this "not required
# in-RFC, but... so the count stops climbing." Practice diverged from that
# single-carrier vision: three PURPOSE-SPECIFIC in-band degrade carriers
# emerged instead (N40/R1/N36, each solving a different soundness hazard at
# a different point in the pipeline), and CR-1c's single-carrier merger was
# never revisited once the three-carrier shape proved sufficient. This table
# is the RFC's own requested closure: the accepted taxonomy, written down so
# a future degrade site does not have to re-derive "which of the three do I
# use" from first principles or invent a fourth.
#
# | Carrier                 | Covers                                        | Taint mechanism                              | Reconstruction path |
# |--------------------------|-----------------------------------------------|-----------------------------------------------|----------------------|
# | `allocDegrade`           | The allocation/sort-derivation chokepoint for ANY classified-decline arm inside `allocateSym` itself, plus every OTHER walk-reachable call site that hits an "unallocatable/unmergeable value" mid-walk, REGARDLESS of whether a `Path`/`w: var WalkCtx` happens to be in scope at that call site (`eqBV`/`neBV`/`cmpBV`'s non-placeholder catch-alls, `iteSV`'s composite-merge arms, `svLeafEq`'s non-seq catch-all, `isVariantConstructSym`'s budget checks, AND `runtime_heap.nim`'s `walkHeapArm` sites, which DO have `w` in scope and correctly use `allocDegrade` anyway — item 8, round-6 re-review). Round-6 re-review correction: an earlier version of this row read "sites with NEITHER a `Path`/`w` NOR a `lower()` wrapper in scope," which `walkHeapArm`'s own call sites contradict outright. `Path`/`w` SCOPE is not what selects the carrier — `allocDegrade` is the one chokepoint for THIS taint mechanism's SOURCE (an allocation/sort-derivation failure) no matter what else happens to be in scope at the call site; the Path-vs-`lower()`-wrapper distinction instead governs which SINK downstream carries the resulting taint onward (`w.sawUnknown` synchronously here vs. a `Path`-scoped fork/drain elsewhere) — a separate axis from carrier CHOICE. Any NEW site that discovers such a failure, with no more specific carrier below applying, belongs here. | Writes `loweringDegradeErrors`/`loweringDidDegrade` (SND-3) UNCONDITIONALLY, plus `currentWalkCtxPtr`'s `.sawUnknown` DIRECTLY/IMMEDIATELY/synchronously (not deferred to a drain) — see `allocDegrade`'s own SINK CHOICE doc, below, for why both are needed. | Almost always `allocateSym(ty, freshDegradeName(tag), pcOut)` on the value's RECONSTRUCTED `IRType` (via `tyOf`/a literal `tXxx()` builder) — total for every `allocateSym`-representable kind. The ONE documented exception is `iteSV`'s `svUninterpRef` arm: `allocateSym`'s `itUninterp` arm only recognises three synthetic name prefixes and hard-raises for an ordinary cluster-E sort name, so that site drops to the lower-level `rawConstOf(ctx, existingSort, freshDegradeName(tag))` instead — a fresh same-SORT const built directly against the ALREADY-KNOWN Z3 sort, bypassing `allocateSym` entirely. This is the axis the walker-v114→v115 iteSV variant bug lived on: picking `allocateSym` vs `rawConstOf` is a property of the SymVal KIND being reconstructed, not a free choice — get it wrong and either `allocateSym` hard-raises (uninterpreted sort) or a `tyOf` round-trip silently drops information `rawConstOf` did not need to know about (diagnostics-only kinds like `svVariant`/`svMultiVariant`, see item 2's `tyOf` note). |
# | R1 placeholder funnel    | A READ of a value ALREADY flagged `isUnsupportedFieldPlaceholder` (an unbacked-element `svSeq`, or any other kind `seqUnsupportedFieldKind` classifies) — i.e. the SECOND touch of a value whose FIRST touch already degraded and manufactured an inert placeholder. `placeholderReadDeclineMsg`/`placeholderReadDeclineKind` (message/kind) + `declinePlaceholderInLower` (the in-`lower()` recording half) + `placeholderBoolDecline`/`placeholderCmpDecline` (the comparison-machinery specialization). A NEW site belongs here whenever it consumes a value that MAY already carry the placeholder flag — the guard (`recv.isUnsupportedFieldPlaceholder`) must run BEFORE any other handling, never after. | Same `loweringDegradeErrors`/`loweringDidDegrade` sink as `allocDegrade` (this funnel is a THIN WRAPPER around it, not an independent mechanism) — the distinguishing feature is the MESSAGE, not the taint plumbing: `placeholderReadDeclineMsg` prefers the ORIGINATING decline reason (`recv.seqUnsupportedFieldReason`) over a generic "unsupported kind" claim, so a cascade of downstream reads on the same tainted receiver reports the honest root cause instead of a fresh misclassification at each hop. | The caller's OWN choice — this funnel never allocates on the caller's behalf. A composite-shaped caller (`iteSV`'s `svSeq` placeholder arm) returns the ALREADY-FLAGGED placeholder itself (`t`); a boolean-shaped caller (`cmpBV`/`eqBV`/`neBV` via `placeholderCmpDecline`, `svLeafEq` via `placeholderBoolDecline`) allocates ONE fresh `svBool` via `allocateSym(tBool(), tag, pcOut)`. Never `rawConstOf` — every current call site's result kind is `allocateSym`-representable. |
# | `degradeStrArm`          | **Routing test: "is this call INSIDE `lowerStrArm`'s own call graph", never "is this a string op"** — a string-typed VALUE degraded from somewhere else entirely (e.g. `allocDegrade`'s own callers touching an `svString`) does NOT route here just because the value happens to be a string; only a RAISE that actually unwinds from within `lowerStrArm`'s call graph does. The ~18 classified-carrier RAISES `lowerStrArm` (`runtime_strings.nim`) can produce (`requireStr`/`needleAsStr`/join/split/regex/bytes/radix/case-fold/the "not modeled" catch-all), caught in ONE `try`/`except` at `lowerStrArm`'s SINGLE call site in `lower`'s dispatch — never at each of the ~18 individual raise sites. Sound ONLY because the unwind from any `lowerStrArm`-internal raise to this one `except` crosses plain proc frames exclusively (never a `walkBlock` frame) REGARDLESS of how many `walkBlock` frames sit above `lower()` in the walker's own call chain (see `degradeStrArm`'s own SOUNDNESS OF THE CHOKEPOINT PLACEMENT doc). A NEW string-arm gap belongs here only if it is ADDED INSIDE `lowerStrArm`'s own call graph (never a raise reachable from a `walkBlock` frame directly — that case needs `allocDegrade` instead, since a `try`/`except` around a `walkBlock`-reachable recursive call is UNSOUND on this toolchain per ADR-0023/B7r2). | Same `loweringDegradeErrors`/`loweringDidDegrade` sink, written once at the `except` handler rather than at each raise site — the caught exception's `kind`/`msg` fields carry the classification through unchanged. | `allocateSym` keyed off `e.kind` (the `IRExpr`'s STATIC expression kind, e.g. `iekStrLen`/`iekStrAt`/`iekStrSplit`) rather than off any runtime value, since the caught exception carries no result-type information — the arm-by-`e.kind` dispatch is itself the reconstruction table (`tInt()` for `iekStrLen`, `tBool()` for `iekStrContains`, `tSeq(tString())` for `iekStrSplit`, ...). Never `rawConstOf`: every `iek*` string-arm result is a primitive/seq kind `allocateSym` builds directly. |
#
# When a genuinely NEW carrier looks tempting: it almost never is. All three
# existing carriers converge on the SAME two sinks
# (`loweringDegradeErrors`/`loweringDidDegrade`, and — for the alloc-time
# path specifically — `currentWalkCtxPtr.sawUnknown`); what differs between
# them is WHEN each one fires (first-touch allocation vs. second-touch read
# vs. a caught classified raise) and WHERE in the call graph it is safe to
# sit (bare allocator, `lower()`-internal, or a single proc-frame-only
# `try`/`except` boundary) — not the plumbing itself. A fourth carrier is
# only justified by a genuinely NEW "when/where," not a new value KIND (a
# new kind is a new arm of the RECONSTRUCTION column, not a new row).
# ----------------------------------------------------------------------------

# `boundsUnchecked` lives in ./walk_expr (RFC-0016 INT-34 B6b): R4 reads it.
proc depositStrIndexOob(oob: Z3Bool) =
  ## RFC-0016 PRC-07. The out-of-bounds predicate of a string element read or
  ## write, lowered in an expression (no path to fork): the checked build's
  ## `IndexDefect` sink, or, with `boundChecks` off, the undefined-access
  ## deposit `drainArithTraps` halts.
  if boundsUnchecked():
    let tr = ArithTrap(cond: oob, ub: some(uncheckedIndexUb()),
                       site: uncheckedIndexSite(""))
    syncArithTrapCond(tr)
  else:
    syncStrIndexOobCond(oob)

proc depositUndefinedOob(oob: Z3Bool) =
  ## RFC-0016 INT-87. `c[i]` on a `cstring` outside `0 .. len(c)`: C reads
  ## past the buffer, undefined whatever the build's checks.
  let tr = ArithTrap(cond: oob, ub: some(uncheckedIndexUb()),
                     site: uncheckedIndexSite(""))
  syncArithTrapCond(tr)

# `lastDrainedClosureExitPc`, the caller taint, undefined and pc a closure
# call is lowered against, `closureBodyCallerPc` and
# `seedCallerHeapThreadvars` live in ./walk_expr (RFC-0016 INT-34 B6b).

var currentClosureCallAxiomStrs* {.threadvar.}: seq[string]
  ## Phase 15 C2b test hook. The SMT-LIB rendering (`Z3_ast_to_string`) of each
  ## asserted closure-call axiom, captured WHILE the Z3 context is live (a raw
  ## `Z3Bool` handle outlives its context as a dangling pointer, so a test must
  ## not stringify `currentClosureCallAxioms` after the run). Lets a test assert
  ## the GROUND multi-return-path encoding — both `=>` arms, no `forall`. Reset
  ## at `runSymexImpl` entry.
  ## CR-9 A0: intentionally LEFT as a threadvar. It is a Z3-context-lifetime-bound
  ## test hook: `tests/tsymex_phase15_C2b_closure_call.nim` reads it POST-RUN.
  ## A WalkCtx field would be freed when the Z3 context is destroyed, leaving a
  ## dangling reference from the test. Migration yields no verdict benefit.

## NOTE: `currentWalkCtxPtr` has been moved earlier (to the R1 cluster, before
## `allocRefSort`) so pre-WalkCtx procs can test the nil-guard. See new location.

proc lowerClosureCall(env: Env, e: IRExpr): SymVal
  ## Phase 15 C2b fwd-decl. Defined AFTER `walk` (it descends the lambda body
  ## via `walk`), called from `lower(iekClosureCall)` (defined before `walk`).

# ---- Solving a path (`trySolve`, `pathInfeasible`, the witness and the
# solver budget): in ./walk_solve (RFC-0016 INT-34 B5, region R2).

# ---- The walk context's verbs (`degrade`, `halted`, `exact`, the frames,
# `solveTargetHit`, `decideVerdict`, the pending take and restore, the call
# carry and the call-summary cache keys): in ./walk_ctx (RFC-0016 INT-34 B6a,
# region R3), with the R0 run state they read.

# ---- Lowering inside a statement and the drains onto the consuming path:
# ---- in ./walk_expr (RFC-0016 INT-34 B6b, region R4). The forward
# ---- declarations below are of routines that stay here.

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path]
const compoundStmtKinds = {isBlock, isIf, isWhile, isTry}
  ## RFC-0016 review R5-2. The statements with statements inside: walked
  ## bare, never reconciled over their span (`reconcileCells`).
proc evalCondSynced(p: Path; cond: IRExpr;
                    w: var WalkCtx): (Z3Bool, seq[Path])
  ## RFC-0016 review R5-2 fwd decl (defined beside `walk`).
proc evalReturnSynced(p: Path; value: IRExpr; proto: Option[SymVal];
                      w: var WalkCtx): seq[Path]
  ## RFC-0016 review R7-1 fwd decl (defined beside `evalCondSynced`).
proc anchorViews(p: Path; cells: seq[AddrCellEntry]; frame: int)
  ## RFC-0005 S8ca fwd decl (defined beside `syncAddrCells`).
proc liveViewMarks(p: Path; w: WalkCtx)
  ## RFC-0005 S8ca fwd decl (defined beside `syncAddrCells`).
proc logInPlace(before: Path; heapsBefore: Table[string, Z3AnyAst];
                after: Path)
  ## RFC-0005 S8ca fwd decl (defined beside `syncAddrCells`).

proc routeRaise(p: Path, typeId: string, msg: Option[string],
                w: var WalkCtx): seq[Path]
  ## Phase 15 E3 fwd decl (defined after `walk`: it walks `finally` bodies).
proc noteOpaqueUndefined(w: var WalkCtx; paths: seq[Path];
                         stmt: IRStmt): seq[Path]
  ## RFC-0016 W3-z R3 fwd decl (defined after `routeRaise`).

# ---- The heap arm (`walkHeapArm`): in ./runtime_heap (RFC-0016 INT-34 B7).

# ---- The statement walkers `walkStmt` dispatches to (RFC-0016 INT-34 B1) -----
# They call `walk` and `evalCondSynced`, so they sit above the expression
# drains, with the statement arms.

proc walkIfFollowConcrete(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): Survivors =
  ## `wmFollowConcrete` counterpart to `isIf`'s `wmExplore` fork-every-arm
  ## loop (below). Reuses `lowerBoolInExpr`/`forkPath` — the same symbolic
  ## lowering and path-forking machinery `wmExplore` uses — but walks ONLY
  ## the concretely-taken arm, appending its predicate (or negation, for a
  ## skipped arm) to the single surviving path's `pc`. That accumulated `pc`
  ## IS the "concrete-trace constraint collection" G1b's soundness pin
  ## checks: it must be satisfiable together with `w.concreteEq` (the
  ## original concrete draws are a model of it, by construction of this
  ## very function — the soundness pin catches a bug in this function, not
  ## a property of the SUT).
  ##
  ## RFC-0005 S8i: each condition's scalar raises are drained
  ## (`drainScalarRaiseForks`), as the explore arm and
  ## `walkWhileFollowConcrete` drain theirs. They were never drained here:
  ## a closure call in the condition that raised on this trace had its raise
  ## dropped, so the handler that caught it was never walked and its
  ## decisions never recorded. The drain routes the raise paths
  ## (`routeRaise` skips the ones the replay did not take) and may return
  ## several continuations (a float -> int conversion's in/out-of-domain
  ## split, parseInt's clean/lax pair): one whose NEW defect-survivor facts
  ## the concrete draws contradict is not this trace and is not followed.
  var survivors: seq[Path]
  for p in paths:
    if w.shouldStop: return exact(survivors)
    # RFC-fuzzer-nextgen G2: snapshot the pc BEFORE this if-statement's own
    # branch predicates are lowered/appended — the "prefix constraints up to
    # that branch" a later flip-solve needs. Side-conditions `lowerBoolInExpr`
    # may push while evaluating THIS if's own conditions land in `cp.pc` after
    # this point, not before — deliberately excluded from `prefixPc` (they
    # describe how THIS decision's own predicate was computed, not what held
    # on entry to it).
    let branchPrefixPc = p.pc
    # RFC-0005 S8i: a worklist of (next branch, path, negated earlier
    # conditions), since a drain can continue on more than one path.
    var states: seq[(int, Path, seq[Z3Bool])] = @[(0, p, newSeq[Z3Bool]())]
    var si = 0
    while si < states.len:
      if w.shouldStop: return exact(survivors)
      let (i, sp, accumNegated) = states[si]
      inc si
      if i >= stmt.branches.len:
        # RFC-fuzzer-nextgen G2: record this DETERMINED decision (an
        # ambiguous one returned before reaching here — every record is
        # therefore backed entirely by modelable conjuncts). No arm fired:
        # `observedTruth` is the conjunction of every branch's negated
        # condition (`mkAnd` on a singleton returns it unchanged, so this
        # collapses to `not condBool` for a plain if/else).
        w.branchTrace.add ConcolicBranchRecord(
          prefixPc: branchPrefixPc, observedTruth: mkAnd(accumNegated),
          armTaken: -1)
        let elsePath = forkPath(sp, sp.pc & accumNegated, sp.env)
        if stmt.elseBody != nil:
          survivors.add walk(stmt.elseBody, @[elsePath], w)
        else:
          survivors.add elsePath
        continue
      # The facts this condition's lowering and drain add (a closure call's
      # exit facts, a drained raise's negation): they must hold on the
      # replay, and they define a closure call's result in `condBool`.
      let factBase = sp.defectSurvivorPc.len
      let (condBool, conds) = evalCondSynced(sp, stmt.branches[i].cond, w)
      for dp in conds:
        if w.shouldStop: return exact(survivors)
        case followGuard(w, dp, condBool, factBase, wckIf)
        of foOffRun:
          # The pins contradict this path or its new facts (RFC-0016 W3-z
          # int6, `followGuard`): not the run, so not followed.
          continue
        of foOpen:
          if w.tailGate:
            # RFC-0016 W3-z R2/R6: the tail walk over-approximates the run (a
            # fresh symbol the pins do not fix), so an open branch is walked
            # both ways, as the explore walk does.
            let armPath = forkPath(dp, dp.pc & accumNegated & @[condBool], dp.env)
            survivors.add walk(stmt.branches[i].body, @[armPath], w)
            states.add (i + 1, dp, accumNegated & @[not condBool])
            continue
          # Walker-boundary concretization for control flow: `cond` isn't
          # pinned by the symbolicated draws alone. Graceful degrade — stop
          # following this path past the ambiguous branch rather than guess
          # (guessing could collect an UNSOUND constraint); counted, not
          # silently dropped — attributed to `wckIf` (R28).
          return exact(survivors & dp)
        of foTrue:
          # RFC-fuzzer-nextgen G2: the taken arm's own condition.
          w.branchTrace.add ConcolicBranchRecord(
            prefixPc: branchPrefixPc, observedTruth: condBool, armTaken: i)
          let armPath = forkPath(dp, dp.pc & accumNegated & @[condBool], dp.env)
          survivors.add walk(stmt.branches[i].body, @[armPath], w)
        of foFalse:
          states.add (i + 1, dp, accumNegated & @[not condBool])
  exact(survivors)

proc walkWhileFollowConcrete(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): Survivors =
  ## `wmFollowConcrete` counterpart to `isWhile`'s `wmExplore` k-unroll loop
  ## (below). RFC-fuzzer-nextgen R14: the explore loop forks BOTH cond=true
  ## (continue) and cond=false (exit) at EVERY unrolled iteration regardless
  ## of what the concrete replay actually did. For an N-iteration concrete
  ## loop that is up to `maxLoopUnwind` hypothetical exits explored, each a
  ## distinct surviving path — and every walker construct AFTER the loop
  ## (most importantly `isIf`'s `walkIfFollowConcrete`) then runs once per
  ## survivor, appending one MORE `w.branchTrace` record per bogus path. The
  ## measured benchmark: a 3-iteration while before one `if` produced
  ## `branchTrace.len == 6` (should be 1 — only the trailing if is a real
  ## decision) with `pcSatByConcreteInputs == false` (the union of every
  ## survivor's `pc`, most of them describing loop trajectories that never
  ## happened, is self-contradictory against `w.concreteEq`).
  ##
  ## Fix: reuse `concreteBranchOutcome` (the same scratch-solver mechanism
  ## `walkIfFollowConcrete` uses) at each iteration's guard. `some(true)` ->
  ## fold `cond` into `pc` and continue looping — NO cond=false exit fork at
  ## this iteration, because the concrete trace did not exit here.
  ## `some(false)` -> fold `not cond` into `pc` and stop — NO cond=true
  ## continuation, because the concrete trace did not continue here.
  ## `none` -> the same walker-boundary-concretization degrade
  ## `walkIfFollowConcrete` uses: stop following this path past the
  ## ambiguous guard (counted via `concolicAmbiguousBranches`, not silently
  ## dropped) rather than guess.
  ##
  ## `maxLoopUnwind` stays as a safety backstop — a genuinely concrete
  ## replay always terminates within the bound it actually ran under, so
  ## this should never bind in practice, but a malformed/adversarial
  ## `concreteEq` (or a caller-supplied trace that doesn't match the walked
  ## program) must not hang the walker. `w.loopStack` bookkeeping mirrors
  ## `wmExplore`'s exactly (break/continue channels, frame push/pop) —
  ## `defer` guarantees the pop runs on every exit path, including the
  ## early `return` on an ambiguous guard.
  var survivors: seq[Path] = @[]
  var active = paths
  w.loopStack.add initLoopFrame(w.exitClock,
                                hsDepth = w.frame.handlerStack.len)   # RFC-0005 S8m
  let frameIx = w.loopStack.high
  defer: discard w.loopStack.pop()
  # RFC-0010 B4: unlike every other ResourceBudget field, `unwind = 0` here
  # deliberately does NOT mean unlimited (`maxLoopUnwind`'s own doc comment,
  # smt/types.nim, already says ">= 1" — the false universal "0 = unlimited"
  # promise lived in the ResourceBudget umbrella comment, not here, and that
  # comment is the one that got corrected). This function's own doc above
  # already explains why: the bound is kept as a safety backstop against "a
  # malformed/adversarial `concreteEq` ... that must not hang the walker" —
  # i.e. even THIS concrete-replay side does not claim safety without some
  # finite bound. `0 ..< 0` (no iterations at all) is therefore the correct,
  # honest behavior for an explicit 0: exhausted immediately, same as any
  # other implausibly-tight budget — not silently reinterpreted as infinite.
  let unwind = w.settings.budget.maxLoopUnwind
  for iter in 0 ..< unwind:
    if w.shouldStop: return exact(survivors)
    if active.len == 0: break
    var nextActive: seq[Path]
    for p in active:
      # RFC-0016 review R7-4: the facts this guard's lowering and drain add
      # (a closure call's exit facts, a drained raise's negation), as
      # `walkIfFollowConcrete` reads them: they define a closure call's
      # result in `cond`, and a result the pins do not reach is undecided.
      let factBase = p.defectSurvivorPc.len
      let (cond, conds) = evalCondSynced(p, stmt.wcond, w)
      for dp in conds:
        # As `walkIfFollowConcrete` checks per continuation: each one walks
        # a body, so a stop request (budget, deadline) must not wait for the
        # rest of a drain's continuations (R8-3).
        if w.shouldStop: return exact(survivors)
        case followGuard(w, dp, cond, factBase, wckWhile)
        of foOffRun:
          # The pins contradict this path or its new facts (RFC-0016 W3-z
          # int6, `followGuard`): not the run, so it neither iterates nor
          # leaves the loop.
          continue
        of foOpen:
          if w.tailGate:
            # RFC-0016 W3-z R2/R6: an open guard on the tail walk forks both
            # ways, as the explore walk's unroll does.
            let truePath = forkPath(dp, dp.pc & @[cond], dp.env)
            let afterBody = walk(stmt.wbody, @[truePath], w)
            let cps = w.loopStack[frameIx].exits.continuePaths.takeAll()
            for cp in cps: nextActive.add cp
            for ap in afterBody: nextActive.add ap
            survivors.add forkPath(dp, dp.pc & @[not cond], dp.env)
            continue
          # Walker-boundary concretization for control flow — same shape as
          # `walkIfFollowConcrete`'s degrade: stop following THIS guard
          # rather than guess which way it went (guessing could collect an
          # UNSOUND constraint). Blunt whole-function stop (matches
          # `walkIfFollowConcrete`), not just a `continue` to the next
          # active path — `defer` still pops the loop frame. Attributed to
          # `wckWhile` (R28).
          return exact(survivors & dp)
        of foTrue:
          # Concretely continued this iteration: fold cond=true, walk the
          # body, feed its continuations into the NEXT iteration's active
          # set. No cond=false exit fork here — the trace did not exit.
          let truePath = forkPath(dp, dp.pc & @[cond], dp.env)
          let afterBody = walk(stmt.wbody, @[truePath], w)
          let cps = w.loopStack[frameIx].exits.continuePaths.takeAll()
          for cp in cps: nextActive.add cp
          for ap in afterBody: nextActive.add ap
        of foFalse:
          # Concretely exited this iteration: fold cond=false, no further
          # iterations for this path. No cond=true continuation here — the
          # trace did not continue.
          survivors.add forkPath(dp, dp.pc & @[not cond], dp.env)
    active = nextActive
  for bp in w.loopStack[frameIx].exits.breakPaths:
    survivors.add bp
  # Any paths still active after maxLoopUnwind iterations: the concrete
  # trace (or a malformed `concreteEq`) claims more iterations than the
  # bound allows. Mark uncertain — same classified degrade as `wmExplore`.
  if active.len > 0:
    # RFC-0005 S1: one `degrade` call records the error (run act, derived at
    # drain) and yields the token every survivor is forked with (path act).
    # RFC-0005 S6a: `beBudgetExhausted` is `dcFabricated` — each survivor
    # leaves the loop with the guard still TRUE on its pc (a continuation
    # the real trace never takes here: ⊤ on the path) and the iterations
    # past the bound are never walked (`{scIncomplete}` on the run).
    if not w.followCut:
      w.followCut = true
      w.followCutAt = w.branchTrace.len
    let d = w.degrade(beBudgetExhausted,
      "while-loop k-unroll budget exhausted (maxLoopUnwind=" &
           $unwind & ") while following a concrete replay that was still " &
           "continuing — the trace claims more iterations than the bound " &
           "allows (beBudgetExhausted)", cap = ckLoopUnwindFollow)
    for p in active:
      survivors.add forkPathTainted(p, p.pc, p.env, d)
  exact(survivors)

proc walkBlock(stmts: seq[IRStmt], paths: seq[Path], w: var WalkCtx): seq[Path] =
  result = paths
  for s in stmts:
    if w.shouldStop: return
    result = walk(s, result, w)
    if result.len == 0: return
    # Phase 14 cycle C3 (ADR-0004). Post-step frontier prune. A
    # `maxFrontierSize` of 0 keeps the unbounded baseline; any
    # positive value triggers highest-uncertainty-first eviction:
    # certain paths sort before uncertain (stable within each
    # tier), and the tail is dropped. Pruned paths' contribution
    # is reported as unknown via the classified `beBudgetExhaustedPrune`
    # degrade (RFC-0005 S1: its run coordinate is derived at drain; S6a
    # split it off `beBudgetExhausted`),
    # which cascades into the final `sxUnknown` verdict cached under
    # `:unk` (NOT `:unsat`).
    if w.settings.budget.maxFrontierSize > 0 and
       result.len > w.settings.budget.maxFrontierSize:
      var certain, uncertain: seq[Path]
      for p in result:
        if p.taint != {}: uncertain.add p
        else:             certain.add p
      var kept: seq[Path]
      for p in certain:
        if kept.len >= w.settings.budget.maxFrontierSize: break
        kept.add p
      for p in uncertain:
        if kept.len >= w.settings.budget.maxFrontierSize: break
        kept.add p
      # v64 (chapulin catalog #5(b), Invariant 7): classify the prune — a
      # bare `sawUnknown` here yielded sxUnknown with EMPTY errors.
      # RFC-0005 S1: HALT site (pruned paths are dropped, not forked), so
      # the token is discarded; the run act is the recorded error.
      # RFC-0005 S6a: split off `beBudgetExhausted` as
      # `beBudgetExhaustedPrune` (`dcOmitted`) — the eviction is a pure
      # under-approximation (`{scIncomplete}` on the run), and its empty path
      # coordinate is sound ONLY because this is a halt: the token must stay
      # discarded (pinned in `tsymex_rfc0005_s6a_budget.nim`).
      haltFrontier(w, result.len - kept.len, "")
      result = kept

func addrPartName(formal: string): string =
  ## RFC-0005 S8bu. The callee-frame local an `addr` actual into an
  ## address-taken variable is bound through (`bindVarLocs`): it is kept
  ## equal both to the variable's cell at the actual's path and to the cell
  ## the call's pointer names.
  "__addrPart#" & formal

proc bindVarLocs(calleePath: Path; callerEnv: Env;
                 callerCells: seq[AddrCellEntry]; callerFrame: int;
                 locs: seq[VarLoc]; varArgs, argVars: seq[(string, string)];
                 params: seq[string];
                 cells: var seq[AddrCellEntry];
                 elemShares: var seq[(string, string)];
                 w: var WalkCtx): string =
  ## RFC-0005 S8bs. A `var` actual that is a path into a routine's variable
  ## (`b.x`, `IRStmt.cVarLocs`) is passed by copy-in/copy-out, through a
  ## temporary written back after the call. That is Nim's semantics only
  ## while the callee cannot reach the location another way; once `addr b`
  ## is taken, a pointer it holds (a global, a capture, a heap field, a
  ## parameter) reaches it, and the write-back landed over the callee's
  ## write through the pointer (the S8bg exhibit's swapped verdicts). So,
  ## when the variable has a cell in the caller's frame, the formal is bound
  ## to the cell at that path (a `bound` entry, `AddrCellEntry`) and the
  ## callee's statements keep the two equal in its order, as for a `var`
  ## formal bound to a whole address-taken variable (`inheritAddrCells`).
  ## An element `s[i]` of a seq with element cells (S8be's `addr s[i]`) is
  ## bound to the cell `s[i]` has when `i` equals its index, else to a fresh
  ## one holding the element, as `walkElemCell` takes it.
  ##
  ## A by-value argument Nim passes by address (`VarLoc`'s `ptr`: a large
  ## or inheritable object, an array) reads the location as the callee's
  ## writes through a pointer leave it: its formal is bound the same way (it
  ## is never written by name). One Nim copies but whose seq or string
  ## memory the copy shares (`copy`) sees the writes to its elements: a seq
  ## with element cells has them under the formal's name too (`elemShares`,
  ## for `inheritElemCells`).
  ##
  ## RFC-0005 S8bu: an `addr lv` actual (`addr`: the cell for the call,
  ## named `temp` in the caller, is the argument; `argVars` pairs each
  ## formal with the caller variable its actual names) is a sub-cell of the
  ## variable's cell at that path: a local of the callee's frame
  ## (`addrPartName`) is bound both to the variable's cell at the path (a
  ## `bound` entry) and to the call's cell (an entry like `addr x`'s), so
  ## the frame keeps the two equal statement by statement
  ## (`syncAddrCells`), and a write through the formal is seen through the
  ## variable's pointer and the other way round. S8bs declined it: the
  ## cell for the call was a second copy of a location the callee could
  ## reach through the pointer, and its write-back after the call landed
  ## over a write through the pointer.
  ##
  ## Returns why the call declines, or "": a path the walk cannot follow,
  ## a variable that has both a cell and element cells, and a `copy` of an
  ## address-taken variable (a write through the pointer to an element is
  ## seen through the copy, an assignment of the whole is not).
  let ctx = w.z3
  for loc in locs:
    if loc.mode == "ref":
      # RFC-0005 S8ca: a `var` actual in a field of an object behind a ref
      # (`grb.x`, the ref read into `root` at the call) is passed by
      # reference: the formal is a `bound` entry on the object's cell at
      # the field path, the heaps `grb.x` reads and writes (`addrCellValue`),
      # so the body's direct access to the object and its writes through the
      # formal are one location. S8bh declined it (`touchMeetsOuter`).
      var formal = ""
      for (f, callerName) in varArgs:
        if callerName == loc.temp: formal = f
      if formal.len == 0 or not callerEnv.hasKey(loc.root) or
         callerEnv[loc.root].kind notin {svRef, svPtr}:
        return "a `var` argument in an object behind a ref is passed in a " &
               "shape the walk does not bind to the object's cell"
      let rv = callerEnv[loc.root]
      let (refAst, pointee) =
        if rv.kind == svRef: (rv.refAst, rv.refPointee)
        else: (rv.ptrAst, rv.ptrPointee)
      let cellName = varLocCellName(formal)
      let e: AddrCellEntry = (local: formal, cell: cellName, ty: pointee,
                              path: loc.path, ixs: @[], bound: true,
                              view: false, slot: "")
      if addrEntryValue(ctx, calleePath, e, refAst).isNone:
        return "a `var` argument in an object behind a ref is a part of " &
               "it the walk does not follow"
      var env2 = calleePath.env
      env2[cellName] = SymVal(kind: svPtr, ptrAst: refAst, ptrFamily: false,
                              ptrPointee: pointee)
      calleePath.env = env2
      cells.add e
      continue
    var rootCells: seq[AddrCellEntry]
    for c in callerCells:
      if c.local == loc.root and callerEnv.hasKey(c.cell) and
         callerEnv[c.cell].kind == svPtr:
        rootCells.add c
    var elems: seq[ElemCell]
    for e in calleePath.elemCells:
      if e.frame == callerFrame and e.root == loc.root and not e.dead:
        elems.add e
    if rootCells.len == 0 and elems.len == 0: continue
    let what = "`" & displayName(loc.root) & "`"
    var formal = ""
    if loc.mode == "addr":
      for (f, callerName) in argVars:
        if callerName == loc.temp: formal = f
      if formal.len == 0 or not callerEnv.hasKey(loc.temp) or
         callerEnv[loc.temp].kind != svPtr:
        return "an `addr` of a part of " & what & ", whose address is " &
               "taken, is passed in a shape the walk does not bind to its cell"
    elif loc.temp.startsWith("#"):
      let k = parseInt(loc.temp[1 .. ^1])
      if k < params.len: formal = params[k]
    else:
      for (f, callerName) in varArgs:
        if callerName == loc.temp: formal = f
    if formal.len == 0: continue
    if loc.mode == "copy":
      if rootCells.len == 1 and elems.len == 0 and "?" notin loc.path and
         "[" notin loc.path:
        # RFC-0005 S8bu: a seq whose address is taken, or a seq field of
        # such a variable, passed by value: the formal shares its memory.
        # It is bound to the cell as a `view` entry (`syncAddrCells`).
        let c = rootCells[0]
        let cellName = varLocCellName(formal)
        let e: AddrCellEntry = (local: formal, cell: cellName, ty: c.ty,
                                path: c.path & loc.path, ixs: c.ixs,
                                bound: true, view: true, slot: "")
        let v = addrEntryValue(ctx, calleePath, e, callerEnv[c.cell].ptrAst)
        if v.isSome and v.get.kind == svSeq:
          var env2 = calleePath.env
          env2[cellName] = callerEnv[c.cell]
          calleePath.env = env2
          cells.add e
          continue
        if v.isSome and v.get.kind == svString:
          # RFC-0005 S8ca: a by-value string shares the memory of the
          # variable. Nim writes a character in place unless that memory
          # is a literal's, which the first write copies (`StrBuf`): of a
          # literal's, the formal is a plain copy (no write through the
          # pointer reaches it); of the string's own, it is a `view` (an
          # in-place character write is seen, any other declines). S8bu
          # declined both, character writes being unmodelled.
          let byName =
            if c.path.len == 0 and loc.path.len == 0 and
               callerEnv.hasKey(c.local) and
               callerEnv[c.local].kind == svString and
               sameSymVal(callerEnv[c.local], v.get):
              callerEnv[c.local].strBuf
            else: sbUnknown
          if byName == sbLiteral: continue
          if byName == sbOwned and calleePath.env.hasKey(formal) and
             calleePath.env[formal].kind == svString:
            var env2 = calleePath.env
            env2[cellName] = callerEnv[c.cell]
            calleePath.env = env2
            cells.add e
            continue
          return "a by-value string shares the memory of " & what &
                 ", whose address is taken, and the walk does not know " &
                 "whether that memory is a literal's (which a write " &
                 "through the pointer copies first) or the string's own " &
                 "(which it writes in place)"
      if rootCells.len > 0:
        return "a by-value argument shares the memory of " & what &
               ", whose address is taken: a write through the pointer to " &
               "an element is seen through it, and an assignment of the " &
               "whole is not"
      if loc.path.len > 0:
        return "a by-value argument shares the memory of a part of " & what &
               ", which has element cells"
      elemShares.add (formal, loc.root)
      continue
    if "?" in loc.path:
      return "the `var` argument is a part of " & what & ", whose address " &
             "is taken, along a path the walk does not follow"
    if rootCells.len > 0 and elems.len > 0 or rootCells.len > 1:
      return "the `var` argument is a part of " & what & ", which has an " &
             "address cell and element cells, or two cells"
    var path: seq[string]
    var ixs: seq[SymVal]
    for st in loc.path:
      if st.startsWith("["):
        let nm = st[1 .. ^1]
        if not callerEnv.hasKey(nm):
          return "the index of the `var` argument into " & what &
                 " is not bound"
        path.add "["
        ixs.add callerEnv[nm]
      else:
        path.add st
    # RFC-0005 S8bu: an `addr` actual binds a local of its own, kept equal
    # to the call's cell too (below).
    let local = if loc.mode == "addr": addrPartName(formal) else: formal
    let cellName = varLocCellName(local)
    var env2 = calleePath.env
    template bindCallCell() =
      if loc.mode == "addr":
        # The call's cell holds the location's value; it is stored again
        # here as the local's term, so both cells read back as one term.
        let ptrV = callerEnv[loc.temp]
        discard addrCellStore(ctx, calleePath, ptrV.ptrPointee, ptrV.ptrAst,
                              env2[local])
        env2[addrCellName(local)] = ptrV
        cells.add (local: local, cell: addrCellName(local), ty: ptrV.ptrPointee,
                   path: @[], ixs: @[], bound: false, view: false, slot: "")
    if rootCells.len == 1:
      let c = rootCells[0]
      let e: AddrCellEntry = (local: local, cell: cellName, ty: c.ty,
                              path: c.path & path, ixs: c.ixs & ixs,
                              bound: true, view: false, slot: "")
      let v = addrEntryValue(ctx, calleePath, e, callerEnv[c.cell].ptrAst)
      if v.isNone:
        return "the `var` argument is a part of " & what & ", whose " &
               "address is taken, along a path the walk does not follow"
      env2[cellName] = callerEnv[c.cell]
      if loc.mode == "addr": env2[local] = v.get
      cells.add e
      bindCallCell()
      calleePath.env = env2
      continue
    # The element of a seq with element cells.
    if loc.mode == "addr":
      # RFC-0005 S8bu: the call's cell and the element's are in one heap,
      # and the element's is addressed through an `ite` a read cannot see
      # past a store to the other, so the frame cannot tell which of the
      # two a statement wrote.
      return "an `addr` of an element of " & what & ", which has element " &
             "cells, is a cell for the call in the element's own heap"
    if path != @["["] or not env2.hasKey(local):
      return "the `var` argument is a part of an element of " & what &
             ", which has element cells"
    let ty = elems[0].ty
    let idx = toZ3Int(ixs[0])
    let typeId = refPointeeTypeId(ty)
    let newRef = freshRef(ctx, allocRefSort(ctx, ty), typeId, calleePath)
    assertFreshness(ctx, calleePath, typeId, newRef, w.settings)
    discard addrCellStore(ctx, calleePath, ty, newRef, env2[formal])
    var addrAst = newRef
    for k in countdown(elems.high, 0):
      let same = idx == elems[k].idx
      addrAst = wrap[Z3AnyAst](ctx,
        checkedIte(ctx, same.raw, elems[k].refAst.raw, addrAst.raw))
    env2[cellName] = SymVal(kind: svPtr, ptrAst: addrAst, ptrFamily: true,
                            ptrPointee: ty)
    cells.add (local: local, cell: cellName, ty: ty, path: @[], ixs: @[],
               bound: true, view: false, slot: "")
    calleePath.env = env2
  ""

proc walkIndexArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isIndex` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # R14: `isIndex` is not a fork-every-arm construct the way `isIf`/
  # `isWhile` are — the in-bounds/present path is the ONLY continuation
  # `survivors` ever gets; the OOB/absent case is a discarded-result
  # `forkDefect` side channel (try/except routing + target-witness
  # search), narrowed per-mode inside `maybeForkDefect` rather than here.
  # Both arms below stay `discard`: there is no separate per-construct
  # behavior to select at THIS dispatch point.
  case w.mode
  of wmExplore: discard
  of wmFollowConcrete: discard
  var survivors: seq[Path]
  for p0 in paths:
    if w.shouldStop: return exact(@[])
    ## Drain-coverage audit: `stmt.ixArr` is a side-effect-free container
    ## expression. The parser A-normalises most container expressions to named
    ## bindings (iekVar) or field projections (iekField); both are pure (no
    ## closure/float→int sinks), so lowerLeafInExpr handles them without
    ## seed+drain.
    # RFC-0005 S8at: a `distinct` over a seq/array/Table is read through
    # its base (`seq[int](d)[i]` is the parser's identity, S8p), as every
    # scalar distinct already is (`ejectBase`).
    lowerAsReceiver = true   ## RFC-0005 S8bw: the element is the read
    let (arrSV0, p1) = lowerLeafInExpr(p0, stmt.ixArr)
    let arrSV = ejectBase(arrSV0)
    # RFC-0005 S8bw (item 2): an array global's element read observes the
    # one element (below); a seq, table or string global's read observes
    # its length or key set, so the whole receiver.
    let p =
      if arrSV.kind != svArray and
         globalReadPart(stmt.ixArr, arrSV).len > 0:
        forkPathTainted(p1, p1.pc, p1.env, w.degrade(
          unwrittenKind(globalReadPart(stmt.ixArr, arrSV)),
          unwrittenMsg(globalReadPart(stmt.ixArr, arrSV)),
          ub = unwrittenUb(globalReadPart(stmt.ixArr, arrSV))))
      else: p1
    # ---- Phase 5: Table[K, V] indexing ----
    if arrSV.kind == svTable:
      if not isBackedTableTy(arrSV.tabKeyTy, arrSV.tabValTy):
        # RFC-0005 S8u: an unbacked table is `allocateSym`'s declined,
        # inert placeholder; its key must not be lowered against the key
        # prototype below (`coerceIntLit` raised on an int literal, a
        # `weInternalWalkerFault`). RFC-0005 S8ar: any unbacked key or
        # value type (`isBackedTableTy`; was a non-string key, and a
        # second arm for the value).
        let d =
          if not isTableKeyTy(arrSV.tabKeyTy):
            w.degrade(seUnsupportedTableKeyType,
              "at index: " & tableKeyDeclineMsg(arrSV.tabKeyTy))
          else:
            w.degrade(seUnsupportedTableValType,
              "at index: " & tableValDeclineMsg(arrSV.tabValTy))
        survivors.add forkPathTainted(p, p.pc, declinedIndexEnv(p.env, stmt, arrSV.tabValTy), d)
        continue
      # RFC-0005 S8ar: every backed key and value type (`tabKeyTerm` /
      # `tabValOf`); was a string key and a 64-bit cell value.
      # RFC-0005 review R1-04: the key is lowered ON this path
      # (`lowerInExpr`), so an in-band decline in it (an unwritten global's
      # `feGlobalHavoc`) taints this path rather than whichever lowering
      # drains next, and its raise forks are taken before the lookup.
      let (keySV, pk) = lowerInExpr(p, stmt.ixIdx, w,
                                    seqElemLitProto(arrSV.tabKeyTy))
      for p in drainScalarRaiseForks(pk, w):
        let kOpt = tabKeyTerm(keySV, arrSV.tabKeyTy)   ## RFC-0005 S8f: noted
        if kOpt.isNone:
          let d = w.degrade(feUnsupportedOp,
            "Table index: key lowered to " & plainEnglishSymValKind(keySV.kind) &
            " — expected a " & $arrSV.tabKeyTy & " (feUnsupportedOp)")
          survivors.add forkPathTainted(p, p.pc, declinedIndexEnv(p.env, stmt, arrSV.tabValTy), d)
          continue
        let ctx = arrSV.tabSize.ctx
        let k = kOpt.get
        # Nim's `Table[K, V].[]` raises `KeyError` when the key is
        # absent. To preserve that semantics in symex we add a
        # presence constraint to the surviving path.
        var presentCond = wrap[Z3Bool](ctx,
          checkedSelect(ctx, arrSV.tabPresentRaw.raw, k.raw))
        let nanOpt = tabKeyNaN(keySV, arrSV.tabKeyTy)   ## RFC-0005 S8at
        if nanOpt.isSome: presentCond = presentCond and not nanOpt.get
        # RFC-0005 S8at: the absent key RAISES (`KeyError`), routed to a
        # handler as any raise is. It only narrowed the surviving path, so
        # `try: t[k] except KeyError: ...` never ran its handler: a false
        # `sxUnsat` for a target in it, and no `sxRaised` at the boundary.
        maybeForkDefect(p, not presentCond, "KeyError", none(string), w)
        # RFC-0005 S8z: read back at the value type's width.
        let tableVal = tabValAt(ctx, arrSV, k.raw)
        var newEnv = p.env
        newEnv[stmt.ixRetName] = tableVal
        # Issue #163 wiring-audit W2 (Table-value sibling): a
        # `Table[string, range[lo..hi]]` value read here has the exact
        # same reach gap as a seq element — see the `isIndex`/svSeq arm's
        # own comment just above for the full rationale. Review R11: routed
        # through `rangeCondsIfNeeded`. RFC-0005 S8ar: a string value is a
        # string of bytes (`seqStrElemConds`, a free string's fact).
        let tblRangeConds = readRangeConds(tableVal, arrSV.tabValTy) &
                            seqStrElemConds(tableVal)
        survivors.add forkPath(p, p.pc & @[presentCond] & tblRangeConds, newEnv)
      continue
    # ---- Phase 5: dynamic seq[T] indexing ----
    if arrSV.kind == svSeq:
      if arrSV.isUnsupportedFieldPlaceholder: # [placeholder-audited]
        # RFC-chapulin-hardening B7r2 (walker v88): a bare local/param/
        # call-return `seq[T]` (T structurally unbacked, e.g. itTuple)
        # allocated via the GENERALIZED Bug-#2 placeholder
        # (`allocateSym`'s `itSeq` arm) is indexed here — an ACTUAL READ
        # of its content. `dsl_parser.nim`'s `nnkDotExpr` field-read
        # arms intercept a declared-FIELD placeholder read at PARSE time
        # (before an `isIndex` node can even be built over it); a bare
        # value has no such static field-access site, so this is the
        # analogous WALK-TIME interception (SND-1 taint-and-continue)
        # for that case — never `select()` from the placeholder's
        # arbitrary-sort (`Z3Int -> Z3Bool`) inert backing array, which
        # would misrepresent (or, for a non-bool real element type,
        # `wrap[]`-crash on) content that was never truly modeled.
        # R1 (walker v89) Q2 fix: this decline previously omitted
        # `stmt.ixLoc` even though the parser already populates it
        # (`parseSeqBracketAccess`'s index arm passes `siteLoc(n)` into
        # `mkIndexStmt`) — the `<loc>: ` prefix idiom exists 60 lines below
        # in this SAME handler (the non-seq receiver-kind decline). Now
        # shares `placeholderReadDeclineMsg` with the in-`lower()` half
        # (`iekSeqLen`/`iekSeqSlice`) so every placeholder-read decline
        # reports the identical message shape. N47-followup (walker v110):
        # kind now derives from `arrSV` too (`placeholderReadDeclineKind`)
        # — a bare-value placeholder still reports `seNestedSeqUnsupported`
        # unchanged, but a receiver rebound by an OPERATION-level decline
        # (e.g. `iekSeqAdd`'s width/elem-support gap) reports THAT decline's
        # own kind instead of the misleading nested-seq claim.
        let d = w.degrade(placeholderReadDeclineKind(arrSV),
          placeholderReadDeclineMsg(arrSV, stmt.ixLoc, "index read"))
        # RFC-0005 S8ba: the read's temporary is bound on the tainted
        # path. Left unbound, its next read was recorded as an unmodelled
        # global (`'__sym_idx_N' is read where ...`).
        survivors.add forkPathTainted(p, p.pc,
          declinedIndexEnv(p.env, stmt, stmt.ixElemTy), d)
        continue
      # Seq index is Z3Int. Lower with an svInt proto for literals;
      # for env-resident BV-typed Nim ints we coerce via bv2int.
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      # CR-9(c) D5 note: reconcileInt is NOT applied here — the intProto
      # already steers index literals to svInt, and toZ3Int(idxSV) handles
      # the BV-typed env var → Z3Int coercion (bv2int). No cross-rep issue.
      let intProto = SymVal(kind: svInt, zi: mkInt(0))
      let (idxSV, idxP) = lowerInExpr(p, stmt.ixIdx, w, some(intProto))
      ## R1 (Invariant-3 soundness fix): `stmt.ixIdx` may itself deposit
      ## scalar-raise-fork predicates (e.g. a `div`/`parseInt` sub-expr).
      ## Undrained, those were silently discarded — no raise fork, no
      ## bounds narrowing. Drain and thread the survivor(s) forward
      ## through the seq-bounds check below, mirroring `isLet`/`isAssign`.
      for cp in drainScalarRaiseForks(idxP, w):
        let lenZi = arrSV.seqLen # [placeholder-audited]
        let idxZi = toZ3Int(idxSV)
        let inLoCond = idxZi >= mkInt(0)
        let inHiCond = idxZi <  lenZi
        ## Phase 16 D1a unconditional under `wmExplore`; R14 narrows the
        ## `wmFollowConcrete` case — see `maybeForkDefect`'s doc comment.
        indexOobSide(cp, not (inLoCond and inHiCond), false, stmt.ixLoc, w)
        # Bind retName = select(seqData, idx) at element type
        var indexed: SymVal
        # Issue #163 wiring-audit W2: a `seq[range[lo..hi]]` element read
        # here NEVER passed through `allocateSym`'s `itInt` arm (the ONE
        # `ty.hasRange` consumer in the runtime) — the backing store is a
        # raw Z3 array (`allocateSeqDataRaw`), not a per-element
        # allocation. Assert the SAME two bounds `bvRangeConds` deposits
        # at allocation time here instead, at the READ site, into THIS
        # survivor's own pc (mirroring `inLoCond`/`inHiCond` below).
        # Design choice (not re-derived, see the #163 wiring-audit
        # handoff): assert on READ, not by universally quantifying the
        # backing array — a `forall` over the array would be exact but
        # drags a quantifier into every seq query, against this engine's
        # lazy-materialisation style. Consequence, documented rather than
        # silently accepted: an element that is never read stays
        # unconstrained in-solver. Sound for VERDICTS (an unread element
        # cannot affect one), but NOT for witnesses — `extractSeqElements`
        # below clamps the reported value for exactly that reason.
        var rangeConds: seq[Z3Bool]
        if not isBackedSeqElemTy(arrSV.seqElemTy):
          # RFC-0016 K9c follow-up: an element the model does not back (the
          # dispatch below raised for it).
          survivors.add unbackedElemSurvivor(cp, cp.pc & @[inLoCond, inHiCond],
            declinedIndexEnv(cp.env, stmt, stmt.ixElemTy), arrSV, stmt.ixLoc,
            "an element read", w)
          continue
        if isTreeSeqElemTy(arrSV.seqElemTy):
          # RFC-0005 S8bc: a tree element, rebuilt from every data array
          # (`seqElemAt`). Its well-formedness is asserted at the read, as
          # W2 asserts a scalar element's range: a string part is bytes, a
          # nested seq's length and a table's size are not negative (and a
          # table's size is tied to its keys), a nested scalar part is in
          # its declared range, a case object's discriminator in its
          # domain. Not the `[0, 1024]` bound of an INPUT seq (`allocateSym`):
          # an element the body stored may hold a longer seq.
          indexed = seqElemAt(arrSV, idxZi)
          rangeConds = svCellWf(indexed, arrSV.seqElemTy, true, bounded = false)
          var newEnv = cp.env
          newEnv[stmt.ixRetName] = indexed
          survivors.add forkPath(cp, cp.pc & @[inLoCond, inHiCond] & rangeConds,
                                 newEnv)
          continue
        case arrSV.seqElemTy.kind
        of itInt:
          case arrSV.seqElemTy.width
          of 8:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[8]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          of 16:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[16]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          of 32:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[32]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          of 64:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          else:
            raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (isVariantReassign's discriminator is always BV/Z3Int-allocated)]
              "isIndex/seq: unsupported elem width " & $arrSV.seqElemTy.width)
          # Review R11: routed through `rangeCondsIfNeeded`; RFC-0016
          # INT-85: a slot the program zeroed is not bounded (`readRangeConds`).
          rangeConds = readRangeConds(indexed, arrSV.seqElemTy)
        of itBool:
          let typed = wrap[Z3Array[Z3Int, Z3Bool]](
            arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
          indexed = ofBool(select(typed, idxZi))
        of itFloat32:   ## Phase 15 F9b
          let typed = wrap[Z3Array[Z3Int, Z3Float32]](
            arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
          indexed = SymVal(kind: svFloat32, fp32: select(typed, idxZi))
          rangeConds = readRangeConds(indexed, arrSV.seqElemTy)   # INT-77, INT-85
        of itFloat64:   ## Phase 15 F9b
          let typed = wrap[Z3Array[Z3Int, Z3Float64]](
            arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
          indexed = SymVal(kind: svFloat64, fp64: select(typed, idxZi))
          rangeConds = readRangeConds(indexed, arrSV.seqElemTy)   # INT-77, INT-85
        of itString:   ## Phase 15 S5: seq[string] element (e.g. split result)
          let typed = wrap[Z3Array[Z3Int, Z3String]](
            arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw) # [placeholder-audited]
          indexed = SymVal(kind: svString, str: select(typed, idxZi))
          # RFC-0005 S8ar: an element of a free `seq[string]` is a Nim
          # string -- bytes (ADR-0006). Asserted at the read, as W2 does
          # an element's range: a free backing array holds any Z3 string.
          rangeConds = seqStrElemConds(indexed)
        of itRef, itPtr:   ## Phase 15 R3 (ADR-0010): seq[ref T] / seq[ptr T] elem.
          # The element is an abstract `Ref_T` address (the backing array is a
          # raw `Z3Array[Z3Int, Ref_T]`). The select goes through raw FFI
          # (`Z3_mk_select` over `seqDataRaw` at the index) because `Ref_T` is a
          # RUNTIME uninterpreted sort the typed `select` can't express. The
          # result is an svRef/svPtr — a later `[]` (isDeref) derefs it through
          # `path.heaps[T]`. GROUND select; NO quantifier (the G4 hang lesson).
          let ctx = w.z3
          let isPtr = arrSV.seqElemTy.kind == itPtr
          let pointee = if isPtr: arrSV.seqElemTy.ptrPointeeTy
                        else: arrSV.seqElemTy.refPointeeTy
          let elemRaw = checkedSelect(ctx, arrSV.seqDataRaw.raw, idxZi.raw) # [placeholder-audited]
          let elemAny = wrap[Z3AnyAst](ctx, elemRaw)
          # RFC-0005 S8ar: the element is as many heap steps from a root
          # as the cell the seq was read from (`seqSteps`).
          if isPtr:
            indexed = SymVal(kind: svPtr, ptrAst: elemAny,
                             ptrFamily: true, ptrPointee: pointee,
                             ptrSteps: arrSV.seqSteps)
          else:
            indexed = SymVal(kind: svRef, refAst: elemAny, refPointee: pointee,
                             refSteps: arrSV.seqSteps)
        else:
          raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (see isVariantReassign above)]
            "isIndex/seq: unsupported elem kind " & $arrSV.seqElemTy.kind)
        var newEnv = cp.env
        # RFC-0005 S8ba: a distinct element is re-boxed (its cell holds
        # the base, `seqCellTy`).
        newEnv[stmt.ixRetName] = reboxSeqCell(stmt.ixElemTy, indexed)
        let inPc = cp.pc & @[inLoCond, inHiCond] & rangeConds
        # RFC-0005 S8bq: an element assignment's bounds check reads
        # nothing (`boundsCheckSynthWord`).
        let unwritten =
          if stmt.ixRetName.startsWith("__sym_" & boundsCheckSynthWord & "_"):
            none(Z3Bool)
          else: uninitReadCond(arrSV, idxZi)
        if unwritten.isSome:
          # RFC-0005 S8bq: the read is exact where the element was
          # written, and a fresh value (tainted) where it was not. The
          # facts select between two models of ONE execution, as
          # `drainConvFloatToIntFresh`'s do, so they ride in
          # `defectSurvivorPc`.
          if $simplify(unwritten.get) != "true":
            let written = forkPath(cp, inPc, newEnv)
            written.defectSurvivorPc.add not unwritten.get
            survivors.add written
          let d = w.degrade(uninitReadKind, uninitReadMsg)
          let fresh = forkPathTainted(cp, inPc, newEnv, d)
          fresh.defectSurvivorPc.add unwritten.get
          survivors.add fresh
        else:
          survivors.add forkPath(cp, inPc, newEnv)
      continue
    # ---- Round-6 B1 (ADR-0028 Leg 1): string-backed seq[byte] index READ.
    # A `data[i]` reaching here with an `svString` receiver means the
    # receiver was allocated string-backed (B1a) but the CONSUMING op's
    # IR is the ordinary `isIndex` node — e.g. a call-chain hop whose OWN
    # parse never routed the dispatch through `iekStrAt` (no qualifying
    # scan loop over ITS OWN same-named parameter), yet the VALUE flowing
    # in at THIS point is the caller's string-backed allocation. Route
    # through the SAME OOB-probe + read logic `iekStrAt`'s lowering uses
    # (SND-4 mirror, `runtime_strings.nim`) so the read stays TOTAL and
    # actually decides — not merely declines.
    if arrSV.kind == svString:
      let intProto = SymVal(kind: svInt, zi: mkInt(0))
      let (idxSV, idxP) = lowerInExpr(p, stmt.ixIdx, w, some(intProto))
      for cp in drainScalarRaiseForks(idxP, w):
        let idxZi = toZ3Int(idxSV)
        let strLenZi = len(arrSV.str)
        let inLoCond = idxZi >= mkInt(0)
        let inHiCond = idxZi <  strLenZi
        if boundsUnchecked():
          decideUndefined(cp, uncheckedIndexUb(),
                          not (inLoCond and inHiCond),
                          uncheckedIndexSite(stmt.ixLoc), w)
        else:
          discard forkDefect(cp, not (inLoCond and inHiCond),
                             "IndexDefect", none(string), w)
        let code = toCode(at(arrSV.str, idxZi))
        var newEnv = cp.env
        newEnv[stmt.ixRetName] = liftBV(intToBv[8](code, Z3BitVec[8]), false)
        survivors.add forkPath(cp, cp.pc & @[inLoCond, inHiCond], newEnv)
      continue
    # ---- Phase 4: static array (the existing path) ----
    if arrSV.kind != svArray:
      # Round-6 B1 backstop: was a hard `doAssert` (a live crash gap),
      # then Round-6 SND-4 mirror: a raw `raise (ref
      # SymexClassifiedDegradeError)`. Round-6 N36 (walker v101): THAT
      # raise was itself still the ADR-0023/SND-3 C-backend goto-exception
      # hazard — reached from inside this `walkBlock`-reachable `for p in
      # paths` loop, identical shape to N31's `iekStrSubstr` fix. In-band
      # walk-level degrade instead, matching this SAME `isIndex` arm's
      # `isUnsupportedFieldPlaceholder`/Table-value-type siblings above.
      let locPrefix = if stmt.ixLoc.len > 0: stmt.ixLoc & ": " else: ""
      let d = w.degrade(feUnsupportedExprKind,
        locPrefix & "isIndex: unsupported receiver kind " &
             plainEnglishSymValKind(arrSV.kind) & " (expected array/seq/table/string) — " &
             "degraded to sxUnknown (feUnsupportedExprKind)")
      survivors.add forkPathTainted(p, p.pc,   # RFC-0005 S8ba: bound
        declinedIndexEnv(p.env, stmt, stmt.ixElemTy), d)
      continue
    let n = arrSV.arrElems.len
    ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
    let (idxSVraw, idxP) = lowerInExpr(p, stmt.ixIdx, w)
    # RFC-0005 S8am: `array[bool, T]`'s index (item 6) -- see
    # `coerceArrayBoolIndex`'s own doc.
    let idxSV = coerceArrayBoolIndex(idxSVraw)
    ## R1 (Invariant-3 soundness fix): `stmt.ixIdx` may itself deposit
    ## scalar-raise-fork predicates. Undrained, those were silently
    ## discarded — no raise fork, no bounds narrowing. Drain and thread
    ## the survivor(s) forward, mirroring `isLet`/`isAssign`.
    for cp in drainScalarRaiseForks(idxP, w):
      # Build the in-bounds & OOB Z3 conditions. RFC-0005 S8z: over the
      # array's index range `ixLo .. ixLo + n - 1` (`array[1..3, T]`), not
      # `0 ..< n`; element `k` is Nim's index `ixLo + k`.
      let (inLoCond, inHiCond) = arrayIndexConds(idxSV, stmt.ixLo, n)
      # OOB defect fork — Phase 16 D1a unconditional under `wmExplore`;
      # R14 narrows the `wmFollowConcrete` case — see `maybeForkDefect`.
      # RFC-0016 PRC-07: a site Nim emits unchecked (`ixUnchecked`, or the
      # build's `boundChecks: off`) halts its out-of-array side.
      indexOobSide(cp, not (inLoCond and inHiCond), stmt.ixUnchecked,
                   stmt.ixLoc, w)
      # RFC-0005 S8ct: an index that may name more positions than a term walk
      # takes reads a fresh value instead (`arrayAccessTooWide`).
      if arrayAccessTooWide(idxSV, stmt.ixLo, n):
        let locPrefix = if stmt.ixLoc.len > 0: stmt.ixLoc & ": " else: ""
        let dw = w.degrade(feUnsupportedOpHavoc,
          locPrefix & "isIndex: an array of " & $n & " elements at a " &
          "symbolic index that may name more than termWalkMaxDepth (" &
          $termWalkMaxDepth & ") of them; the element read is a fresh value " &
          "(feUnsupportedOpHavoc)", cap = ckTermWalkRead)
        survivors.add forkPathTainted(cp, cp.pc & @[inLoCond, inHiCond],
          declinedIndexEnv(cp.env, stmt, stmt.ixElemTy), dw)
        continue
      # In-bounds path continues with binding; build the value via ite.
      var indexed = arraySelect(arrSV.arrElems, idxSV, stmt.ixLo)
      var unwrittenPart =
        if stmt.ixCheckOnly: ""
        else: globalReadPart(stmt.ixArr, indexed, simplified = true)
      # RFC-0005 S8bz (item 3): an aggregate element is not read by itself;
      # the access on its temporary picks the part (`glWatched`). A part
      # the solver shows independent of every unwritten leaf is that part.
      if unwrittenPart.len > 0 and heapTreeTy(tyOf(indexed)) and
         heapCompoundTy(tyOf(indexed)):
        indexed = unwrittenLeafSplit(w.z3, cp, indexed,
                                     [inLoCond, inHiCond], w.settings)
        glWatched.incl stmt.ixRetName
        unwrittenPart = ""
      # RFC-0005 S6b: `iteSV` is called here DIRECTLY (no `lower()`
      # wrapper), so a merge degrade's pending taint (`allocDegrade` /
      # `degradeAlloc`) would otherwise be drained by whatever `lower()`
      # runs NEXT -- on this path in practice, on a sibling in principle
      # (the race `iteSV`'s group-arm note describes). Its fresh-symbol
      # sites are `dcFreshSymbol` now, so the taint must land on the path
      # that binds the merged value: drain it here, by construction.
      let cpM = drainPendingLowerEffects(cp)
      var newEnv = cpM.env
      newEnv[stmt.ixRetName] = indexed
      if unwrittenPart.len > 0 and
         (stmt.ixIdx.kind == iekIntLit or
          not unwrittenIndependent(w.z3, cpM, indexed,
                                   [inLoCond, inHiCond], w.settings)):
        survivors.add forkPathTainted(cpM, cpM.pc & @[inLoCond, inHiCond],
          newEnv, w.degrade(unwrittenKind(unwrittenPart),
                            unwrittenMsg(unwrittenPart),
                            ub = unwrittenUb(unwrittenPart)))
      else:
        survivors.add forkPath(cpM, cpM.pc & @[inLoCond, inHiCond], newEnv)
  exact(survivors)

proc walkIndexAssignArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isIndexAssign` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # N14 (RFC-chapulin-hardening bucket-2): `xs[idx] = v` element ASSIGNMENT.
  # Mirrors `isIndex`'s own OOB fork exactly (same `0 <= idx < len`
  # predicate, same unconditional `IndexDefect` fork per Phase 16 D1a) but
  # REBINDS `stmt.iaRecvName` to a new `svSeq` (`store(old.data, idx, v)`,
  # via `storeSeqElem` — the SAME helper `lowerSeqLit`/HOF `.map` already
  # use for construction) instead of binding a fresh read result.
  var survivors: seq[Path]
  for p0 in paths:
    if w.shouldStop: return exact(@[])
    # The parse site (dsl_parser.nim's `nnkAsgn` arm) only ever emits this
    # statement for a bare `nnkSym` receiver already classified `itSeq`.
    # RFC-0005 batch 6: read through `recvValue`, so a global the walk
    # has not written is its entry value (was a `KeyError`: the path was
    # dropped, a false `sxUnsat`).
    let (recvSV, p) = recvValue(p0, stmt.iaRecvName, w)
    if recvSV.kind == svArray and recvSV.arrElems.len > 0:
      # RFC-0005 S8z: `a[i] = v` on an array at a symbolic index (it was
      # `feUnsupportedStmtKind`). The same `IndexDefect` fork as `isIndex`,
      # over the array's own index range (`iaLo`), then the receiver is
      # rebound to the array with every position `k` replaced by
      # `ite(i == iaLo + k, v, old[k])` (`arrayStore`) -- the per-element
      # form of a Z3 `store`, since `svArray` keeps one value per element.
      let n = recvSV.arrElems.len
      let (idxSVraw, idxP) = lowerInExpr(p, stmt.iaIdx, w)
      # RFC-0005 S8am: `array[bool, T]`'s index (item 6) -- see
      # `coerceArrayBoolIndex`'s own doc.
      let idxSV = coerceArrayBoolIndex(idxSVraw)
      for cp in drainScalarRaiseForks(idxP, w):
        let (inLoCond, inHiCond) = arrayIndexConds(idxSV, stmt.iaLo, n)
        indexOobSide(cp, not (inLoCond and inHiCond), stmt.iaUnchecked,
                     stmt.iaLoc, w)
        let elemTy = recvSV.arrElemTy
        let (valSV, valP) = lowerInExpr(cp, stmt.iaVal, w,
                                        seqElemLitProto(elemTy))
        for vp in drainScalarRaiseForks(valP, w):
          let aligned = alignIntKind(valSV, recvSV.arrElems[0].kind)
          if aligned.isSome and arrayAccessTooWide(idxSV, stmt.iaLo, n):
            # RFC-0005 S8ct: see `arrayAccessTooWide`. The write is dropped, as
            # below: a stale env (`feUnsupportedStmtKind`), never an sxUnsat.
            let locPrefix = if stmt.iaLoc.len > 0: stmt.iaLoc & ": " else: ""
            let dw = w.degrade(feUnsupportedStmtKind,
              locPrefix & "isIndexAssign: an array of " & $n & " elements at " &
              "a symbolic index that may name more than termWalkMaxDepth (" &
              $termWalkMaxDepth & ") of them; the write is dropped",
              cap = ckTermWalkWrite)
            survivors.add forkPathTainted(vp, vp.pc & @[inLoCond, inHiCond],
                                          vp.env, dw)
            continue
          if aligned.isNone:
            # The write is dropped (the array keeps its old element): a
            # stale env, so `feUnsupportedStmtKind` (dcSubstituted), which
            # licenses no sxUnsat -- never the fresh class.
            let locPrefix = if stmt.iaLoc.len > 0: stmt.iaLoc & ": " else: ""
            let d = w.degrade(feUnsupportedStmtKind,
              locPrefix & "isIndexAssign: array element write of " &
                   plainEnglishSymValKind(valSV.kind) & " over " &
                   plainEnglishSymValKind(recvSV.arrElems[0].kind) &
                   " not modelled; the write is dropped")
            survivors.add forkPathTainted(vp, vp.pc & @[inLoCond, inHiCond],
                                          vp.env, d)
            continue
          let vpM = drainPendingLowerEffects(vp)
          var newEnv = vpM.env
          newEnv[stmt.iaRecvName] = SymVal(kind: svArray,
            arrElems: arrayStore(recvSV.arrElems, idxSV, stmt.iaLo, aligned.get),
            arrElemTy: elemTy)
          survivors.add forkPath(vpM, vpM.pc & @[inLoCond, inHiCond], newEnv)
      continue
    if recvSV.kind != svSeq:
      # Defense in depth (W2b precedent, `iekSeqAdd`'s own kind-mismatch
      # arm): SHOULD be unreachable given the parse-time itSeq gate, but a
      # representation-mismatch route (e.g. a string-backed receiver, per
      # the B1a classifier) is not machine-checked closed. Decline in-band
      # rather than a raw `doAssert` crash — same idiom as `isIndex`'s own
      # non-array/seq/table/string receiver-kind decline immediately above.
      let locPrefix = if stmt.iaLoc.len > 0: stmt.iaLoc & ": " else: ""
      let d = w.degrade(feUnsupportedExprKind,
        locPrefix & "isIndexAssign: receiver lowered to " &
             plainEnglishSymValKind(recvSV.kind) &
             " — expected svSeq (feUnsupportedExprKind)")
      survivors.add forkPathTainted(p, p.pc, p.env, d)
      continue
    if recvSV.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # A bare/field-sourced placeholder seq (structurally-unbacked elem
      # type, Bug #2/B7r2 machinery) is being written through. Mirrors the
      # `isIndex` read-side placeholder decline immediately above (same
      # shared `placeholderReadDeclineKind`/`placeholderReadDeclineMsg`
      # chokepoint) — never `storeSeqElem` into the placeholder's inert
      # arbitrary-sort backing array.
      let d = w.degrade(placeholderReadDeclineKind(recvSV),
        placeholderReadDeclineMsg(recvSV, stmt.iaLoc, "mutation (index assign)"))
      survivors.add forkPathTainted(p, p.pc, p.env, d)
      continue
    # RFC-0005 S8cd: the bounds check reads the length; the elements are
    # untouched (`recvValue`).
    let lenDecline = observeRecvPart(p, SymVal(kind: svInt, zi: recvSV.seqLen), w) # [placeholder-audited]
    if lenDecline.isSome:
      survivors.add forkPathTainted(p, p.pc, p.env, lenDecline.get)
      continue
    let intProto = SymVal(kind: svInt, zi: mkInt(0))
    let (idxSV, idxP) = lowerInExpr(p, stmt.iaIdx, w, some(intProto))
    for cp in drainScalarRaiseForks(idxP, w):
      let lenZi = recvSV.seqLen # [placeholder-audited]
      let idxZi = toZ3Int(idxSV)
      let inLoCond = idxZi >= mkInt(0)
      let inHiCond = idxZi <  lenZi
      indexOobSide(cp, not (inLoCond and inHiCond), false, stmt.iaLoc, w)
      # In-bounds survivor: lower the RHS with a proto matching the
      # declared element type (`seqElemLitProto`), then `storeSeqElem` —
      # `isBackedSeqElemTy` (checked by construction: any placeholder
      # receiver already declined above) guarantees `recvSV.seqElemTy` is
      # one of `storeSeqElem`'s own covered kinds.
      let valProto = seqElemLitProto(recvSV.seqElemTy)
      let (valSV, valP) = lowerInExpr(cp, stmt.iaVal, w, valProto)
      for vp in drainScalarRaiseForks(valP, w):
        if not isBackedSeqElemTy(recvSV.seqElemTy):
          # RFC-0016 K9c follow-up: no array to store into (`storeSeqElem`
          # raised). The value is lowered first, so its raises are kept; on
          # a reachable in-bounds side the receiver becomes a placeholder,
          # so every later read of it declines too.
          var envD = vp.env
          var scratch: seq[Z3Bool]
          envD[stmt.iaRecvName] = allocateSym(
            tUnsupportedFieldSeq(recvSV.seqElemTy, "an element stored into a " &
              "seq of an element type the model does not back"),
            freshDegradeName("__seqAssignUnbacked"), scratch)
          survivors.add unbackedElemSurvivor(vp, vp.pc & @[inLoCond, inHiCond],
            envD, recvSV, stmt.iaLoc, "an element store", w)
          continue
        # RFC-0005 S8bc: every leaf of a tree element (`seqStoreArrs`); a
        # value that does not fit declines on this path.
        let storedOpt = seqStoreArrs(recvSV, idxZi, valSV)
        if storedOpt.isNone:
          let kind = seqStoreDeclineKind(recvSV.seqElemTy)
          let locPrefix = if stmt.iaLoc.len > 0: stmt.iaLoc & ": " else: ""
          let d = w.degrade(kind, locPrefix &
            "isIndexAssign: a " & plainEnglishSymValKind(valSV.kind) &
            " that does not fit an element of the seq (" &
            $recvSV.seqElemTy & ") (" & $kind & ")")
          var envD = vp.env
          var scratch: seq[Z3Bool]
          envD[stmt.iaRecvName] = allocateSym(
            tUnsupportedFieldSeq(recvSV.seqElemTy, "a store that does not " &
              "fit the element type", kind = kind),
            freshDegradeName("__seqAssignDecline"), scratch)
          survivors.add forkPathTainted(vp,
            vp.pc & @[inLoCond, inHiCond], envD, d)
          continue
        # N27 audit (item 1, round-6 fix round 3): rebinding the receiver
        # after a successful store. `recvSV` was already declined above
        # (this arm's own `isUnsupportedFieldPlaceholder` check at the top
        # of the `for p in paths` loop, `continue`d on the placeholder
        # branch) and is never reassigned before this point — the
        # `.seqLen` read below is reached only on the non-placeholder path.
        var newEnv = vp.env
        newEnv[stmt.iaRecvName] = mkSeqSV(recvSV.seqLen, storedOpt.get, # [placeholder-audited]
          recvSV.seqElemTy)
        survivors.add forkPath(vp, vp.pc & @[inLoCond, inHiCond], newEnv)
  exact(survivors)

proc walkSeqPopArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isSeqPop` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # N14 (RFC-chapulin-hardening bucket-2): `retName := recvName.pop()`.
  # `result = data[len-1]; len' = len-1` — Nim's real `pop()` semantics
  # (verified against the stdlib doc: "Returns the last item of `s` and
  # removes it from `s`. Raises IndexDefect if `s` is empty."). The
  # backing DATA array is left UNCHANGED (no store): every read of the
  # shrunk seq goes through a bound check against the NEW (smaller)
  # `seqLen`, so the stale value at the old last slot is permanently
  # unreachable — the exact same "leave it, it's inert" argument `del`'s
  # own doc comment makes for its post-shrink slot, one level simpler here
  # (no swap-in needed at all).
  var survivors: seq[Path]
  for p0 in paths:
    if w.shouldStop: return exact(@[])
    # RFC-0005 batch 6: an unbound global receiver is its entry value
    # (`recvValue`; was a `KeyError`, reported as a walker fault).
    let (recvSV, p) = recvValue(p0, stmt.spRecvName, w)
    if recvSV.kind != svSeq:
      let locPrefix = if stmt.spLoc.len > 0: stmt.spLoc & ": " else: ""
      let d = w.degrade(feUnsupportedExprKind,
        locPrefix & "isSeqPop: receiver lowered to " &
             plainEnglishSymValKind(recvSV.kind) &
             " — expected svSeq (feUnsupportedExprKind)")
      survivors.add forkPathTainted(p, p.pc, declinedPopEnv(p.env, stmt), d)
      continue
    if recvSV.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      let d = w.degrade(placeholderReadDeclineKind(recvSV),
        placeholderReadDeclineMsg(recvSV, stmt.spLoc, "mutation (.pop)"))
      survivors.add forkPathTainted(p, p.pc, declinedPopEnv(p.env, stmt), d)
      continue
    let lenZi = recvSV.seqLen # [placeholder-audited]
    # RFC-0005 S8cd: `pop` reads the length and the last element, no other
    # (`recvValue`).
    let lenDecline = observeRecvPart(p, SymVal(kind: svInt, zi: lenZi), w)
    if lenDecline.isSome:
      survivors.add forkPathTainted(p, p.pc, declinedPopEnv(p.env, stmt),
                                    lenDecline.get)
      continue
    let emptyCond = not (lenZi > mkInt(0))
    if boundsUnchecked():
      # RFC-0016 PRC-07: `pop` reads `s[len - 1]`, unchecked with `boundChecks`
      # off: an empty seq reads before its data.
      decideUndefined(p, uncheckedIndexUb(), emptyCond,
                      uncheckedIndexSite(stmt.spLoc), w)
    else:
      discard forkDefect(p, emptyCond, "IndexDefect", none(string), w) ## Phase 16 D1a parity
    let newLenZi = lenZi - mkInt(1)
    if not isBackedSeqElemTy(recvSV.seqElemTy):
      # RFC-0016 K9c follow-up: the popped element has no array to be read
      # from (`seqElemAt`'s fallback, a `weInternalWalkerFault`).
      var envD = declinedPopEnv(p.env, stmt)
      var scratch: seq[Z3Bool]
      envD[stmt.spRecvName] = allocateSym(
        tUnsupportedFieldSeq(recvSV.seqElemTy, "an element popped from a " &
          "seq of an element type the model does not back"),
        freshDegradeName("__seqPopUnbacked"), scratch)
      survivors.add unbackedElemSurvivor(p, p.pc & @[not emptyCond], envD,
        recvSV, stmt.spLoc, "`pop`", w)
      continue
    let popped = seqElemAt(recvSV, newLenZi) # [placeholder-audited]
    let elemDecline = observeRecvPart(p, popped, w)
    if elemDecline.isSome:
      survivors.add forkPathTainted(p, p.pc & @[not emptyCond],
                                    declinedPopEnv(p.env, stmt), elemDecline.get)
      continue
    # N27 audit (item 1, round-6 fix round 3): rebinding the receiver after
    # a successful pop. `recvSV` was already declined above (this arm's own
    # `isUnsupportedFieldPlaceholder` check at the top of the `for p in
    # paths` loop, `continue`d on the placeholder branch) and is never
    # reassigned before this point — the `.seqDataRaw` read below is
    # reached only on the non-placeholder path.
    var newEnv = p.env
    # RFC-0005 S8bc: every data array of a tree element, unchanged.
    newEnv[stmt.spRecvName] = mkSeqSV(newLenZi, seqArrs(recvSV), # [placeholder-audited]
      recvSV.seqElemTy)
    newEnv[stmt.spRetName] = reboxSeqCell(stmt.spElemTy, popped)   # RFC-0005 S8ba
    let unwritten = uninitReadCond(recvSV, newLenZi)
    if unwritten.isSome:
      # RFC-0005 S8bq: as `isIndex`'s element read.
      if $simplify(unwritten.get) != "true":
        let written = forkPath(p, p.pc & @[not emptyCond], newEnv)
        written.defectSurvivorPc.add not unwritten.get
        survivors.add written
      let d = w.degrade(uninitReadKind, uninitReadMsg)
      let fresh = forkPathTainted(p, p.pc & @[not emptyCond], newEnv, d)
      fresh.defectSurvivorPc.add unwritten.get
      survivors.add fresh
    else:
      survivors.add forkPath(p, p.pc & @[not emptyCond], newEnv)
  exact(survivors)

proc walkTabKeysArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isTabKeys` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # RFC-0005 S8bc (item 6). `tkRetName := the keys of tkRecv`, the key
  # sequence a `for` over a Table's `pairs` / `keys` / `values` walks
  # (`parseTableForLoop`). Bound to a FRESH `seq[K]` `ks` whose length is
  # the table's size; for every position `j` a loop can reach
  # (`j < maxLoopUnwind`: the k-unroll walks no further, and declines past
  # it), `j < size` implies
  #
  #   * `ks[j]` is present in the table, and
  #   * `pos[ks[j]] == j` for one fresh array `pos` from keys to positions,
  #     so the elements are pairwise distinct (O(n) facts, not O(n^2)).
  #
  # Each `ks[j]` is a key term of the run (`tabKeyTerm` registers it), so
  # the S8f realizability facts (`containerCardConds`: a table's size is
  # at least the number of distinct present key terms) make the `size`
  # distinct present keys ALL the table's keys: one more would exceed the
  # size, and an unnamed key would too. The sequence is therefore an
  # enumeration of the table, in a FREE order. Nim's order is the hash
  # order, one of the models: nothing is forked away and nothing dropped,
  # so an sxUnsat holds; a candidate may depend on the order, so a path
  # where the table can have two or more entries is tainted
  # `feTableIterOrder` (`dcFreshSymbol`: replay-gated, S10), and one where
  # it has at most one is exact and clean. A string key is a string of
  # bytes (`seqStrElemConds`). The parser declines a float key (a NaN
  # entry counts in the size but is never present).
  var survivors: seq[Path]
  for p0 in paths:
    if w.shouldStop: return exact(survivors)
    let (tsv, p) = lowerInExpr(p0, stmt.tkRecv, w)
    let locPrefix = if stmt.tkLoc.len > 0: stmt.tkLoc & ": " else: ""
    if tsv.kind != svTable or
       tsv.tabKeyTy.kind notin {itString, itInt, itBool}:
      let d = w.degrade(feUnsupportedOp,
        locPrefix & "isTabKeys: receiver lowered to " &
        plainEnglishSymValKind(tsv.kind) &
        " -- expected a Table with a string, integer or bool key " &
        "(feUnsupportedOp)")
      var fresh: seq[Z3Bool]
      var env2 = p.env
      env2[stmt.tkRetName] = allocateSym(tSeq(stmt.tkKeyTy),
        freshDegradeName("__tabKeysDegrade"), fresh)
      survivors.add forkPathTainted(p, p.pc, env2, d)
      continue
    let ctx = requireCurrentContext()
    let keyTy = tsv.tabKeyTy
    var ks = SymVal(kind: svSeq, seqLen: tsv.tabSize,
      seqDataRaw: allocateSeqDataRaw(keyTy, freshDegradeName("__tabKeys")),
      seqElemTy: keyTy)
    let dom = constFalseStoreKeys(ctx, tsv.tabPresentRaw.raw)
    block literalKeys:
      # RFC-0016 S8cg. Keys the SUT stored as integer literals: each of the
      # first `maxLoopUnwind` positions is spelled as a choice among them
      # (`ite` over fresh selectors), so a product with a key splits on its
      # literal values before Nim's overflow check (`mulOverflowSplit`).
      # The domain fact below already confines a key to them, so no model
      # is pruned: a position past the size is never read.
      if keyTy.kind != itInt or dom.isNone or dom.get.len == 0 or
         dom.get.len > mulSplitLeafBudget:
        break literalKeys
      var lits: seq[RawZ3Ast]
      for d in dom.get:
        if Z3_get_ast_kind(ctx.raw, d) != Z3_NUMERAL_AST: break literalKeys
        var dup = false
        for l in lits:
          if Z3_get_ast_id(ctx.raw, l) == Z3_get_ast_id(ctx.raw, d): dup = true
        if not dup: lits.add d
      var hold: seq[Z3AnyAst]
      var data = ks.seqDataRaw.raw # [placeholder-audited]
      for j in 0 ..< w.settings.budget.maxLoopUnwind:
        var t = lits[^1]
        for i in countdown(lits.len - 2, 0):
          let sel = mkBoolVar(ctx, freshDegradeName("__tabKeyChoice"))
          hold.add wrap[Z3AnyAst](ctx, sel.raw)
          t = checkedIte(ctx, sel.raw, lits[i], t)
          hold.add wrap[Z3AnyAst](ctx, t)
        data = checkedStore(ctx, data, mkZ3IntLit(int64(j)).raw, t)
        hold.add wrap[Z3AnyAst](ctx, data)
      ks.seqDataRaw = wrap[Z3AnyAst](ctx, data) # [placeholder-audited]
    var facts: seq[Z3Bool]
    # The position array, built raw (its key sort is runtime, as
    # `tabTreeDataVars`'s arrays are) and wrapped at once so its reference
    # is held; `intHold` keeps the Int sort's witness term alive across
    # `Z3_mk_array_sort`.
    var posArr = none(Z3AnyAst)
    let intHold = mkZ3IntLit(0)
    var keyed = true
    for j in 0 ..< w.settings.budget.maxLoopUnwind:
      let kj = seqElemAt(ks, mkZ3IntLit(int64(j)))
      facts.add seqStrElemConds(kj)
      let term = tabKeyTerm(kj, keyTy)
      if term.isNone:
        keyed = false
        break
      if posArr.isNone:
        let keySort = ctx.checkErr Z3_get_sort(ctx.raw, term.get.raw)
        let intSort = ctx.checkErr Z3_get_sort(ctx.raw, intHold.raw)
        let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, keySort, intSort)
        let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
          freshDegradeName("__tabKeyPos").cstring)
        posArr = some(wrap[Z3AnyAst](ctx,
          ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort)))
      let present = wrap[Z3Bool](ctx,
        checkedSelect(ctx, tsv.tabPresentRaw.raw, term.get.raw))
      let pos = wrap[Z3Int](ctx,
        checkedSelect(ctx, posArr.get.raw, term.get.raw))
      let jz = mkZ3IntLit(int64(j))
      facts.add ((not (jz < tsv.tabSize)) or (present and pos == jz))
      # RFC-0005 batch 4: a table the SUT built from the empty one is
      # present only at the keys it stored (`constFalseStoreKeys`), so
      # `ks[j]` is one of them: the same fact as `present` in a form Z3
      # can case-split on. `s += k * v` over `pairs` multiplied two free
      # 64-bit terms, whose key was bounded only through the presence
      # array: Z3 4.13.4 ran out of its 20M budget on that query from a
      # fresh context (SAT in about 40K units with the keys spelled).
      if dom.isSome and dom.get.len > 0:
        var anyKey = wrap[Z3Bool](ctx, checkedEq(ctx, term.get.raw, dom.get[0]))
        for i in 1 ..< dom.get.len:
          anyKey = anyKey or
            wrap[Z3Bool](ctx, checkedEq(ctx, term.get.raw, dom.get[i]))
        facts.add ((not (jz < tsv.tabSize)) or anyKey)
    if not keyed:
      # Unreachable for a key type the guard above admits; kept in band.
      let d = w.degrade(feUnsupportedOp,
        locPrefix & "isTabKeys: a key of type " & $keyTy &
        " has no table key term (feUnsupportedOp)")
      var env2 = p.env
      env2[stmt.tkRetName] = ks
      survivors.add forkPathTainted(p, p.pc, env2, d)
      continue
    var env2 = p.env
    env2[stmt.tkRetName] = ks
    let atMostOne = tsv.tabSize <= mkZ3IntLit(1)
    let lit = $simplify(atMostOne)
    if lit != "false":
      survivors.add forkPath(p, p.pc & facts & @[atMostOne], env2)
    if lit != "true":
      let d = w.degrade(feTableIterOrder,
        locPrefix & "iteration over a Table with two or more entries: " &
        "Nim visits the keys in hash order, the model in any order -- a " &
        "witness is replayed against the real order (feTableIterOrder) -- " &
        facetNote("tables.Table/iterationOrder"))
      survivors.add forkPathTainted(p, p.pc & facts & @[not atMostOne],
                                    env2, d)
  exact(survivors)

proc walkSetLenArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isSetLen` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # RFC-0005 S8bl (item 1). `slRetName := setLen(slBase, slLen)`, the value
  # system's `setLen` magic leaves in its `var` argument (`parseSetLen`
  # guards the length and writes the result back). A magic has no body:
  # before S8bl the call was registered with an EMPTY one and the argument
  # kept its old value (a string's: a false sxSat; a seq's walked into the
  # `seqs_v2` payload cast).
  #
  #   * a seq: the length is `slLen`; each data array is the view
  #     `lambda i. ite(i < oldLen, arr[i], zero)`, so a grown slot reads
  #     the element's zero and a kept one its value (a shrunk-then-grown
  #     seq reads zeros: the second call's `oldLen` is the shrunk length);
  #   * a string (or a string-backed `seq[byte]`): the first `slLen` bytes
  #     when it shrinks, else the string followed by a pad of
  #     `slLen - len` NUL bytes -- a fresh string, whose length and
  #     all-NUL content are facts of the path (no quantifier).
  var survivors: seq[Path]
  for p0 in paths:
    if w.shouldStop: return exact(survivors)
    let (baseSV, p1) = lowerInExpr(p0, stmt.slBase, w)
    let (lenSV0, p) = lowerInExpr(p1, stmt.slLen, w)
    let locPrefix = if stmt.slLoc.len > 0: stmt.slLoc & ": " else: ""
    let lenOk = lenSV0.kind in {svInt, svBV8, svBV16, svBV32, svBV64}
    var env2 = p.env
    if baseSV.kind == svSeq and baseSV.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      let d = w.degrade(placeholderReadDeclineKind(baseSV),
        placeholderReadDeclineMsg(baseSV, stmt.slLoc, "mutation (setLen)"))
      env2[stmt.slRetName] = baseSV
      survivors.add forkPathTainted(p, p.pc, env2, d)
      continue
    if baseSV.kind == svSeq and lenOk and
       isBackedSeqElemTy(baseSV.seqElemTy) and
       defaultZeroTotal(baseSV.seqElemTy):
      let ctx = requireCurrentContext()
      let newLen = toZ3Int(lenSV0)
      let oldLen = baseSV.seqLen # [placeholder-audited]
      # A grown slot is a `newSeq` element (batch 6: one zeroing with
      # `lowerSeqNew`).
      let zeroArrs = seqNewZeroArrs(baseSV.seqElemTy)
      inc sliceViewCounter
      let iVar = mkIntVar("__setlen_i" & $sliceViewCounter)
      let kept = iVar < oldLen
      var arrs: seq[Z3AnyAst]
      for k, arr in seqArrs(baseSV):
        let old = wrap[Z3AnyAst](ctx, checkedSelect(ctx, arr.raw, iVar.raw))
        let z = wrap[Z3AnyAst](ctx,
          checkedSelect(ctx, zeroArrs[k].raw, iVar.raw))
        let body = wrap[Z3AnyAst](ctx,
          checkedIte(ctx, kept.raw, old.raw, z.raw))
        arrs.add lambdaOver(ctx, iVar, body)
      env2[stmt.slRetName] = mkSeqSV(newLen, arrs, baseSV.seqElemTy)
      survivors.add forkPath(p, p.pc, env2)
    elif baseSV.kind == svString and lenOk:
      let newLen = toZ3Int(lenSV0)
      let oldLen = len(baseSV.str)
      let grows = newLen > oldLen
      # Two paths, the shrink (or no change) and the grow, so each binds a
      # plain term (a `str.at` over an `ite` of strings ran Z3 out of
      # `seqQueryRLimit`). The grow appends a fresh pad of the added
      # length in `("\0")*`, a fact of the path (no quantifier).
      #
      # RFC-0005 S8bx (item 5): the result is a fresh string LEAF `r`
      # with the byte-domain fact every string input carries
      # (`allocateSym`), bound to the prefix / extension by an equation.
      # A byte read of the result, `int2bv[8](str.to_code(str.at(r, i)))
      # == n`, is then a byte test on a byte leaf, which `seqLenCaps`
      # rewrites to the character form `str.at(r, i) == "\xNN"`: Z3
      # decides that, where the code form over a `str.at` of the concat
      # (or substr) was left undecided by both pinned Z3s within
      # `seqQueryRLimit`.
      var leafShrink: seq[Z3Bool]
      var rShrink = allocateSym(tString(),
        freshDegradeName("__setLenStr"), leafShrink)
      # RFC-0005 S8cl (item 4): a `newString`'s memory is its own.
      if stmt.slFresh: rShrink.strBuf = sbOwned
      var envShrink = env2
      envShrink[stmt.slRetName] = rShrink
      survivors.add forkPath(p, p.pc & leafShrink & @[not grows,
        rShrink.str == substr(baseSV.str, mkInt(0), newLen)], envShrink)
      var leafGrow: seq[Z3Bool]
      var rGrow = allocateSym(tString(),
        freshDegradeName("__setLenStr"), leafGrow)
      let pad = mkStringVar(freshDegradeName("__setLenPad"))
      if stmt.slFresh: rGrow.strBuf = sbOwned
      env2[stmt.slRetName] = rGrow
      survivors.add forkPath(p, p.pc & leafGrow & @[grows,
        len(pad) == newLen - oldLen,
        matches(pad, star(mkRegex(mkString("\x00")))),
        rGrow.str == concat(baseSV.str, pad)], env2)
    else:
      let d = w.degrade(feUnsupportedOp,
        locPrefix & "setLen: the argument lowered to " &
        plainEnglishSymValKind(baseSV.kind) & " and the length to " &
        plainEnglishSymValKind(lenSV0.kind) & " -- expected a seq of " &
        "a backed element with a zero, or a string, and an integer " &
        "(feUnsupportedOp)")
      var fresh: seq[Z3Bool]
      env2[stmt.slRetName] = allocateSym(stmt.slTy,
        freshDegradeName("__setLenDegrade"), fresh)
      survivors.add forkPathTainted(p, p.pc, env2, d)
  exact(survivors)

proc walkVariantReassignArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isVariantReassign` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # R14: `obj.kind = tagLiteral` — the RHS is a LITERAL. The only fork is
  # the RFC-0005 S8f branch-change `FieldDefect` below, routed through
  # `maybeForkDefect` (which narrows it under `wmFollowConcrete`, exactly
  # as `isVariantField`'s out-of-arm fork is narrowed).
  case w.mode
  of wmExplore: discard
  of wmFollowConcrete: discard
  # Phase 11 cycle 6 — `obj.kind = tagLiteral`: the discriminator becomes
  # the literal tag.
  #
  # RFC-0005 S8f (walker 154). Nim raises `FieldDefect` ("assignment to
  # discriminant changes object branch") when the old discriminator selects
  # a DIFFERENT source branch than the new one, and keeps the fields when
  # it selects the same branch (probed on the pinned toolchain: a `var`
  # param, a local, and a default-initialised object all behave so). The
  # walker used to model the transition as legal with the new arm's fields
  # zero-initialised (ADR-0003 D5, the pre-2.0 `nimOldCaseObjects`
  # behaviour) -- so `x.kind = pfB` on a `var` param was a clean `sxSat`
  # whose witness (`kind: pfA`) raised `FieldDefect` instead of reaching
  # the target. Now: fork the defect on "different branch" and continue
  # on "same branch" with the branch's fields carried over.
  var out2: seq[Path]
  for p0 in paths:
    # RFC-0005 batch 6: an unbound global receiver is its entry value
    # (`recvValue`). The arm skipped it, so its `FieldDefect` was never
    # forked (a false `sxUnsat` on the raise).
    let (oldSV, p) = recvValue(p0, stmt.vrObjName, w)
    if unwrittenDisc(oldSV).len > 0 and   # RFC-0005 S8cd
       reassignReadsDisc(oldSV, stmt.vrBranches):
      # RFC-0005 S8bw (item 2): a global whose discriminator no write
      # reached (another field was written first).
      # RFC-0005 batch 6: an S8as global's discriminator is its entry
      # value, any of its type: the path is tainted and the reassignment
      # modelled on it (`unwrittenKind`); any other declines.
      let part = unwrittenDisc(oldSV)
      let d = w.degrade(unwrittenKind(part), unwrittenMsg(part),
                        ub = unwrittenUb(part))
      if unwrittenKind(part) != feGlobalHavoc:
        out2.add forkPathTainted(p, p.pc, p.env, d)
        continue
      taintInPlace(p, d)
    if oldSV.kind notin {svVariant, svMultiVariant}:
      # RFC-0005 S8i: a declined construction's placeholder.
      out2.add degradeUnmodelledReassign(p, stmt.vrObjName, oldSV.kind, w)
      continue
    if oldSV.kind == svMultiVariant:
      # RFC-0005 S8bw (item 1): the parser emits this statement for a
      # single-axis variant only (a multi-axis one takes the symbolic
      # form); a multi-variant here declines as an unmodelled reassignment.
      # This was a `doAssert`.
      out2.add degradeUnmodelledReassign(p, stmt.vrObjName, oldSV.kind, w)
      continue
    let oldDisc = oldSV.vDisc[]
    let tagOrd = int64(stmt.vrNewTag)
    let newDiscInner: SymVal =
      case oldDisc.kind
      of svBV8:  liftBV(mkBitVec[8](tagOrd),  oldDisc.signed)
      of svBV16: liftBV(mkBitVec[16](tagOrd), oldDisc.signed)
      of svBV32: liftBV(mkBitVec[32](tagOrd), oldDisc.signed)
      of svBV64: liftBV(mkBitVec[64](tagOrd), oldDisc.signed)
      of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(tagOrd))  # A6
      of svBool: ofBool(mkBool(tagOrd != 0))   ## RFC-0005 S8cp: a `bool` disc
      else:
        raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (isVariantReassignSymbolic's discriminator is always BV/Z3Int-allocated)]
          "isVariantReassign: disc must be BV or Z3Int kind")
    if stmt.vrMode == dwmChecked:
      maybeForkDefect(p, not sameBranchCond(oldDisc, stmt.vrNewTag, stmt.vrBranches),
                      "FieldDefect", none(string), w)
      if w.shouldStop: return exact(out2)
    let newDiscBoxed = new(SymVal)
    newDiscBoxed[] = newDiscInner
    let outcomes = discWriteOutcomes(stmt.vrMode, oldSV.vArmFields, oldDisc,
                                     stmt.vrNewTag, stmt.vrBranches,
                                     variantDiscEq(oldDisc, tagOrd),
                                     stmt.vrVariantTy, oldSV.vImage)
    let pM = drainPendingLowerEffects(p)
    for o in outcomes:
      # RFC-0016 PRC-07: an outcome that records a decline or a havoc is not
      # recorded for a side the guard rules out (`x.k = ka` of a `ka`).
      if (o.decline or o.havoc) and guardLiteral(o.cond) == glFalse: continue
      let child = discOutcomePath(pM, o, w)
      if o.decline:
        out2.add child
        continue
      let newSV = SymVal(kind: svVariant,
                         vDisc: newDiscBoxed,
                         vDiscName: oldSV.vDiscName,
                         vObjectName: oldSV.vObjectName,
                         vArmFields: o.arms,
                         vArmFieldNames: oldSV.vArmFieldNames,
                         vPlainFields: oldSV.vPlainFields,       # shared:
                         vPlainFieldNames: oldSV.vPlainFieldNames, # preserved.
                         vImage: (if o.keepImage: oldSV.vImage else: @[]),
                         vActive: oldSV.vActive)   # RFC-0016 PRC-07 B
      child.env[stmt.vrObjName] = newSV
      out2.add child
  return exact(out2)

proc walkVariantReassignSymbolicArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isVariantReassignSymbolic` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # R14: unlike `isVariantReassign` (above), the RHS here IS symbolic —
  # this construct genuinely forks one path per tag in the discriminator's
  # domain, the same "fork every arm" shape `isIf`/`isWhile` have (though
  # bounded by the variant's own arity, not an iteration count, so it
  # cannot blow up the way an unbounded `while` unroll can). `wmExplore`
  # below is unchanged; `wmFollowConcrete` narrows to the ONE concretely-
  # matching tag via `followConcreteTag` (defined per `oldSV`/`oldAxis`
  # case below, right before each's own tag-fork loop) — same
  # `concreteBranchOutcome` mechanism `walkIfFollowConcrete`/
  # `walkWhileFollowConcrete` use, with the same sound "fork everything"
  # fallback when the concrete draws don't determine a unique match.
  case w.mode
  of wmExplore: discard
  of wmFollowConcrete: discard
  # Phase 14 cycle A4b (ADR-0003 D4). Symbolic-RHS disc reassign:
  # fork one path per arm-ordinal in the disc's domain. Each path
  # is constrained `rhsSV == k_ord` AND the variant SymVal in env
  # is rebuilt with the new disc SET TO THAT TAG'S CONSTANT.
  # For itMultiVariant: only the named axis's disc is updated; other
  # axes are preserved as-is.
  # RFC-0005 S8f (walker 154): per tag, fork `FieldDefect` when the old
  # discriminator's source branch differs from the tag's (Nim's runtime
  # check -- see `isVariantReassign` above), and continue on the same
  # branch with that branch's fields carried (`carryBranchFields`).
  var out2: seq[Path]
  for p0 in paths:
    # RFC-0005 batch 6: as `isVariantReassign`'s receiver (`recvValue`).
    let (oldSV, p) = recvValue(p0, stmt.vrsObjName, w)
    if unwrittenDisc(oldSV).len > 0 and   # RFC-0005 S8cd
       reassignReadsDisc(oldSV, stmt.vrsBranches):
      # RFC-0005 S8bw (item 2): as `isVariantReassign` above.
      # RFC-0005 batch 6: an S8as global's discriminator is its entry
      # value, any of its type: the path is tainted and the reassignment
      # modelled on it (`unwrittenKind`); any other declines.
      let part = unwrittenDisc(oldSV)
      let d = w.degrade(unwrittenKind(part), unwrittenMsg(part),
                        ub = unwrittenUb(part))
      if unwrittenKind(part) != feGlobalHavoc:
        out2.add forkPathTainted(p, p.pc, p.env, d)
        continue
      taintInPlace(p, d)
    ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
    let (rhsSV, pr) = lowerInExpr(p, stmt.vrsRhs, w)
    proc rhsEq(tagOrd: int64): Z3Bool =
      case rhsSV.kind
      of svBV8:  rhsSV.bv8  == mkBitVec[8](tagOrd)
      of svBV16: rhsSV.bv16 == mkBitVec[16](tagOrd)
      of svBV32: rhsSV.bv32 == mkBitVec[32](tagOrd)
      of svBV64: rhsSV.bv64 == mkBitVec[64](tagOrd)
      of svInt:  rhsSV.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
      of svBool: rhsSV.bo   == mkBool(tagOrd != 0)  ## RFC-0005 S8u: bool disc
      else:
        raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (see above)]
          "isVariantReassignSymbolic: RHS must lower to a BV, " &
          "Z3Int or Bool kind (got " & $rhsSV.kind & ")")
    ## R1 (Invariant-3 soundness fix): `stmt.vrsRhs` may itself deposit
    ## scalar-raise-fork predicates. Undrained, those were silently
    ## discarded — no raise fork, no bounds narrowing. Drain and thread
    ## the survivor(s) forward, mirroring `isLet`/`isAssign`.
    ## RFC-0005 S8g (walker 155): the `else:` arm (key -1) is a candidate
    ## too. Its guard is "the RHS equals no explicit tag" (the same
    ## membership `isVariantField` uses), and its new discriminator is the
    ## symbolic RHS itself, not a constant: every else value shares the
    ## one else branch, so a `kC -> kD` reassignment keeps `c`.
    proc tagGuard(explicit: seq[int]): proc (tagOrd: int64): Z3Bool =
      result = proc (tagOrd: int64): Z3Bool =
        if tagOrd >= 0: return rhsEq(tagOrd)
        result = mkBool(true)
        for t in explicit:
          result = result and not rhsEq(int64(t))
    for cp in drainScalarRaiseForks(pr, w):
      case oldSV.kind
      of svVariant:
        var candidateTags, explicitTags: seq[int]
        for tag in oldSV.vArmFields.keys:
          candidateTags.add tag
          if tag >= 0: explicitTags.add tag
        let guard = tagGuard(explicitTags)
        let followTag = followConcreteTag(w.mode, w.z3, w.concreteEq, w.settings,
                                          guard, candidateTags)
        for tag in candidateTags:
          if followTag.isSome and tag != followTag.get(): continue
          let chosen = forkPath(cp, cp.pc & @[guard(int64(tag))], cp.env)
          if stmt.vrsMode == dwmChecked:
            maybeForkDefect(chosen, not sameBranchCond(oldSV.vDisc[], tag, stmt.vrsBranches),
                            "FieldDefect", none(string), w)
            if w.shouldStop: return exact(out2)
          let newDiscConst: SymVal =
            case oldSV.vDisc[].kind
            of svBV8:  liftBV(mkBitVec[8](int64(tag)),  oldSV.vDisc[].signed)
            of svBV16: liftBV(mkBitVec[16](int64(tag)), oldSV.vDisc[].signed)
            of svBV32: liftBV(mkBitVec[32](int64(tag)), oldSV.vDisc[].signed)
            of svBV64: liftBV(mkBitVec[64](int64(tag)), oldSV.vDisc[].signed)
            of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(int64(tag)))  # A6
            of svBool: ofBool(mkBool(tag != 0))   ## RFC-0005 S8u: bool disc
            else:
              raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (see above)]
                "isVariantReassignSymbolic: old disc must be BV, Z3Int or Bool")
          let newDiscInner =
            if tag < 0: discFromRhs(rhsSV, oldSV.vDisc[]) else: newDiscConst
          let newDiscBoxed = new(SymVal)
          newDiscBoxed[] = newDiscInner
          let outcomes = discWriteOutcomes(stmt.vrsMode, oldSV.vArmFields,
                                           oldSV.vDisc[], tag, stmt.vrsBranches,
                                           symEq(oldSV.vDisc[], newDiscInner),
                                           stmt.vrsVariantTy, oldSV.vImage)
          let chosenM = drainPendingLowerEffects(chosen)
          for o in outcomes:
            # RFC-0016 PRC-07: an outcome that records a decline or a havoc is not
            # recorded for a side the guard rules out (`x.k = ka` of a `ka`).
            if (o.decline or o.havoc) and guardLiteral(o.cond) == glFalse: continue
            let child = discOutcomePath(chosenM, o, w)
            if o.decline:
              out2.add child
              continue
            let newSV = SymVal(kind: svVariant,
                               vDisc: newDiscBoxed,
                               vDiscName: oldSV.vDiscName,
                               vObjectName: oldSV.vObjectName,
                               vArmFields: o.arms,
                               vArmFieldNames: oldSV.vArmFieldNames,
                               vPlainFields: oldSV.vPlainFields,
                               vPlainFieldNames: oldSV.vPlainFieldNames,
                               vImage: (if o.keepImage: oldSV.vImage else: @[]),
                               vActive: oldSV.vActive)   # RFC-0016 PRC-07 B
            child.env[stmt.vrsObjName] = newSV
            out2.add child
      of svMultiVariant:
        # Locate the named axis (vrsDiscName); other axes preserve
        # their disc + arm state.
        var axisIx = -1
        for i, ax in oldSV.mvAxes:
          if ax.discName == stmt.vrsDiscName:
            axisIx = i; break
        doAssert axisIx >= 0,
          "isVariantReassignSymbolic on svMultiVariant: no axis named " &
          stmt.vrsDiscName
        let oldAxis = oldSV.mvAxes[axisIx]
        var candidateTags, explicitTags: seq[int]
        for tag in oldAxis.armFields.keys:
          candidateTags.add tag
          if tag >= 0: explicitTags.add tag
        let guard = tagGuard(explicitTags)
        let followTag = followConcreteTag(w.mode, w.z3, w.concreteEq, w.settings,
                                          guard, candidateTags)
        for tag in candidateTags:
          if followTag.isSome and tag != followTag.get(): continue
          let chosen = forkPath(cp, cp.pc & @[guard(int64(tag))], cp.env)
          if stmt.vrsMode == dwmChecked:
            maybeForkDefect(chosen, not sameBranchCond(oldAxis.disc[], tag, stmt.vrsBranches),
                            "FieldDefect", none(string), w)
            if w.shouldStop: return exact(out2)
          let newDiscConst: SymVal =
            case oldAxis.disc[].kind
            of svBV8:  liftBV(mkBitVec[8](int64(tag)),  oldAxis.disc[].signed)
            of svBV16: liftBV(mkBitVec[16](int64(tag)), oldAxis.disc[].signed)
            of svBV32: liftBV(mkBitVec[32](int64(tag)), oldAxis.disc[].signed)
            of svBV64: liftBV(mkBitVec[64](int64(tag)), oldAxis.disc[].signed)
            of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(int64(tag)))  # A6
            of svBool: ofBool(mkBool(tag != 0))   ## RFC-0005 S8u: bool axis
            else:
              raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (see above)]
                "isVariantReassignSymbolic: axis disc must be a BV or bool kind")
          let newDiscInner =
            if tag < 0: discFromRhs(rhsSV, oldAxis.disc[]) else: newDiscConst
          let newDiscBoxed = new(SymVal)
          newDiscBoxed[] = newDiscInner
          let outcomes = discWriteOutcomes(stmt.vrsMode, oldAxis.armFields,
                                           oldAxis.disc[], tag, stmt.vrsBranches,
                                           symEq(oldAxis.disc[], newDiscInner))
          let chosenM = drainPendingLowerEffects(chosen)
          for o in outcomes:
            # RFC-0016 PRC-07: an outcome that records a decline or a havoc is not
            # recorded for a side the guard rules out (`x.k = ka` of a `ka`).
            if (o.decline or o.havoc) and guardLiteral(o.cond) == glFalse: continue
            let child = discOutcomePath(chosenM, o, w)
            if o.decline:
              out2.add child
              continue
            var newAxes = oldSV.mvAxes
            newAxes[axisIx] = VariantAxisSym(
              discName: oldAxis.discName, disc: newDiscBoxed,
              armFields: o.arms,
              armFieldNames: oldAxis.armFieldNames)
            let newSV = SymVal(kind: svMultiVariant,
                               mvObjectName: oldSV.mvObjectName,
                               mvAxes: newAxes,
                               mvPlainFields: oldSV.mvPlainFields,
                               mvPlainFieldNames: oldSV.mvPlainFieldNames)
            child.env[stmt.vrsObjName] = newSV
            out2.add child
      else:
        # RFC-0005 S8i: a declined construction's placeholder (this was a
        # `doAssert false`, surfacing the decline as an internal fault).
        out2.add degradeUnmodelledReassign(cp, stmt.vrsObjName, oldSV.kind, w)
  return exact(out2)

proc walkVariantConstructSymArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isVariantConstructSym` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # Round-6 A3 (ADR-0029). Fork-per-tag SYMBOLIC-discriminant variant
  # CONSTRUCTION — clones `isVariantReassignSymbolic`'s fork-per-tag shape
  # (same tag loop, same `disc == tag` pc append) with the deliberate
  # divergence: construction has no "active arm" data to preserve (Nim
  # itself only accepts a non-constant discriminant in constructor syntax
  # when no arm-specific field is set — the parser's `of itVariant:` arm
  # enforces this), so EVERY declared arm's fields are that field type's
  # `default(T)` in each fork. (Walker <= 153 allocated them FRESH, which
  # let a witness claim an arm-field value real Nim never holds; RFC-0005
  # S8f.)
  #
  # The `maxVariantConstructorForks` budget is a STRUCTURAL check against
  # `stmt.vcsTagSet.len` — before any solver work, uniform across every
  # input path (the tag SET is fixed at parse time; only which tags are
  # ultimately SAT-feasible depends on the path). Reuses the existing
  # `beBudgetExhausted` classified-decline kind (SND-4 "mirror, don't
  # reinvent" — this IS a walk budget running out with paths still live,
  # exactly that kind's own doc comment). No `NimNode` exists here to
  # build a `siteMsg`-shaped message from, so `stmt.vcsLoc` (the
  # PARSE-TIME-captured file:line:col + `n.repr`) is glued in VERBATIM.
  var out2: seq[Path]
  let vcsTy = stmt.vcsVariantTy
  let vcsBudget = w.settings.budget.maxVariantConstructorForks
  if vcsBudget > 0 and stmt.vcsTagSet.len > vcsBudget:
    # RFC-0005 S6a: `beBudgetExhaustedUnmodelled` (`dcSubstituted`), not
    # the k-unroll's `beBudgetExhausted` — the construction is skipped,
    # the destination bound to a fresh value (RFC-0005 S8ba; it was left
    # unbound) and `vcsDiscExpr`/`vcsPlainFields` are
    # never lowered, so their raise forks are dropped: a stale env.
    let d = w.degrade(beBudgetExhaustedUnmodelled,
      stmt.vcsLoc & ": variant constructor fork budget exhausted " &
           "(maxVariantConstructorForks=" & $vcsBudget & ", feasible " &
           "tags=" & $stmt.vcsTagSet.len & ") — construction unmodeled " &
           "(beBudgetExhaustedUnmodelled)", cap = ckVariantForks)
    for p in paths:
      # RFC-0005 S8ba: `stmt.vcsResultVar` is bound to a fresh value of
      # the variant type on the tainted path (`declinedVariantEnv`). It
      # was left UNBOUND, and the parser's A-normalised `let p = <temp>`
      # then read it at once and declined a second time as an unmodelled
      # global (`feGlobalReadUnmodelled`, RFC-0005 S6a's pin). SND-1's
      # per-path taint is forced via `forkPathTainted` so the verdict
      # never rides a bare `w.sawUnknown` alone. RFC-0005 S1: one token
      # `d`, forked onto every path.
      out2.add forkPathTainted(p, p.pc, declinedVariantEnv(p.env, stmt), d)
    return selfTainted(out2)
  # N9 (round-6 review remediation), made RECURSIVE by D2 (round-6 review
  # remediation). `maxVariantConstructorForks` above only bounds the OUTER
  # fork count (`vcsTagSet.len`); the per-fork field-allocation loop below
  # walks EVERY declared arm of `vcsTy` (construction has no "active arm"
  # to narrow to — see this stmt kind's own doc comment), so the real
  # per-construct allocation cost is `vcsTagSet.len` (bounded above) TIMES
  # the total LEAF-ALLOCATION cost across ALL arms' fields (previously
  # bounded only by a FLAT field COUNT, which undercounted any composite
  # field type — `array[N, T]`/nested tuple/nested variant — whose own
  # allocation recurses; see `allocCostOf`'s doc comment, `smt/types.nim`,
  # for the full gap writeup and the recursion it mirrors from
  # `allocateSym`). A second STRUCTURAL check — same before-any-solver-
  # work timing as the fork-count check, same `beBudgetExhausted` decline
  # kind (SND-4 "mirror, don't reinvent") — catches a wide- or deeply-
  # fielded variant whose fork count alone sits comfortably under budget.
  var vcsArmFieldCost = 0'i64
  for arm in vcsTy.vArms:
    for ft in arm.fieldTypes:
      vcsArmFieldCost = satAdd64(vcsArmFieldCost, allocCostOf(ft))
  let vcsFieldAllocs = satMul64(int64(stmt.vcsTagSet.len), vcsArmFieldCost)
  let vcsFieldBudget = w.settings.budget.maxVariantConstructorFieldAllocs
  if vcsFieldBudget > 0 and vcsFieldAllocs > int64(vcsFieldBudget):
    # RFC-0005 S6a: same substitution as the fork-count budget above.
    let d = w.degrade(beBudgetExhaustedUnmodelled,
      stmt.vcsLoc & ": variant constructor field-allocation budget " &
           "exhausted (maxVariantConstructorFieldAllocs=" &
           $vcsFieldBudget & ", forks=" & $stmt.vcsTagSet.len &
           " x leaf-allocs-per-fork=" & $vcsArmFieldCost & " = " &
           $vcsFieldAllocs & ") — construction unmodeled " &
           "(beBudgetExhaustedUnmodelled)", cap = ckVariantFieldAllocs)
    for p in paths:
      # Same safe-degrade idiom as the fork-count budget above.
      out2.add forkPathTainted(p, p.pc, declinedVariantEnv(p.env, stmt), d)
    return selfTainted(out2)
  # N39 (round-6 fix round 5). GUARD-BEFORE-CALL, hoisted above the
  # `paths`/`tag` fork loops (mirrors the two budget checks immediately
  # above — a STRUCTURAL check against `vcsTy` itself, uniform across
  # every input path, before any solver work): every declared arm's
  # fields allocate FRESH in EVERY fork regardless of `tag` (this stmt
  # kind's own doc comment above), so if ANY arm anywhere carries a field
  # type `allocateSym` cannot back (an `itUninterp`
  # `__ownership:`/`__unsupported:`/`__unsupported_witness:` placeholder,
  # or an unsupported `itTable`/`itSet` shape — `classifyFieldType`
  # legitimately produces these for a variant arm field;
  # `scopedDeclineFieldTy`'s Bug #2 scoped decline only special-cases
  # `itSeq`), EVERY fork would hit the SAME raw
  # `raise (ref Symex*Error)` from inside this `for p in paths: for tag
  # in stmt.vcsTagSet: ... allocateSym(...)` nest — the exact C-backend
  # goto-exception hazard ADR-0023/SND-3 exists to ban (N36/N37
  # precedent: `isIndex`'s Table[K,V]-indexing decline, `isVariantReassign`'s
  # `defaultZero`-wrap). Caught EMPIRICALLY this slice via the stash
  # method: an unguarded reach under block-nesting silently produced
  # `sxUnsat` (0 errors) instead of the honest `sxUnknown` below — see
  # `tests/tsymex_r6_n39_variant_field_alloc.nim`. Degrades the WHOLE
  # construction (not per-tag: since every fork allocates every arm, a
  # per-tag distinction would be a false precision this stmt kind
  # structurally cannot offer) via the identical safe-degrade idiom the
  # two budget checks above already use.
  var vcsFieldIssue: Option[FieldAllocIssue] = none(FieldAllocIssue)
  block findVcsFieldIssue:
    for arm in vcsTy.vArms:
      for ft in arm.fieldTypes:
        vcsFieldIssue = unallocatableFieldIssue(ft)
        if vcsFieldIssue.isSome: break findVcsFieldIssue
  if vcsFieldIssue.isSome:
    let d = w.degrade(vcsFieldIssue.get.kind,
      stmt.vcsLoc & ": variant constructor field allocation " &
           "unmodeled — " & vcsFieldIssue.get.msg &
           " (arm-field allocation, not param-entry)")
    for p in paths:
      # Same safe-degrade idiom as the two budget checks above.
      out2.add forkPathTainted(p, p.pc, declinedVariantEnv(p.env, stmt), d)
    return selfTainted(out2)
  # RFC-0005 S8f: Nim accepts a runtime discriminator in constructor
  # syntax only when no arm field is set, so every arm field is its
  # type's `default(T)` -- walker <= 153 allocated each one FRESH, and a
  # target on `p.rq == 777` was a clean `sxSat` whose witness could never
  # reach it. A field type `defaultZero` cannot build declines the whole
  # construction, the same safe-degrade idiom as the checks above.
  block findVcsZeroIssue:
    for arm in vcsTy.vArms:
      for j, ft in arm.fieldTypes:
        if not defaultZeroTotal(ft):
          let d = w.degrade(feUnsupportedOp,
            stmt.vcsLoc & ": variant constructor arm field `" &
                 vcsTy.vObjectName & "." & arm.fieldNames[j] &
                 "` has no modelled default value (" & $ft & ")")
          for p in paths:
            out2.add forkPathTainted(p, p.pc, declinedVariantEnv(p.env, stmt), d)
          return selfTainted(out2)
  for p in paths:
    let (discSV, pr) = lowerInExpr(p, stmt.vcsDiscExpr, w)
    proc vcsDiscEq(tagOrd: int64): Z3Bool =
      case discSV.kind
      of svBV8:  discSV.bv8  == mkBitVec[8](tagOrd)
      of svBV16: discSV.bv16 == mkBitVec[16](tagOrd)
      of svBV32: discSV.bv32 == mkBitVec[32](tagOrd)
      of svBV64: discSV.bv64 == mkBitVec[64](tagOrd)
      of svInt:  discSV.zi   == mkZ3IntLit(tagOrd)
      else:
        raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (isVariantConstructSym's discriminator is always BV/Z3Int-allocated)]
          "isVariantConstructSym: disc must lower to a BV or Z3Int " &
          "kind (got " & $discSV.kind & ")")
    ## R1-style Invariant-3 soundness: `stmt.vcsDiscExpr` may itself
    ## deposit scalar-raise-fork predicates. Drain and thread the
    ## survivor(s) forward, mirroring `isVariantReassignSymbolic`.
    ## RFC-0005 review R1-04: each plain field is lowered ON the path that
    ## binds it (`lowerInExpr`), so its in-band decline (an unwritten
    ## global's `feGlobalHavoc`) taints that path; the raw `lower` here left
    ## the taint queued for whatever lowering ran next, on a sibling path or
    ## none. Its raise forks are drained in field order, as Nim evaluates
    ## the constructor's fields.
    var fieldPaths: seq[(Path, seq[SymVal])]
    for cp0 in drainScalarRaiseForks(pr, w):
      var cur = @[(cp0, newSeq[SymVal]())]
      for fe in stmt.vcsPlainFields:
        var nxt: seq[(Path, seq[SymVal])]
        for (fp, vals) in cur:
          let (fv, fp2) = lowerInExpr(fp, fe, w)
          for fp3 in drainScalarRaiseForks(fp2, w):
            nxt.add (fp3, vals & @[fv])
        cur = nxt
      fieldPaths.add cur
    for (cp, plainFields) in fieldPaths:
      for tag in stmt.vcsTagSet:
        var armFields = initOrderedTable[int, seq[SymVal]]()
        var armNames  = initOrderedTable[int, seq[string]]()
        for arm in vcsTy.vArms:
          armNames[arm.tagOrdinal] = arm.fieldNames
          var fields: seq[SymVal]
          for j, ft in arm.fieldTypes:
            inc variantConstructSymFreshCounter
            let path = "__variantConstructSym." & vcsTy.vObjectName & ".@" &
                       arm.tagName & "." & arm.fieldNames[j] & ".fork" &
                       $tag & "." & $variantConstructSymFreshCounter
            # RFC-0005 S8f: Nim sets no arm field in a runtime-
            # discriminator constructor, so every arm field is its
            # type's `default(T)` (`findVcsZeroIssue` above guarantees
            # `defaultZeroTotal` for every one).
            fields.add defaultZero(ft, path)
          armFields[arm.tagOrdinal] = fields
        let discBoxed = new(SymVal)
        discBoxed[] = discConst(vcsTy.vDiscTy, int64(tag))
        var newSV = SymVal(kind: svVariant, vDisc: discBoxed,
                           vDiscName: vcsTy.vDiscName,
                           vObjectName: vcsTy.vObjectName,
                           vArmFields: armFields, vArmFieldNames: armNames,
                           vPlainFields: plainFields,
                           vPlainFieldNames: vcsTy.vPlainFieldNames)
        # RFC-0016 PRC-07 slice B: every arm field is its zero, so the
        # union's bytes are the zero of the initialisation.
        let gate = unionImageGate(vcsTy)
        if gate.isSome: newSV.vImage = zeroImage(gate.get)
        if activeMemberTracked(vcsTy): newSV.vActive = activeOf(discBoxed[])
        var newEnv = cp.env
        newEnv[stmt.vcsResultVar] = newSV
        out2.add forkPath(cp, cp.pc & @[vcsDiscEq(int64(tag))], newEnv)
  return exact(out2)

proc walkVariantFieldArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isVariantField` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # R14: same shape as `isIndex` (not named in the finding, but identical
  # in structure) — the in-arm path is the only continuation `survivors`
  # gets; out-of-arm is a discarded-result `forkDefect` side channel,
  # narrowed per-mode inside `maybeForkDefect`. Nothing separate to
  # select here.
  case w.mode
  of wmExplore: discard
  of wmFollowConcrete: discard
  # Phase 11 cycle 5 — A-normalised arm-field access. Forks: the
  # in-arm path adds `disc IN matchingTags` to pc and binds
  # `retName` to an ite-chain over the matching arms' field
  # SymVals; the out-of-arm path adds `disc NOT IN matchingTags`
  # and (under `tFieldDefect`) is solved for a witness.
  var survivors: seq[Path]
  for p0 in paths:
    if w.shouldStop: return exact(@[])
    ## Drain-coverage audit: `stmt.vfRecv` is always an env-resident var —
    ## the parser A-normalises so variant object accesses are through named
    ## bindings (no complex expression as receiver). A violation here means
    ## the parser emitted a non-var receiver and drains would be needed.
    let (recv, p) = lowerLeafInExpr(p0, stmt.vfRecv)
    # Phase 14 cycle A1c: select the axis-local disc + arm tables
    # by SymVal kind. For svMultiVariant, locate the axis whose
    # arm field-name lists include vfFieldName — the parser
    # selected the same axis via the same membership test.
    var disc: SymVal
    var armFieldsTbl: OrderedTable[int, seq[SymVal]]
    var armFieldNamesTbl: OrderedTable[int, seq[string]]
    case recv.kind
    of svVariant:
      disc            = recv.vDisc[]
      armFieldsTbl    = recv.vArmFields
      armFieldNamesTbl = recv.vArmFieldNames
      # RFC-0016 PRC-07 slice B (cpp, `--fieldChecks:off`): the arm an access
      # is defined through is the union's active member, the arm last
      # written, not the discriminator's. int6-f: only where the access is
      # unchecked; a checked one tests the discriminator (below).
      if recv.vActive != nil and fieldsUnchecked(): disc = recv.vActive[]
    of svMultiVariant:
      var found = false
      for ax in recv.mvAxes:
        for _, names in ax.armFieldNames.pairs:
          if stmt.vfFieldName in names:
            disc             = ax.disc[]
            armFieldsTbl     = ax.armFields
            armFieldNamesTbl = ax.armFieldNames
            found = true
            break
        if found: break
      doAssert found,
        "isVariantField on svMultiVariant: no axis owns field " &
        stmt.vfFieldName
    else:
      # #163 regression fix (post-round-9 gate). A receiver that is
      # NEITHER `svVariant` NOR `svMultiVariant` here is reachable ONLY
      # when the receiver's own CONSTRUCTION already declined --
      # `dsl_parser.nim`'s `itVariant`/`itMultiVariant` object-constructor
      # edge-case arms bind a type-correct but non-variant-shaped
      # placeholder (`unsupportedFieldPlaceholder`: no literal IR
      # constructor exists for a variant-shaped value, so the placeholder
      # is a plain `mkIntLit(0)`, deliberately not variant-shaped) --
      # never a fresh walker bug. This used to be a bare `doAssert false`
      # (an uncatchable `AssertionDefect`, reported at the `runSymex`
      # boundary as `weInternalWalkerFault` -- an internal-bug
      # attribution for an ordinary, everywhere-applicable consequence of
      # an existing, honestly-classified construction gap). Degrade this
      # ONE path in-band instead: record the classified decline and drop
      # the path (mirrors `isUnsafeCast`'s "halt this path" idiom) rather
      # than fabricate arm data for a receiver that was never a real
      # variant to begin with. RFC-0005 S1: HALT site — token discarded.
      w.halted(seVariantFieldOnDeclinedCtor,
        "variant field '" & stmt.vfFieldName & "' read on a " &
             "receiver whose construction was already declined " &
             "(non-variant SymVal kind=" & $recv.kind & ") " &
             "(seVariantFieldOnDeclinedCtor)")
      continue
    # Build the matching-arm equalities + collect each arm's SymVal
    # for the requested field.
    var armEqs: seq[Z3Bool]
    var armBindings: seq[(int, SymVal)]
    for tag in stmt.vfMatchingTags:
      let armNames  = armFieldNamesTbl[tag]
      let fieldIx   = armNames.find(stmt.vfFieldName)
      if fieldIx < 0: continue
      let armEq =
        if tag == -1:
          # Phase 14 cycle A2: else-arm membership is the
          # conjunction of negations against all non-else arms on
          # the same axis (ADR-0003 D2).
          var conj: Z3Bool
          var seeded = false
          for otherTag in armFieldsTbl.keys:
            if otherTag == -1: continue
            let neg = not variantDiscEq(disc, int64(otherTag))
            if not seeded: conj = neg; seeded = true
            else:          conj = conj and neg
          if not seeded:
            raise newException(ValueError,  # [raise-audited: category-c: documented parser-invariant (own comment family: parser should not have emitted such an IR)]
              "isVariantField: else-only variant has no non-else " &
              "arms to negate against (degenerate; the parser " &
              "should not have emitted such an IR)")
          conj
        else:
          variantDiscEq(disc, int64(tag))
      armEqs.add armEq
      armBindings.add (tag, armFieldsTbl[tag][fieldIx])
    doAssert armEqs.len > 0,
      "isVariantField: parser produced an empty matchingTags list"
    var inArmCond = armEqs[0]
    for k in 1 ..< armEqs.len:
      inArmCond = inArmCond or armEqs[k]
    let outOfArmCond = not inArmCond
    # FieldDefect fork — Phase 16 D1a unconditional under `wmExplore`;
    # R14 narrows the `wmFollowConcrete` case — see `maybeForkDefect`'s
    # doc comment (same shape as `isIndex`'s OOB fork: a discarded-result
    # side channel for try/except routing + target-witness search, not a
    # fork-every-arm construct).
    var declinedSide: seq[Path]
    var exactCond: Option[Z3Bool]   # the out-of-arm side the bytes answer
    var exactVal: SymVal
    var cppWrite = false
    var activeOk: Option[Z3Bool]   # int6-f: a checked read's active member
    if fieldsUnchecked():
      # RFC-0016 PRC-07: no `FieldDefect`; the side is a union access.
      if recv.kind == svVariant and recv.vActive != nil and stmt.vfWrite:
        # slice B, cpp: a write to any member is defined and makes it the
        # active one (`lowerVariantFieldSet` records it): no side to halt
        # or decline, and no constraint on the path.
        cppWrite = true
      else:
        var denv = p.env
        var scratch: seq[Z3Bool]
        denv[stmt.vfRetName] = allocateSym(stmt.vfFieldTy,
          freshDegradeName("__declinedFieldRead"), scratch)
        var declinedCond = outOfArmCond
        var declineAny = true
        # slice B, c: the out-of-arm side is the union's bytes. A read is
        # the field's bytes of the image (every arm alike); a write is
        # exact in the arms it leaves with a value in every field, the
        # rest is declined (`fieldChecksOffLayout`, path-local).
        if recv.kind == svVariant and recv.vImage.len > 0 and
           stmt.vfVariantTy != nil:
          let lay = vl.variantLayout(stmt.vfVariantTy)
          let tp = vl.accessPlace(lay, stmt.vfMatchingTags, stmt.vfFieldName)
          if lay.ok and tp.isSome:
            if stmt.vfWrite:
              var ok: Z3Bool
              var seeded = false
              for tag in recv.vArmFields.keys:
                if tag < 0 or tag in stmt.vfMatchingTags or
                   not writeExactArm(lay, tag, tp.get):
                  continue
                let c = variantDiscEq(disc, int64(tag))
                ok = (if seeded: ok or c else: c)
                seeded = true
              if seeded:
                exactCond = some(ok)
                exactVal = denv[stmt.vfRetName]   # the pre-write read is unused
                declinedCond = declinedCond and not ok
            else:
              let v = bitsPlace(imgReadDef(recv.vImage, tp.get.off - lay.unionOff,
                                           tp.get.size),
                                tp.get, none((vl.Place, SymVal)))
              if v.isSome:
                exactCond = some(outOfArmCond)
                exactVal = v.get
                declineAny = false
        if declineAny:
          declinedSide = inactiveFieldSide(p, declinedCond, denv, stmt.vfLoc, w,
                                           stmt.vfWrite)
    else:
      maybeForkDefect(p, outOfArmCond, "FieldDefect", none(string), w)
      # RFC-0016 int6-f (cpp): a checked read the discriminator admits is
      # still a read of a union member; where an unchecked region wrote
      # another arm's member (`vActive`), it is not the active one, which is
      # undefined. A write makes its member active (`lowerVariantFieldSet`).
      if recv.kind == svVariant and recv.vActive != nil and not stmt.vfWrite:
        var actIn: Z3Bool
        var seeded = false
        for tag in stmt.vfMatchingTags:
          if armFieldNamesTbl[tag].find(stmt.vfFieldName) < 0: continue
          let c =
            if tag == -1:
              var conj = mkBool(true)
              for otherTag in armFieldsTbl.keys:
                if otherTag != -1:
                  conj = conj and not variantDiscEq(recv.vActive[], int64(otherTag))
              conj
            else: variantDiscEq(recv.vActive[], int64(tag))
          actIn = (if seeded: actIn or c else: c)
          seeded = true
        if seeded:
          let inactive = inArmCond and not actIn
          discard inactiveFieldSide(p, inactive, p.env, stmt.vfLoc, w,
                                    checkedRead = true)
          activeOk = some(not inactive)
    if w.shouldStop: return exact(@[])
    survivors.add declinedSide
    # In-arm path — bind retName to the ite-chain over arms.
    var bound = armBindings[armBindings.len - 1][1]
    for k in countdown(armBindings.len - 2, 0):
      let eqB = variantDiscEq(disc, int64(armBindings[k][0]))
      bound = iteSV(eqB, armBindings[k][1], bound)
    # RFC-0005 S6b: drain the arm fold's merge-degrade taint onto THIS
    # path (see `isIndex`'s array arm: a direct `iteSV` call).
    let pM = drainPendingLowerEffects(p)
    var newEnv = pM.env
    newEnv[stmt.vfRetName] = bound
    # RFC-0016 PRC-07 slice B: a field whose bytes a constructor Nim emits
    # without zeroing left unwritten is indeterminate; observing one taints
    # the path (a hit through it is replayed), as a `{.noinit.}` read does.
    proc observed(path: Path; val: SymVal; w: var WalkCtx): Path =
      let part = unwrittenIn(val)
      if part.len == 0: return path
      forkPathTainted(path, path.pc, path.env, w.degrade(
        unwrittenKind(part), unwrittenMsg(part), ub = unwrittenUb(part)))
    if cppWrite:
      survivors.add forkPath(pM, pM.pc, newEnv)
    else:
      var inArm = forkPath(pM, pM.pc & @[inArmCond] &
                             (if activeOk.isSome: @[activeOk.get] else: @[]),
                           newEnv)
      survivors.add (if stmt.vfWrite: inArm else: observed(inArm, bound, w))
    if exactCond.isSome:
      var envX = pM.env
      envX[stmt.vfRetName] = exactVal
      var exact = forkPath(pM, pM.pc & @[exactCond.get], envX)
      survivors.add (if stmt.vfWrite: exact else: observed(exact, exactVal, w))
  exact(survivors)

proc walkCallArm(stmt: IRStmt, paths: seq[Path],
    w: var WalkCtx): Survivors {.noinline.} =
  ## RFC-0005 batch 6. `walkStmt`'s `isCall` arm, in a proc of its
  ## own: `walkStmt` recurses once per statement nesting level and per
  ## call level, and a debug build gives every arm's locals their own
  ## stack slots in its one frame.
  # R14: a resolved `isCall` is NOT itself a fork-every-arm construct —
  # `stmt.callee` names exactly ONE statically-resolved `ProcSig` (the
  # opaque/uncached/uninstantiated/depth-capped early-outs below all
  # produce exactly one path per input path too, via a fresh havoc'd
  # retSym; only the raise-escape channel can add more, orthogonal to
  # `w.mode`). The callee body is walked with `walk(sig.body, ...)` —
  # THIS SAME `w` (mode/concreteEq carried by reference) — so any
  # `if`/`while`/etc. INSIDE the callee already follows the concrete
  # trace correctly once THEIR OWN dispatch arms do (isIf per G1b;
  # isWhile/isVariantReassignSymbolic per this R14 pass). There is no
  # separate "which arm of this call" decision for follow-concrete to
  # narrow at the call site itself — the discard below is correct BY
  # CONSTRUCTION, not an oversight.
  case w.mode
  of wmExplore: discard
  of wmFollowConcrete: discard
  # ---- #137: opaque effectful call ----
  if stmt.opaque:
    # Issue #163 slice 4: an opaque call the parser proved INERT
    # (`isInertOpaqueCall`, dsl_parser.nim — statement position, every
    # argument plainly value-typed) is a no-op here: no taint, no
    # `w.sawUnknown`, no classified error. Returning the input paths
    # unchanged is exactly what an empty block does, and is identical to
    # the treatment `{.symexTransparent.}`'s parse-time drop (slice 1)
    # produces for the same shape of call.
    #
    # Soundness: with no bound result and nothing writable passed in, the
    # only channel left for such a callee to affect the SUT is a
    # module-level global (or a capture). The walker models globals; the
    # parser sets `opaqueInert` only where that channel is closed: a
    # catalogued stdlib routine writes no user global (RFC-0005 S8as), and a
    # user, `{.symexOpaque.}` or foreign callee is inert only when its effect
    # summary (`opaqueWriteSummary`, `opaqueArgEffects`) says it writes
    # nothing the SUT reads, with its raises forked (`opaqueRaiseTypes`,
    # `opaqueDefectTypes`). Dropping the taint here cannot introduce a false
    # verdict. What
    # it forgoes is a callee that never returns or raises (`echo` can
    # raise IOError) reached out of the intended order — a pre-existing,
    # symmetric gap: an opaque call placed AFTER the target was already
    # invisible to it before this change. Ordering, not soundness, moves.
    if stmt.opaqueInert:
      # #163 review R1: inert means a no-op for CONTROL FLOW and RESULT
      # BINDING (there is no bound result — `isInertOpaqueCall` only ever
      # fires in statement position), NOT a no-op for the ARGUMENT
      # EXPRESSIONS themselves. Those are real Nim expressions the caller
      # evaluates before the call runs, and `isInertArg` (dsl_parser.nim)
      # checks only the argument's STATIC RESULT TYPE — never its
      # expression shape — so an inline defect-fork shape among them
      # (div/mod by zero, signed overflow, `parseInt`, `s[i]`, a seq
      # slice — `rhsHasInlineDefectFork`'s class) is admitted here too,
      # and can raise on its own. Raise obligations are a RUNTIME side
      # effect of `lower()` (it populates sinks like `divByZeroConds`),
      # never a static IR artifact, so skipping the lowering — as the
      # fast path used to — makes the obligation never exist at all.
      #
      # Mirror the ordinary resolved-callee arm a few hundred lines
      # below (`argVals.add lower(p.env, stmt.cargs[i], argProto)`
      # followed by `drainScalarRaiseForks`): lower each argument for
      # its SIDE EFFECTS ONLY (the value itself is discarded — there is
      # nothing to bind on the inert path) and drain the raise-fork
      # sinks it populates before returning the survivors. The call
      # itself is still never walked and never taints — only the
      # arguments' own defect obligations become live.
      var out1: seq[Path]
      for p in paths:
        if w.shouldStop: return exact(@[])
        seedCallerHeapThreadvars(p)
        w.sinks.convFloatToIntBoundConds = @[]
        w.sinks.rangeDefectConds = @[]
        w.sinks.parseIntRaiseConds = @[]
        w.sinks.divByZeroConds = @[]
        w.sinks.overflowConds = @[]
        w.sinks.strIndexOobConds = @[]
        w.sinks.seqOobConds = @[]
        w.sinks.arithTrapConds = @[]
        w.sinks.uninitReadConds = @[]                ## RFC-0005 S8bv
        w.sinks.regexRaiseMsgs = @[]
        w.sinks.raiseOrder = @[]              ## RFC-0005 S8bb: the order log
        claimStrayPendingTaint()        ## RFC-0005 review R1-04
        for arg in stmt.cargs:
          discard lower(p.env, arg)
        let pd = drainPendingLowerEffects(p)
        for sp in drainScalarRaiseForks(pd, w):  ## parseInt/div-mod/overflow/index raise forks
          out1.add sp
      # RFC-0005 S8as: the call ran (on the survivors of its arguments'
      # raise forks), so each name its effect summary lists
      # (`IRStmt.opaqueHavoc`) may hold anything of its type now.
      # RFC-0005 S8ax: and each heap cell it reaches; and it may raise.
      # RFC-0016 W3-z R3 (finding U2): the main walk reads the scan of the
      # callee's body, before the call's own havoc taints the paths (the
      # listing takes clean paths only).
      if not w.tailGate and stmt.opaqueUndefined != {}:
        out1 = noteOpaqueUndefined(w, out1, stmt)
      for sp in out1: havocOpaqueWrites(w, sp, stmt)
      return exact(opaqueRaiseForks(w, out1, stmt))
    # Don't resolve a body; allocate fresh retSym; mark path
    # uncertain so any target reached on this path degrades to
    # sxUnknown rather than emitting an unsound witness.
    #
    # Issue #163: say WHY, and name the call. This arm used to set
    # `w.sawUnknown` bare, which is what the Invariant-7 backstop in
    # `runSymexImpl` reports as `weInternalWalkerFault` ("the walker itself
    # hit a bug here") — a misdiagnosis for an ordinary unmodelled call, and
    # the one an `echo` ahead of the interesting branch produced. The drain
    # dedups by message, so N calls to the same callee collapse to one
    # entry while two different callees each get named.
    # RFC-0005 S1: one `degrade` (record + token), forked onto every path.
    # RFC-0005 S8ax: a summary the parser could not bound says why.
    let d = w.degrade(feOpaqueCallUnmodelled,
      "opaque call `" & stmt.callee & "` is not modeled — " &
           (if stmt.opaqueWhy.len > 0: stmt.opaqueWhy & "; " else: "") &
           "its result " &
           "and any state it touches are unknown, so every path through it " &
           "is tainted. If the call cannot affect the code under test " &
           "(void, value arguments, nothing read back), mark it " &
           "`{.symexTransparent.}` and symex will drop it instead")
    var out2: seq[Path]
    for p in paths:
      var newEnv = p.env
      var pcInit: seq[Z3Bool]
      if stmt.retName.len > 0:
        inc w.synthZ3
        let z3Name = stmt.retName & "_op" & $w.synthZ3
        newEnv[stmt.retName] = freshRetSym(stmt.retTy, z3Name, pcInit)
      out2.add forkPathTainted(p, p.pc & pcInit, newEnv, d)
    return exact(out2)
  if not w.procs.hasKey(stmt.callee):
    # The callee's `ProcSig` is absent. Pre-G1c this "should not happen"
    # (the parser rejected unresolved callees at compile time); G1c adds a
    # legitimate cause — a generic instantiation OVER the per-proc cap is
    # intentionally NOT registered (`maxInstantiationsPerProc`), so its
    # `mkCall` key has no `ProcSig`. Treat it exactly like the depth-bail
    # arm: continue with a FRESH unconstrained retSym (so a downstream read
    # of `stmt.retName` does not KeyError) and mark the surviving paths
    # uncertain so any target reached on them degrades to sxUnknown — never
    # an unsound witness. `geInstantiationCapped` is surfaced from
    # `prog.parseErrors` (see `runSymexImpl`), so the unknown is never silent.
    # RFC-0005 S1b (§2.2 table, §2.5 point 3): the decline's kind now rides
    # the never-registered callee KEY (`unregisteredCalleeKey`, minted by
    # `ensureProcRegistered` for the over-cap / distinct-barrier /
    # unresolvable-`getImpl` declines), so this arm records it at the walk
    # site through `degrade` — the recorded error is the run act and its
    # token the path act (was a kindless run mark + kindless ⊤ token). A
    # missing callee with NO parse-time decline behind it has no modelled
    # cause at all: that is a walker/parser bug, recorded as such.
    var declineKind: SymexErrorKind
    # RFC-0016 K7b: a decline of class `dcOmitted` (`feUnadmitted`) halts:
    # continuing on a fresh return value would carry no taint, so a hit past
    # the call would be a clean `sxSat`.
    if unregisteredCalleeKind(stmt.callee, declineKind) and
       classOf(declineKind) == dcOmitted:
      return w.halted(declineKind,
        "call to unregistered callee `" & stmt.callee & "` reached at " &
             "walk time -- declined at parse time (" & $declineKind &
             "); the path ends here, what follows is not modelled",
        scope = calleeKeyed(stmt.callee))
    let d =
      if unregisteredCalleeKind(stmt.callee, declineKind):
        w.degrade(declineKind,
          "call to unregistered callee `" & stmt.callee & "` reached at " &
               "walk time — declined at parse time (" & $declineKind &
               "); the call returns a fresh unconstrained value and the " &
               "callee's effects are not modelled",
          scope = calleeKeyed(stmt.callee))   # RFC-0005 S8 (§2.5 point 3)
      else:
        w.degrade(weInternalWalkerFault,
          "call to callee `" & stmt.callee & "` reached at walk time with " &
               "no registered ProcSig and no parse-time decline behind it " &
               "(weInternalWalkerFault)")
    var out2: seq[Path]
    for p in paths:
      var newEnv = p.env
      var pcInit: seq[Z3Bool]
      if stmt.retName.len > 0:
        inc w.synthZ3
        let z3Name = stmt.retName & "_cap" & $w.synthZ3
        newEnv[stmt.retName] = freshRetSym(stmt.retTy, z3Name, pcInit)
      out2.add forkPathTainted(p, p.pc & pcInit, newEnv, d)
    return exact(out2)
  let sig = w.procs[stmt.callee]
  # Statistics
  if not w.callStats.hasKey(stmt.callee):
    w.callStats[stmt.callee] = CallStat(name: stmt.callee, walked: 0, cacheHits: 0)
  # Depth check. RFC-0010 B4 round 2 (REVERTED): a `cap > 0 and` guard was
  # added here so `maxCallDepth = 0` would mean unlimited, matching
  # `maxFrontierSize`/`maxSplitParts`'s house style. Two independent
  # reviewers reproduced a SIGSEGV under `maxCallDepth: 0` against ordinary
  # linear recursion (e.g. `f(n) = if n > 0: f(n-1) + 1 else: 0`): with the
  # cap disabled, `walk` recurses NATIVELY once per SUT call-stack level,
  # and `w.activeCalls`'s cycle-breaking only fires for recursion with
  # IDENTICAL argument shapes (`argShapeKey`/`symValHash` hash the Z3 AST,
  # which differs at every level of `f(n-1)`) -- so it never catches this,
  # the ordinary case, not a pathological one. A native-stack-exhaustion
  # SIGSEGV takes the whole test BINARY down (every other suite sharing
  # it), which is worse than the `sxUnknown` this guard was meant to avoid
  # and a more severe Invariant-3 violation than the bug it fixed. Unlike
  # `maxClosureInlineCount` (`applyClosureGround` below, guard correctly
  # kept -- the walker declines a forward-declared self-referencing closure
  # with `ceClosureUnknownCallee` before it can recurse) there is no
  # equivalent decline here: EVERY recursive call reaches this depth check.
  # `maxCallDepth` is therefore a THIRD documented "0 does not mean
  # unlimited" exception alongside `maxLoopUnwind`/`seqInlineThreshold` --
  # see `ResourceBudget`'s umbrella doc comment and this field's own doc,
  # both in smt/types.nim, for the full rationale. An explicit 0 exhausts
  # on the very first call, by design; a caller wanting deep analysis
  # writes an explicit bound sized to the SUT's real max call depth
  # instead. RFC-0005 S8ca: a count cannot know what a level costs (more
  # on cpp than on c) or what the thread's stack holds, so a call is also
  # not inlined when the native stack left is under one more level's need
  # (`nativeStackShort`, below).
  # RFC-0005 S8ax: past `maxCallDepth` the walk goes one level deeper
  # while the frontier is not growing (`depthMayExtend`) and the stack is
  # under the hard budget (`maxRecursionDepth`). A path no execution can
  # take is dropped first either way (S8an, below).
  # RFC-0005 S8ca: and, whatever the depth budget, not past the native
  # stack the walk needs (`nativeStackShort`); the decline is in-band, a
  # hard-budget decline the extension's root reads as one.
  let stackLeft = nativeStackShort(w)
  let overDepth = stackLeft >= 0 or
    w.callStack.len >= w.settings.budget.maxCallDepth
  var depthLive: seq[Path]
  var extendDepth = false
  if overDepth:
    for p in paths:
      if not pathInfeasible(w.z3, p, w.settings): depthLive.add p
    if depthLive.len == 0: return exact(@[])
    extendDepth = stackLeft < 0 and depthMayExtend(w, depthLive.len)
  if overDepth and not extendDepth:
    # The decline, and its history: `depthBail`.
    let atHard = stackLeft >= 0 or
      w.callStack.len >= hardCallDepth(w.settings)
    if atHard: inc w.depthHardHits
    if stackLeft >= 0: nativeStackCutFlag = true
    exact(depthBail(w, stmt, depthLive,
      (if stackLeft >= 0: dcutStack
       elif atHard: dcutHard
       else: dcutFrontier), stackLeft))
  else:
    let paths = (if extendDepth: depthLive else: paths)  # RFC-0005 S8ax
    # RFC-0005 S8ax: the first extended level is the extension's root. A
    # recursion that reaches the hard budget below it is unbounded on
    # some path; every path it returns then carries a chain of returns as
    # long as the extension, and each later query pays for it. Measured
    # (Linux, Z3 5.1, loaded host) on `sumTo(n) == 465` with `n >= 0`
    # unconstrained: 44.5 s declining at `maxCallDepth = 3` without the
    # extension, 393 s with a hard budget of 4 when the paths that
    # bottomed out within it were kept, killed at 900 s past 5. So the
    # root drops everything the extension walked and declines here, at
    # `maxCallDepth`, exactly as before S8ax: an unbounded recursion costs
    # what it did, and only one its arguments bound is followed.
    let extRoot = extendDepth and
      w.callStack.len == w.settings.budget.maxCallDepth
    let hardMark = w.depthHardHits
    let outerExtMark = w.extHardMark
    if extRoot: w.extHardMark = hardMark
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop:
        w.extHardMark = outerExtMark
        return exact(@[])
      # RFC-0005 S8ax: abandoned (`depthMayExtend`); the root declines.
      if extRoot and w.depthHardHits > hardMark: break
      # Phase 15 R1b: seed the caller-heap threadvars from THIS path so a
      # CLOSURE call lowered out of `p.env` below (a closure passed as an
      # argument, or invoked while lowering an actual) descends with this
      # path's threaded heap (ADR-0010 R1b — the closure-arm companion to the
      # structural `isCall` forkPath threading).
      seedCallerHeapThreadvars(p)
      # Lower actuals in the caller env once; reused for cache key
      # and for callee env construction.
      var argVals: seq[SymVal]
      w.sinks.convFloatToIntBoundConds = @[]  ## CR-9 Stage 6 Group-1: WalkCtx field
      w.sinks.rangeDefectConds = @[] ## R16-2: WalkCtx field
      w.sinks.parseIntRaiseConds = @[]        ## CR-9 Stage 6 Group-2: WalkCtx field
      w.sinks.divByZeroConds = @[]            ## R16-3: WalkCtx field
      w.sinks.overflowConds = @[]             ## R16-4: WalkCtx field
      w.sinks.strIndexOobConds = @[]          ## SND-4: WalkCtx field
      w.sinks.seqOobConds = @[]                ## N14: WalkCtx field
      w.sinks.arithTrapConds = @[]            ## RFC-0005 S8i: WalkCtx field
      w.sinks.uninitReadConds = @[]                ## RFC-0005 S8bv
      w.sinks.regexRaiseMsgs = @[]            ## RFC-0005 S8ay: WalkCtx field
      w.sinks.raiseOrder = @[]                ## RFC-0005 S8bb: the order log
      claimStrayPendingTaint()          ## RFC-0005 review R1-04
      for i, formal in sig.params:
        ## v69 (sello #1): shape a bare-literal actual at the FORMAL's width.
        ## Round-6 B5 (ADR-0028 Leg 1, chained composition): `intLitProto`
        ## always shapes a plain `itInt` formal's literal actual as BV — the
        ## type-driven default. A formal `collectIntOffsetParams` traced
        ## (`IRParam.isIntOffset`, now also set for CALLEES via
        ## `parseCalleeImpl`, not just top-level entry procs) instead needs
        ## an svInt proto, so a LITERAL offset argument (e.g. the corpus's
        ## own `readCStringHelper(s, 0)` first hop) arrives Int-sorted
        ## exactly like a traced VARIABLE argument already does (a
        ## non-literal lowers untouched regardless of proto — this only
        ## ever affects literal shaping).
        ## R3 (S2): stamp the proto's width metadata from the formal's own
        ## static type so a LITERAL offset argument keeps its overflow
        ## fork (`coerceIntLit` propagates it through onto the literal).
        let argProto = if formal.isIntOffset:
                         some(SymVal(kind: svInt, zi: mkInt(0),
                                     ziWidth: formal.ty.width,
                                     ziSigned: formal.ty.signed))
                       else: intLitProto(formal.ty)
        argVals.add lower(p.env, stmt.cargs[i], argProto)
      let pd = drainPendingLowerEffects(p)  ## re-review S-3: drain float bounds + closure-arg heap
      # CR-21/R16-3: drain parseInt and div/mod-by-zero raise conditions accumulated
      # during arg-lowering. `drainScalarRaiseForks` chains both drains and returns
      # the surviving non-raise continuations. The callee dispatch below runs once
      # per continuation (typically 1 path, so zero overhead on the common case).
      for p in drainScalarRaiseForks(pd, w):  ## R16-3: parseInt + div/mod-by-zero raise forks
        if w.shouldStop: break
        # Cache lookup — pure procs with deterministic-arg-shape hits
        # are served without re-walking. The cache entry's `pcDelta`
        # carries the returning-path constraints; we extend the
        # current path with them.
        let key = argShapeKey(stmt.callee, argVals)
        if key in w.activeCalls:
          # Mutual / direct recursion with identical args — the call
          # is already being walked further up the stack. Break the
          # cycle: return a fresh symbolic retval, mark uncertain.
          w.callStats[stmt.callee] = CallStat(
            name: stmt.callee,
            walked: w.callStats[stmt.callee].walked,
            cacheHits: w.callStats[stmt.callee].cacheHits + 1)
          var newEnv = p.env
          var pcInit: seq[Z3Bool]
          if stmt.retName.len > 0:
            inc w.synthZ3
            let z3Name = stmt.retName & "_cyc" & $w.synthZ3
            newEnv[stmt.retName] = freshCallRet(stmt, p.env, z3Name, pcInit)   # S8be
          # RFC-0005 S1b (§2.2 table): the cycle cut now records its own
          # `weRecursionCycleCut` through `degrade` (was a path-only
          # kindless ⊤ token that recorded nothing and marked the run only
          # if a later target hit on this path did). The callee's body —
          # its var-param/heap effects and raises — is not walked for this
          # occurrence, so the degrade is run-relevant even when the cut
          # path never reaches a finding.
          let d = w.degrade(weRecursionCycleCut,
            "recursive call to `" & stmt.callee & "` with an argument " &
                 "shape already being walked up the stack — cycle cut " &
                 "with a fresh unconstrained return value; the callee's " &
                 "effects are not modelled for this call " &
                 "(weRecursionCycleCut)")
          survivors.add forkPathTainted(p, p.pc & pcInit, newEnv, d)
          continue
        # RFC-0005 S8ax: a hit needs the same actuals (the key is a hash)
        # and, for a summary whose walk dropped an arm or path against its
        # context, the same drops under this caller's facts.
        var hit = -1
        let outerIn = outerState(p.env, sig.captures)   # RFC-0005 S8be
        if w.callCache.hasKey(key):
          let bucket = w.callCache[key]
          for ei in 0 ..< bucket.len:
            if cacheArgsSame(bucket[ei].args, argVals) and
               cacheOuterSame(bucket[ei].outer, outerIn) and
               pruneFactsHold(w.z3, p, bucket[ei].pruneFacts, w.settings):
              hit = ei
              break
        if hit >= 0:
          let entry = w.callCache[key][hit]
          w.callStats[stmt.callee] = CallStat(
            name: stmt.callee,
            walked: w.callStats[stmt.callee].walked,
            cacheHits: w.callStats[stmt.callee].cacheHits + 1)
          var newEnv = p.env
          if stmt.retName.len > 0:
            newEnv[stmt.retName] = entry.retSym
          for ex in entry.exits:
            survivors.add forkPath(p, p.pc & ex, newEnv)
          continue
        # Build callee env
        var calleeEnv: Env
        # #140: track var-param formal→actual binding for write-back.
        var varArgs: seq[(string, string)]   # (formalName, callerVarName)
        for i, formal in sig.params:
          calleeEnv[formal.name] = argVals[i]
          if formal.isVar and stmt.cargs[i].kind == iekVar:
            varArgs.add (formal.name, stmt.cargs[i].vname)
          # RFC-0005 S8bz (item 3): the copy-in observed nothing; a read of
          # the formal does.
          if formal.isVar and unwrittenIn(argVals[i]).len > 0:
            glWatched.incl formal.name
          # RFC-0005 batch 11: the global a `var` actual names (`glVarGlobal`).
          if formal.isVar:
            var root = stmt.cargs[i]
            while root != nil and root.kind in {iekField, iekIndex}:
              root = if root.kind == iekField: root.obj else: root.arr
            var g = ""
            if root != nil and root.kind == iekVar:
              if isGlobalEnvName(root.vname): g = root.vname
              else: g = glVarGlobal.getOrDefault(root.vname, "")
            if g.len > 0: glVarGlobal[formal.name] = g
            else: glVarGlobal.del formal.name
        # RFC-0005 S8an: the callee also reaches every module-level global
        # and, for a routine declared inside another, the enclosing
        # variables it captures. Nim shares those locations with the
        # caller; the walk copies each binding in here and carries the
        # callee's value back out on every exit (`carryOuterBindings`),
        # which is the same thing for one call running at a time. A root
        # of a `var`/`addr` actual that is one of them is WITHHELD
        # (`guarded`): it would reach the callee twice, and copy-in/
        # copy-out of the argument would then not be Nim's semantics. A
        # callee that touches a withheld name declines.
        let guarded = guardedOuterNames(stmt.cGuardRoots, sig.captures)
        discard threadOuterBindings(calleeEnv, p.env,
                                               sig.captures, guarded)
        # RFC-0005 S8ax: an address-taken variable the callee reaches by
        # name -- a capture, or the caller variable a `var` formal is --
        # keeps its address cell there (`inheritAddrCells`).
        let calleeAddrCells = inheritAddrCells(calleeEnv, p.env,
          w.frame.addrCells, varArgs, sig.captures, guarded)
        # Allocate retSym with a *runtime-fresh* Z3 name. Phase 15 G3: a
        # non-bool, non-void return type (float/string/composite as well as
        # int) routes through `freshRetSym` so a value-returning generic
        # instantiated at e.g. `float64` gets a correctly-typed placeholder.
        # Any init-side constraints (string byte-range floor, …) are threaded
        # onto the post-call survivor paths below (where `retSym` flows out).
        inc w.synthZ3
        let z3Name = stmt.retName & "_c" & $w.synthZ3
        var retInit: seq[Z3Bool]
        # RFC-0005 S8z: a closure-returning callee's value is the
        # `svClosure` its body builds, handed to the caller per returned
        # path below; there is no symbol to allocate (it was
        # `allocateSym(itUninterp)`, a `weInternalWalkerFault`).
        let closureRet = not sig.isVoid and
                         retCarriesClosure(stmt.retTy)   # S8be: tuples too
        let retSym = if sig.isVoid or closureRet:
                       SymVal(kind: svBool, bo: mkBool(true))  ## placeholder
                     else:
                       # Round-6 B5: thread the parse-time-traced offset
                       # positions so a chained scan's second-hop offset
                       # allocates svInt instead of the type-driven BV
                       # default (see `IRStmt.isCall.retIntOffsetPositions`).
                       # RFC-0005 S8be: otherwise in the sort of its
                       # actuals, bounded by its type (`freshCallRet`).
                       if stmt.retIntOffsetPositions.len > 0:
                         freshRetSym(stmt.retTy, z3Name, retInit,
                                     stmt.retIntOffsetPositions)
                       else:
                         freshCallRet(stmt, p.env, z3Name, retInit)
        let pruneMark = ctxPruneLog.len   # RFC-0005 S8as/S8ax
        # RFC-0005 S8ax: the walks entered at each call depth, the
        # frontier the adaptive depth reads (`depthMayExtend`).
        while w.depthWalks.len <= w.callStack.len: w.depthWalks.add 0
        inc w.depthWalks[w.callStack.len]
        let ptrRisk = varFormalPtrRisk(w, sig.params, stmt.cargs,
                                       stmt.cVarPtrSafe)   ## RFC-0005 S8bn
        w.callStack.add initCallFrame(w.exitClock,
          callee = stmt.callee, retSym = retSym,
          retName = stmt.retName,
          retTy = (if sig.isVoid: nil else: stmt.retTy),   # RFC-0005 S8l
          ptrRiskFormals = ptrRisk.risk,
          ptrSafeFormals = ptrRisk.safe,
          sp = nativeStackPointer())   # RFC-0005 S8ca: `nativeStackShort`
        w.callStats[stmt.callee] = CallStat(
          name: stmt.callee,
          walked: w.callStats[stmt.callee].walked + 1,
          cacheHits: w.callStats[stmt.callee].cacheHits)
        w.activeCalls.incl key
        # Phase 15 R1b call-ENTRY heap threading: the callee inherits the
        # CALLER's logical-heap state (`heaps` / `heapDepth` / `allocCounters`)
        # as its starting heap, instead of R1's fresh-empty default. `forkPath`
        # deep-copies all three (`deepCopyHeapState` + by-value `heapDepth`), so
        # a deref in the callee reads the SAME heap array the caller already
        # constrained (ADR-0010 R1b). Live as of R1 (heaps are no longer empty).
        let calleePath = forkPath(p, p.pc, calleeEnv)
        # RFC-0005 S8bs: a `var` actual that is a part of an address-taken
        # variable is bound to its cell (`bindVarLocs`).
        var entryCells = calleeAddrCells
        var elemShares: seq[(string, string)]
        var paramNames: seq[string]
        # RFC-0005 S8bu: each formal with the caller variable its actual
        # names (an `addr` actual's cell, `bindVarLocs`).
        var argVars: seq[(string, string)]
        for i, f in sig.params:
          paramNames.add f.name
          if i < stmt.cargs.len and stmt.cargs[i].kind == iekVar:
            argVars.add (f.name, stmt.cargs[i].vname)
        let locWhy = bindVarLocs(calleePath, p.env, w.frame.addrCells,
          w.frame.frameId, stmt.cVarLocs, varArgs, argVars, paramNames,
          entryCells, elemShares, w)
        if locWhy.len > 0:
          taintInPlace(calleePath, w.degrade(feUnsupportedOp,
            "RFC-0005 S8bs: call to `" & stmt.callee & "`: " & locWhy &
                 "; the callee's writes through the two are not modelled " &
                 "in its order (feUnsupportedOp)"))
        # Phase 15 E1: per-frame exception context. Save the caller's frame
        # (handler stack + in-flight exn) and install a fresh one before walking
        # the callee body — a `try` opened inside the callee must not leak to
        # the caller. Inert in E1 (handlerStack/inFlightExn always empty), wired
        # so E3/E5 raise-flow threading is correct by construction.
        pushFrame(w)
        # RFC-0005 S8be: and an element cell, likewise.
        inheritElemCells(calleePath, w.frameStack[^1].frameId,
          w.frame.frameId, varArgs & elemShares, sig.captures, guarded)
        let calleeFrameId = w.frame.frameId
        w.frame.addrCells = entryCells    ## RFC-0005 S8ax; S8bs
        anchorViews(calleePath, entryCells, calleeFrameId)   ## RFC-0005 S8ca
        w.frame.outerNames = sig.captures      ## RFC-0005 S8ax
        # RFC-0005 S8bx (item 3): an `mpairs` view passed with its table.
        let viewWhy = bindViewAliases(stmt, sig, p.env, w)
        let calleeIn =
          if viewWhy.len == 0: calleePath
          else:
            forkPathTainted(calleePath, calleePath.pc, calleePath.env,
              w.degrade(feUnsupportedOp,
                "`" & stmt.callee & "` receives an `mpairs` view and its " &
                "Table, " & viewWhy & " (RFC-0005 S8bx; feUnsupportedOp)"))
        let guardMark = callGuardedNames.len   ## RFC-0005 S8an
        for g in guarded: callGuardedNames.add g
        let fallThroughRaw = walk(sig.body, @[calleeIn], w)
        callGuardedNames.setLen(guardMark)
        # Round-6 A6-rider (walker v86): a callee whose body reaches the end
        # via IMPLICIT fallthrough (no explicit `return`) after a
        # CONDITIONAL, multi-statement `result = expr` assignment —
        # `parseCalleeImpl`'s own documented "general parser path" for
        # procs that aren't a single bare `result = expr` body (its
        # comment: "Procs with conditional / multi-step result-assignment
        # land via the general parser path ... need cycle-2 work to model
        # `result` as a mutable binding") — used to leave `retSym`
        # COMPLETELY UNCONSTRAINED: nothing tied the caller-visible return
        # value to the callee's actual computed `result`. Confirmed via
        # isolated bisection (`tests/tsymex_r6_a6r_callwitness.nim`) to be
        # a genuine SOUNDNESS gap, not merely a witness-extraction cosmetic
        # issue — a deliberately-unreachable target (whose impossibility
        # depends on the callee's read of its `seq[byte]` argument) proved
        # a FALSE `sxSat` pre-fix, with the reported witness floating free
        # of the solver's actual (nonexistent) justification — chapulin's
        # BLOCKER #12 "all-zero witness on an otherwise sxSat target" is
        # the visible symptom of this cause: `retSym` was free, so Z3 chose
        # a satisfying `retSym` directly and left every `data` cell
        # unconstrained (defaulting to 0), independent of whether the
        # target was genuinely reachable at all. The closure-call path
        # (`applyClosureGround`, see `retBindEq(funcApp, cp.env["result"])`
        # below) was ASSUMED at the time to already handle this exact shape
        # correctly -- that assumption was FALSE (confirmed N16, walker
        # v96): `applyClosureGround`'s fallThrough loop had no `else` twin
        # at all until N16 added one, mirroring this arm's idiom. As of
        # v96 both paths carry the identical else-twin; mirror that idiom
        # here for the ordinary call-inlining path. Composite
        # (non-scalar-wired) return kinds fall through to the SAME
        # in-band-degrade net `isReturn`'s explicit-return arm already
        # uses (never raise — Invariant 3), so an implicit-result
        # fallthrough of an unsupported composite kind stays a classified
        # `sxUnknown`, not a crash.
        var fallThrough: seq[Path]
        if sig.isVoid:
          fallThrough = fallThroughRaw
        elif closureRet:
          # RFC-0005 S8z: as `completeReturn`'s closure arm.
          for cp in fallThroughRaw:
            if cp.env.hasKey("result") and
               closureValueBuilt(cp.env["result"], stmt.retTy):
              fallThrough.add cp
            else:
              let d = w.degrade(ceUnsupportedHof,
                "a closure-returning callee returns no lambda the walker " &
                "built (an untouched nil proc, or a proc value from elsewhere)")
              fallThrough.add forkPathTainted(cp, cp.pc, cp.env, d)
        else:
          for cp in fallThroughRaw:
            if cp.env.hasKey("result"):
              let retVal = cp.env["result"]
              if retVal.kind notin retBindWiredKinds or
                  not retBindKindsAgree(retSym, retVal):  # RFC-0005 S8u
                # RFC-0005 S6b: `feUnsupportedOpHavoc` -- as `isReturn`'s
                # composite arm: the per-call `retSym` is left free, the
                # callee's effects ride `cp`, nothing is dropped.
                let d = w.degrade(feUnsupportedOpHavoc,
                  "composite-typed implicit-result fallthrough (kind " &
                       plainEnglishSymValKind(retVal.kind) & ") is not yet wired — path degraded " &
                       "to sxUnknown (feUnsupportedOp)")
                fallThrough.add forkPathTainted(cp, cp.pc, cp.env, d)
              elif (let nd = noinitReturnDegrade(retVal, w); nd.isSome):
                # RFC-0016 0.10.0 review H5: as `completeReturn`'s.
                fallThrough.add forkPathTainted(cp, cp.pc, cp.env, nd.get)
              elif not noteUninitReturn(retSym, retVal, cp.pc) and
                   svMentionsUninit(retVal):
                # RFC-0005 S8bq: as `completeReturn`'s.
                let d = w.degrade(uninitReadKind, uninitReturnMsg)
                fallThrough.add forkPathTainted(cp, cp.pc, cp.env, d)
              else:
                let (rSym, rVal) = reconcileInt(retSym, retVal)
                fallThrough.add forkPath(cp, cp.pc & @[retBindEq(rSym, rVal)],
                                         cp.env)
            else:
              # R2 (walker v90): a fallthrough path that never touched
              # `result` at all — legal Nim, and DISTINCT from the
              # `cp.env.hasKey("result")` branch above (v86's original
              # fix). `result` still holds the return type's ZERO VALUE on
              # such a path (Nim zero-initializes every `result` slot
              # before the body runs); pre-fix, `cp` was forwarded here
              # totally UNCHANGED — `retSym` stayed exactly as free as it
              # was before v86, reintroducing v86's own false-`sxSat` shape
              # for the never-assigned case (confirmed RED in
              # `tests/tsymex_r6_r2_zerodefault_result.nim`). Bind `retSym`
              # to `defaultZero(stmt.retTy, ...)` via the SAME `retBindEq`
              # the assigned branch above uses, instead of leaving it free.
              # `defaultZero`/`retBindEq` both still raise `ValueError` (or
              # `SymexRefUnresolvedError`) for a handful of composite kinds
              # neither is wired for (float, nested variant, distinct,
              # ref/ptr, non-string-keyed table, non-int64 hash set) — for
              # those, fall through to the SAME classified `sxUnknown`
              # decline the `retVal.kind notin {...}` branch above uses,
              # never bind a value the walker cannot back soundly.
              try:
                let zeroVal = defaultZero(stmt.retTy, stmt.retName & ".zerodefault")
                let (rSym, rVal) = reconcileInt(retSym, zeroVal)
                fallThrough.add forkPath(cp, cp.pc & @[retBindEq(rSym, rVal)],
                                         cp.env)
              except ValueError:
                # RFC-0005 S6b: `feUnsupportedOpHavoc` -- the free per-call
                # `retSym` ranges over the whole type, zero included.
                let d = w.degrade(feUnsupportedOpHavoc,
                  "composite-typed implicit-result fallthrough " &
                       "(untouched-result path, kind " & $stmt.retTy.kind &
                       ") has no sound zero-default (" &
                       getCurrentExceptionMsg() &
                       ") — path degraded to sxUnknown (feUnsupportedOp)")
                fallThrough.add forkPathTainted(cp, cp.pc, cp.env, d)
        # Phase 15 E3 inter-proc propagation. Capture any raises that escaped the
        # CALLEE's own handlers (recorded on the callee frame's `escaped` channel
        # by `routeRaise`) BEFORE popFrame restores the caller frame. After the
        # pop, re-route each through the CALLER's handler stack: a `try` around
        # this call site catches the helper's raise. Heap/pc state at the raise
        # point is preserved on `er.path` (R1b merge — structural now, inert until
        # Cluster R). The handler-body continuations join the call's survivors.
        let calleeEscaped = w.frame.exits.escaped.contents
        let calleeCells = w.frame.addrCells   ## RFC-0005 S8ax
        popFrame(w)
        for er in calleeEscaped:
          var rEnv = p.env
          # RFC-0005 S8an: the callee's writes to globals and captures
          # (before the `var` write-back, which is the later store).
          carryOuterBindings(rEnv, er.path.env, sig.captures, guarded)
          # RFC-0005 S8ac: the callee wrote its `var` formals through the
          # caller's variables before it raised; the handler sees those
          # writes (#140's write-back ran on the returning paths only).
          for (formalName, callerName) in varArgs:
            if er.path.env.hasKey(formalName):
              rEnv[callerName] = er.path.env[formalName]
          let carried = carryAddrCells(rEnv, er.path.env, calleeCells,
            varArgs, sig, guarded, w)   ## RFC-0005 S8ax
          var raisePath = forkPath(er.path, er.path.pc, rEnv)
          carryElemCells(raisePath, w.frame.frameId, calleeFrameId,
            varArgs & elemShares, sig.captures, guarded)   ## RFC-0005 S8be; S8bs
          raisePath = settleAddrCells(raisePath, carried, w)
          let touched = touchedGuard(er.path.env, guarded)
          if touched.len > 0:
            raisePath = forkPathTainted(raisePath, raisePath.pc, rEnv,
                                        guardDegrade(w, stmt.callee, touched))
          if er.crash: crashRaise(raisePath, er.typeId, w)   # RFC-0005 S8cu
          else: survivors.add routeRaise(raisePath, er.typeId, er.msg, w)
          if w.shouldStop:
            w.extHardMark = outerExtMark   # RFC-0005 S8ax
            return exact(survivors)
        let frame = w.callStack[w.callStack.high]
        w.callStack.setLen(w.callStack.high)
        w.activeCalls.excl key
        # Cache: single-return, single-fall-through-free, non-uncertain
        # calls cache for argShape-keyed reuse. Phase 15 E3: a callee that
        # escaped a raise is NOT cached — its summary is incomplete (a cache hit
        # would replay the normal return but silently drop the escaped raise).
        # ADR-0012: the cache replays only `pcDelta` (branch + retInit), NOT the
        # callee's `defectSurvivorPc`. An arith-defect callee normally ESCAPES
        # (calleeEscaped != [] ⇒ already not cached); but a callee that CATCHES
        # its own defect (try/except) could add a defect-survivor fact without
        # escaping. Conservatively skip caching when the callee added any such
        # fact, so a cache hit can never silently drop a `not overflow`/`not
        # divByZero` feasibility constraint. (Sound; merely less reuse.)
        # RFC-0005 S8u: nor when the callee allocated or wrote the heap
        # (`heapUnchanged`). A hit replays only `pcDelta`, so a second
        # `new(result)` callee with the same argument shape would return
        # the first call's address, and a heap write would be lost.
        # RFC-0005 S8ac: nor when a `var` formal is bound to a caller
        # variable. A hit replays only `pcDelta`, never the #140
        # write-back, so the second call's writes would be lost.
        # RFC-0005 S8an: nor when the callee reached a global or a
        # capture. A hit replays only `pcDelta`: a read would return the
        # first call's value across a write in between, and a write would
        # be lost.
        # RFC-0005 S8as/S8ax: a callee whose walk dropped a path or arm as
        # infeasible in this caller's context is cached with those drops
        # (`pruneFactsSince`): a hit re-checks them (`pruneFactsHold`).
        # S8as left such a call uncached, which cost `fib` every reuse.
        var pruneFacts: seq[seq[Z3Bool]]
        let exitPaths = frame.exits.returnedPaths.contents & fallThrough
        # RFC-0005 S8be: a callee threading globals, capture cells or
        # captures is cached keyed by their values, when no exit wrote
        # one (`exitKeepsOuter`); a withheld one still is not.
        var cacheable = calleeEscaped.len == 0 and not closureRet and
          varArgs.len == 0 and guarded.len == 0 and exitPaths.len > 0 and
          exitPaths.len <= callCacheExitsMax
        if cacheable:
          for cp in exitPaths:
            if not exitKeepsOuter(cp.env, outerIn, sig.captures) or
               cp.taint != {} or
               cp.defectSurvivorPc.len != p.defectSurvivorPc.len or
               not heapUnchanged(cp, p) or
               not factsPrefixSame(cp.pc, p.pc):
              cacheable = false
              break
        if cacheable and pruneFactsSince(pruneMark, p, pruneFacts):
          # Phase 15 G3: `retInit` (retSym init-side constraints, e.g. the
          # string byte-range floor) must ride in each exit's delta so a
          # cache REPLAY re-asserts them on the cached retSym.
          var exits: seq[seq[Z3Bool]]
          for cp in exitPaths:
            exits.add retInit & cp.pc[p.pc.len ..< cp.pc.len]
          let entry = CallCacheEntry(retSym: retSym, exits: exits,
                                     args: argVals, outer: outerIn,
                                     pruneFacts: pruneFacts)
          # A bucket holds one entry per distinct context it was walked
          # in, up to `callCacheBucketMax`; past it the call is walked.
          if not w.callCache.hasKey(key): w.callCache[key] = @[]
          if w.callCache[key].len < callCacheBucketMax:
            w.callCache[key].add entry
        for cp in frame.exits.returnedPaths.contents & fallThrough:
          var newEnv = p.env
          if stmt.retName.len > 0:
            newEnv[stmt.retName] =
              if closureRet and cp.env.hasKey("result") and
                  closureValueBuilt(cp.env["result"], stmt.retTy):
                cp.env["result"]    # RFC-0005 S8z
              elif cp.taint == {} and cp.env.hasKey("result"):
                # RFC-0005 S8bl (item 2): a result Z3's rewriter folds to
                # literals is bound AS them (the pc keeps `retSym ==
                # result`, so nothing else changes): the caller's later
                # terms over it stay ground. A scan chain over a pinned
                # string otherwise re-entered the S8ag split with a fresh
                # start symbol each iteration, and Z3 spent its whole
                # `seqQueryRLimit` refuting each infeasible loop exit.
                groundedLike(retSym, cp.env["result"])
              else: retSym
          # RFC-0005 S8an: the callee's globals and captures, as it left
          # them (before the `var` write-back, which is the later store).
          carryOuterBindings(newEnv, cp.env, sig.captures, guarded)
          # #140: propagate var-param mutations back to caller's env.
          for (formalName, callerName) in varArgs:
            if cp.env.hasKey(formalName):
              newEnv[callerName] = cp.env[formalName]
          let carried = carryAddrCells(newEnv, cp.env, calleeCells,
            varArgs, sig, guarded, w)   ## RFC-0005 S8ax
          # Phase 15 R1b return-MERGE: the post-call caller path carries the
          # callee's exit heap state back out (ADR-0010 R1b).
          # `forkPathMerged(cp, ...)` forks from `cp` (the returned
          # CALLEE path), so:
          #   * `heaps`: REPLACEMENT — the callee's final `heaps` become the
          #     caller's, so callee heap modifications are observed downstream.
          #   * `heapDepth`: threaded from `cp` (the callee's exit depth).
          # `allocCounters`, however, must NOT be a plain replacement: we take
          # `max(caller[T], callee[T])` per type key so the freshness invariant
          # holds — a post-call caller `new T` uses a counter strictly above any
          # callee allocation and cannot collide with a callee-allocated ref on
          # this path. (Inert until R2 wires `isNew`/`allocCounters` increments;
          # the merge is correct by construction now.)
          # Phase 15 G3: `retInit` threads the retSym init constraints onto the
          # surviving caller path (where `retSym` becomes visible).
          # R3 hardening / RFC-0005 S1: taint is neither a bare propagate
          # nor a token join here — a post-call path is tainted by anything
          # EITHER the caller (`p`) or the callee (`cp`) picked up, so this
          # site uses the dedicated `forkPathMerged` (the union
          # `cp.taint + p.taint`; was `p.uncertain or cp.uncertain`).
          let merged = settleAddrCells(
            forkPathMerged(cp, cp.pc & retInit, newEnv, p), carried, w)
          carryElemCells(merged, w.frame.frameId, calleeFrameId,
            varArgs & elemShares, sig.captures, guarded)   ## RFC-0005 S8be; S8bs
          # RFC-0005 S8an: the callee wrote a withheld root directly.
          let touched = touchedGuard(cp.env, guarded)
          if touched.len > 0:
            taintInPlace(merged, guardDegrade(w, stmt.callee, touched))
          for tkey, callerCount in p.allocCounters:
            let calleeCount = merged.allocCounters.getOrDefault(tkey, 0)
            if callerCount > calleeCount:
              merged.allocCounters[tkey] = callerCount
          survivors.add merged
    w.extHardMark = outerExtMark
    if extRoot and w.depthHardHits > hardMark:
      return exact(depthBail(w, stmt, paths, dcutHard))
    exact(survivors)

proc walkUnsupported(stmt: IRStmt, paths: seq[Path],
                     w: var WalkCtx): Survivors =
  ## RFC-0016 K7b. The `isUnsupported` arm. A path that reaches the decline
  ## but that no execution can take is dropped, not tainted (RFC-0005 S8bc);
  ## the rest meet the node's classified kind:
  ##   * a kind of class `dcOmitted` (`feUnadmitted`) is a HALT: the record
  ##     is the run act, and no path survives it, so no clean `sxSat` rides
  ##     past a cell the walker could not classify;
  ##   * any other kind forks every path through tainted (`surviving`), as
  ##     before: the dropped mutation left `env` stale relative to the real
  ##     program, and the taint chokepoints demote a later hit.
  ## RFC-0005 S8: the record carries the node's parse-minted anchor.
  ## RFC-0016 W1-d2 (W-07): there is no early return that passes a routine
  ## without overflow checks; the marker declines on every setting.
  var live: seq[Path]
  for p in paths:
    if not pathInfeasible(w.z3, p, w.settings): live.add p
  if live.len == 0: return exact(live)
  # RFC-0016 INT-76: a halting marker (`unHalt`) ends the path too: its
  # site bound no value, so a later read has nothing of the right sort.
  if classOf(stmt.unKind) == dcOmitted or stmt.unHalt:
    return w.halted(stmt.unKind, stmt.reason,
                    scope = siteAnchored(stmt.unMarker))
  let d = w.degrade(stmt.unKind, stmt.reason,
                    scope = siteAnchored(stmt.unMarker))
  surviving(live, d)

proc walkHeapViewed(stmt: IRStmt, paths: seq[Path],
                    w: var WalkCtx): Survivors =
  ## `walkHeapArm` one path at a time, for a walk holding a `viewMarks`
  ## entry: each path's heap writes are logged in place, which needs the
  ## paths `walkHeapArm` leaves live (the unwrap `walkStmt` does not do).
  var outs: seq[Path]
  for p in paths:
    if w.shouldStop: break
    let heapsBefore = p.heaps
    for q in walkHeapArm(stmt, @[p], w).live:
      if q != p: logInPlace(p, heapsBefore, q)
      outs.add q
  exact(outs)

proc walkStmt(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): Survivors =
  if w.shouldStop or stmt == nil or paths.len == 0:
    return exact(paths)
  case stmt.kind
  of isBlock:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    if stmt.blkArith.claims or stmt.blkScoped:
      # RFC-0016 W1-d2c. A routine body: its arithmetic is its own, whoever
      # called it, and the caller's resumes after it. RFC-0016 PRC-07, int6:
      # so are the checks it is compiled with, its effective scope.
      let pushed = arithFrames.enterBody(stmt.blkArith)
      if stmt.blkScoped: checkScopes.add stmt.blkOn
      let plain = IRStmt(kind: isBlock, stmts: stmt.stmts,
                         blkLabel: stmt.blkLabel)
      result = walkStmt(plain, paths, w)
      if stmt.blkScoped: checkScopes.setLen(checkScopes.len - 1)
      if pushed: arithFrames.leave()
      return
    if stmt.blkLabel.len == 0:
      return exact(walkBlock(stmt.stmts, paths, w))
    # RFC-0005 S8m: a labelled block is a break target (a source `block` a
    # `break` names, or a desugared loop body a `continue` leaves). Paths
    # that `break` it resume after it, beside its fall-through.
    w.loopStack.add initLoopFrame(w.exitClock,
                                  hsDepth = w.frame.handlerStack.len,
                                  label = stmt.blkLabel)
    let frameIx = w.loopStack.high
    var survivors = walkBlock(stmt.stmts, paths, w)
    # The parked exits were reconciled at the leaves and guards they passed
    # through (`reconcileCells`), and rejoin as they are.
    survivors.add w.loopStack[frameIx].exits.breakPaths.contents
    discard w.loopStack.pop()
    exact(survivors)
  of isIf:
    case w.mode
    of wmExplore: discard
    of wmFollowConcrete:
      ## RFC-fuzzer-nextgen G1b: fills the G1a seam. Follows only the
      ## concretely-taken arm and collects its predicate — see
      ## `walkIfFollowConcrete`'s doc comment above. `wmExplore`'s
      ## fork-every-arm loop below is UNCHANGED (only reached for
      ## `wmExplore`), so this branch does not perturb it.
      return walkIfFollowConcrete(stmt, paths, w)
    var survivors: seq[Path]
    if stmt.ifJoin and stmt.branches.len == 1 and stmt.elseBody == nil:
      # RFC-0005 S8w: a short-circuit chain's guard (`IRStmt.ifJoin`). The
      # body and the skip path are joined back into one path where that is
      # exact (`mergeJoinPaths`), so the rest of the chain -- and the
      # program after it -- is walked once, not once per outcome.
      let br = stmt.branches[0]
      for p in paths:
        if w.shouldStop: return
        # RFC-0016 review R5-2: reconciled where it is evaluated.
        let (condBool, cont) = evalCondSynced(p, br.cond, w)
        # RFC-0005 S8bb: no continuation (the guard raised on every path,
        # a rejected pattern) walks no arm and no skip path.
        # RFC-0005 S8bl: a guard that folds to a literal takes one side
        # only (`guardLiteral`).
        let lit = guardLiteral(condBool)
        for cp in cont:
          if lit == glFalse:
            survivors.add forkPath(cp, cp.pc, cp.env)
            continue
          let armPath = forkPath(cp, cp.pc & @[condBool], cp.env)
          let armOut = walk(br.body, @[armPath], w)
          if w.shouldStop: return
          if lit == glTrue:
            survivors.add armOut
            continue
          let skipPath = forkPath(cp, cp.pc & @[not condBool], cp.env)
          survivors.add mergeJoinPaths(cp, condBool, armOut, skipPath)
      return exact(survivors)
    for p in paths:
      if w.shouldStop: return
      # Phase 15 S10b: evaluating a branch condition may itself raise (a
      # `parseInt` on a non-digit string). The raise fork happens during cond
      # evaluation — its sub-path is routed as `ValueError` and the digits
      # continuation (`cp`) carries the non-raise constraint forward to ALL
      # subsequent arms and the else. `cp` threads that digits-constrained base
      # path across the branch loop.
      # RFC-0005 S8g: a condition's scalar drain can return SEVERAL
      # continuations (a float -> int conversion's in-range / out-of-range
      # split, parseInt's clean / lax split). Each one walks every later arm
      # and the else with its own negated-conditions prefix; only `cont[0]`
      # was followed before, so the others' arms were never explored.
      var states = @[(p, newSeq[Z3Bool]())]
      for br in stmt.branches:
        var next: seq[(Path, seq[Z3Bool])]
        for (cp0, accumNegated) in states:
          ## CR-9 Stage 2: encapsulate seed→reset→lowerBool→drain via wrapper.
          ## NI-1 semantics preserved: lowerBoolInExpr seeds from the CURRENT
          ## cp (the path passed to the wrapper), NOT the original p.
          # RFC-0016 review R5-2: the drain and the reconcile, where the
          # guard is evaluated (`evalCondSynced`).
          let (condBool, cont) = evalCondSynced(cp0, br.cond, w)
          # DES-4 invariant: `condBool` was computed from the pre-drain
          # `cp.env` and is a Z3 AST; neither the drain nor the reconcile
          # renames a term it reads, so it stays valid on every continuation.
          # RFC-0005 S8bb: the guard raised on every path (a rejected
          # pattern, `drainRegexRaises`): no arm, no later guard and no
          # else is walked. This re-added the pre-drain path as a
          # continuation, so code after a `RegexError` in a guard ran on
          # the call's placeholder value.
          # RFC-0005 S8bl: a guard that folds to a literal takes one side
          # only (`guardLiteral`).
          let lit = guardLiteral(condBool)
          for cp in cont:
            if lit != glFalse:
              let armPath = forkPath(cp, cp.pc & accumNegated & @[condBool],
                                     cp.env)
              if not ifArmInfeasible(w, armPath, condBool,
                                     cast[pointer](br.body), br.body):
                survivors.add walk(br.body, @[armPath], w)
              if w.shouldStop: return
            if lit != glTrue:
              next.add (cp, accumNegated & @[not condBool])
        states = next
      for (cp, accumNegated) in states:
        let elsePath = forkPath(cp, cp.pc & accumNegated, cp.env)
        if accumNegated.len > 0 and
           ifArmInfeasible(w, elsePath, accumNegated[^1],
                           cast[pointer](stmt), stmt.elseBody):
          continue
        if stmt.elseBody != nil:
          survivors.add walk(stmt.elseBody, @[elsePath], w)
        else:
          survivors.add elsePath
    exact(survivors)
  of isLet:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    var out2: seq[Path]
    for p in paths:
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      ## drainParseIntRaises is a FORK — NOT inside the wrapper; called on pb.
      ## v69 (sello #1): shape a bare-literal RHS at the DECLARED width.
      ## Round-6 B7r2 (walker v88): a literal-seeded scan/pair-loop counter
      ## (`stmt.lIsIntOffsetLocal`, set via `ctx.intOffsetLiteralLocals` —
      ## see its doc comment) gets an `svInt` proto instead — sound
      ## unconditionally for a literal (no def-use tracing risk) and a
      ## no-op for a non-literal `lvalue` (the proto is ignored by
      ## `lower`'s `iekVar` arm either way, so a genuine param-derived
      ## rebind like `var i = start` is unaffected — it already inherits
      ## `start`'s own representation via plain env lookup).
      ## R3 (S2): stamp the proto's width metadata from the local's own
      ## declared/inferred type (`stmt.lty`, when it is `itInt` — a bare
      ## `var pos = 0` infers `int`, width 64 signed; anything else falls
      ## back to that same 64/signed default, the static type an untyped
      ## int-literal local always has in Nim) so the promoted counter stays
      ## overflow-checkable (`coerceIntLit` propagates it onto the literal).
      let (loWidth, loSigned) = if stmt.lty != nil and stmt.lty.kind == itInt:
                                   (stmt.lty.width, stmt.lty.signed)
                                 else: (64, true)
      let letProto = if stmt.lIsIntOffsetLocal:
                       some(SymVal(kind: svInt, zi: mkInt(0),
                                   ziWidth: loWidth, ziSigned: loSigned))
                     else: intLitProto(stmt.lty)
      let (lv, pb) = lowerInExpr(p, stmt.lvalue, w, letProto)
      for cp in drainScalarRaiseForks(pb, w):   ## R16-3: parseInt + div/mod-by-zero raise forks
        var newEnv = cp.env
        newEnv[stmt.lname] = lv
        out2.add forkPath(cp, cp.pc, newEnv)
    exact(out2)
  of isAssign:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    var out2: seq[Path]
    for p in paths:
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      ## drainParseIntRaises is a FORK — NOT inside the wrapper; called on pb.
      ## v69 (sello #1): shape a bare-literal RHS at the target's CURRENT
      ## representation (assign IR carries no declared type).
      let (av, pb) = lowerInExpr(p, stmt.avalue, w,
                                 envLitProto(p.env, stmt.aname))
      for cp0 in drainScalarRaiseForks(pb, w):   ## R16-3: parseInt + div/mod-by-zero raise forks
        ## A range target's `RangeDefect` is its RHS conversion's
        ## (`lowerConvIntRange`), drained above with the other raises.
        var newEnv = cp0.env
        newEnv[stmt.aname] = av
        out2.add forkPath(cp0, cp0.pc, newEnv)
    exact(out2)
  of isWhile:
    case w.mode
    of wmExplore: discard
    of wmFollowConcrete:
      ## RFC-fuzzer-nextgen R14: fills the gap `walkIfFollowConcrete` (G1b)
      ## left open for `while` — see `walkWhileFollowConcrete`'s doc comment
      ## above. `wmExplore`'s fork-both-ways k-unroll below is UNCHANGED
      ## (only reached for `wmExplore`), so this branch does not perturb it.
      return walkWhileFollowConcrete(stmt, paths, w)
    # Phase 6: k-unroll. Each iteration forks on the guard.
    var survivors: seq[Path] = @[]
    var active = paths
    w.loopStack.add initLoopFrame(w.exitClock,
                                  hsDepth = w.frame.handlerStack.len)   # RFC-0005 S8m
    let frameIx = w.loopStack.high
    # RFC-0005 S8y: the loop's identity for `Path.loopIters` -- the IR
    # statement itself, the same object on every execution in this walk.
    let loopId = cast[int](stmt)
    # RFC-0010 B4: `unwind = 0` deliberately does NOT mean unlimited here —
    # see `walkWhileFollowConcrete`'s matching note above for the full
    # rationale (`maxLoopUnwind`'s own doc comment, smt/types.nim, already
    # says ">= 1"; the corrected false promise lived in the ResourceBudget
    # umbrella comment, not here). This arm's own reason is even more direct:
    # a loop whose trip count is symbolic keeps a feasible "guard still
    # true" arm on every iteration (RFC-0005 S8k prunes only the infeasible
    # ones; before S8k every iteration forked both arms unconditionally), so
    # `active` need not shrink on its own; only `unwind` is sure to empty it. Treating 0 as "no bound" would not
    # terminate for essentially ANY while loop reaching this arm — not just
    # pathological ones — which is a direct Invariant-3 (never hang) violation,
    # not a corner case worth silently capping around.
    let unwind = w.settings.budget.maxLoopUnwind
    for iter in 0 ..< unwind:
      if w.shouldStop: break
      if active.len == 0: break
      var nextActive: seq[Path]
      for p in active:
        ## CR-9 Stage 2: encapsulate seed→reset→lowerBool→drain via wrapper.
        ## RFC-0016 review R5-2: reconciled where it is evaluated
        ## (`evalCondSynced`), each test.
        let (cond, conds) = evalCondSynced(p, stmt.wcond, w)
        ## R1 (Invariant-3 soundness fix): the guard `stmt.wcond` may itself
        ## deposit scalar-raise-fork predicates (e.g. `s[i]` OOB, `x div 0`)
        ## into the sinks `lowerBoolInExpr` reset at entry. Undrained, those
        ## predicates were silently discarded — no raise fork, no bounds
        ## narrowing — so a target reachable only PAST a real raise on the
        ## guard was falsely `sxSat`. Drain here, exactly as `isIf` does for
        ## its branch conditions, and thread the survivor(s) forward into
        ## both the true (body) and false (exit) continuations. `cond` was
        ## built from `pb`'s (pre-drain) env, which the drain does not
        ## mutate, so it stays a valid Z3 AST against each drained survivor.
        for dp in conds:
          # RFC-0005 S8k: each arm is walked only if it is not provably
          # infeasible on `dp` (`loopArmInfeasible`: a literal guard is
          # decided without the solver, an undecided one is walked). Before
          # S8k both arms were forked on every iteration, so a concrete
          # loop's impossible "guard still true" continuations ran to the
          # unroll bound and reported `beBudgetExhausted`, and nested loops
          # grew as a power of the bound.
          if not loopArmInfeasible(w.z3, dp, cond, w.settings):
            # cond=true: walk body
            let truePath = forkPath(dp, dp.pc & @[cond], dp.env)
            truePath.atIteration(loopId, iter + 1)   # RFC-0005 S8y
            inc symexLoopIterations
            let afterBody = walk(stmt.wbody, @[truePath], w)
            # Continue-paths from the body merge into next-iter active.
            let cps = w.loopStack[frameIx].exits.continuePaths.takeAll()
            for cp in cps: nextActive.add cp
            for ap in afterBody: nextActive.add ap
          # cond=false: exit loop (use dp — the drained path with domain
          # bounds folded in).
          if not loopArmInfeasible(w.z3, dp, not cond, w.settings):
            let exitPath = forkPath(dp, dp.pc & @[not cond], dp.env)
            exitPath.atIteration(loopId, iter)       # RFC-0005 S8y
            survivors.add exitPath
      # RFC-0016 K7 (CRH-01): bound the sets this statement grows.
      capLoopFrontier(nextActive, w)
      capLoopFrontier(survivors, w)
      active = nextActive
    # RFC-0005 S8k: a path still active after the last unrolled body faces
    # the guard once more, exactly as the real loop does. Where the guard is
    # provably false there, the loop has ended on that path after exactly
    # `unwind` iterations: it leaves CLEAN through the exit arm, and no
    # iteration was omitted. Only a path whose guard may still hold is the
    # exhausted survivor below. The guard's own raises are routed as on
    # every earlier iteration (Nim evaluates it on this path too).
    if active.len > 0 and not w.shouldStop:
      var undecided: seq[Path]
      for p in active:
        let (cond, conds) = evalCondSynced(p, stmt.wcond, w)
        for dp in conds:
          if loopArmInfeasible(w.z3, dp, cond, w.settings):
            survivors.add forkPath(dp, dp.pc & @[not cond], dp.env)
          elif not pathInfeasible(w.z3, dp, w.settings):
            # RFC-0005 S8bl: a guard that folds to a literal `true` is
            # walked without the solver (`loopArmInfeasible`), so a path
            # whose pc is itself contradictory -- its every term ground, as
            # a scan over a pinned string now is -- ran to the bound and
            # recorded `beBudgetExhausted`. No execution takes it: dropped.
            undecided.add dp
      active = undecided
    # Break-paths exit the loop directly (with their accumulated pc/env).
    for bp in w.loopStack[frameIx].exits.breakPaths:
      survivors.add bp
    # Any paths still active after maxLoopUnwind iterations are
    # exhausted: cond=true was still SAT-able. Mark uncertain.
    if active.len > 0:
      # v64 (chapulin catalog #5(b), Invariant 7): record the classified
      # reason — a bare `sawUnknown` here yielded sxUnknown with EMPTY errors.
      # N20 (RFC-chapulin-hardening bucket-2, walker v121): `stmt.
      # wHasAssumedBound` (parse-time, `collectAssumedLoopBound`) routes to a
      # DISTINCT kind when a `symexAssume` on the guard's own variable(s)
      # exists — RFC-0005 S8k: an assume that really bounds the loop now
      # prunes the "guard still true" arm and never reaches here; one that
      # does not (too loose for the unroll budget) still does, and the
      # diagnostic should say so honestly instead of
      # implying an unbounded/genuinely-exhausted loop. Status/soundness
      # behavior is IDENTICAL either way (still tainted, still sxUnknown) —
      # only the classification differs.
      # RFC-0005 S6a: both kinds are `dcFabricated`. Every survivor below is
      # forked onto the post-loop continuation with `p.pc` — the guard still
      # satisfiable, NOT `not cond` — so the continuation is fiction (⊤ on
      # the path), and the omitted iterations void any UNSAT claim
      # (`{scIncomplete}` on the run).
      let cap = ckLoopUnwind     ## RFC-0016 K7a: both branches cut this cap
      var d: Degrade
      if stmt.wHasAssumedBound:
        # Round-6 fix round 3 (item 5): softened wording — `wHasAssumedBound`
        # is a purely LEXICAL name-match (`collectAssumedLoopBound`), with no
        # awareness of the assumed bound's actual MAGNITUDE relative to
        # `maxLoopUnwind`. A guard var appearing in e.g.
        # `symexAssume(n < 1_000_000)` against `maxLoopUnwind = 5` sets this
        # flag too, even though that "bound" is functionally useless for
        # fitting inside the unroll budget — see
        # `tests/tsymex_r6_n20_boundedloop.nim`'s magnitude-useless-assume
        # pin. The old wording ("trip counts beyond the bound are
        # unexplored") implied the assumed bound was known to be tight
        # enough to matter; it is not — the k-unroll never checks that.
        # RFC-0005 S1: `degrade` records + returns the survivors' token.
        d = w.degrade(beBudgetExhaustedAssumedBound,
          "while-loop k-unroll budget exhausted (maxLoopUnwind=" &
               $unwind & ") with the guard still satisfiable — an assumed " &
               "bound exists on a guard variable (symexAssume), but it " &
               "does not end the loop within the unroll budget on this path " &
               "(or the per-iteration feasibility check ran out of its " &
               "budget) (beBudgetExhaustedAssumedBound)", cap = cap)
      else:
        d = w.degrade(beBudgetExhausted,
          "while-loop k-unroll budget exhausted (maxLoopUnwind=" &
               $unwind & ") with the guard still satisfiable — trip counts " &
               "beyond the bound are unexplored (beBudgetExhausted)", cap = cap)
      for p in active:
        survivors.add forkPathTainted(p, p.pc, p.env, d)
    discard w.loopStack.pop()
    exact(survivors)
  of isBreak:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    let target = w.jumpTarget(stmt.brkLabel)
    if target < 0:
      # break outside any loop / named block. RFC-0005 S8m: the parser now
      # resolves every source `break` (a `block`'s, an unrolled loop's) to
      # its target, so this is reachable only from hand-built IR (Nim
      # rejects a `break` with nothing to leave).
      # RFC-0005 S1b: HALT site — the recorded `weBreakOutsideLoop` is the run
      # act (was a kindless run mark with no error); token discarded.
      return w.halted(weBreakOutsideLoop,
        "`break` reached with no enclosing loop or block to leave — the " &
             "breaking path is dropped (weBreakOutsideLoop)")
    # RFC-0005 S8m: through every `finally` the jump leaves (`exitJump`).
    for p in paths:
      exitJump(p, target, isCont = false, w)
    exact(@[])
  of isContinue:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    let target = w.jumpTarget("")
    if target < 0:
      # continue outside any loop — rejected by Nim itself, so reachable only
      # from hand-built IR. RFC-0005 S1b: HALT site, same kind as `break`.
      return w.halted(weBreakOutsideLoop,
        "`continue` reached with no enclosing loop — the path is dropped " &
             "(weBreakOutsideLoop)")
    # RFC-0005 S8m: through every `finally` the jump leaves (`exitJump`).
    for p in paths:
      exitJump(p, target, isCont = true, w)
    exact(@[])
  of isIndex:
    walkIndexArm(stmt, paths, w)
  of isIndexAssign:
    walkIndexAssignArm(stmt, paths, w)
  of isSeqPop:
    walkSeqPopArm(stmt, paths, w)
  of isTabKeys:
    walkTabKeysArm(stmt, paths, w)
  of isSetLen:
    walkSetLenArm(stmt, paths, w)
  of isVariantReassign:
    walkVariantReassignArm(stmt, paths, w)
  of isVariantReassignSymbolic:
    walkVariantReassignSymbolicArm(stmt, paths, w)
  of isVariantConstructSym:
    walkVariantConstructSymArm(stmt, paths, w)
  of isVariantField:
    walkVariantFieldArm(stmt, paths, w)
  of isReturn:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    # RFC-0005 S8l: a `return` inside a `finally` that runs on a RAISED exit
    # (`raisedFinallyLoops`, this frame) is backend-divergent -- c re-raises the
    # in-flight exception, cpp returns (probed). HALT the path.
    if w.frame.raisedFinallyLoops.len > 0:
      return w.halted(eeFinallyReturnOnRaise, "`return` inside a `finally` running on a raised exit: the c backend re-raises, cpp returns -- path dropped (eeFinallyReturnOnRaise)")
    # RFC-0005 S8j (top level) / R1 (callee): lower `stmt.retExpr` and
    # drain its scalar raises, so a raise in the returned expression routes
    # to its handler (`return 100 div x`, a `Natural` result's range check).
    # RFC-0005 S8l: the value is bound to `result` on the returning path
    # (Nim assigns `result` before leaving), and the path leaves through
    # `exitReturn`, which runs every enclosing `finally` of this frame first
    # (innermost first, each able to read and write `result`, raise, or
    # `return` again) and only then completes the return (`completeReturn`:
    # the SUT's `topReturnedPaths`, or the callee frame's `retSym` binding).
    # Before S8l a `return` completed at once and no `finally` ever ran on
    # it: `try: return x finally: symexTarget("fin")` never reached its label
    # (a false `sxUnsat`), in a callee and at top level.
    for p in paths:
      if stmt.retExpr == nil:
        exitReturn(p, w)
        continue
      let proto = if w.callStack.len == 0: envLitProto(p.env, "result")
                  else: some(w.callStack[w.callStack.high].retSym)
      ## RFC-0016 review R7-1: lowered, drained, bound to `result` and
      ## reconciled where the value is evaluated (`evalReturnSynced`): a
      ## bare closure call in it (`return c()`) may write a capture or an
      ## address-taken variable a `finally` or a `var` write-back then reads.
      let bound = evalReturnSynced(p, stmt.retExpr, proto, w)
      for bp in bound: exitReturn(bp, w)
    exact(@[])
  of isCall:
    walkCallArm(stmt, paths, w)
  of isAssert:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    var out2: seq[Path]
    for p0 in paths:
      if w.shouldStop: return
      ## CR-9 Stage 2: encapsulate seed→reset→lowerBool→drain via wrapper.
      ## drainScalarRaiseForks is a FORK — NOT inside the wrapper; called on pb0.
      let (cond, pb0) = lowerBoolInExpr(p0, stmt.acond, w)
      ## RFC-0005 S8g: every continuation (was `cont[0]` only).
      for p in drainScalarRaiseForks(pb0, w):  ## R16-3: parseInt + div/mod-by-zero raise forks
        discard forkDefect(p, not cond, "AssertionDefect", none(string), w)   ## Phase 16 D1a
        out2.add forkPath(p, p.pc & @[cond], p.env)
    exact(out2)
  of isAssume:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    ## Phase 16 SND-2 (ADR-0019): filter/prune, NOT assert. Shares steps
    ## (1) lowerBoolInExpr+drainScalarRaiseForks (whose stages include the
    ## float→int domain fork since RFC-0005 S8g),
    ## and (4) conjoin cond into pc VERBATIM with the isAssert arm above —
    ## those steps surface raises arising from EVALUATING cond itself (e.g.
    ## `symexAssume(1 div x == 0)` with symbolic x must still surface
    ## DivByZeroDefect) and are not assert-specific. The ONE thing omitted is
    ## step (3): `forkDefect(... "AssertionDefect" ...)` — a violatable
    ## `symexAssume` must NEVER itself produce a false sxRaised(AssertionDefect).
    ##
    ## RFC-0005 S8cb: a literal `false` (`quit`, `parseExitCall`) ends every
    ## path here. Carried on with a false pc, the path would lower what follows
    ## the `quit`, which an arm's stand-in value does not type.
    if stmt.acond.kind == iekBoolLit and not stmt.acond.bval:
      return exact(@[])
    var out2: seq[Path]
    for p0 in paths:
      if w.shouldStop: return
      let (cond, pb0) = lowerBoolInExpr(p0, stmt.acond, w)
      let pin = assumedStringPin(stmt.acond)
      for p in drainScalarRaiseForks(pb0, w):   ## RFC-0005 S8g: every continuation
        var env2 = p.env
        if pin.name.len > 0 and env2.hasKey(pin.name) and
           env2[pin.name].kind == svString:
          # RFC-0005 S8bl (item 2): `symexAssume(s == "lit")` pins `s` to
          # the literal on this path, so the path reads it AS the literal
          # from here on. The pc carries the equality, so every query is
          # unchanged up to it; what changes is that every later term over
          # `s` is ground, and Z3's rewriter evaluates it (`str.indexof`,
          # `str.substr`, `str.at` of a literal). Before, each read went
          # through the S8ag index-split word equations, and refuting an
          # infeasible loop exit over the pinned string took Z3 the whole
          # `seqQueryRLimit` (20M, ~100 s) per exit: an unrecognised pair
          # loop over a 9-pair literal (B6-1-red, B6-6) spent 200-750 s.
          # The parameter's model value is read from the solver's model,
          # which satisfies the same equality (`initialEnv` is untouched).
          env2[pin.name] = SymVal(kind: svString, str: mkString(pin.lit))
        out2.add forkPath(p, p.pc & @[cond], env2)
    exact(out2)
  of isTargetLabel:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    when defined(symexTestInjectWalkerFault):
      # CR-1c fault-injection hook (RFC-chapulin-hardening, Cluster 2):
      # compiled OUT of every normal build/test — only present under the
      # `-d:symexTestInjectWalkerFault` define, wired for exactly one test
      # file via its companion `tests/tsymex_phase16_CR1c_internal_fault.nim.cfg`
      # (Nim auto-reads `<testfile>.nim.cfg`). Raises a synthetic, genuinely
      # UNANTICIPATED-shaped exception (plain `ValueError`, indistinguishable
      # in TYPE from a real walker bug) the moment dispatch reaches a
      # sentinel `symexTarget("__inject_walker_fault__")` label, regardless
      # of whether that label is the run's actual solve target — this
      # exercises the last-resort `walk` dispatch catch end-to-end on BOTH
      # backends through the unmodified `dt-bounded.sh` harness.
      if stmt.tname == "__inject_walker_fault__":
        raise newException(ValueError,  # [raise-audited: category-c: test-injection-only (compiled out of every normal build; only present under -d:symexTestInjectWalkerFault, wired for one dedicated fault-injection test)]
          "CR-1c synthetic fault (symexTestInjectWalkerFault)")
      # Round-3 Defect-net variant (crash-doctrine decision, Corey
      # 2026-08-06): a SECOND sentinel raising an `AssertionDefect` — the
      # exact type the ~63 internal doAsserts produce — so the new outermost
      # `except Defect` arm is exercised end-to-end (including the fiber
      # trampoline ferrying the Defect across the fiber switch on Windows).
      if stmt.tname == "__inject_walker_defect__":
        raise newException(AssertionDefect,  # [raise-audited: category-c: test-injection-only (see above)]
          "round-3 synthetic defect (symexTestInjectWalkerFault)")
      # RFC-0005 S8ce: arm a raise shape (`injectShapeFault`); `dispatch`
      # fires here and now.
      const s8cePrefix = "__inject_s8ce_"
      if stmt.tname.startsWith(s8cePrefix) and stmt.tname.endsWith("__"):
        injectedShape = stmt.tname[s8cePrefix.len ..< stmt.tname.len - 2]
        injectShapeFault("dispatch")
    if w.target.kind == stkLabel and w.target.label == stmt.tname:
      for p in paths:
        if w.shouldStop: return
        # RFC-0005 S1c (§2.3): EVERY path reaching the label is solved,
        # tainted or not (was: a tainted path skipped `trySolve` -- "bailed-
        # call retSyms are unconstrained" -- and marked the run with a
        # kindless ⊤). A SAT on a clean path is a winner; a SAT on an
        # `scSpurious`-tainted path is a CANDIDATE (`admitSolvedHit`): the
        # enlarged program reaches the label, reality is unknown until S10's
        # replay, and it blocks `sxUnsat` without ever halting the walk.
        # RFC-0005 S8cn: in a closure body, the calling path's branches too. Its
        # pc starts empty: `if n != 77: f(n)` with `a == 77` in the body was a
        # false `sxSat` (a named callee keeps the pc).
        let solveOn = if closureBodyCallerPc.len == 0: p
                      else: forkPath(p, closureBodyCallerPc & p.pc, p.env)
        let (st, wit, candErrs, why) = solveTargetHit(w, solveOn)
        case st
        # RFC-0005 S1: `pathTaint` is PRODUCED here -- the hitting path's
        # taint, which `admitSolvedHit` routes on.
        of sxSat:    w.admitSolvedHit(RawResult(status: sxSat, witness: wit,
                                                soundness: Soundness(pathTaint: p.taint,
                                                     witnessUndefined: ubOrdinals(p.undefined)),
                                                undefinedViaOnly: ubOrdinals(p.undefinedViaOnly),   # W3-z R7
                                                nilDerefOnPath: p.nilDeref,
                                                errors: candErrs))
        of sxUnknown:
          # RFC-0005 S1b (§3.1 solver-undef row): Z3 gave up on a path that
          # reaches the target — record it (was a kindless run mark, so a
          # run whose only degrade was a solver resource-out was stamped
          # `weInternalWalkerFault` by the Invariant-7 backstop). Since S1c
          # this is also the ONLY unsolved skip (§2.3 "the unsolved-skip is
          # itself an omission"), on a tainted path as on a clean one.
          w.halted(beSolverUndef,
            "solver returned unknown on a path reaching target label `" &
                 stmt.tname & "` (queryRLimit=" &
                 $w.settings.budget.queryRLimit & "): " & why &
                 " (beSolverUndef)")
        of sxUnsat:  discard
        of sxRaised: discard   ## Phase 15 E2a: trySolve never returns sxRaised
    exact(paths)
  of isRaise:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    # Phase 15 E3 handler-aware raise. The walker reaches a `raise` on a feasible
    # (already-forked) path. We resolve the type id + message of the exception,
    # then hand each path to `routeRaise`, which consults the current frame's
    # handler stack: a matching `except` CONSUMES the raise (the path transfers
    # into the handler body and continues — those continuation paths flow OUT of
    # this arm); an unmatched raise either escapes to the caller (via the frame's
    # `escaped` channel, drained by the `isCall` arm) or surfaces at the SUT
    # boundary as a public `sxRaised` finding (E2b semantics, target-gated).
    #
    # Resolve the type id + message of the exception being raised. A bare
    # `raise` (re-raise) with an in-flight exn re-raises THAT exn's type;
    # with no in-flight exn and an empty handler stack it is an
    # `eeRaiseOutsideHandler` classified error (nothing to re-raise).
    var raiseTypeId = stmt.raiseTypeId
    var raiseMsg = evalRaiseMsg(paths[0].env, stmt.raiseMsg)
    if stmt.raiseIsReraise:
      if w.frame.inFlightExn.isSome:
        # Re-raise the in-flight exception (propagate its ExnRecord).
        let exn = w.frame.inFlightExn.get
        raiseTypeId = exn.typeId
        raiseMsg = exn.msg
      elif w.frame.handlerStack.len == 0:
        # Bare `raise` at top level with nothing to re-raise → classified
        # error. Round-6 N37: was a raw `raise (ref
        # SymexRaiseOutsideHandlerError)` -- this `isRaise` handling sits
        # directly inside `walk()`, reached from inside nested `walkBlock`
        # frames (a bare `raise` is valid Nim syntax anywhere, not only
        # lexically inside an `except` -- it re-raises the current
        # exception at runtime and Defects if there is none), the exact
        # C-backend goto-exception hazard N36 closed elsewhere in this
        # file, generalized here to a WALK-level (not lowering-level) site.
        # Empirically CONFIRMED this slice (stash method): a block+loop
        # wrapping the raising call proved a FALSE `sxUnsat` with ZERO
        # errors pre-fix; the identical shape via a plain (unwrapped) call
        # frame was already an honest classified `sxUnknown`. In-band
        # walk-level degrade instead, mirroring the sibling branch
        # immediately below (no survivors -- a raise that reaches neither a
        # handler nor a genuine re-raise target never returns control) plus
        # a classified error record (the sibling branch has none to record
        # since it has no offending TYPE/MESSAGE, unlike this one).
        # RFC-0005 S1: HALT site — token discarded; the recorded error is
        # the run act (was `for p in paths: w.sawUnknown = true`; `paths`
        # is never empty here — `walk` returns early on an empty frontier).
        return w.halted(eeRaiseOutsideHandler,
          "bare `raise` (re-raise) with no in-flight exception " &
               "(eeRaiseOutsideHandler)")
      else:
        # Inside a handler with no recorded in-flight exn yet — handler-stack
        # re-raise is E3+. Surface as unknown rather than guess.
        # (`paths` is never empty here — `walk` returns early on an empty
        # frontier — so the old per-path loop was an unconditional mark.)
        # RFC-0005 S1b: HALT site — the recorded kind is the run act (was a
        # kindless run mark with no error).
        return w.halted(eeHandlerReraiseUnmodelled,
          "bare `raise` (re-raise) inside a `try` with no in-flight " &
               "exception — not modelled (real Nim raises ReraiseDefect); " &
               "the path is dropped (eeHandlerReraiseUnmodelled)")
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return exact(survivors)
      survivors.add routeRaise(p, raiseTypeId, raiseMsg, w)
    exact(survivors)
  of isTry:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    # Phase 15 E3. `try: body  (except [T,…]: h)*  [finally: f]`. Push a handler
    # frame for the try's `except` arms onto the CURRENT call frame's handler
    # stack, walk the body (raises within consult this frame), then pop. A raise
    # in the body is routed by `routeRaise` to the first matching arm (exact
    # type-string membership at E3; subtype catch is E4; a bare `except:` is
    # catch-all). The handler bodies' continuation paths emerge from `routeRaise`
    # and are returned alongside the body's normal fall-through.
    let myDepth = w.frame.handlerStack.len  ## index this try's HandlerFrame sits at
    # A try claims, at its depth, only what was parked while it ran. An entry
    # parked before it began belongs to another try at the same depth: one
    # whose `except` arm holds this try, walked by `routeRaise` with the
    # handler stack cut back to the matched frame. Claiming that entry walked
    # an earlier catch's continuation through the rest of the arm a second
    # time.
    let since = w.exitClock.mark
    w.frame.handlerStack.add HandlerFrame(handlers: stmt.tryHandlers,
                                          finallyBlock: stmt.tryFinally,
                                          loopLen: w.loopStack.len)   # RFC-0005 S8m
    let bodyPaths = walk(stmt.tryBody, paths, w)
    # Pop our handler frame — it is no longer active once the body is walked.
    if w.frame.handlerStack.len > myDepth:
      w.frame.handlerStack.setLen(myDepth)
    # Claim, at our depth, every channel the frame holds for a try
    # (`HeldExits`, in its order); each claim leaves every other entry in
    # place, with its serial.
    let held = w.frame.exits.held.claimAt(since, myDepth)
    # The handler-body continuations for raises CAUGHT at our depth (routed
    # by `routeRaise` while walking the body or a callee called from the body).
    # These join the body's normal fall-through; the caught path exits the try.
    var continuations = bodyPaths
    for c in held.caught:
      continuations.add c.path
    # Phase 15 E5: the RAISED exit continuations deferred to this try's
    # finally (recorded by `routeRaise` on `pendingRaise` at our depth when a
    # raise in the body found no matching `except` but is guarded by our
    # `finally`). These run the finally on the RAISED path and re-propagate.
    let raisedConts = held.pendingRaise.contents
    # RFC-0005 S8l: the RETURN exits deferred to this try's finally
    # (`exitReturn` recorded them at our depth: a `return` in the body or in
    # an `except` arm). Only a try with a `finally` is ever recorded.
    var returnConts: seq[Path]
    for pr in held.pendingReturn:
      returnConts.add pr.path
    # RFC-0005 S8m: likewise the `break` / `continue` exits deferred to this
    # try's finally (`exitJump`: a jump in the body or an `except` arm).
    let jumpConts = held.pendingJump.contents
    if stmt.tryFinally == nil:
      # No finally: normal continuations flow through; any raised continuations
      # re-propagate immediately (re-route through the now-popped outer stack).
      var survivors = continuations
      for rc in raisedConts:
        if w.shouldStop: return exact(survivors)
        survivors.add routeRaise(rc.path, rc.typeId, rc.msg, w)
      exact(survivors)
    else:
      # Phase 15 E5 finally composition. The finally runs ONCE per exit
      # continuation (never combinatorially): once on the merged normal-exit
      # set, and once per raised-exit continuation. The handler stack is already
      # popped to `myDepth`, so a raise INSIDE the finally routes to the
      # NEXT-OUTER try/finally (or escapes / surfaces) — it does NOT re-enter
      # this finally (no loop).
      var survivors: seq[Path]
      # (a) NORMAL exits: walk finally; finally fall-through survives. A raise in
      #     the finally is routed by `routeRaise` (replaces — there is no
      #     in-flight exn on a normal exit, so a finally raise is a fresh raise,
      #     NOT an `eeRaiseOutsideHandler`). `inFlightExn` stays untouched (none).
      if continuations.len > 0:
        survivors.add walk(stmt.tryFinally, continuations, w)
        if w.shouldStop: return exact(survivors)
      # (a') RETURN exits (RFC-0005 S8l): walk the finally on each with
      #     `result` already bound, as Nim runs it. The finally's fall-through
      #     continues the SAME return outward (`exitReturn`: the next-outer
      #     finally of this frame, else the return completes). A raise in the
      #     finally is routed by `routeRaise` and replaces the return; a
      #     `return` in the finally is a new return exit that overrides it
      #     (the handler stack is already popped to `myDepth`, so neither
      #     re-enters this finally).
      if returnConts.len > 0:
        for fp in walk(stmt.tryFinally, returnConts, w):
          exitReturn(fp, w)
        if w.shouldStop: return exact(survivors)
      # (a'') JUMP exits (RFC-0005 S8m): walk the finally on each `break` /
      #     `continue` that leaves this try, as Nim runs it. Its fall-through
      #     continues the SAME jump outward (`exitJump`: the next-outer
      #     finally the jump leaves, else the target loop / block). A raise
      #     in the finally replaces the jump (`routeRaise`); a `return` or
      #     another jump in it overrides (probed: `try: return 5 finally:
      #     break` in a loop continues after the loop).
      for jc in jumpConts:
        for fp in walk(stmt.tryFinally, @[jc.path], w):
          exitJump(fp, jc.target, jc.isCont, w)
        if w.shouldStop: return exact(survivors)
      # (b) RAISED exits: for each, set `inFlightExn` to the original exn for the
      #     finally's duration (so a bare re-raise inside finally sees it), walk
      #     the finally on the raised path; the survivors are the paths where the
      #     finally fell through WITHOUT raising — on those the ORIGINAL exn is
      #     RE-RAISED (re-routed outward). Where the finally itself raised, that
      #     new exn was already routed by `routeRaise` and REPLACES the original
      #     (so we do NOT re-raise the original on those sub-paths).
      for rc in raisedConts:
        if w.shouldStop: return exact(survivors)
        let savedInFlight = w.frame.inFlightExn
        w.frame.inFlightExn = some(ExnRecord(typeId: rc.typeId, msg: rc.msg))
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8
        # RFC-0005 S8l: a `return` here declines; S8m: so does a jump that
        # leaves this finally.
        w.frame.raisedFinallyLoops.add w.loopStack.len
        let finallyNormal = walk(stmt.tryFinally, @[rc.path], w)
        discard w.frame.raisedFinallyLoops.pop()
        w.frame.inFlightExn = savedInFlight
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8
        for fp in finallyNormal:
          if w.shouldStop: return exact(survivors)
          # Finally fell through on this sub-path → re-propagate the ORIGINAL.
          survivors.add routeRaise(fp, rc.typeId, rc.msg, w)
      exact(survivors)
  of isDeref, isNew, isDerefWrite:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    # Stage 7 (CR-7) Cluster R: heap read, allocation, and heap write arms
    # extracted into `walkHeapArm` (defined above, before this proc body).
    # `isIndex` is left inline (handles Table/seq/array/ref — multi-theory).
    # RFC-0005 S8ca: an element's write-back (`dwInPlace`) on a path with a
    # live view is logged as in-place steps, path by path.
    var viewed = false
    if stmt.kind == isDerefWrite and stmt.dwInPlace:
      for p in paths:
        liveViewMarks(p, w)
        if p.viewMarks.len > 0: viewed = true
    if not viewed:
      walkHeapArm(stmt, paths, w)
    else:
      walkHeapViewed(stmt, paths, w)
  of isUnsupported:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    # SND-1: an unmodeled statement dropped its mutation, so `env` is now
    # STALE relative to the real program. Taint-and-continue (SND-1, RFC
    # Cluster 1): mirror the `maxCallDepth` bail arm above — mark the run
    # and fork every path through tainted rather than continuing with
    # unmarked (and therefore falsely-trustable) state. This is
    # Invariant-3-safe AND preserves downstream exploration: the existing
    # taint chokepoints (`isTargetLabel`, `routeRaise`) demote any later
    # sxSat/sxRaised on this path to sxUnknown, so a dropped mutation can
    # never surface a silently-wrong witness. RFC-0005 S1b (§2.2 table —
    # §0.2's flagship example): the node now carries its classified kind
    # (`mkUnsupported(kind, reason)`), so the arm records it through
    # `degrade` — the run act — and forks every path with its token (was a
    # kindless run mark + kindless ⊤ token, recording nothing). A Class-A
    # node's kind is its parse-time error's kind, recorded again HERE where a
    # path actually reaches the decline (the reach-anchored record §2.5
    # point 1 builds on); a Class-B node's is `feUnsupportedStmtKind`.
    # RFC-0005 S8: the reach record carries the node's parse-minted anchor.
    # RFC-0005 S8bc (item 5): a path that reaches the decline but that no
    # execution can take is dropped, not tainted, as S8an drops one at the
    # call-depth bail (`pathInfeasible`). The walker forks `if` arms without
    # a feasibility check, so a SCOPED decline (a parse-time guard such as
    # `newSeq`'s / `initTable`'s length above 2^20) was reached on every
    # path, bound or not: `if n < 0 or n > 50: return` then `newSeq(n)`
    # turned every dead label into sxUnknown. A dropped path has no
    # behaviour to lose (its every later query carries the same UNSAT
    # constraints); an undecided query keeps the path, tainted as before.
    # RFC-0005 S8bn's late-address and proc-field declines rely on this:
    # they sit under forks the walk makes without a feasibility check.
    # RFC-0016 W1-d2 (W-07): the S8cu early return that passed a routine
    # without overflow checks where the settings model the wrap is gone. Its
    # signed `+`, `-` and `*` are undefined on overflow in C, not a wrap, and
    # nothing here tells the arithmetic which routine it is in: the marker
    # declines (the degrade below) on every setting.
    walkUnsupported(stmt, paths, w)
  of isUndefined:
    # RFC-0016 PRC-07. The path performs an operation C leaves undefined: it
    # ends here through `haltUndefined`, decided at the op as the arithmetic
    # and index ones are (`decideUndefined`: provably unreachable is dropped
    # and logged, anything else halts).
    for p in paths:
      if w.shouldStop: break
      decideUndefined(p, stmt.udKind, w.z3.mkBool(true), stmt.udSite, w)
    exact(@[])
  of isUnsafeCast:
    case w.mode  ## RFC-fuzzer-nextgen G1a seam — inert until G1b/G2.
    of wmExplore: discard
    of wmFollowConcrete: discard
    # Phase 15 R11 (ADR-0010, RFC §R11). An unsafe pointer materialisation
    # (`cast[ptr T]`/`addr`/`unsafeAddr`) is unmodelable in the logical-heap
    # model. HALT the path: the verdict degrades to
    # `sxUnknown` (Invariant 3), and DROP the path (`@[]`) so the unmodelable
    # pointer binding (which was NOT added to env) is never referenced
    # downstream (a subsequent `p[]` deref would otherwise key-fault on the
    # unbound name). The classified `heUnsafeCast` (sevError) was emitted at
    # parse time into `prog.parseErrors` (drained into `RawResult.errors` on
    # every verdict branch), so the unknown is never silent.
    # RFC-0005 S1: the former `w.sawUnknown = true` here is gone — the run
    # coordinate is DERIVED at drain, and that parse-time sevError
    # `heUnsafeCast` (emitted by `dsl_parser.nim` at the one site that builds
    # this node) is exactly what derives it.
    # RFC-0005 S8 (§2.5 point 1): the halt now ALSO records its reach, under
    # the parse record's own anchor (`siteAnchored(stmt.ucMarker)`), exactly
    # as the `isUnsupported` arm above does. Before S8 the only record was
    # the parse-time one, which says the cast EXISTS, not that a path reached
    # it -- the blanket veto made that distinction moot; S9 deleted the veto
    # and joins on it. The token is discarded: a halted path needs no carrier.
    w.halted(heUnsafeCast,
      "unsafe pointer materialisation (" & stmt.ucReason & ") reached at " &
      "walk time -- path halted", scope = siteAnchored(stmt.ucMarker))

const capSnapPrefix = "__capsnap#"
  ## RFC-0005 S8ax. A frame-local name (no `__gl:` prefix, so no call
  ## threads it) holding a cell's value as a statement began, at one
  ## statement nesting depth: `__capsnap#<depth>#<cell>`.

func capSnapName(depth: int; cell: string): string =
  capSnapPrefix & $depth & "#" & cell

proc syncCapCellsFromCells(p: Path; w: WalkCtx): Path =
  ## RFC-0005 S8ax. `p` resumes in the current frame after a raise (a
  ## handler, a `finally`): a capture whose cell differs from its local was
  ## written through the cell by the call that raised, and the local takes
  ## it. (Every other write the raise carries reaches both: a closure
  ## applied here writes the local and the cell to one value.)
  if w.frame.capCells.len == 0: return p
  var env2 = p.env
  var changed = false
  for (local, cell) in w.frame.capCells:
    if env2.hasKey(local) and env2.hasKey(cell) and
       not sameSymVal(env2[local], env2[cell]):
      env2[local] = env2[cell]
      changed = true
  if changed: forkPath(p, p.pc, env2) else: p

const addrSnapPrefix = "__addrsnap#"
  ## RFC-0005 S8ax. As `capSnapPrefix`, for an address-taken variable's
  ## value as a statement began: `__addrsnap#<depth>#<local>`.

func addrSnapName(depth: int; local: string): string =
  addrSnapPrefix & $depth & "#" & local

type CellProducer = object
  ## RFC-0016 review R6. What `reconcileCells` reads of whatever produced the
  ## effect it reconciles: a leaf statement (`producerOf`) or a guard a
  ## compound evaluates itself (the default value: no call, no store, no
  ## write by name). No `IRStmt` is built for a guard.
  isCall: bool
  cargs: seq[IRExpr]          ## a call's actuals
  cVarLocs: seq[VarLoc]       ## a call's `var` and `addr` actuals
  cGuardRoots: seq[string]    ## a call's by-address roots
  indexRecv: string           ## the receiver an element store writes ("" none)
  assigned: string            ## the name an assignment or `let` writes ("" none)
  assignsChar: bool           ## the assignment writes one character of the
                              ## variable it names (`s[i] = c`)

func lastWriteTo(src: CellProducer; local: string): bool =
  ## RFC-0005 S8ax. The statement's last effect is the write of `local` by
  ## name (an assignment or declaration of it): its value is the later one.
  local.len > 0 and src.assigned == local

func indexesInto(src: CellProducer; name: string): bool =
  ## The producer stores an element of `name` (`name[i] = v`).
  name.len > 0 and src.indexRecv == name

func producerOf(stmt: IRStmt): CellProducer =
  ## RFC-0016 review R6. The facts `reconcileCells` reads of a leaf statement
  ## (`walk`, `leaveStmt`); a compound one is never reconciled.
  doAssert stmt.kind notin compoundStmtKinds   # `reconcileCells`
  case stmt.kind
  of isCall:
    CellProducer(isCall: true, cargs: stmt.cargs, cVarLocs: stmt.cVarLocs,
                 cGuardRoots: stmt.cGuardRoots)
  of isIndexAssign: CellProducer(indexRecv: stmt.iaRecvName)
  of isAssign:
    CellProducer(assigned: stmt.aname,
                 assignsChar: stmt.avalue.kind == iekStrSetAt)
  of isLet: CellProducer(assigned: stmt.lname)
  else: CellProducer()

proc dropSnapshots(env: var Env; prefix: string; depth: int): bool =
  ## RFC-0005 S8ax. Delete `env`'s snapshots under `prefix` taken at `depth`
  ## or deeper (a path that left a nested statement early, a `break`, still
  ## carries its). True when any was deleted.
  var stale: seq[string]
  for k in env.keys:
    if k.startsWith(prefix):
      let rest = k[prefix.len .. ^1]
      let hash = rest.find('#')
      if hash > 0 and parseInt(rest[0 ..< hash]) >= depth: stale.add k
  for k in stale: env.del k
  stale.len > 0

const viewFreedPrefix = "__viewFreed#"
  ## RFC-0005 S8bu. Set (to any value) on a path where a `view` entry's
  ## cell was assigned whole or resized while a raise unwound
  ## (`syncAddrCellsFromHeap`); the next `syncAddrCells` taints the path.

proc heapTermOf(p: Path; key: string): HeapTerm =
  ## RFC-0005 S8ca. The term of heap array `key` on `p` (`HeapTerm`).
  if p.heaps.hasKey(key): (ast: p.heaps[key], input: "")
  else: (ast: Z3AnyAst(), input: heapInputName(p, key))

proc viewHeapKeys(c: AddrCellEntry): Option[seq[string]] =
  ## RFC-0005 S8ca. The heap arrays a `view` entry's value is read from
  ## (`addrEntryValue`): the cell's own leaves, or, in an object held field
  ## by field (`fieldSplitPointee`), the leaves of the field its path
  ## starts with. none for a cell held another way (a case object's).
  var keys: seq[string]
  if c.path.len == 0 and c.ty.kind != itVariant and
     not fieldSplitPointee(c.ty):
    for suf in heapLeafSuffixes(c.ty): keys.add refPointeeTypeId(c.ty) & suf
  elif c.path.len > 0 and fieldSplitPointee(c.ty):
    let i = c.ty.fieldNames.find(c.path[0])
    if i < 0: return none(seq[string])
    for suf in heapLeafSuffixes(c.ty.fields[i]):
      keys.add fieldHeapKey(c.ty, c.path[0]) & suf
  else:
    return none(seq[string])
  some(keys)

proc anchorViews(p: Path; cells: seq[AddrCellEntry]; frame: int) =
  ## RFC-0005 S8ca. `p` enters `frame`, whose `view` entries (`bindVarLocs`)
  ## take the cell's value now: each is marked with its heap arrays' terms
  ## (`ViewMark`).
  for c in cells:
    if not c.view: continue
    let keys = viewHeapKeys(c)
    if keys.isNone: continue
    var at: seq[HeapTerm]
    for k in keys.get: at.add heapTermOf(p, k)
    p.viewMarks.add ViewMark(local: c.local, frame: frame, keys: keys.get,
                             at: at)

proc liveViewMarks(p: Path; w: WalkCtx) =
  ## RFC-0005 S8ca. Drop `p`'s marks of returned frames, and its in-place
  ## steps once no mark is left.
  var kept: seq[ViewMark]
  for m in p.viewMarks:
    if liveFrame(w, m.frame): kept.add m
  if kept.len != p.viewMarks.len: p.viewMarks = kept
  if p.viewMarks.len == 0 and p.inPlaceSteps.len > 0: p.inPlaceSteps = @[]

proc logInPlace(before: Path; heapsBefore: Table[string, Z3AnyAst];
                after: Path) =
  ## RFC-0005 S8ca. Record on `after` each heap array an in-place element
  ## write changed from `before` (whose arrays were `heapsBefore`) as an
  ## in-place step. Only while a view is live: no one reads them otherwise.
  if after.viewMarks.len == 0: return
  for k, arr in after.heaps:
    let was: HeapTerm =
      if heapsBefore.hasKey(k): (ast: heapsBefore[k], input: "")
      else: (ast: Z3AnyAst(), input: heapInputName(before, k))
    let now: HeapTerm = (ast: arr, input: "")
    if not sameHeapTerm(was, now):
      after.inPlaceSteps.add (key: k, before: was, after: now)

proc viewMarkOf(p: Path; local: string; w: WalkCtx): int =
  ## RFC-0005 S8ca. The position in `p.viewMarks` of the `view` entry
  ## `local` of the current frame (or of the live frame it was inherited
  ## from: a capture), -1 when it has none.
  result = -1
  for i, m in p.viewMarks:
    if m.local == local and m.frame == w.frame.frameId: return i
  for i, m in p.viewMarks:
    if m.local == local and liveFrame(w, m.frame): result = i

proc viewInPlace(p: Path; mi: int): tuple[moved, inPlace: bool] =
  ## RFC-0005 S8ca. Whether the heap arrays of mark `mi` changed since it
  ## was taken, and whether every change is a chain of in-place steps
  ## (`Path.inPlaceSteps`) from its terms to the current ones. Identity is
  ## tracked by the write, not by the term's shape: an assignment of the
  ## whole that rebuilds an equal term, or one whose data happens to be a
  ## store chain over the old, is not an in-place step, so the copy no
  ## longer follows (Nim gave the variable other memory).
  let m = p.viewMarks[mi]
  for i, k in m.keys:
    var cur = m.at[i]
    let now = heapTermOf(p, k)
    var hops = 0
    while not sameHeapTerm(cur, now):
      result.moved = true
      var found = false
      for st in p.inPlaceSteps:
        if st.key == k and sameHeapTerm(st.before, cur):
          cur = st.after
          found = true
          break
      inc hops
      if not found or hops > p.inPlaceSteps.len: return (true, false)
  result.inPlace = true

proc reanchorView(p: Path; mi: int) =
  ## RFC-0005 S8ca. Mark `mi` takes the current terms of its arrays.
  for i, k in p.viewMarks[mi].keys:
    p.viewMarks[mi].at[i] = heapTermOf(p, k)

func capCellOf(w: WalkCtx; local: string): string =
  ## RFC-0005 S8ca. The env cell of `local` when the current frame keeps
  ## one (`CallFrameCtx.capCells`), else "".
  for (cl, cell) in w.frame.capCells:
    if cl == local: return cell
  ""

proc linkCapAddrCells(paths: seq[Path]; w: WalkCtx): seq[Path] =
  ## RFC-0005 S8ca. After a statement, each by-reference capture of the
  ## frame whose variable's address is taken: its address cell's pointer
  ## is threaded beside its env cell (`capAddrName`), the env cell takes
  ## the variable's value (`syncAddrCells` may just have read it from the
  ## cell), and the closure-body mark (`capBoundName`) is spent. Before
  ## S8ca the three copies (the local, the env cell, the address cell)
  ## declined every statement of the frame.
  for p in paths:
    var env2 = p.env
    var changed = false
    for (local, cell) in w.frame.capCells:
      if env2.hasKey(capBoundName(cell)):
        env2.del capBoundName(cell)
        changed = true
      for c in w.frame.addrCells:
        if c.local != local or c.bound or c.view or not env2.hasKey(c.cell) or
           env2[c.cell].kind != svPtr or not env2.hasKey(local):
          continue
        let an = capAddrName(cell)
        if not env2.hasKey(an) or not sameSymVal(env2[an], env2[c.cell]):
          env2[an] = env2[c.cell]
          changed = true
        if env2.hasKey(cell) and not sameSymVal(env2[cell], env2[local]):
          env2[cell] = env2[local]
          changed = true
    result.add(if changed: forkPath(p, p.pc, env2) else: p)

proc syncAddrCells(src: CellProducer; outs: seq[Path]; depth: int;
                   w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8ax. After `stmt`, each address-taken variable of the
  ## current frame (`CallFrameCtx.addrCells`) and the heap at its cell are
  ## made equal again. The side that changed since the statement began wins
  ## (`addrSnapName` holds the variable's value then, which was the cell's):
  ## memory written through a pointer is read into the variable; the
  ## variable written by name is stored into the cell. Both written within
  ## one statement is two writes the walk cannot order, unless the
  ## statement's last effect is the write by name (`lastWriteTo`):
  ## declined (`feUnsupportedOp`), the variable's value winning. So is a
  ## variable a closure also captures (its env cell is a third copy).
  ## RFC-0005 S8bx (item 3): a `slot` entry the same, with the Table's value
  ## at the key for the heap at the cell; a table write that may have removed
  ## the key leaves the view on a slot Nim's `del` refills from another
  ## entry, and declines too.
  let ctx = w.z3
  # RFC-0005 S8bu: a local with two entries (an `addr` actual's local,
  # `addrPartName`: a part of a variable's cell, and the call's cell) takes
  # a second pass, so a write that reached one of its cells and was read
  # into the local reaches the other in the same statement.
  var passes = 1
  for i, c in w.frame.addrCells:
    for j in 0 ..< i:
      if w.frame.addrCells[j].local == c.local: passes = 2
      # RFC-0005 S8cn: two views into one seq or Table may be one location.
      if c.slot.len > 0 and w.frame.addrCells[j].slot == c.slot: passes = 2
  for i, p in outs:
    var env2 = p.env
    var q: Path = nil
    var writtenThrough: seq[string]   ## RFC-0005 S8cn: seqs a view wrote into
    var clash: seq[string]
    var lost: seq[string]   ## RFC-0005 S8bs
    var freed: seq[string]   ## RFC-0005 S8bu
    var viewWhy = ""         ## RFC-0005 S8bx
    ## RFC-0005 S8cn: a `slot` entry whose key may have left, for the fork below.
    var removal: seq[tuple[local: string; ty: IRType; tab, snap: SymVal;
                           key: Z3AnyAst; rm: Z3Bool; gone: bool]]
      ## CRH-07: `key` is owned; a raw one outlived its `keyO`.
    for c in w.frame.addrCells:
      if c.view and env2.hasKey(viewFreedPrefix & c.local):
        env2.del(viewFreedPrefix & c.local)
        if q == nil: q = forkPath(p, p.pc, p.env)
        freed.add displayName(c.local)
    for pass in 0 ..< passes:
      for c in w.frame.addrCells:
        if c.slot.len > 0:
          # RFC-0005 S8bx (item 3): the location is the Table's value at the
          # key. A statement nested in this one has synced already, and left
          # the view the same term as the table's value at the key.
          # RFC-0005 S8cn: the Table is the part of `c.slot` at `c.path` when
          # an object holding it came.
          if not env2.hasKey(c.local) or not env2.hasKey(c.slot): continue
          # The holder's Table went to this call through a temporary: the
          # callee kept the view and it equal, and the write-back that follows
          # brings the Table here.
          if src.isCall and c.path.len > 0:
            var pending = false
            for l in src.cVarLocs:
              if l.mode == "var" and l.root == c.slot and l.path == c.path:
                pending = true
            if pending: continue
          let tabO = locGet(env2[c.slot], c.path, @[])
          let tabV = if tabO.isSome: tabO.get else: env2[c.slot]
          if tabV.kind == svSeq:
            # RFC-0005 S8cn (item 5): `f(s[i], s)`, one location as the
            # Table's slot is. A resize or an assignment of the whole gave the
            # seq other memory, and the formal still points at the old: not
            # modelled. Told by the statement, not by the term's shape (S8ca's
            # point, `viewInPlace`: `s = c` may be a store chain over `s`). Only
            # an element store is in place. A call given both formals checks
            # its own.
            let snapS = addrSnapName(depth, c.slot)
            let snapQ = if env2.hasKey(snapS): locGet(env2[snapS], c.path, @[])
                        else: none(SymVal)
            var pairedCall = false
            if src.isCall:
              var hasV, hasS = false
              for arg in src.cargs:
                if arg.kind == iekVar and arg.vname == c.local: hasV = true
                elif irFieldPath(arg) == c.slot: hasS = true
              pairedCall = hasV and hasS
            if snapQ.isSome and not sameSymVal(tabV, snapQ.get) and
               not pairedCall and c.slot notin writtenThrough and
               not src.indexesInto(c.slot):
              if q == nil: q = forkPath(p, p.pc, p.env)
              viewWhy = "the seq was resized or assigned whole while its " &
                        "element was held"
              continue
            let elemO = locGet(tabV, @["["], c.ixs)
            if elemO.isNone:
              viewWhy = "the walk does not follow an element of this seq"
              continue
            let xv = env2[c.local]
            if sameSymVal(xv, elemO.get): continue
            let snapX = addrSnapName(depth, c.local)
            let vCh = env2.hasKey(snapX) and not sameSymVal(xv, env2[snapX])
            let tCh = snapQ.isSome and not sameSymVal(tabV, snapQ.get)
            if not vCh and not tCh: continue
            if q == nil: q = forkPath(p, p.pc, p.env)
            let tabLast = lastWriteTo(src, c.slot) or
              src.indexesInto(c.slot)
            if vCh and tCh and not lastWriteTo(src, c.local) and not tabLast:
              viewWhy = "the view and the seq were both written in one statement"
            elif vCh and not tabLast:
              let nv = locSet(tabV, @["["], c.ixs, xv)
              let holder = if nv.isSome: locSet(env2[c.slot], c.path, @[], nv.get)
                           else: none(SymVal)
              if holder.isNone:
                viewWhy = "the walk does not find the seq in its holder"
                continue
              env2[c.slot] = holder.get
              env2[c.local] = locGet(nv.get, @["["], c.ixs).get
              # A sibling view of this seq (`f(s[0], s[1], s)`) sees an element
              # store, not a resize.
              writtenThrough.add c.slot
            else:
              env2[c.local] = elemO.get
            continue
          let keyO = if tabV.kind == svTable: tabKeyTerm(c.ixs[0], tabV.tabKeyTy)
                     else: none(Z3AnyAst)
          if keyO.isNone:
            viewWhy = "the table is not a modelled Table value"
            continue
          let gone = env2.hasKey(viewGonePrefix & c.local)
          let xv = env2[c.local]
          let snapV = addrSnapName(depth, c.local)
          let snapT = addrSnapName(depth, c.slot)
          let snapO = if env2.hasKey(snapT): locGet(env2[snapT], c.path, @[])
                      else: none(SymVal)
          # `del` stores only presence: the value at the key is still equal.
          let rm =
            if snapO.isSome and snapO.get.kind == svTable:
              presenceRemoved(tabV.tabPresentRaw, snapO.get.tabPresentRaw)
            else: mkBool(ctx, false)
          if not gone and guardLiteral(rm) == glFalse and
             sameSymVal(xv, tabValAt(ctx, tabV, keyO.get.raw)):
            continue
          let vCh = env2.hasKey(snapV) and not sameSymVal(xv, env2[snapV])
          let tCh = snapO.isSome and not sameSymVal(tabV, snapO.get)
          if not vCh and not tCh: continue
          if q == nil: q = forkPath(p, p.pc, p.env)
          let grownName = viewGrownPrefix & c.local
          if tCh:
            let g = tabV.tabSize > snapO.get.tabSize
            env2[grownName] = SymVal(kind: svBool,
              bo: if env2.hasKey(grownName): env2[grownName].bo or g else: g)
          if vCh and env2.hasKey(grownName):
            # The edge where a key was added declines; the walk goes on where
            # none was.
            let g = env2[grownName].bo
            if not loopArmInfeasible(ctx, q, g, w.settings):
              let dq = forkPath(q, q.pc & @[g], env2)
              taintInPlace(dq, w.degrade(feUnsupportedOp,
                "the `mpairs` view of a Table a callee holds was written after " &
                     "a key was added: Nim may have rehashed the Table, by a " &
                     "capacity not modelled (RFC-0005 S8cn; feUnsupportedOp)"))
              result.add drainPendingLowerEffects(dq)
              q = forkPath(q, q.pc & @[not g], q.env)
            env2.del(grownName)
          # RFC-0005 S8cn: the statement's last effect orders the two: `v =
          # f(t)` the view's write, `t[k] = f(v)` the table's store (a call's
          # argument is evaluated first). Two calls in one expression are not
          # two statements here, and stay declined (`twoCalls`).
          let tabLast = lastWriteTo(src, c.slot) or src.indexesInto(c.slot)
          if vCh and tCh and not lastWriteTo(src, c.local) and not tabLast:
            viewWhy = "the view and the table were both written in one statement"
          elif vCh and not tabLast:
            # On the emptied slot a write stays in the slot: the key is not
            # back (`rw_live`).
            if gone: continue
            var e2 = env2
            const tabTmp = addrSnapPrefix & "tab"
            e2[addrSnapPrefix & "key"] = c.ixs[0]
            e2[tabTmp] = tabV
            let t2 = lower(e2, mkTableSet(mkVar(tabTmp),
              mkVar(addrSnapPrefix & "key"), mkVar(c.local)))
            # RFC-0016 INT-37 (R2-08): this raw `lower` drains its own queue
            # onto the path it lowered for, so no later lowering claims it.
            taintInPlace(q, asDegrade(takePending()))
            let holder = locSet(env2[c.slot], c.path, @[], t2)
            if holder.isNone:
              viewWhy = "the walk does not find the Table in its holder"
              continue
            env2[c.slot] = holder.get
            env2[c.local] = tabValAt(ctx, t2, keyO.get.raw)
          elif snapO.isSome:
            # S8bx declined every presence that was not literally true. Only
            # an all-`true` chain since the statement began (`presenceRemoved`)
            # keeps the key, whatever its stores' keys are; a removal goes to
            # the fork below.
            if not gone and guardLiteral(rm) == glFalse:
              env2[c.local] = tabValAt(ctx, tabV, keyO.get.raw)
            else:
              removal.add (local: c.local, ty: c.ty, tab: tabV, snap: snapO.get,
                           key: keyO.get, rm: rm, gone: gone)
          continue
        if not env2.hasKey(c.local) or not env2.hasKey(c.cell) or
           env2[c.cell].kind != svPtr:
          continue
        let refAst = env2[c.cell].ptrAst
        # RFC-0005 S8bs: a `bound` entry's location is a part of its cell.
        let curO = addrEntryValue(ctx, (if q == nil: p else: q), c, refAst)
        if curO.isNone:
          if displayName(c.local) notin lost: lost.add displayName(c.local)
          continue
        let cur = curO.get
        let xv = env2[c.local]
        if c.view:
          # RFC-0005 S8bu: a `view` follows only an in-place write. S8ca:
          # an in-place write is a logged step (`viewInPlace`), not a term
          # of the right shape; Nim's by-value formal is never written by
          # name.
          let mi = viewMarkOf((if q == nil: p else: q), c.local, w)
          if mi < 0:
            if not sameSymVal(xv, cur) and displayName(c.local) notin freed:
              freed.add displayName(c.local)
            continue
          let (moved, inPlace) = viewInPlace((if q == nil: p else: q), mi)
          if not moved: continue
          if q == nil: q = forkPath(p, p.pc, p.env)
          reanchorView(q, mi)
          if inPlace: env2[c.local] = cur
          elif displayName(c.local) notin freed: freed.add displayName(c.local)
          continue
        if sameSymVal(xv, cur): continue
        if q == nil: q = forkPath(p, p.pc, p.env)
        let snap = addrSnapName(depth, c.local)
        let hasSnap = env2.hasKey(snap)
        if hasSnap and sameSymVal(xv, env2[snap]):
          env2[c.local] = cur
          continue
        # RFC-0005 S8ca: a closure body that ran with this capture bound to
        # the cell (`capBoundName`) kept the two equal at each exit, so the
        # write it carried back by name is the cell's value.
        let capCell = capCellOf(w, c.local)
        if capCell.len > 0 and env2.hasKey(capBoundName(capCell)) and
           hasSnap and not sameSymVal(cur, env2[snap]) and
           not lastWriteTo(src, c.local):
          env2[c.local] = cur
          continue
        if not (hasSnap and sameSymVal(cur, env2[snap])) and
           not lastWriteTo(src, c.local) and displayName(c.local) notin clash:
          clash.add displayName(c.local)
        # RFC-0005 S8ca: an element of the variable written by name is
        # written in its memory; its store is an in-place step.
        let heapsBefore = q.heaps
        let st = addrEntryStore(ctx, q, c, refAst, xv)
        if src.indexesInto(c.local) or
           (c.local.len > 0 and src.assignsChar and
            src.assigned == c.local):   # a character, by name
          logInPlace(q, heapsBefore, q)
        if st.isSome: env2[c.local] = keepStrBuf(st.get, xv)   # S8ca
        elif displayName(c.local) notin lost: lost.add displayName(c.local)
    let dropped = dropSnapshots(env2, addrSnapPrefix, depth)
    if q == nil and not dropped and clash.len == 0 and lost.len == 0 and
       freed.len == 0 and viewWhy.len == 0 and removal.len == 0:
      result.add p
      continue
    if q == nil: q = forkPath(p, p.pc, env2)
    else: q.env = env2
    if viewWhy.len > 0:
      taintInPlace(q, w.degrade(feUnsupportedOp,
        "an `mpairs` view and its Table passed to one call: " & viewWhy &
             "; the two are one location in Nim, and the order of the " &
             "writes is not modelled (RFC-0005 S8bx; feUnsupportedOp)"))
    if clash.len > 0:
      taintInPlace(q, w.degrade(feUnsupportedOp,
        "RFC-0005 S8ax: the address-taken variable(s) " & clash.join(", ") &
             " were written by name and through a pointer within one " &
             "statement, or are also captured by a closure; the order of " &
             "the writes is not modelled (feUnsupportedOp)"))
    if lost.len > 0:
      taintInPlace(q, w.degrade(feUnsupportedOp,
        "RFC-0005 S8bs: the `var` formal(s) " & lost.join(", ") & " are " &
             "bound to a part of an address-taken variable that the walk " &
             "no longer finds in its cell (feUnsupportedOp)"))
    if freed.len > 0:
      taintInPlace(q, w.degrade(feUnsupportedOp,
        "RFC-0005 S8bu: the by-value seq formal(s) " & freed.join(", ") &
             " share the memory of an address-taken variable that was " &
             "assigned whole or resized through a pointer: Nim's copy still " &
             "points at the old memory, which it may have freed; the walk " &
             "does not model freed memory (feUnsupportedOp)"))
    if removal.len > 1:
      viewWhy = "two views' keys may have been removed in one statement"
      taintInPlace(q, w.degrade(feUnsupportedOp,
        "an `mpairs` view and its Table passed to one call: " & viewWhy &
             " (RFC-0005 S8cn; feUnsupportedOp)"))
    elif removal.len == 1:
      # RFC-0005 S8cn (item 4): as `parseTableForLoop`'s `reload`, for the
      # callee's own reads. The key is kept; or it left a one-entry table and
      # the slot is empty (reading zero until written); or it was put back on
      # that slot; else the slot depends on the hashes.
      let r = removal[0]
      let lenNow = r.tab.tabSize
      let held = wrap[Z3Bool](ctx, checkedSelect(ctx, r.tab.tabPresentRaw.raw, r.key.raw))
      let empty = lenNow == mkInt(ctx, 0)
      let back = lenNow == mkInt(ctx, 1) and held
      let one = r.snap.tabSize == mkInt(ctx, 1)
      let goneName = viewGonePrefix & r.local
      let onSlot = if r.gone: empty else: r.rm and one and empty
      let putBack = if r.gone: back else: r.rm and one and back
      var keep = env2
      keep[r.local] = tabValAt(ctx, r.tab, r.key.raw)
      keep.del(goneName)
      var slotEnv = env2
      if not r.gone: slotEnv[r.local] = defaultZero(r.ty, "__viewGoneZero")
      slotEnv[goneName] = SymVal(kind: svBool, bo: mkBool(ctx, true))
      var arms: seq[Z3Bool]
      arms.add onSlot
      arms.add putBack
      if not r.gone: arms.add(not r.rm)
      result.add drainPendingLowerEffects(forkPath(q, q.pc & @[onSlot], slotEnv))
      result.add drainPendingLowerEffects(forkPath(q, q.pc & @[putBack], keep))
      if not r.gone:
        result.add drainPendingLowerEffects(forkPath(q, q.pc & @[not r.rm], keep))
      var none = mkBool(ctx, true)
      for a in arms: none = none and not a
      # `degrade` reports at once, so the arm is taken only if it can happen.
      if not loopArmInfeasible(ctx, q, none, w.settings):
        let dq = forkPath(q, q.pc & @[none], env2)
        taintInPlace(dq, w.degrade(feUnsupportedOp,
          "a key was removed from the Table a callee holds with its `mpairs` " &
               "view: the view's slot depends on the keys' hashes, which are " &
               "not modelled (RFC-0005 S8cn; feUnsupportedOp)"))
        result.add drainPendingLowerEffects(dq)
      continue
    result.add drainPendingLowerEffects(q)

proc syncAddrCellsFromHeap(p: Path; w: WalkCtx): Path =
  ## RFC-0005 S8ax. `p` resumes in the current frame after a raise (a
  ## handler, a `finally`): an address-taken variable out of step with its
  ## cell was written through a pointer by the call that raised (every
  ## statement before the raising one left the two equal, and a write by
  ## name in the raising statement -- an assignment of the call's value,
  ## a `var` actual's copy-out -- never happens on its raise, or reaches
  ## the cell too, `inheritAddrCells`), so the variable takes the cell's
  ## value.
  var env2 = p.env
  var changed = false
  var reanchor: seq[int]   ## RFC-0005 S8ca
  for c in w.frame.addrCells:
    if env2.hasKey(c.local) and env2.hasKey(c.cell) and
       env2[c.cell].kind == svPtr:
      # RFC-0005 S8bs: a `bound` entry's location is a part of its cell.
      let cur = addrEntryValue(w.z3, p, c, env2[c.cell].ptrAst)
      if cur.isNone: continue
      if c.view:
        # RFC-0005 S8bu: a `view` follows only an in-place write (S8ca:
        # a logged step, `viewInPlace`); any other is marked for the next
        # statement's sync to taint.
        let mi = viewMarkOf(p, c.local, w)
        let (moved, inPlace) =
          if mi >= 0: viewInPlace(p, mi)
          else: (not sameSymVal(env2[c.local], cur.get), false)
        if not moved: continue
        if mi >= 0: reanchor.add mi
        if inPlace: env2[c.local] = cur.get
        else: env2[viewFreedPrefix & c.local] = cur.get
        changed = true
      elif not sameSymVal(env2[c.local], cur.get):
        env2[c.local] = cur.get
        changed = true
  if not changed: return p
  result = forkPath(p, p.pc, env2)
  for mi in reanchor: reanchorView(result, mi)

const elemSnapPrefix = "__elemsnap#"
  ## RFC-0005 S8be. As `addrSnapPrefix`, for a seq with element cells as a
  ## statement began (`__elemsnap#<depth>#s#<root>`) and the value of each
  ## of the frame's element cells then (`__elemsnap#<depth>#c#<k>`, `k` its
  ## position in `Path.elemCells`).

func elemSnapName(depth: int; what: string): string =
  elemSnapPrefix & $depth & "#" & what

proc frameElemCells(p: Path; frame: int): seq[int] =
  ## RFC-0005 S8be. The positions in `p.elemCells` of `frame`'s live cells.
  for k, e in p.elemCells:
    if e.frame == frame and not e.dead: result.add k

proc withElem(sv: SymVal; idx: Z3Int; v: SymVal): SymVal =
  ## RFC-0005 S8be. The `svSeq` `sv` with element `idx` set to `v`. Only a
  ## seq with element cells reaches here, and the parser gives cells only to
  ## a backed seq of scalars, strings or objects (`elemCellOf`). RFC-0005
  ## S8bo: an object element is leaf-split (S8bc), every leaf stored
  ## (`seqStoreArrs`). A value that does not fit declines in-band and leaves
  ## the element (`seqStoreDecline`; a caller drains the pending decline).
  let arrs = seqStoreArrs(sv, idx, v)
  if arrs.isNone:
    discard seqStoreDecline("a write through a pointer to an element",
                            sv.seqElemTy, v)
    return sv
  withSeqArrsOf(sv, arrs.get)

proc snapElemCells(p: Path; depth: int; w: WalkCtx): Path =
  ## RFC-0005 S8be. `p` with this frame's seqs with element cells, and the
  ## cells' values, recorded as the statement at `depth` begins.
  let ks = frameElemCells(p, w.frame.frameId)
  if ks.len == 0: return p
  var env2 = p.env
  for k in ks:
    let e = p.elemCells[k]
    env2[elemSnapName(depth, "c#" & $k)] =
      addrCellValue(w.z3, p, e.ty, e.refAst)
    if p.env.hasKey(e.root):
      env2[elemSnapName(depth, "s#" & e.root)] = p.env[e.root]
  forkPath(p, p.pc, env2)

proc sameSeqLen(a, b: SymVal): bool =
  ## RFC-0005 S8be. `a` and `b` are seqs of one length term. A placeholder
  ## is never the same (its cells then die: the conservative side).
  a.kind == svSeq and b.kind == svSeq and
    not a.isUnsupportedFieldPlaceholder and # [placeholder-audited]
    not b.isUnsupportedFieldPlaceholder and # [placeholder-audited]
    cast[pointer](a.seqLen.raw) == cast[pointer](b.seqLen.raw) # [placeholder-audited]

proc shadowedElem(p: Path; ks: seq[int]; k: int): Option[Z3Bool] =
  ## RFC-0005 S8ca. When element cell `k` (of `ks`, the frame's live cells)
  ## is shadowed: an older live cell of its seq has an equal index, and
  ## `walkElemCell` handed that one out, so no pointer writes `k`'s. A
  ## store at an address `walkElemCell` built (`ite(i == j, old, new)`)
  ## leaves `k`'s heap read a different term though its value is
  ## unchanged; read back after the older cell's, it clobbered the
  ## element (an `addr s[i]` actual of a seq with element cells, S8bu's
  ## "in the element's own heap"). none when no older cell may shadow it.
  let e = p.elemCells[k]
  var conds: seq[Z3Bool]
  for j in ks:
    if j >= k: break
    let o = p.elemCells[j]
    if o.root == e.root and not o.dead:
      let c = o.idx == e.idx
      let f = foldedBool(e.idx.ctx, c)
      if f.isNone: conds.add c
      elif f.get: return some(c)   # shadowed outright
  if conds.len == 0: return none(Z3Bool)
  var c = conds[0]
  for i in 1 ..< conds.len: c = c or conds[i]
  some(c)

proc withCellElem(p: Path; ks: seq[int]; k: int; sv: SymVal;
                  cur: SymVal): SymVal =
  ## RFC-0005 S8ca. `sv` with element cell `k`'s value `cur` read into its
  ## element, unless an older cell shadows it (`shadowedElem`).
  let e = p.elemCells[k]
  let sh = shadowedElem(p, ks, k)
  if sh.isNone: return withElem(sv, e.idx, cur)
  let f = foldedBool(e.idx.ctx, sh.get)
  if f.isSome and f.get: return sv
  withElem(sv, e.idx, iteSV(sh.get, seqElemAt(sv, e.idx), cur))

proc syncElemCells(src: CellProducer; outs: seq[Path]; depth: int;
                   w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8be. After the producer, each seq of the current frame with element
  ## cells and the heap at those cells are made equal again, the side that
  ## changed since the statement began winning (`elemSnapName`):
  ##
  ## * the seq resized or assigned whole (its length is another term, or
  ##   the statement's last effect is its write by name, `lastWriteTo`,
  ##   whatever value it writes -- RFC-0005 S8bo):
  ##   Nim may have moved its elements, so its cells die (a dereference
  ##   that may reach one declines, `danglingFork`);
  ## * the seq's elements written: each cell takes its element's value;
  ## * a cell written through a pointer: its element takes the value.
  ##
  ## Both written within one statement is two writes the walk cannot
  ## order: declined (`feUnsupportedOp`), the seq winning -- except in a
  ## call, whose callee kept the two equal itself (`inheritElemCells`). So
  ## is a seq a closure also captures (its env cell is a third copy).
  ##
  ## Run only where effects are produced (`reconcileCells`).
  let ctx = w.z3
  for p in outs:
    let ks = frameElemCells(p, w.frame.frameId)
    if ks.len == 0:
      var env0 = p.env
      if dropSnapshots(env0, elemSnapPrefix, depth):
        result.add forkPath(p, p.pc, env0)
      else:
        result.add p
      continue
    var q = forkPath(p, p.pc, p.env)
    var env2 = q.env
    var clash: seq[string]
    var roots: seq[string]
    for k in ks:
      if q.elemCells[k].root notin roots: roots.add q.elemCells[k].root
    for root in roots:
      if not env2.hasKey(root): continue
      for (cl, _) in w.frame.capCells:
        if cl == root and displayName(root) notin clash:
          clash.add displayName(root)
      let sNow = env2[root]
      let sKey = elemSnapName(depth, "s#" & root)
      let seqCh = env2.hasKey(sKey) and not sameSymVal(sNow, env2[sKey])
      var written: seq[int]
      for k in ks:
        let e = q.elemCells[k]
        if e.root != root: continue
        let cKey = elemSnapName(depth, "c#" & $k)
        if env2.hasKey(cKey) and
           not sameSymVal(addrCellValue(ctx, q, e.ty, e.refAst), env2[cKey]):
          written.add k
      if sNow.kind in {svVariant, svMultiVariant, svTuple}:
        # RFC-0005 S8bo: a case object's field cells. A statement that may
        # have changed its arm (the discriminator is another term) kills
        # them: the pointer names another arm's memory. Otherwise the side
        # that changed wins, as for an element: a write by name (of the
        # field, or of the whole object in the same arm, whose memory Nim
        # reuses) reaches the cell, a write through the pointer the field.
        # RFC-0005 S8cb: per cell, as a multi-axis object's other axes keep
        # their memory (`fieldMemorySame`); a tuple's never moves.
        let snapV = if env2.hasKey(sKey): env2[sKey] else: sNow
        var live: seq[int]
        for k in ks:
          if q.elemCells[k].root != root: continue
          if seqCh and not fieldMemorySame(sNow, snapV, q.elemCells[k].field):
            q.elemCells[k].dead = true
          else:
            live.add k
        if seqCh:
          for k in written:
            if k in live and not src.isCall and
               displayName(root) notin clash:
              clash.add displayName(root)
          for k in live:
            let e = q.elemCells[k]
            discard addrCellStore(ctx, q, e.ty, e.refAst,
                                  armFieldValue(sNow, e.field, e.tags))
        else:
          var vNew = sNow
          for k in written:
            let e = q.elemCells[k]
            vNew = withArmField(vNew, e.field, e.tags,
                                addrCellValue(ctx, q, e.ty, e.refAst))
          env2[root] = vNew
        continue
      # RFC-0005 S8bo: a write of the seq by name kills its cells whatever
      # it assigns: Nim's `=copy`/`=sink` frees the old data and points the
      # seq at another block, even of the same length, and even of the same
      # elements (`s = t` after `let t = s`, a callee's `s = t` repeating
      # the caller's value). Before S8bo it had to change the seq's term
      # too, so a whole assignment of an equal value (or a cached callee's)
      # left the cells live: a read through one was a confirmed `sxSat` on
      # memory Nim had freed.
      if lastWriteTo(src, root) or
         seqCh and not sameSeqLen(sNow, env2[sKey]):
        for k in ks:
          if q.elemCells[k].root == root: q.elemCells[k].dead = true
        continue
      if sNow.kind != svSeq: continue
      var sNew = sNow
      if seqCh:
        if written.len > 0 and not src.isCall and
           displayName(root) notin clash:
          clash.add displayName(root)
      else:
        for k in written:
          let e = q.elemCells[k]
          sNew = withCellElem(q, ks, k, sNew,
                              addrCellValue(ctx, q, e.ty, e.refAst))   # S8ca
        env2[root] = sNew
      # Only the side that changed is copied: a cell another cell of the
      # same index shadows is never one a pointer holds (`walkElemCell`
      # hands out the older one).
      if seqCh:
        for k in ks:
          let e = q.elemCells[k]
          if e.root != root: continue
          discard addrCellStore(ctx, q, e.ty, e.refAst, seqElemAt(sNew, e.idx))
    discard dropSnapshots(env2, elemSnapPrefix, depth)
    q.env = env2
    if clash.len > 0:
      taintInPlace(q, w.degrade(feUnsupportedOp,
        "RFC-0005 S8be: the seq(s) " & clash.join(", ") & " were written " &
             "by name and through a pointer to an element within one " &
             "statement, or are also captured by a closure; the order of " &
             "the writes is not modelled (feUnsupportedOp)"))
    result.add drainPendingLowerEffects(q)

proc syncElemCellsFromHeap(p: Path; w: WalkCtx): Path =
  ## RFC-0005 S8be. As `syncAddrCellsFromHeap`, for element cells: `p`
  ## resumes in the current frame after a raise, and an element out of
  ## step with its cell was written through a pointer by the call that
  ## raised, so the element takes the cell's value -- unless the seq was
  ## resized since the raising statement began (its innermost snapshot),
  ## when its cells die.
  let ks = frameElemCells(p, w.frame.frameId)
  if ks.len == 0: return p
  var q = forkPath(p, p.pc, p.env)
  var env2 = q.env
  for k in ks:
    let e = q.elemCells[k]
    if e.field.len > 0 and env2.hasKey(e.root) and
       env2[e.root].kind in {svVariant, svMultiVariant, svTuple}:
      # RFC-0005 S8bo: a field cell. The object changed arm since the
      # raising statement began (its innermost snapshot): the cell dies;
      # else the field takes the cell's value.
      var snapV = env2[e.root]
      var bestV = -1
      for key, v in env2:
        if key.startsWith(elemSnapPrefix) and key.endsWith("#s#" & e.root):
          let rest = key[elemSnapPrefix.len .. ^1]
          let d = parseInt(rest[0 ..< rest.find('#')])
          if d > bestV:
            bestV = d
            snapV = v
      let cur = env2[e.root]
      if not fieldMemorySame(cur, snapV, e.field):
        q.elemCells[k].dead = true
        continue
      env2[e.root] = withArmField(cur, e.field, e.tags,
                                  addrCellValue(w.z3, q, e.ty, e.refAst))
      continue
    if not env2.hasKey(e.root) or env2[e.root].kind != svSeq: continue
    var snap = SymVal(kind: svBool)
    var best = -1
    for key, v in env2:
      if key.startsWith(elemSnapPrefix) and key.endsWith("#s#" & e.root):
        let rest = key[elemSnapPrefix.len .. ^1]
        let d = parseInt(rest[0 ..< rest.find('#')])
        if d > best:
          best = d
          snap = v
    if best >= 0 and not sameSeqLen(env2[e.root], snap):
      q.elemCells[k].dead = true
      continue
    let cur = addrCellValue(w.z3, q, e.ty, e.refAst)
    if not sameSymVal(seqElemAt(env2[e.root], e.idx), cur):
      env2[e.root] = withCellElem(q, ks, k, env2[e.root], cur)   # S8ca
  q.env = env2
  drainPendingLowerEffects(q)

proc frameHasCells(paths: seq[Path]; w: WalkCtx): bool =
  ## RFC-0005 S8ax. Whether the current frame keeps anything
  ## `reconcileCells` reconciles: a by-reference capture, an address-taken
  ## variable, or a live element cell on one of `paths`.
  if w.frame.capCells.len > 0 or w.frame.addrCells.len > 0: return true
  for p in paths:
    for e in p.elemCells:
      if e.frame == w.frame.frameId and not e.dead: return true
  false

proc snapCells(paths: seq[Path]; depth: int; w: WalkCtx): seq[Path] =
  ## RFC-0005 S8ax. `paths` with each of the frame's captures, address-taken
  ## variables (and a `slot` view's Table) and element cells recorded as an
  ## evaluation at `depth` begins, for `reconcileCells` to tell which side
  ## it wrote.
  for p0 in paths:
    let p = snapElemCells(p0, depth, w)   # RFC-0005 S8be
    var env2 = p.env
    var changed = false
    for (local, cell) in w.frame.capCells:
      if env2.hasKey(local) and env2.hasKey(cell):
        env2[capSnapName(depth, cell)] = env2[local]
        changed = true
    for c in w.frame.addrCells:
      if env2.hasKey(c.local) and env2.hasKey(c.cell):
        env2[addrSnapName(depth, c.local)] = env2[c.local]
        changed = true
      elif c.slot.len > 0 and env2.hasKey(c.local) and env2.hasKey(c.slot):
        env2[addrSnapName(depth, c.local)] = env2[c.local]   # RFC-0005 S8bx
        env2[addrSnapName(depth, c.slot)] = env2[c.slot]
        changed = true
    result.add(if changed: forkPath(p, p.pc, env2) else: p)

proc reconcileCells(src: CellProducer; outs0: seq[Path]; depth: int;
                    w: var WalkCtx): seq[Path] =
  ## RFC-0016 review R5-1/R5-2. Make each of the frame's two-sided
  ## locations equal again after an evaluation that began at `depth`
  ## (`snapCells`): element cells (`syncElemCells`), by-reference captures
  ## (the loop below), address-taken variables and `slot` views
  ## (`syncAddrCells`). The side that changed since the snapshot wins; both
  ## changed is a clash, declined.
  ##
  ## The invariant (the one statement of it; other docs point here): every
  ## effect is reconciled exactly once, where it is produced, against a
  ## snapshot taken just before it. What this reads of the producer is a
  ## `CellProducer`.
  ##
  ## A compound statement (`compoundStmtKinds`: a block, labelled or not, an
  ## `if` -- a `case` is one --, a `while`, a `try`) produces no effect of its
  ## own beyond the expressions it evaluates itself, so it is never reconciled
  ## over its span: a pass over its span compared its children's synced
  ## effects -- the two sides equal in value, not always in term -- against a
  ## snapshot from before them and declined writes that never clashed. The
  ## reconcile points are every place the walker evaluates source code in a
  ## frame:
  ##
  ## * every leaf statement (`walk`, `leaveStmt`): every `IRStmtKind` outside
  ##   `compoundStmtKinds`, `isCall` included (a callee's effects reach the
  ##   caller's cells only through its statement);
  ## * every guard a compound evaluates itself (`evalCondSynced`): each
  ##   `if`/`elif` condition, a short-circuit chain's joined guard
  ##   (`ifJoin`), each `while` test, the final one after the last unrolled
  ##   body included (explore walk; the follow walk has none: it degrades
  ##   `beBudgetExhausted` instead), and the follow-mode variants
  ##   (`walkIfFollowConcrete`, `walkWhileFollowConcrete`). A `case` is an
  ##   if-chain: its scrutinee is evaluated once, ahead of the chain (a
  ##   scrutinee that applies a closure is let-bound there, a leaf, R8-1), and
  ##   each `of` test compares it;
  ## * a `return`'s value (`evalReturnSynced`), before the path parks in
  ##   `exitReturn` and a `finally` or a `var` write-back reads the frame.
  ##
  ## Both expression points share `evalReconciled` (snapshot, lower, drain,
  ## reconcile). A guard hands `reconcileCells` a default `CellProducer`, no
  ## statement; a `return` value the assignment of `result`.
  ##
  ## Which of them produce an effect: the parser hoists a call into a
  ## statement of its own (`call(__sym_f_N := f(..))`, a leaf) when it is an
  ## operand (`c() * 10`, `c() > 0`, `v > 0 and c()`), a scrutinee, or an
  ## `if`/`case` expression. It leaves a by-value closure call
  ## (`closureCallIR`: a lambda, a proc-valued `let`, a proc field) in place
  ## when the call is the WHOLE expression: a bare `return c()`, a bare
  ## `if c():` / `elif c():`, a bare `while c():` (and `while n < 5 and c():`,
  ## which lowers to a guard `if` in the body). Those guard and `return`
  ## points reconcile the effect where it is produced. The `ifJoin` guard
  ## is a synthetic `__sym_sc_N` (or its `not`) or a bitset membership test,
  ## never a call. Their tests are `tsymex_0016_r8a_inlinecalls` (its header
  ## records which reconcile each fixture turns red without).
  ##
  ## A parked exit (`break`, `continue`, a `return` or a jump held for a
  ## `finally`) needs nothing more where it rejoins: it was reconciled at
  ## each leaf and guard it passed. A raise resumes with the cell winning
  ## (`syncCapCellsFromCells`, `syncAddrCellsFromHeap`,
  ## `syncElemCellsFromHeap`). The k-unroll summarises no iteration: every
  ## body it runs is walked statement by statement, and an exhausted path
  ## leaves tainted. A closure applied in an expression runs its body's
  ## statements through `walk`, so its own leaves reconcile them.
  let outs = syncElemCells(src, outs0, depth, w)   # RFC-0005 S8be
  if w.frame.capCells.len == 0:
    return syncAddrCells(src, outs, depth, w)
  var byAddr: seq[string]
  if src.isCall:
    for (local, _) in w.frame.capCells:
      if local in src.cGuardRoots: byAddr.add displayName(local)
  for p in outs:
    var env2 = p.env
    var touched = false
    var clash = byAddr
    for (local, cell) in w.frame.capCells:
      let snap = capSnapName(depth, cell)
      if not env2.hasKey(local) or not env2.hasKey(cell): continue
      if not env2.hasKey(snap):
        # Registered by this statement: `registerCapCell` bound both.
        if not sameSymVal(env2[local], env2[cell]):
          env2[cell] = env2[local]
          touched = true
        continue
      let lCh = not sameSymVal(env2[local], env2[snap])
      let cCh = not sameSymVal(env2[cell], env2[snap])
      # Both written to one value is a closure applied here carrying its
      # write to both (`applyClosureGround`).
      let agree = sameSymVal(env2[local], env2[cell])
      if lCh and cCh and not agree or
         cCh and not lCh and not src.isCall:
        if displayName(local) notin clash: clash.add displayName(local)
      if lCh:
        env2[cell] = env2[local]
      elif cCh:
        env2[local] = env2[cell]
      touched = true
    # This depth's snapshots, and any a path that left a nested statement
    # early (a `break`) still carries.
    var stale: seq[string]
    for k in env2.keys:
      if k.startsWith(capSnapPrefix):
        let rest = k[capSnapPrefix.len .. ^1]
        let hash = rest.find('#')
        if hash > 0 and parseInt(rest[0 ..< hash]) >= depth: stale.add k
    for k in stale: env2.del k
    if not touched and stale.len == 0 and clash.len == 0:
      result.add p
      continue
    var q = forkPath(p, p.pc, env2)
    if clash.len > 0:
      taintInPlace(q, w.degrade(ceCaptureByRefUnmodelled,
        "the by-reference capture(s) " & clash.join(", ") & " of a " &
             "closure were written through the closure's env and in the " &
             "frame within one statement, or passed by address while the " &
             "closure may run; the order of the two is not modelled " &
             "(ceCaptureByRefUnmodelled)"))
    result.add q
  # The capture pass keeps its survivors one for one.
  doAssert result.len == outs.len
  if w.frame.addrCells.len > 0:
    result = syncAddrCells(src, result, depth, w)   # RFC-0005 S8ax
    result = linkCapAddrCells(result, w)             # RFC-0005 S8ca

template evalReconciled(p: Path; w: var WalkCtx; producer: CellProducer;
                        q, lowering: untyped): seq[Path] =
  ## RFC-0016 review R8-2. The skeleton both evaluation points share (a guard,
  ## a `return` value): evaluate, then reconcile. `lowering` is an expression
  ## of the continuations (`seq[Path]`, scalar raises drained) with `q` bound
  ## to the path it lowers from. When the frame keeps no cells it runs on `p`
  ## as it stands. Otherwise `q` is `p` snapshotted at a fresh depth
  ## (`snapCells`), and what `lowering` returns is reconciled against that
  ## snapshot as the effect `producer` names (`reconcileCells`, which states
  ## the invariant). `lowering` may leave its value in a variable of the
  ## caller: it renames no term it reads.
  block:
    let snapped = frameHasCells(@[p], w)
    var depth = 0
    var snap = p
    if snapped:
      inc w.capSyncDepth
      depth = w.capSyncDepth
      snap = snapCells(@[p], depth, w)[0]
    let outs = block:
      let q = snap
      lowering
    if snapped:
      dec w.capSyncDepth
      reconcileCells(producer, outs, depth, w)
    else: outs

proc evalCondSynced(p: Path; cond: IRExpr;
                    w: var WalkCtx): (Z3Bool, seq[Path]) =
  ## RFC-0016 review R5-2. A guard a compound statement evaluates itself
  ## (an `if` condition, a `while` guard test): `lowerBoolInExpr`, its
  ## scalar raises drained (`drainScalarRaiseForks`), and the continuations
  ## reconciled as a leaf `let` of the guard would be (`evalReconciled`,
  ## default `CellProducer`: no statement). A bare by-value closure call
  ## (`if c():`, `elif c():`, `while c():`) stays in the guard, so this is
  ## where its effect is produced; a call that is an operand of the guard is
  ## a leaf before it.
  var b: Z3Bool
  let conts = evalReconciled(p, w, CellProducer(), q):
    let (b0, p2) = lowerBoolInExpr(q, cond, w)
    b = b0
    drainScalarRaiseForks(p2, w)
  (b, conts)

proc evalReturnSynced(p: Path; value: IRExpr; proto: Option[SymVal];
                      w: var WalkCtx): seq[Path] =
  ## RFC-0016 review R7-1. A `return`'s value: `lowerInExpr`, its scalar
  ## raises drained (`drainScalarRaiseForks`, R1: `s[i]` out of bounds,
  ## `x div 0`), each survivor bound to `result` once, and the survivors
  ## reconciled as the assignment of `result` they end with
  ## (`evalReconciled`, `CellProducer(assigned: "result")`). The path leaves
  ## through `exitReturn`, which runs every enclosing `finally`; those and a
  ## `var` write-back read the frame after the closure call the value applied
  ## (a bare `return c()`, by value, stays inline in the value).
  evalReconciled(p, w, CellProducer(assigned: "result"), q):
    let (retVal, pr) = lowerInExpr(q, value, w, proto)
    var bound: seq[Path]
    for cp in drainScalarRaiseForks(pr, w):
      var newEnv = cp.env
      newEnv["result"] = retVal
      bound.add forkPath(cp, cp.pc, newEnv)
    bound

proc exitGroupFieldPaths*(): seq[string] =
  ## RFC-0016 INT-35 (R6-03). The exit-group fields of `WalkCtx` and the
  ## frames it holds (`collectExitGroupFields`); compiling it is the check.
  var w: WalkCtx
  collectExitGroupFields(w, "WalkCtx", result)

proc visitExitsSince(w: var WalkCtx; since: ExitMark;
                     visit: proc (p: var Path) {.closure.}) =
  ## RFC-0005 review R5. `visit` the path of every exit-channel entry parked
  ## after `since`, to replace it in place, on every channel of every group
  ## `forEachExitGroup` reaches.
  forEachExitGroup(w, g): g.visitSince(since, visit)

proc stampExitsSince(w: var WalkCtx; since: ExitMark; taint: Taint;
                     ub: set[UbKind] = {}) =
  ## RFC-0005 review R2 (SD2), R3 (T1), R4, R5. Taint every exit-channel entry
  ## parked after `since`: the paths a statement sent down an exit channel,
  ## wherever a claim has left them since. Identified by serial, not by
  ## position: an `isTry` walked inside the statement may claim entries
  ## around them. Each path is replaced by a tainted fork, never mutated: a
  ## sibling may share the ref. The entry keeps its serial (`exits.nim`).
  ##
  ## The channels are the ones `visitExitsSince` reaches; a channel added
  ## to any of its groups is stamped, and `stmtExitTaintProbe` parks on it
  ## and pins the stamp, with no list to extend.
  if not w.exitClock.parkedSince(since): return   # nothing parked
  w.visitExitsSince(since, proc (p: var Path) =
    p = forkPathTainted(p, p.pc, p.env, carriedDegrade(taint, ub)))

type StmtMark = object
  ## RFC-0016 INT-36 (R3-17). Where a statement began: the exit clock's
  ## reading, and how many findings (`w.found`) and candidates
  ## (`w.candidates`) were filed. Both only grow during a walk.
  exits: ExitMark
  found, candidates: int

proc stmtMark(w: WalkCtx): StmtMark =
  StmtMark(exits: w.exitClock.mark, found: w.found.len,
           candidates: w.candidates.len)

proc stampFindingsSince(w: var WalkCtx; m: StmtMark; taint: Taint;
                        ub: set[UbKind] = {}) =
  ## RFC-0016 INT-36 (R3-17). Join `taint` (and `ub`) into every finding
  ## filed since `m`, as the paths the statement produced are. A winner the
  ## join makes `scSpurious` moves to the candidates, in filing order, as
  ## `admitSolvedHit` files a tainted hit: it no longer halts the walk and
  ## only a replay can promote it.
  for i in m.candidates ..< w.candidates.len:
    w.candidates[i].soundness.pathTaint =
      w.candidates[i].soundness.pathTaint + taint
    w.candidates[i].soundness.witnessUndefined =
      w.candidates[i].soundness.witnessUndefined + ubOrdinals(ub)
  if m.found >= w.found.len: return
  var kept = w.found[0 ..< m.found]
  for i in m.found ..< w.found.len:
    var r = w.found[i]
    r.soundness.pathTaint = r.soundness.pathTaint + taint
    r.soundness.witnessUndefined = r.soundness.witnessUndefined + ubOrdinals(ub)
    if scSpurious in r.soundness.pathTaint:
      r.witnessExtraction = @[]
      w.candidates.add r
    else:
      kept.add r
  w.found = move kept

proc stampStatementSince(w: var WalkCtx; m: StmtMark; taint: Taint;
                         ub: set[UbKind] = {}) =
  ## The end of a statement that left stray taint: on its exit-channel
  ## entries (`stampExitsSince`) and on its findings (`stampFindingsSince`).
  ## The paths it returns are the caller's to taint (`walk`).
  stampExitsSince(w, m.exits, taint, ub)
  stampFindingsSince(w, m, taint, ub)

proc taintAll(paths: seq[Path]; taint: Taint;
              ub: set[UbKind] = {}): seq[Path] =
  ## Each of `paths` as a fork joined with `taint`.
  result = newSeqOfCap[Path](paths.len)
  for p in paths:
    result.add forkPathTainted(p, p.pc, p.env, carriedDegrade(taint, ub))

type
  StmtShape = enum
    ## RFC-0016 INT-34. How `enterStmt` bracketed a statement's capture cells.
    ssBare       ## the frame keeps no cells (or nothing to walk): bare
    ssCompound   ## a compound statement: a depth, no snapshot, no reconcile
    ssLeaf       ## a leaf statement: snapshotted, then reconciled

  StmtBracket = object
    ## RFC-0016 INT-34 (0005 review R2-14). What `enterStmt` set aside and
    ## set up around one statement, for `leaveStmt` to settle and put back.
    outerPending: PendingDegrade
      ## The lowering queue the enclosing statement left (`setAsidePending`).
    outerStray: Taint
    outerStrayUb: set[UbKind]
      ## The enclosing statement's stray (`w.stmtStrayTaint`/`stmtStrayUb`).
    since: StmtMark
      ## Where the statement began: its exits and findings are those after.
    shape: StmtShape
    depth: int
      ## The capture-sync depth of the snapshot (`ssLeaf` only).
    ins: seq[Path]
      ## The paths the statement walks: the entry paths with the set-aside
      ## queue joined, and snapshotted (`ssLeaf`).

proc enterStmt(stmt: IRStmt; paths: seq[Path]; w: var WalkCtx): StmtBracket =
  ## RFC-0016 INT-34. The opening half of `walk`'s statement bracket, in
  ## order: set the caller's lowering queue and stray aside, mark where the
  ## statement began, taint the entry paths with the set-aside queue, and
  ## snapshot the frame's cells for a leaf statement (`snapCells`). A nil
  ## statement, no path, or a frame with no cells is walked bare; a compound
  ## statement takes a depth but no snapshot (`walk` says why).
  result.outerPending = setAsidePending()
  result.outerStray = w.stmtStrayTaint
  result.outerStrayUb = w.stmtStrayUb
  w.stmtStrayTaint = {}
  w.stmtStrayUb = {}
  result.since = w.stmtMark
  result.ins =
    if result.outerPending.taint == {}: paths
    else: taintAll(paths, result.outerPending.taint, result.outerPending.ub)
  if stmt == nil or result.ins.len == 0 or not frameHasCells(result.ins, w):
    result.shape = ssBare
  elif stmt.kind in compoundStmtKinds:
    inc w.capSyncDepth
    result.shape = ssCompound
  else:
    inc w.capSyncDepth
    result.shape = ssLeaf
    result.depth = w.capSyncDepth
    result.ins = snapCells(result.ins, result.depth, w)

proc leaveStmt(stmt: IRStmt; b: StmtBracket; outs: seq[Path];
               w: var WalkCtx): seq[Path] =
  ## RFC-0016 INT-34. The closing half of `walk`'s statement bracket, in
  ## order: reconcile a leaf statement's cells against its snapshot
  ## (`reconcileCells`), take the stray (the statement's own plus whatever
  ## is still queued, which picks up anything the reconcile queued, e.g.
  ## `syncAddrCells`' `mkTableSet` lowering), put the caller's queue and
  ## stray back, and stamp the stray on every path the statement produced.
  result = outs
  case b.shape
  of ssBare: discard
  of ssCompound: dec w.capSyncDepth
  of ssLeaf:
    dec w.capSyncDepth
    result = reconcileCells(producerOf(stmt), outs, b.depth, w)
  let left = takePending()
  let stray = w.stmtStrayTaint + left.taint
  let strayUb = w.stmtStrayUb + left.ub
  restorePending(b.outerPending)
  w.stmtStrayTaint = b.outerStray
  w.stmtStrayUb = b.outerStrayUb
  if stray != {}:
    result = taintAll(result, stray, strayUb)
    stampStatementSince(w, b.since, stray, strayUb)

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path] =
  ## `walkStmt`, bracketed as one statement (`enterStmt`, `leaveStmt`;
  ## RFC-0016 INT-34 folded `walkCapSynced` into it, 0005 review R2-14). The
  ## bracket keeps two disciplines.
  ##
  ## **The lowering queue** (RFC-0005 review R1-04, R2 (SD1/SD2), R3 (T1)).
  ## The statement is the unit of the pending-lowering-taint discipline. A
  ## lowering decline cannot fork a path from inside `lower`: it queues its
  ## taint (`queueDegrade`) for the walk arm that called `lower` to
  ## drain onto the path it lowered for.
  ##
  ## A statement owns what it queues, and only that. What is queued when it
  ## begins belongs to the enclosing statement -- an expression half
  ## lowered around a body walked mid-expression, or an arm's undrained
  ## deposit before it walks a child -- so it is set aside for the
  ## statement and put back when it returns, for the enclosing statement's
  ## drain (R2 SD1: R1-04 took it as this statement's own and cleared it,
  ## and when the statement left only through `return`/`break`/`continue`
  ## it landed on no path at all). The paths the statement starts from
  ## continue the path it was queued for, so they carry it too: a target
  ## the statement reaches is not solved clean on what it says is not
  ## modelled.
  ##
  ## When the statement returns, nothing it lowered may still be queued,
  ## and nothing may have been found queued by one of its lowerings
  ## (`claimStrayPendingTaint`, the drain's entry check). Either is a
  ## deposit whose path is not known (a raw `lower` with no drain of its
  ## own), so every path the statement produced carries it: the ones it
  ## returns, and the ones it parked on an exit channel (R2 SD2,
  ## `stampExitsSince`). Before R1-04, the variant constructor's plain
  ## fields left an unwritten global's `feGlobalHavoc` queued for the next
  ## drain, a sibling's or none, and the path that read the global reached
  ## a target as a clean `sxSat`.
  ##
  ## The statement's exits are the entries parked after the serial it
  ## began at (R3 T1: R2 took per-channel length marks, and an `isTry` in a
  ## handler body that claimed an older `caught` entry shrank the channel
  ## under its mark, so the new entry landed below it unstamped). A
  ## statement with nothing queued on either side allocates nothing.
  ##
  ## RFC-0016 INT-36 (R3-17): and the findings it filed (`stampStatementSince`):
  ## a hit solved mid-statement, before the stray was found, was filed from a
  ## path that did not carry it yet.
  ##
  ## **The capture cells** (RFC-0005 S8ax). Each by-reference capture of the
  ## current frame (`CallFrameCtx.capCells`) is kept equal to its env cell.
  ##
  ## Nim keeps a variable a closure captures by reference in a heap env the
  ## closure shares with its frame: a write through either is seen by the
  ## other, wherever the closure is applied. The walk keeps the local as
  ## the frame's own binding and the cell (`capCellName`, a `__gl:` name, so
  ## every call threads it as it threads a global) as the one the closure
  ## reads and writes away from the frame. After each statement the side
  ## that changed since it began wins: a write to the local is copied to
  ## the cell; a write to the cell (a call applied the closure) is copied
  ## to the local. Declined (`ceCaptureByRefUnmodelled`), the local's value
  ## winning:
  ##
  ## * both written, to different values: two writes the walk cannot order;
  ## * the cell written by anything but a call statement (an expression's
  ##   closure call applied the closure away from here): the statement may
  ##   have read the local before the write;
  ## * a call statement passing a capture by address (`var`, `addr`): Nim's
  ##   parameter IS the cell, which the callee's copy is not.
  ##
  ## A raise resuming here takes the cell's value (`syncCapCellsFromCells`).
  ##
  ## Likewise each address-taken variable and its heap cell
  ## (`syncAddrCells`), and each element cell and its element
  ## (`syncElemCells`, RFC-0005 S8be). Reconciled where an effect is
  ## produced: each leaf statement (`leaveStmt`), each guard
  ## (`evalCondSynced`) and each `return` value (`evalReturnSynced`).
  ## Only a leaf statement is snapshotted and reconciled: a compound one is
  ## walked bare, its leaves and guards reconciling themselves
  ## (`reconcileCells`). It still takes a depth, so a path that leaves it
  ## early (a `break`) carrying an inner leaf's snapshots rejoins where
  ## every snapshot is shallower, and the next one drops them
  ## (`dropSnapshots`) rather than reading them as its own.
  var b = enterStmt(stmt, paths, w)
  let outs = walkStmt(stmt, move b.ins, w).live
  leaveStmt(stmt, b, outs, w)

# ---- Statement exit-taint test hook (H1 pattern) -----------------------------
# `Path`/`WalkCtx` are not exported past the runtime unit (`walk_types.nim`), so -- as
# `h1PathHasHeapFields` and `rfc0005S1CarrierProbe` -- the hook below drives
# the real `walk`, `routeRaise`, `park` and `stampExitsSince` for
# `tests/tsymex_rfc0005_r2_walktaint.nim` and reports what it observed. It
# exists solely for that test and has no role in the walker; it saves and
# restores every threadvar it touches. The source shapes that would reach
# these holes set the calling expression's queue aside themselves
# (`takePendingLowerEffects`) or drain at the site, so the hook stands in for
# a statement that queues taint it does not drain.

type
  StmtExitTaintProbe* = object
    ## Observations `stmtExitTaintProbe` reports (see its doc).
    resultLen*: int
    pendingAfter*: Taint     ## the caller's queue once the `break` returned
    breakTaint*: Taint       ## the taint of the path the `break` sent out
    channelsParked*: int
      ## How many channels the walk's exit groups hold (one loop frame, one
      ## call frame): `parkOnEach` parked one path on each.
    channelTaints*: seq[Taint]
      ## The taint of each entry parked after the mark, one per channel,
      ## once one path was parked on every channel and the stamp ran.
    priorTaint*: Taint       ## an entry parked before the statement began
    caughtTaints*: seq[Taint]
      ## The `caught` entries after a second raise into a handler that holds
      ## an inner try, stamped as that raise's statement.

proc stmtExitTaintProbe*(): StmtExitTaintProbe =
  ## Three statements, each on a fresh walk context:
  ##   1. A `break` inside one loop frame on a clean path, with
  ##      `{scSpurious}` queued by the (simulated) enclosing statement: the
  ##      queue must be the caller's again afterwards, and the break path
  ##      must carry it.
  ##   2. One path parked on every exit channel after an entry parked
  ##      earlier, then `stampExitsSince` from between them: each new entry
  ##      carries the taint, the earlier one does not. The channels are
  ##      reached by the walk the stamp uses (`forEachExitGroup`), so a
  ##      channel added to a group is parked on and pinned with no edit here.
  ##   3. Two raises caught by one bare `except` whose arm holds an inner
  ##      `try`; the second is stamped as its own statement. Its entry must
  ##      carry the taint wherever the inner try's claim left it.
  let savedPending = setAsidePending()
  let spur: Taint = {scSpurious}
  template np(): Path = Path(pc: @[], env: initOrderedTable[string, SymVal]())
  proc probeCtx(): WalkCtx =
    result.exitClock = newExitClock()
    result.topExits = result.exitClock.newExits(CallExits)
    result.frame = initCallFrameCtx(result.exitClock)
  var w = probeCtx()
  w.loopStack.add initLoopFrame(w.exitClock)
  queueDegrade(spur)
  let r = walk(mkBreak(), @[np()], w)
  result.resultLen = r.len
  result.pendingAfter = peekPending().taint
  if w.loopStack[0].exits.breakPaths.len > 0:
    result.breakTaint = w.loopStack[0].exits.breakPaths.contents[0].taint
  restorePending(savedPending)
  var w2 = probeCtx()
  w2.loopStack.add initLoopFrame(w2.exitClock)
  w2.callStack.add initCallFrame(w2.exitClock)
  w2.loopStack[0].exits.breakPaths.park(np())
  let since = w2.exitClock.mark
  var parked = 0
  let mk = proc (): Path =
    inc parked
    np()
  forEachExitGroup(w2, g): g.parkOnEach(mk)
  result.channelsParked = parked
  stampExitsSince(w2, since, spur)
  result.priorTaint = w2.loopStack[0].exits.breakPaths.contents[0].taint
  var taints: seq[Taint]
  w2.visitExitsSince(since, proc (p: var Path) = taints.add p.taint)
  result.channelTaints = taints
  var w3 = probeCtx()
  w3.frame.handlerStack.add HandlerFrame(handlers: @[ExceptHandler(
    typeIds: @[], body: mkBlock(@[mkTry(mkBlock(@[]), @[])]))])
  discard routeRaise(np(), "E", none(string), w3)
  let since3 = w3.exitClock.mark
  discard routeRaise(np(), "E", none(string), w3)
  stampExitsSince(w3, since3, spur)
  for c in w3.frame.exits.held.caught: result.caughtTaints.add c.path.taint

type
  StrayFindingProbe* = object
    ## Observations `strayFindingProbe` reports (see its doc).
    foundBefore*, foundAfter*, candidatesAfter*: int
    foundAfterExitsOnly*: int
      ## What the statement's end left in `w.found` before INT-36: the exit
      ## stamp alone (`stampExitsSince`).
    earlierFoundKept*: bool
    movedTaint*, stmtCandidateTaint*: Taint

proc strayFindingProbe*(): StrayFindingProbe =
  ## RFC-0016 INT-36 (R3-17). A walk context holding a clean winner filed
  ## before a statement began; the statement files a candidate and a clean
  ## winner, and ends with `{scSpurious, scIncomplete}` stray. Run twice:
  ## with the exit stamp alone (the statement end before INT-36) and with
  ## the statement stamp `walk` runs (`stampStatementSince`). For
  ## `tests/tsymex_0016_int36_collector.nim` only.
  let stray: Taint = {scSpurious, scIncomplete}
  proc staged(m: var StmtMark): WalkCtx =
    result.exitClock = newExitClock()
    result.topExits = result.exitClock.newExits(CallExits)
    result.frame = initCallFrameCtx(result.exitClock)
    result.found.add RawResult(status: sxRaised, raisedTypeId: "before")
    m = result.stmtMark
    result.admitSolvedHit(RawResult(status: sxSat,
      soundness: Soundness(pathTaint: {scSpurious})))
    result.admitSolvedHit(RawResult(status: sxSat))
  var m0: StmtMark
  var w0 = staged(m0)
  stampExitsSince(w0, m0.exits, stray)
  result.foundAfterExitsOnly = w0.found.len
  var m: StmtMark
  var w = staged(m)
  result.foundBefore = w.found.len
  stampStatementSince(w, m, stray)
  result.foundAfter = w.found.len
  result.candidatesAfter = w.candidates.len
  result.earlierFoundKept = w.found.len > 0 and
    w.found[0].status == sxRaised and w.found[0].raisedTypeId == "before" and w.found[0].soundness.pathTaint == {}
  if w.candidates.len == 2:
    result.stmtCandidateTaint = w.candidates[0].soundness.pathTaint
    result.movedTaint = w.candidates[1].soundness.pathTaint

type
  StrayClaimProbe* = object
    ## Observations `strayClaimProbe` reports (see its doc).
    tripped*: bool       ## the entry check stopped on the stray
    strayKept*: Taint    ## what the statement kept for its paths
    pendingAfter*: Taint ## the queue once the probe drained it

proc strayClaimProbe*(): StrayClaimProbe =
  ## RFC-0016 INT-37 (R2-08). A lowering's entry check
  ## (`claimStrayPendingTaint`) on a walk context with `{scSpurious}` left
  ## queued by no lowering of its own: a debug build stops on it, a release
  ## build keeps it for the statement. Restores every threadvar it touches.
  ## For `tests/tsymex_0016_int37_probes.nim` only.
  let savedPending = setAsidePending()
  let savedCtx = currentWalkCtxPtr
  let savedSinks = currentLowerSinks
  var w: WalkCtx
  w.exitClock = newExitClock()
  w.topExits = w.exitClock.newExits(CallExits)
  w.frame = initCallFrameCtx(w.exitClock)
  currentWalkCtxPtr = addr w
  currentLowerSinks = addr w.sinks
  queueDegrade({scSpurious})
  try:
    claimStrayPendingTaint()
  except AssertionDefect:
    result.tripped = true
  result.strayKept = w.stmtStrayTaint
  discard takePending()
  result.pendingAfter = peekPending().taint
  currentWalkCtxPtr = savedCtx
  currentLowerSinks = savedSinks
  restorePending(savedPending)

proc routeRaise(p: Path, typeId: string, msg: Option[string],
                w: var WalkCtx): seq[Path] =
  ## Phase 15 E3. Route a raise on path `p` carrying `typeId`/`msg`. This is the
  ## single handler-matching primitive, called both inline by `walk(isRaise)` and
  ## by the `isCall` arm for inter-procedural propagation of a callee's escaped
  ## raise. It searches the CURRENT call frame's handler stack top-down for the
  ## first `ExceptHandler` whose `typeIds` contains `typeId` (EXACT-STRING
  ## membership — subtype catch is E4; an empty `typeIds` is a bare `except:`
  ## catch-all matching everything).
  ##
  ## MATCH → the raise is CONSUMED: walk the matched handler body on `p` with
  ## `inFlightExn` set to the raised exn (so a bare `raise` re-raises it), cleared
  ## on normal handler exit. The handler body's continuation paths are recorded on
  ## the frame's `caught` channel (tagged by the catching try's depth) so they
  ## EXIT the try via the owning `isTry` arm — they must NOT flow back inline into
  ## the try body at the raise site. `routeRaise` itself returns `@[]` (the raise
  ## terminates the current straight-line path).
  ##
  ## NO MATCH (or empty handler stack) → propagate. If this is a callee frame
  ## (`frameStack` non-empty), record the raise on the frame's `escaped` channel
  ## for the caller's `isCall` arm to re-route (inter-proc). Otherwise we are at
  ## the SUT boundary: surface a public `sxRaised` finding (E2b semantics,
  ## target-gated) and terminate the path (return `@[]`).
  # RFC-0005 S1c (§2.6): a TAINTED path's raise is routed like any other
  # (was: killed unconditionally -- "bailed-call retSyms are unconstrained" --
  # with a kindless ⊤ run mark, including for a handler-caught raise). The
  # taint rides the path through the handler body / escape / finally exactly
  # as `pc` does (every fork joins it), so nothing downstream can mistake it
  # for clean: a boundary `sxRaised` it produces is filed as a CANDIDATE by
  # `admitSolvedHit` below, never a winner. Killing it instead dropped every
  # behaviour past the raise -- an omission the run could not account for.
  # Phase 15 E4. Subtype matching (replaces E3's exact-string membership). An
  # unknown raised type (not in `exnTable` nor `userExnHierarchy`) is matched
  # ONLY against a bare `except:` — never a named handler — and records a
  # `eeUnknownExnType` sevWarning (Invariant 3: no silent false-negative). A
  # known type matches a named handler `ht` iff `isSubtypeOf(typeId, ht, …)`.
  #
  # RFC-0005 S6b (RFC §3.1 round-2 row): that match rule is a BEHAVIOUR
  # SUBSTITUTION, now classified (`eeUnknownExnType` -> dcSubstituted) and
  # tainting instead of inert. The warning is recorded ONCE, through
  # `degrade`'s `dsUnknownExn` sink (same sinks, same `sevWarning`), and
  # counts on the run through `taintsRun`'s carve-out: an unknown raise
  # voids `sxUnsat`, because every omission it causes -- a named handler's
  # continuation never walked, a boundary finding the `stkRaisedExn` filter
  # or the defect-ness guess suppressed -- is run-global. The token joins
  # the PATH exactly where the guess is acted on and the path survives:
  #   - a NAMED handler passed over only because the type is unknown -- the
  #     path continuing past it (a later bare `except:`, a `finally`, an
  #     escape) is a continuation reality may never take;
  #   - the SUT boundary, where the finding's `raisedIsDefect` and its
  #     surfacing are decided from a type the walker cannot resolve.
  # A bare `except:` reached with no named handler skipped is EXACT (it
  # catches everything in Nim too), so that handler continuation stays clean.
  # An escape to a caller carries the path on unchanged; the caller's
  # `routeRaise` decides again for its own handlers.
  # RFC-0005 S8i. Under `wmFollowConcrete` a raise the concrete replay did
  # not take is not routed: its handler would be walked and recorded as a
  # decision of THIS trace (a `ConcolicBranchRecord` inside a handler that
  # never ran, and a result path whose pc the draws contradict, so
  # `pcSatByConcreteInputs` went false). A let-site `x div y` with `y != 0`
  # concretely routed its `DivByZeroDefect` path into the handler before
  # this. The explore mode is unchanged; `maybeForkDefect` already skipped
  # the concretely-false defect forks it owns.
  if w.mode == wmFollowConcrete and
     concretelyInfeasible(w.z3, w.concreteEq, p.pc & p.defectSurvivorPc,
                          w.settings):
    return @[]
  let raisedKnown = isKnownExnType(typeId, w.statics.exnTable,
                                   w.statics.userExnHierarchy)
  var unknownTok: Degrade
  if not raisedKnown:
    unknownTok = w.degrade(eeUnknownExnType, typeId, dsUnknownExn)
  # RFC-0005 S8ax: a capture the raising call wrote through its cell is
  # the local's value wherever the raise resumes in this frame.
  var rp = syncCapCellsFromCells(p, w)
  # RFC-0005 S8ax: likewise an address-taken variable whose cell the
  # raising call wrote through a pointer takes the cell's value.
  rp = syncAddrCellsFromHeap(rp, w)
  # RFC-0005 S8be: and an element a pointer to it wrote.
  rp = syncElemCellsFromHeap(rp, w)
  var unknownJoined = false
  # RFC-0016 W1-c2 (W-03, INT-27). Under `--panics:on` a Defect is not
  # catchable: it prints its report and ends the process (probed on the pinned
  # Nim 2.2.10: rc 1, `[OverflowDefect]` on stderr, and neither an `except
  # Defect` / `except OverflowDefect` / bare `except:` arm nor a `finally`
  # runs). So its defect-ness is tested BEFORE the handler search and it takes
  # the S8cu crash channel, which no arm and no `finally` sees. A type the
  # walker cannot resolve is not decided here: it keeps the unknown-type
  # decline above (`eeUnknownExnType`).
  # NAMED KNOWN GAP: destructors that run while a panic unwinds are not
  # modelled (a `=destroy` side effect is neither walked nor reported).
  when buildSemantics.panics:
    if raisedKnown and isDefect(w.statics.exnTable, typeId,
                                w.statics.userExnHierarchy):
      crashRaise(rp, typeId, w)
      return @[]
  # 1. Search the handler stack top-down for the first matching arm.
  for i in countdown(w.frame.handlerStack.high, 0):
    let hf = w.frame.handlerStack[i]
    for h in hf.handlers:
      var matched = h.typeIds.len == 0   ## bare `except:` always catches
      if not matched and raisedKnown:
        for ht in h.typeIds:
          if isSubtypeOf(typeId, ht, w.statics.exnTable,
                         w.statics.userExnHierarchy):
            matched = true
            break
      if not matched and not raisedKnown and not unknownJoined:
        # RFC-0005 S6b: a named handler skipped on an unknown type -- every
        # continuation past this point is substituted (joined once).
        rp = forkPathTainted(rp, rp.pc, rp.env, unknownTok)
        unknownJoined = true
      if matched:
        # MATCH. Pop the handler stack down to BELOW the matched frame for the
        # duration of the handler body (an inner try no longer guards us, and a
        # re-raise inside the handler must propagate to the NEXT-outer try, not
        # re-enter this one). Restore afterwards.
        let savedStack = w.frame.handlerStack
        let savedInFlight = w.frame.inFlightExn
        w.frame.handlerStack.setLen(i)
        # RFC-0005 S8l: the matched try's `finally` still guards its handler
        # body -- Nim runs it when the arm returns or raises (probed:
        # `except ValueError: return 5` runs the finally with result == 5;
        # `except ValueError: raise newException(KeyError, "k")` runs it
        # before the KeyError leaves). Keep it at depth `i` with no `except`
        # arms, so a return from the arm is deferred to it (`exitReturn`)
        # and a raise from the arm reaches it (`pendingRaise`); the owning
        # `isTry` (depth `i`) claims both. Before S8l the frame was dropped
        # with its arms and neither exit ran the finally.
        if hf.finallyBlock != nil:
          w.frame.handlerStack.add HandlerFrame(handlers: @[],
                                                finallyBlock: hf.finallyBlock,
                                                loopLen: hf.loopLen)
        # RFC-0005 S8m: the arm is lexically outside every loop / labelled
        # block the try body entered, but the raise is routed from inside
        # them. Cut the loop stack back to the try's entry for the arm, so a
        # `break` / `continue` there leaves the loop enclosing the TRY
        # (probed: `for i: (try: (for j: raise) except: break)` leaves the
        # `i` loop). Before S8m it left the innermost live loop -- the `j`
        # loop -- and walked on inside the try body's loop.
        let loopCut = min(hf.loopLen, w.loopStack.len)
        let savedLoops = w.loopStack[loopCut .. ^1]
        w.loopStack.setLen(loopCut)
        w.frame.inFlightExn = some(ExnRecord(typeId: typeId, msg: msg))
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8: mirror into
                                                     ## the lower-time threadvars
                                                     ## so getCurrent* see this exn
                                                     ## during the handler body.
        let handlerPaths = walk(h.body, @[rp], w)
        w.loopStack.add savedLoops   # RFC-0005 S8m
        # Normal handler exit: clear the in-flight exn, restore the stack.
        w.frame.handlerStack = savedStack
        w.frame.inFlightExn = savedInFlight
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8
        # Record the handler continuations on the frame's `caught` channel tagged
        # by the catching try's depth (`i`). The owning `isTry` claims them and
        # merges them into ITS continuation, so the caught path exits the try
        # instead of resuming the try body after the raise site.
        for hp in handlerPaths:
          w.frame.exits.held.caught.park((depth: i, path: hp))
        return @[]
    # Phase 15 E5: a `finally` guards the raise too: it runs on the RAISED
    # exit path before the raise propagates onward, deferred to that try's
    # `isTry` arm (which claims `pendingRaise` at its depth, runs the
    # finally, and composes the result) -- the raised-path analogue of E3's
    # caught channel, and why a `try: raise … finally: …` (no except) runs
    # its finally before the escape/boundary fall-through below.
    # RFC-0005 S8ac: no arm of this try matched, and it has a `finally`.
    # Nim runs that finally BEFORE an outer `except` sees the raise: defer to
    # this try's `isTry` arm, which walks the finally and re-routes the
    # raise from here outward (the stack is popped to this depth by then).
    # Before S8ac the search went on to the outer tries first, so a
    # `try: (try: raise finally: u = 1) except: ...` ran the outer handler
    # without the inner finally's write (a false sxUnsat on `u == 1`).
    if hf.finallyBlock != nil:
      w.frame.exits.held.pendingRaise.park((depth: i, path: rp, typeId: typeId,
                                          msg: msg))
      return @[]
  # 2. No handler matched in this frame.
  if w.frameStack.len > 0:
    # We are inside a callee — let the raise escape to the caller's handlers.
    # The caller's `isCall` arm drains `escaped` after we return. Carry the
    # raise-site path so heap/pc state is preserved (R1b; structural now).
    w.frame.exits.escaped.park(EscapedRaise(path: rp, typeId: typeId,
                                               msg: msg))
    return @[]
  # 3. Top-level (SUT) frame: surface as a public sxRaised finding.
  # Phase 15 E6. A raise of a Nim `Defect` subtype is a CONTRACT VIOLATION that
  # must surface as `sxRaised{isDefect: true}` regardless of the user's search
  # target (a reachable defect is never silently dropped — that would let a
  # property test pass an input the SUT would crash on). EXCEPT when the
  # defect's `DefectKind` is in `settings.defectExclusions` (default: OOM +
  # stack-overflow): those are suppressed, since modelling them yields spurious
  # findings for virtually all real SUTs. A non-defect `CatchableError` raise
  # keeps the E2b target-gated behavior (only surfaced under an assertion or a
  # matching `stkRaisedExn` search; otherwise the path just terminates).
  let raisedIsDefect = isDefect(w.statics.exnTable, typeId,
                                w.statics.userExnHierarchy)
  let defectExcluded =
    raisedIsDefect and
    typeIdToDefectKind(typeId) in w.settings.defectExclusions
  if defectExcluded: haltExcludedDefect(rp, typeId, w)  ## RFC-0016 K7b
  let wantsRaise =
    if defectExcluded:
      false  ## E6: an excluded defect is suppressed (no finding).
    elif raisedIsDefect:
      true   ## E6: a non-excluded defect always surfaces.
    else:
      case w.target.kind
      of stkAssertionViolation:
        true   ## a reachable raise is a violation finding
      of stkRaisedExn:
        w.target.typeFilter.len == 0 or w.target.typeFilter == typeId
      else:
        false  ## e.g. an stkLabel search: the raise just terminates the path
  if wantsRaise:
    # RFC-0005 S6b: an unknown type's defect-ness (hence `raisedIsDefect` and
    # whether it surfaces at all) is a guess -- the finding rides a tainted
    # path, so it is a candidate, never a clean `sxRaised`.
    if not raisedKnown and not unknownJoined:
      rp = forkPathTainted(rp, rp.pc, rp.env, unknownTok)
      unknownJoined = true
    # RFC-0005 S1c: solved on a tainted path too (`solveTargetHit`).
    let (st, wit, candErrs, why) = solveTargetHit(w, rp)
    case st
    of sxSat:
      let iv = InternalVerdict(kind: ivRaised,
                               raisedTypeId: typeId,
                               raisedMsg: msg,
                               raisedWitness: wit,
                               raisedIsDefect: raisedIsDefect)  ## Phase 15 E6
      # RFC-0005 S1: `pathTaint` PRODUCED at the raised-finding hit; S1c
      # routes on it (clean -> `found`, spurious-tainted -> `candidates`).
      var r = toPublic(iv)
      r.soundness.pathTaint = rp.taint
      r.soundness.witnessUndefined = ubOrdinals(rp.undefined)
      r.undefinedViaOnly = ubOrdinals(rp.undefinedViaOnly)   # W3-z R7
      r.nilDerefOnPath = rp.nilDeref   # RFC-0005 S8k
      r.errors.add candErrs
      w.admitSolvedHit(r)
    of sxUnknown:
      # RFC-0005 S1b (§3.1 solver-undef row): the raised finding's path could
      # not be decided — record it (was a kindless run mark).
      w.halted(beSolverUndef,
        "solver returned unknown on a path raising `" & typeId &
             "` (queryRLimit=" & $w.settings.budget.queryRLimit &
             "): " & why & " (beSolverUndef)")
    of sxUnsat:   discard
    of sxRaised:  discard   ## trySolve never returns sxRaised
  @[]

proc noteOpaqueUndefined(w: var WalkCtx; paths: seq[Path];
                         stmt: IRStmt): seq[Path] =
  ## RFC-0016 W3-z R3 (finding U2). The main walk's reading of
  ## `IRStmt.opaqueUndefined`, which only the K10b tail walk read before: an
  ## opaque call whose body may be undefined was invisible to `tUndefined`
  ## (a trusted `sxUnsat` over a reachable overflow inside the callee) and to
  ## `SymexResult.undefined`. The body is not walked, so the behaviour is
  ## POSSIBLE, not shown: under `tUndefined` a requested kind is the target's
  ## hit, solved on the path at the call (its `witnessUndefined` carries the
  ## kind, so the sat is never trusted); under any other target the kind is
  ## listed, as `haltUndefined` lists a reached op (clean paths, bounded, one
  ## per kind and callee). The path CONTINUES (the call is not a halt, a target
  ## after it stays reachable) but carries the kinds in `Path.undefined`, as
  ## the tail gate's halt does for the run: a sat through it is never trusted.
  let tgt = w.target
  let site = "opaque call `" & stmt.callee & "` (its body may be undefined)"
  for p in paths:
    if w.mode == wmFollowConcrete and
       concretelyInfeasible(w.z3, w.concreteEq, p.pc & p.defectSurvivorPc,
                            w.settings):
      result.add p
      continue
    for k in stmt.opaqueUndefined:
      let isHit = tgt.kind == stkUndefined and k in tgt.ubKinds
      var listIt = tgt.kind != stkUndefined and scSpurious notin p.taint and
                   w.undefinedFound.len < maxUndefinedFindings
      for u in w.undefinedFound:
        if u.kind == k and u.site == site: listIt = false
      if (isHit and not w.shouldStop) or listIt:
        let solveOn = if closureBodyCallerPc.len == 0: p
                      else: forkPath(p, closureBodyCallerPc & p.pc, p.env)
        let (st, wit, candErrs, why) = solveTargetHit(w, solveOn)
        case st
        of sxSat:
          if isHit:
            w.admitSolvedHit(RawResult(status: sxSat, witness: wit,
              soundness: Soundness(pathTaint: p.taint,
                                   witnessUndefined: ubOrdinals(p.undefined + {k})),
              nilDerefOnPath: p.nilDeref, errors: candErrs))
          else:
            w.undefinedFound.add RawUndefined(kind: k, site: site, witness: wit)
        of sxUnknown:
          if isHit:
            w.halted(beSolverUndef,
              "solver returned unknown on a path reaching " & $k & " in " &
              site & ": " & why & " (beSolverUndef)")
        of sxUnsat, sxRaised: discard
    let np = forkPath(p, p.pc, p.env)
    np.undefined = p.undefined + stmt.opaqueUndefined
    for k in stmt.opaqueUndefinedVia:
      if k notin w.procValueSites: w.procValueSites.add k
    # RFC-0016 W3-z R7: what the call's proc-value variables alone add stays
    # apart (`Path.undefinedViaOnly`); a fixed kind is fixed from here on.
    let viaKinds = stmt.opaqueUndefined - stmt.opaqueUndefinedFixed
    np.undefinedViaOnly = (p.undefinedViaOnly - stmt.opaqueUndefinedFixed) +
                          (viaKinds - (p.undefined - p.undefinedViaOnly))
    result.add np


# ---- Phase 15 Cluster C (C2b): closure CALL application ----------------------

proc flattenLeafAsts(sv: SymVal): seq[RawZ3Ast] =
  ## Phase 15 C2b. The FLATTENED sequence of per-leaf raw Z3 asts of a SymVal,
  ## in the SAME order `sortOfTuple` walks the sorts (ADR-0009 D2/D5). Used to
  ## build the `Z3_mk_app` argument vector — the funcSym's domain is the
  ## flattened env-leaf sorts ++ param sorts, so its argument asts are the
  ## flattened env-leaf asts ++ the flattened arg-leaf asts. Nested tuples
  ## flatten recursively; every other kind is a single leaf via `rawAnyAstOf`.
  case sv.kind
  of svTuple:
    for f in sv.fields:
      for a in flattenLeafAsts(f): result.add a
  else:
    result.add rawAnyAstOf(sv)

proc symValFromRawAst(raw: RawZ3Ast, ty: IRType): SymVal =
  ## Phase 15 C2b. Wrap a raw Z3 ast (the result of a closure funcSym
  ## application) into the typed SymVal its `lambdaRetTy` calls for. The funcSym
  ## range sort was declared from `ty` (`sortOfTuple` of an `allocateSym(ty)`
  ## representative), so the wrap is sort-consistent by construction (ADR-0009
  ## D4). Single-leaf scalar return types only (the C2a `buildClosure` asserts
  ## a single-leaf range sort).
  let ctx = requireCurrentContext()
  case ty.kind
  of itInt:
    case ty.width
    of 8:  liftBV(wrap[Z3BitVec[8]](ctx, raw),  ty.signed)
    of 16: liftBV(wrap[Z3BitVec[16]](ctx, raw), ty.signed)
    of 32: liftBV(wrap[Z3BitVec[32]](ctx, raw), ty.signed)
    of 64: liftBV(wrap[Z3BitVec[64]](ctx, raw), ty.signed)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: caught immediately at its sole call site (applyClosureGround wraps this in a same-frame try/except ValueError, zero intervening walk/loop frames)]
        "symValFromRawAst: unsupported int width " & $ty.width)
  of itBool:
    ofBool(wrap[Z3Bool](ctx, raw))
  of itFloat32:
    SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, raw))
  of itFloat64:
    SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, raw))
  of itBitSet:   ## RFC-0005 S8bq: one bit-vector
    bitSetSV(wrap[Z3AnyAst](ctx, raw), ty.bsElemTy)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: caught immediately at its sole call site (see above)]
      "symValFromRawAst: unsupported closure return type kind " & $ty.kind)

proc applyClosureGround(clo: SymVal, argSyms: seq[SymVal],
                        label: string; callerEnv: Env;
                        bodyOverride: IRStmt = nil;
                        varOuts: seq[tuple[name: string, param: int]] = @[];
                        ptrArgs: seq[IRExpr] = @[]; ptrCodes: seq[int] = @[];
                        locs: seq[VarLoc] = @[];
                        argNames: seq[string] = @[]):
                        SymVal   ## Phase 15 C4 fwd-decl.

proc havocUnknownClosureEffects(e: IRExpr; env: Env) =
  ## RFC-0005 S8bh. A call through a proc value the walk cannot resolve
  ## (`ceClosureUnknownCallee`) may write every `var` actual and every heap
  ## cell (its arguments', and whatever its own captures reach). The call
  ## declines; its effects are havocked rather than dropped, so a fact the
  ## call may have changed is not kept past it: each `var` actual gets a
  ## fresh value of its formal's type, and each heap a fresh array of its
  ## sort. RFC-0005 S8bn (item 6): and each module-level global bound on
  ## the calling path (`env`), which any routine may write; before S8bn only
  ## the path's taint stood for that, and the global kept its value past
  ## the call.
  if currentWalkCtxPtr == nil: return
  let ctx = requireCurrentContext()
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  var gnames: seq[string]
  for k in env.keys:
    if isGlobalEnvName(k): gnames.add k
  sort(gnames)
  for g in gnames:
    let sv = env[g]
    if sv.kind notin {svInt, svBV8, svBV16, svBV32, svBV64, svBool, svFloat32,
                      svFloat64, svString, svRef, svTuple, svArray, svSeq}:
      continue
    var facts: seq[Z3Bool]
    let v = allocateSym(tyOf(sv), freshDegradeName("__closureUnknownGlobal"),
                        facts)
    for f in facts: currentClosureExitPc.add f
    wp[].closureVarOuts.add (name: g, val: v)
  for k, t in e.ccVarTys:
    if t.isNil or k >= e.ccArgs.len or e.ccArgs[k].kind != iekVar: continue
    var facts: seq[Z3Bool]
    let v = allocateSym(t, freshDegradeName("__closureUnknownVarOut"), facts)
    for f in facts:
      currentClosureExitPc.add f
      # RFC-0005 batch 5 (S8bi's `rskClosureExit` on S8bh's havoc): the
      # fresh value's facts hold once the call completed, in order.
      wp[].sinks.raiseOrder.add rskClosureExit
    wp[].closureVarOuts.add (name: e.ccArgs[k].vname, val: v)
  if wp[].callerHeaps.len > 0:
    var fresh = initTable[string, Z3AnyAst]()
    var keys: seq[string]
    for k in wp[].callerHeaps.keys: keys.add k
    sort(keys)
    for k in keys:
      let h = wp[].callerHeaps[k]
      let srt = Z3_get_sort(ctx.raw, h.raw)
      fresh[k] = wrap[Z3AnyAst](ctx, freshOfSort(ctx, srt))
    wp[].closureDidMutateHeap = true; currentClosureDidMutateHeap = true
    wp[].closureExitHeaps = fresh; currentClosureExitHeaps = fresh
    wp[].closureExitAllocCounters = wp[].callerAllocCounters
    currentClosureExitAllocCounters = wp[].callerAllocCounters
    wp[].closureExitLiveRefs = wp[].callerLiveRefs
    currentClosureExitLiveRefs = wp[].callerLiveRefs

proc touchMeetsOuter(touch, outer: seq[string]): string =
  ## RFC-0005 S8bh. The first location a call's `var`/`addr` actuals involve
  ## (`ccTouch`) that the closure body can also reach outside its formals
  ## (`lambdaOuter`), or "" when none. `*` in `outer` reaches everything; a
  ## `t:?` on either side meets every object type on the other.
  if touch.len == 0: return ""
  if "*" in outer: return touch[0]
  var anyOuterT = false
  for o in outer:
    if o.startsWith("t:"): anyOuterT = true
  for t in touch:
    if t in outer: return t
    if t == "t:?" and anyOuterT: return t
    if t.startsWith("t:") and "t:?" in outer: return t
  # RFC-0005 S8cq: a by-value actual whose memory the formal may share meets a
  # body that reaches anything outside its formals (`byValueTouch`).
  if sharedTouch in touch and outer.len > 0: return sharedTouch
  ""

proc lowerClosureCall(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C2b (ADR-0009 D6). Closure APPLICATION. Resolve `e.ccCallee` to an
  ## `svClosure`, descend the lambda body ONCE collecting its return sub-paths
  ## `(pc_i, v_i)`, apply the per-site funcSym at the GROUND `(env, args)` of
  ## THIS occurrence (raw `Z3_mk_app`), and assert one GROUND implication per
  ## sub-path:
  ##     implies(and(branch_conds_i), funcApp == v_i)
  ## into `currentClosureCallAxioms` (drained into every `trySolve`). The call
  ## RESULT is the funcApp itself (the axioms constrain it). NEVER a
  ## `∀env,args` axiom — the function is applied at the ground occurrence and
  ## equated to a value, the same decidable shape as G4's eject-pin (the hang
  ## lesson). The body is reached via the site→body map (`svClosure` carries the
  ## site, not the body IR). Descent uses the live `walk` via `currentWalkCtxPtr`
  ## (this proc runs in the `lower` evaluator, which has no `WalkCtx`).
  let ctx = requireCurrentContext()
  # ---- 1. Resolve the callee to an svClosure (Invariant 3 on failure). ----
  let nilCallee = env.hasKey(e.ccCallee) and isNilClosure(env[e.ccCallee])
  if not env.hasKey(e.ccCallee) or env[e.ccCallee].kind != svClosure or
     nilCallee:
    # RFC-0005 S7: `dcSubstituted` -- a stand-in returned before the call's
    # arguments are lowered (their raises are dropped). `closureDegrade` puts
    # ⊤ on the consuming path, not only in the closure sink.
    # RFC-0016 INT-65: a call through a nil proc value ends the process
    # natively (SIGSEGV, c and cpp); the walk does not model that crash here.
    if nilCallee:
      closureDegrade(ceUnsupportedHof,
        "a call through the nil proc value `" & e.ccCallee & "` (natively " &
          "a SIGSEGV) is not modelled (ceUnsupportedHof)")
    else:
      closureDegrade(ceClosureUnknownCallee,
        "closure call through `" & e.ccCallee &
             "` does not resolve to a closure value in scope")
    havocUnknownClosureEffects(e, env)   ## RFC-0005 S8bh, S8bn
    # No semantics: a stand-in of the declared result type (RFC-0005 S8cd; it
    # was an `int64` whatever that type was, so `f(k).len` over a proc value
    # with no target declined as `iekSeqLen: unsupported receiver kind` and
    # `for x in f(k)` leaked its taint). Its allocation facts hold of every
    # value of the type, so they join the closure axioms, which constrain
    # nothing but this occurrence's own leaves.
    var facts: seq[Z3Bool]
    result = allocateSym((if e.ccRetTy.isNil: tInt(64, true) else: e.ccRetTy),
                         freshDegradeName("__closureUnknownCallee"), facts)
    for f in facts:
      currentClosureCallAxioms.add f
      currentClosureCallAxiomStrs.add $f
    return result
  # RFC-0005 S9: the by-reference captures as they stand at THIS call.
  let clo = refreshByRefCaptures(env[e.ccCallee], env)
  # RFC-0005 S8as: the names this expression read before the call (its own
  # arguments' reads come after the mark: Nim reads them before the call).
  let readBefore = loweringReadNames
  var argSyms: seq[SymVal]
  for a in e.ccArgs: argSyms.add lower(env, a)
  # RFC-0005 S8bh: the call's `var`/`addr` effects. Each `var` formal's
  # exit value is written to its actual (an `iekVar`: the variable, or the
  # temporary the parser writes back to a non-variable lvalue), as the
  # `isCall` arm's #140 write-back does for a direct call. Actuals that
  # share one location (`ccAlias`) run the body specialised to it
  # (`aliasBodies`). The model holds only while the body cannot reach those
  # locations another way (`touchMeetsOuter`) and an `addr` cell's pointer
  # cannot outlive the call (`ptrLocal`); otherwise the call declines.
  var bodyOverride: IRStmt = nil
  var outs: seq[tuple[name: string, param: int]]
  # RFC-0005 batch 9: and a by-value seq, table, set or array (`byValueTouch`).
  if e.ccVarTys.len > 0 or e.ccAddrArgs.len > 0 or e.ccTouch.len > 0:
    let siteKey = (clo.closureSite.siteHash, clo.closureSite.declOrder)
    let bodies =
      if currentLowerSinks != nil:
        currentLowerSinks[].closureBodies
      else: currentClosureBodies
    if bodies.hasKey(siteKey):
      let cb = bodies[siteKey]
      let met = touchMeetsOuter(e.ccTouch, cb.outer)
      if met.len > 0:
        let what = if met.startsWith("n:"): "`" & displayName(met[2 .. ^1]) & "`"
                   elif met == "*": "a location"
                   elif met == sharedTouch: "the memory of a by-value argument"
                   else: "a heap cell of that type"
        let msg = "closure call through `" & e.ccCallee & "`: an argument's " &
               "location, " & what & ", can also be reached by " &
               "the body outside its formals (a capture, a global or a proc " &
               "value it calls): the body's accesses through the two are " &
               "not one location in the walk (RFC-0005 S8bh)"
        # One call per kind, each spelled on its own line: the S7 source pins
        # (`tsymex_rfc0005_s7_closure`) read a site's kind off that line.
        if met.startsWith("n:"):
          closureDegrade(ceCaptureByRefUnmodelled, msg)
        else:
          closureDegrade(feUnsupportedOp, msg)
      for k in e.ccAddrArgs:
        if k >= cb.ptrLocal.len or not cb.ptrLocal[k]:
          closureDegrade(feUnsupportedOp,
            "closure call through `" & e.ccCallee & "`: argument " & $(k + 1) &
                 " is `addr` of a location, and the body may let the pointer " &
                 "escape the call (it is stored, returned, captured or passed " &
                 "on): the pointee is modelled as a cell for the call only " &
                 "(RFC-0005 S8bh)")
      var gone = -1
      var keep = -1
      for k, a in e.ccAlias:
        if a != k:
          if gone >= 0:
            gone = -2
            break
          gone = k
          keep = a
      if gone == -2:
        closureDegrade(feUnsupportedOp,
          "closure call through `" & e.ccCallee & "`: more than two `var` " &
               "arguments share one location (RFC-0005 S8bh)")
      elif gone >= 0:
        var found = false
        for ix, pr in cb.aliasPairs:
          if pr.keep == keep and pr.gone == gone:
            bodyOverride = cb.aliasBodies[ix]
            found = true
        if not found:
          closureDegrade(feUnsupportedOp,
            "closure call through `" & e.ccCallee & "`: `var` arguments " &
                 $(keep + 1) & " and " & $(gone + 1) & " are one location, " &
                 "and the body has no form specialised to that (RFC-0005 S8bh)")
      for k, t in e.ccVarTys:
        if t.isNil or k >= e.ccArgs.len: continue
        if e.ccArgs[k].kind != iekVar:
          closureDegrade(feUnsupportedOp,
            "closure call through `" & e.ccCallee & "`: `var` argument " &
                 $(k + 1) & " names no variable to write back (RFC-0005 S8bh)")
          continue
        let src = if e.ccAlias.len > k: e.ccAlias[k] else: k
        if src < cb.params.len:
          outs.add (name: e.ccArgs[k].vname, param: src)
  let nWrites = closureEnvWrites.len
  # RFC-0005 S8bu: the caller variable each argument names, for an `addr`
  # actual's cell (`bindVarLocs`).
  var argNames: seq[string]
  for a in e.ccArgs: argNames.add(if a.kind == iekVar: a.vname else: "")
  result = applyClosureGround(clo, argSyms, "`" & e.ccCallee & "`", env,
                              bodyOverride, outs, e.ccArgs, e.ccVarPtrSafe,
                              e.ccVarLocs, argNames)
  var clash: seq[string]
  for i in nWrites ..< closureEnvWrites.len:
    let nm = closureEnvWrites[i][0]
    if nm in readBefore and displayName(nm) notin clash:
      clash.add displayName(nm)
  if clash.len > 0:
    queueDegrade(ceCaptureByRefUnmodelled,
      "closure call through `" & e.ccCallee & "` writes " & clash.join(", ") &
           ", which the same expression reads; the order of that read and " &
           "the write is not modelled (ceCaptureByRefUnmodelled)")

proc applyClosureGround(clo: SymVal, argSyms: seq[SymVal],
                        label: string; callerEnv: Env;
                        bodyOverride: IRStmt = nil;
                        varOuts: seq[tuple[name: string, param: int]] = @[];
                        ptrArgs: seq[IRExpr] = @[]; ptrCodes: seq[int] = @[];
                        locs: seq[VarLoc] = @[];
                        argNames: seq[string] = @[]):
                        SymVal =
  ## Phase 15 C4 (factored from C2b `lowerClosureCall`). Apply an `svClosure`
  ## to a vector of already-lowered argument SymVals at the GROUND occurrence:
  ## build the per-site funcSym application (raw `Z3_mk_app` over flattened
  ## env-leaf ++ arg asts), descend the lambda body ONCE, and assert one GROUND
  ## implication per body return sub-path (`implies(branch_conds_i, funcApp ==
  ## v_i)`) into `currentClosureCallAxioms` — NEVER a `∀env,args` axiom (the G4
  ## hang lesson). The call RESULT is the funcApp the axioms constrain. Shared
  ## by `lowerClosureCall` (C2b) and the C4 HOF inline path (one application per
  ## seq element). `label` is a human-readable site tag for error messages.
  let ctx = requireCurrentContext()
  doAssert clo.kind == svClosure, "applyClosureGround: not an svClosure"
  let siteKey = (clo.closureSite.siteHash, clo.closureSite.declOrder)
  # CR-9 Stage 4: read closureBodies from live WalkerStatics when in a walk,
  # else fall back to threadvar (applyClosureGround is always in a walk in
  # practice — lowerClosureCall short-circuits when ptr==nil — but the guard
  # keeps the code correct for any future probe path).
  let closureBodiesLive =
    if currentLowerSinks != nil:
      currentLowerSinks[].closureBodies
    else:
      currentClosureBodies
  if not closureBodiesLive.hasKey(siteKey):
    # The closure was constructed but its body was never stashed — should not
    # happen (buildClosure always stashes). Classify rather than crash.
    # RFC-0005 S7: as the unresolved-callee site (`dcSubstituted`).
    closureDegrade(ceClosureUnknownCallee,
      "closure call through " & label & ": lambda body not reachable for descent")
    var fresh: seq[Z3Bool]
    return allocateSym(tInt(64, true), "__closureNoBody", fresh)
  let cb = closureBodiesLive[siteKey]
  # ---- 2. The call's RESULT at THIS occurrence. ----
  # RFC-0005 S7 (§2.4, the closure-axiom sink): a FRESH constant of the
  # funcSym's range sort, one per call occurrence. It was the funcSym APPLIED
  # to the occurrence's (env-leaf ++ argument) asts, but the body can read
  # state that is not in that vector (the heap, through a captured ref), so
  # two calls with equal arguments were forced equal across an intervening
  # heap write by the GLOBAL ground axioms each occurrence asserts -- a false
  # `sxUnsat`. Each occurrence's result is now defined only by its own axioms
  # (`bc_i ⇒ r == v_i`): definitional, so the global pool never prunes a
  # model of another symbol. The funcSym stays declared (`buildClosure`): the
  # sort is read from it.
  let funcApp =
    if closureRetStructured(cb.retTy):
      # RFC-0005 S8n: a variant result is a fresh variant (fresh leaves per
      # occurrence, as the scalar constant below); S8p: likewise a
      # multi-variant, tuple, string or seq result. Its allocation facts
      # (a discriminator's legal tags, a seq's length) hold of every real
      # value, so they
      # join the closure axioms, which constrain nothing but this
      # occurrence's own leaves. Before S8n the call declined
      # (`seUnsupportedCompoundSortLeaf` + `feUnsupportedOp`): the funcSym
      # has no variant sort.
      var allocFacts: seq[Z3Bool]
      let fresh = allocateSym(cb.retTy, freshDegradeName("__closureRet.structured"),
                              allocFacts)
      for f in allocFacts:
        currentClosureCallAxioms.add f
        currentClosureCallAxiomStrs.add $f
      fresh
    else:
      let appRaw = ctx.checkErr Z3_mk_fresh_const(ctx.raw, "__closureRet",
        Z3_get_range(ctx.raw, clo.closureRawFD))
      try:
        symValFromRawAst(appRaw, cb.retTy)
      except ValueError:
        # Round-6 N30: `symValFromRawAst` only wraps a closure's ground
        # application for `itInt`/`itBool`/`itFloat32`/`itFloat64` — any OTHER
        # return type (e.g. a closure returning `string`) raised `ValueError`
        # unconditionally, for BOTH the assigned and untouched paths alike,
        # uncaught here, surfacing as an internal-fault decline
        # (`weInternalWalkerFault`) instead of an honest classified one. Mirrors
        # the SAME try/except + `feUnsupportedOp` idiom the fallThrough loop
        # below already uses for `defaultZero`'s composite-kind gaps (N16,
        # walker v96): classify, never crash, and fall back to
        # `defaultZero(cb.retTy, ...)` for a well-typed (if unconstrained)
        # placeholder — `closureCallErrors` forces every path reaching this
        # call to `sxUnknown` regardless of what value `funcApp` settles to
        # (Invariant 3), so the fallback's content need not be trustworthy,
        # only type-correct enough that a downstream consumer does not crash.
        # RFC-0005 S7: `feUnsupportedOp` (`dcSubstituted`, S6b's closure-sink
        # row): the fallback below is not tied to any body value, so `closureDegrade`
        # puts ⊤ on the consuming path, not only in the closure sink.
        closureDegrade(feUnsupportedOp,
          "closure call through " & label &
               ": return type kind " & $cb.retTy.kind &
               " has no funcApp wrap in symValFromRawAst (" &
               getCurrentExceptionMsg() &
               ") — path degraded to sxUnknown (feUnsupportedOp)")
        # N46 (round-6 re-review, ADR-0023/SND-3 class widening): this call
        # used to be `defaultZero(cb.retTy, ...)`, which itself still raises
        # `ValueError` for a handful of composite kinds (itUninterp,
        # itSet/itTable, itVariant/itMultiVariant, itDistinct — see
        # `defaultZero`'s own doc comment). Every OTHER call site of
        # `defaultZero` wraps it in a local `try`/`except` (runtime.nim
        # ~7717, ~8451, ~9217 below); this one did not — a closure/HOF
        # lambda returning one of those composite kinds, called inside a
        # loop, reached `defaultZero`'s raw raise here unguarded, the exact
        # ADR-0023 silent-loss shape. Use `allocateSym` instead of
        # `defaultZero`: it is TOTAL for every classifiable type since N40
        # (never raises — self-classifies via `allocDegrade` on an
        # unsupported kind), so no try/except is needed at all. A fresh
        # symbolic placeholder (vs. `defaultZero`'s zero value) is sound
        # here for the SAME reason the comment above already gives: this
        # whole path is already forced to `sxUnknown` by `closureCallErrors`
        # regardless of what value `funcApp` settles to.
        var freshRawWrapPc: seq[Z3Bool]
        allocateSym(cb.retTy, freshDegradeName("__closureRet.rawwrapfail"),
                    freshRawWrapPc)
  # ---- 3. Inline-budget guard (CallFrameCtx.closureInlineCount). ----
  # `currentWalkCtxPtr` is nil only outside an active walk (the C2a probes never
  # reach here). If absent, fall back to the funcApp alone (no descent, no
  # axiom) — sound but imprecise; classified so the verdict degrades.
  if currentWalkCtxPtr == nil:
    # No active walk: `closureDegrade` writes the threadvar (its live-field
    # sync is a no-op here) and joins the pending taint (RFC-0005 S7).
    closureDegrade(ceInlineBudgetExceeded,
      "closure call through " & label &
           " lowered with no active walk context (no body descent)")
    return funcApp
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  template w: untyped = wp[]   ## the live WalkCtx (mutable through the ptr)
  # RFC-0010 B4: `maxClosureInlineCount = 0` is already documented (this
  # field's own comment, smt/types.nim) as the unlimited sentinel; the guard
  # below had no `> 0` gate, so it fired on the FIRST closure application
  # instead. Same `cap > 0 and` house style as `maxFrontierSize`/`maxSplitParts`.
  if w.settings.budget.maxClosureInlineCount > 0 and
     w.frame.closureInlineCount >= w.settings.budget.maxClosureInlineCount:
    # RFC-0005 S6a: `dcSubstituted` (as is the no-walk-context guard above):
    # `funcApp` stands in for a body that is never descended, so the body's
    # captured-variable writes and raises are dropped. RFC-0005 S7: recorded
    # through `closureDegrade`, so the consuming path carries the ⊤ taint
    # itself (the closure veto that once guarded the SAT side is gone, S9).
    closureDegrade(ceInlineBudgetExceeded,
      "closure-application descent exceeded maxClosureInlineCount (" &
           $w.settings.budget.maxClosureInlineCount & ") at " & label)
    return funcApp
  # RFC-0005 S9 (capture by reference). Applied in the frame that built it,
  # the closure's by-reference captures were re-read at the call
  # (`refreshByRefCaptures`). Anywhere else the env does not bind their
  # names, so the body reads the construction-time snapshot -- a value the
  # variable may no longer hold: decline (`dcSubstituted`) and descend on it.
  #
  # RFC-0005 S8ax: the env cell of each one (`capCellName`), threaded to
  # every frame as a global is, holds the variable as it stands now: the
  # body reads that, wherever it is applied. Only a capture with no cell
  # (built where no walk kept one) still declines.
  var cellOf = initTable[string, string]()
  for nm in clo.closureMutCaptures:
    let cell = capCellName(clo.closureFrame, nm)
    if callerEnv.hasKey(cell): cellOf[nm] = cell
  var uncelled: seq[string]
  for nm in clo.closureMutCaptures:
    if not cellOf.hasKey(nm): uncelled.add nm
  if uncelled.len > 0 and clo.closureFrame != w.frame.frameId:
    closureDegrade(ceCaptureByRefUnmodelled,
      "closure call through " & label & " outside the frame that built it: " &
           "its by-reference capture(s) " & displayNames(uncelled).join(", ") &
           " are read as they stood at construction, not as they stand now " &
           "(ceCaptureByRefUnmodelled)")
  # ---- 4. Descend the lambda body ONCE; collect return sub-paths. ----
  # Fresh descent env: params bound to the concrete call args, captures bound
  # from the svClosure's env tuple (by capture name, matching the stash order).
  var descentEnv: Env = initOrderedTable[string, SymVal]()
  if clo.closureEnv != nil and clo.closureEnv[].kind == svTuple:
    let envRec = clo.closureEnv[]
    for i, nm in envRec.fieldNames:
      descentEnv[nm] = envRec.fields[i]
  # RFC-0005 S8as: the module-level variables as the caller holds them.
  # They are one location in every frame, so the body reads what the caller
  # wrote (an unbound one reads its entry value, `entryValueOf`). Before
  # S8as the body met none of them, and a read declined.
  for k, v in callerEnv:
    if isGlobalEnvName(k) and not descentEnv.hasKey(k): descentEnv[k] = v
  # RFC-0005 S8as: a closure call earlier in the same expression may have
  # written one of them, or (applied in the frame that built this closure)
  # one of its captures: the body meets that write (`closureEnvWrites`).
  let inFrame = clo.closureFrame == w.frame.frameId
  for (k, v) in closureEnvWrites:
    if isGlobalEnvName(k) or (inFrame and k in clo.closureMutCaptures and
                              descentEnv.hasKey(k)):
      descentEnv[k] = v
  # RFC-0005 S8ax: away from its frame a capture is its cell's value.
  if not inFrame:
    for nm, cell in cellOf:
      if descentEnv.hasKey(cell): descentEnv[nm] = descentEnv[cell]
  let byRefEntry = descentEnv  ## RFC-0005 S9: the captures as the body met them
  for i, p in cb.params:
    if i < argSyms.len: descentEnv[p.name] = argSyms[i]
  # Push a call frame whose retSym IS the funcApp: `walk(isReturn)` binds each
  # returning path's value to it as `funcApp == v_i` on that path's pc delta.
  let ptrRisk = varFormalPtrRisk(w, cb.params, ptrArgs, ptrCodes)
  w.callStack.add initCallFrame(w.exitClock,
    callee = "closure@" & $clo.closureSite.siteHash & "/" &
            $clo.closureSite.declOrder,
    retSym = funcApp, retName = "__closureRet",
    # RFC-0005 S8m: a bare `return` that never assigned `result` binds the
    # zero value, as the fall-through twin below does. With no `retTy` the
    # path joined `returnedPaths` unbound, and the explicit-return loop
    # below took its LAST BRANCH CONDITION for the value binding: `if y > 0:
    # return` asserted `y > 0` as a ground axiom of the whole run.
    retTy = cb.retTy,
    # RFC-0005 S8bn (item 3): the lambda's `var` formals a pointer may
    # address (all of them for a call that carries no codes).
    ptrRiskFormals = ptrRisk.risk, ptrSafeFormals = ptrRisk.safe,
        sp = nativeStackPointer())   # RFC-0005 S8ca: `nativeStackShort`
  let frameIx = w.callStack.high
  # RFC-0005 S8bu: the calling frame's address cells, for the formals bound
  # to them below.
  let callerCells = w.frame.addrCells
  let callerFrameId = w.frame.frameId
  # Per-frame exception context for the body, and bump the inline budget.
  pushFrame(w)
  w.frame.closureInlineCount = w.frameStack[^1].closureInlineCount + 1
  # RFC-0005 S8ax: the captures (and globals) the body reaches by name are
  # not its own variables: `walkAddrCell` gives none of them a cell.
  for k in byRefEntry.keys: w.frame.outerNames.add k
  # RFC-0005 S8ax: the body keeps each celled capture equal to its cell
  # statement by statement, as the building frame does (`walk`), so a call
  # in the body that applies the closure again meets the body's writes.
  for nm, cell in cellOf:
    w.frame.capCells.add (local: nm, cell: cell)
  # Phase 15 R1b call-ENTRY heap threading for the CLOSURE arm: the closure
  # body descends with the CALLER's threaded heap (seeded into the caller-heap
  # threadvars by the walk arm before this expression was lowered), instead of
  # R1's fresh-empty default — so a deref inside the closure body reads the SAME
  # heap the caller already constrained (ADR-0010 R1b). Empty when unset (no
  # caller heap), preserving pre-R1b behaviour. The Table assignments are
  # value-copies (Nim semantics), so the closure descent cannot alias-mutate the
  # caller's tables.
  #
  # Phase 15 CR-5: seed `liveRefs` from the caller's live refs so
  # `assertFreshness` for a `new T` inside the closure body emits
  # `newRef != callerRef` distinctness inequalities against every ref the
  # caller already minted.  Without seeding, the empty `liveRefs` lets Z3
  # alias a closure-body `new T` with a caller ref (spurious aliasing witness).
  # CR-9 Stage 6 Group-3: read caller-heap values from WalkCtx fields when a
  # walk is active (the LIVE store); fall back to threadvars otherwise.
  # `w` is always available here (applyClosureGround has `w: var WalkCtx`).
  #
  # RFC-0005 S7: the calling expression's pending lowering effects are set
  # aside for the descent and reinstated after it (`PendingLowerEffects`), so
  # the body's own statement arms can neither wipe nor steal them. If an
  # EARLIER closure call in the same expression already wrote the heap, the
  # body descends from that call's exit heap (its writes precede this call).
  let pending = takePendingLowerEffects(w)
  let chainHeap = pending.didMutate
  let descentBase = Path(pc: @[], env: descentEnv,
                         taint: {},  ## RFC-0005 S1: descent starts clean
                         heaps: (if chainHeap: pending.exitHeaps
                                 else: pending.callerHeaps),
                         heapDepth: pending.callerHeapDepth,
                         allocCounters: (if chainHeap: pending.exitAlloc
                                         else: pending.callerAlloc),
                         liveRefs: (if chainHeap: pending.exitLiveRefs
                                    else: pending.callerLiveRefs))  ## Phase 15 CR-5
  # RFC-0005 S8bu: a formal whose actual is an address-taken variable of the
  # calling frame, or a path into one, is bound to the variable's cell, as
  # a direct call's is (`inheritAddrCells`, `bindVarLocs`): the body keeps
  # the two equal statement by statement, so its writes through the formal
  # and through a pointer it holds land on one location in its order.
  # Before S8bu such a call declined, and a by-value argument Nim passes by
  # address (a large object) was passed as a copy, missing the body's
  # writes through the pointer (swapped verdicts). The calling frame's
  # element cells are read for `bindVarLocs` (an element `s[i]` of a seq
  # with element cells). A whole variable's write-back by name is dropped:
  # the cell carries the write, and the calling statement reads it back
  # (`syncAddrCells`).
  var boundOuts: seq[string]
  block bindCells:
    var varArgs: seq[(string, string)]
    for o in varOuts:
      let src = cb.params[o.param].name
      varArgs.add (src, o.name)
    var entryCells: seq[AddrCellEntry]
    for c in callerCells:
      if not callerEnv.hasKey(c.cell) or callerEnv[c.cell].kind != svPtr:
        continue
      for (formal, callerName) in varArgs:
        if callerName == c.local:
          let cell = if c.bound: varLocCellName(formal) else: addrCellName(formal)
          descentBase.env[cell] = callerEnv[c.cell]
          entryCells.add (local: formal, cell: cell, ty: c.ty, path: c.path,
                          ixs: c.ixs, bound: c.bound, view: c.view, slot: "")
          if callerName notin boundOuts: boundOuts.add callerName
      # RFC-0016 S8ch: a module-level variable's cell, threaded with the
      # globals (`descentEnv`): the body reaches both by name.
      if not c.bound and isModuleGlobalEnvName(c.local) and
         descentBase.env.hasKey(c.local) and descentBase.env.hasKey(c.cell):
        entryCells.add c
    if locs.len > 0:
      descentBase.elemCells = w.callerElemCells
      var paramNames: seq[string]
      var argVars: seq[(string, string)]
      for i, p in cb.params:
        paramNames.add p.name
        if i < argSyms.len and i < argNames.len and argNames[i].len > 0:
          argVars.add (p.name, argNames[i])
      var elemShares: seq[(string, string)]
      let why = bindVarLocs(descentBase, callerEnv, callerCells, callerFrameId,
                            locs, varArgs, argVars, paramNames, entryCells,
                            elemShares, w)
      if why.len > 0:
        closureDegrade(feUnsupportedOp,
          "closure call through " & label & ": " & why & "; the body's " &
               "writes through the two are not modelled in its order " &
               "(feUnsupportedOp, RFC-0005 S8bu)")
      # A by-value seq sharing its caller's element cells has them under
      # the formal's name in the body (`inheritElemCells`); the body cannot
      # write the formal, so nothing is carried back.
      inheritElemCells(descentBase, callerFrameId, w.frame.frameId,
                       elemShares, @[], @[])
    w.frame.addrCells = entryCells
    anchorViews(descentBase, entryCells, w.frame.frameId)   ## RFC-0005 S8ca
  # RFC-0005 S8ca: a by-reference capture whose variable's address is taken
  # (its pointer threaded beside its env cell, `capAddrName`) is bound to
  # the address cell, as a named callee's capture is (`inheritAddrCells`):
  # the body keeps the two equal, and the calling path is marked
  # (`capBoundName`) so the owning frame reads the cell's value.
  var boundCaps: seq[tuple[cell: string; p: SymVal]]
  for nm, cell in cellOf:
    let an = capAddrName(cell)
    if not descentBase.env.hasKey(an) or descentBase.env[an].kind != svPtr:
      continue
    w.frame.addrCells.add (local: nm, cell: an,
                           ty: descentBase.env[an].ptrPointee, path: @[],
                           ixs: @[], bound: false, view: false, slot: "")
    boundCaps.add (cell: cell, p: descentBase.env[an])
  # RFC-0005 S8cn: a decline this call has already made (`closureDegrade`) waits,
  # in `pending`, for the path consuming the call's value, and a target in the
  # body was reached before that, clean, on what the decline says is not modelled:
  # `gw(gs)` through a `var` proc value, a false `sxSat`. The body starts with it
  # too, and the consuming path still gets its own (`restorePendingLowerEffects`).
  # So with a decline the calling path has already passed (`f(t["a"], t)`'s marker).
  let bodyEntry =
    if pending.queue.taint + currentCallerTaint != {}:
      forkPathTainted(descentBase, descentBase.pc, descentBase.env,
                      carriedDegrade(pending.queue.taint + currentCallerTaint,
                                     pending.queue.ub + currentCallerUb))
    else: descentBase
  # RFC-0005 S8bh: the body specialised to the call's shared locations.
  let outerBodyPc = closureBodyCallerPc
  closureBodyCallerPc = outerBodyPc & currentCallerPc
  let fallThrough = walk((if bodyOverride != nil: bodyOverride else: cb.body),
                         @[bodyEntry], w)
  closureBodyCallerPc = outerBodyPc
  let frame = w.callStack[frameIx]
  # RFC-0005 S7: capture the raises that escaped the body's own handlers
  # BEFORE `popFrame` discards the closure frame (as the `isCall` arm does);
  # `drainClosureRaises` routes them from the calling path.
  let escapedRaises = w.frame.exits.escaped.contents
  popFrame(w)
  w.callStack.setLen(frameIx)
  restorePendingLowerEffects(w, pending)
  for b in boundCaps:   # RFC-0005 S8ca: the mark (`capBoundName`)
    closureEnvWrites.add (capBoundName(b.cell), b.p)
  # RFC-0005 S9 (capture by reference). A body that WRITES a by-reference
  # capture writes the caller's variable; the descent env is the body's own,
  # and nothing carries the write back. Any exit -- a value exit or an
  # escaping raise -- whose capture is not the one the body met declines
  # the call (`dcSubstituted`: the write is dropped).
  # RFC-0005 S9 / S8an / S8as (capture by reference). A body that WRITES a
  # by-reference location -- a mutable capture, or a module-level variable,
  # whether or not the lambda captured it lexically -- writes the caller's
  # variable; the descent env is the body's own. A name is written when an
  # exit (a value exit or an escaping raise) binds it to anything but the
  # value the body met.
  var written: seq[string]
  block collectWritten:
    var exitEnvs: seq[Env]
    for cp in fallThrough: exitEnvs.add cp.env
    for cp in frame.exits.returnedPaths: exitEnvs.add cp.env
    for er in escapedRaises: exitEnvs.add er.path.env
    var ownCells: seq[string]   ## RFC-0005 S8ax: carried with their capture
    for _, cell in cellOf: ownCells.add cell
    for ee in exitEnvs:
      for nm, v in ee:
        if nm in ownCells: continue
        let byRef = isGlobalEnvName(nm) or
          (nm in clo.closureMutCaptures and byRefEntry.hasKey(nm))
        if byRef and nm notin written and
           (not byRefEntry.hasKey(nm) or not sameSymVal(v, byRefEntry[nm])):
          written.add nm
  # RFC-0005 S8as: the write is carried back. Each written name gets one
  # fresh value per call occurrence, defined by one GROUND axiom per value
  # exit -- `exitPc_i ⇒ w == v_i`, v_i the name as exit i left it -- the
  # shape of the call result's own axioms (`assertArm` below): definitional,
  # so the global pool prunes no model of any other symbol, and an exit
  # whose arm was dropped (a tainted sub-path) leaves `w` free. The calling
  # path binds the name to `w` (`closureEnvWrites`, drained by
  # `drainPendingLowerEffects`); a raising exit carries its own values out
  # with the raise (`ClosureRaise.writes`). Before S8as every such call
  # declined (`ceCaptureByRefUnmodelled`). Still declined, scoped: a
  # capture written by a closure applied outside the frame that built it
  # (the env there does not hold the variable), and a name whose value
  # reaches heap cells (`irTypeRefFree`).
  var carried: seq[(string, SymVal)]
  var raiseWrites = newSeq[seq[(string, SymVal)]](escapedRaises.len)
  block writeBack:
    var declined: seq[string]
    for nm in written:
      template exitVal(ee: Env): SymVal =
        if ee.hasKey(nm): ee[nm]
        elif byRefEntry.hasKey(nm): byRefEntry[nm]
        else: entryValueOf(nm)   # an unbound global this exit left alone
      var ty: IRType = nil
      for cp in fallThrough:
        if cp.env.hasKey(nm): ty = tyOf(cp.env[nm])
      for cp in frame.exits.returnedPaths:
        if ty == nil and cp.env.hasKey(nm): ty = tyOf(cp.env[nm])
      for er in escapedRaises:
        if ty == nil and er.path.env.hasKey(nm): ty = tyOf(er.path.env[nm])
      if not isGlobalEnvName(nm) and not inFrame and not cellOf.hasKey(nm):
        declined.add displayName(nm) & " (applied outside the frame that " &
                     "built the closure)"
        continue
      if ty == nil or not irTypeRefFree(ty) or
         (not byRefEntry.hasKey(nm) and programGlobal(nm).isNone):
        declined.add displayName(nm) & " (its value reaches heap cells)"
        continue
      var facts: seq[Z3Bool]
      let wv = allocateSym(ty, freshDegradeName("__closureWrite_" &
                                                displayName(nm)), facts)
      var ok = wv.kind in retBindWiredKinds
      var exits: seq[(seq[Z3Bool], SymVal)]
      for cp in frame.exits.returnedPaths:
        if cp.taint == {}: exits.add (cp.pc, exitVal(cp.env))
      for cp in fallThrough:
        if cp.taint == {}: exits.add (cp.pc, exitVal(cp.env))
      for (_, ev) in exits:
        if not retBindKindsAgree(wv, ev): ok = false
      if not ok:
        declined.add displayName(nm) & " (no value binding for its type)"
        continue
      for f in facts:
        currentClosureCallAxioms.add f
        currentClosureCallAxiomStrs.add $f
      for (pc, ev) in exits:
        let eq = retBindEq(wv, ev)
        var ax = eq
        if pc.len > 0:
          var guard = pc[0]
          for k in 1 ..< pc.len: guard = guard and pc[k]
          ax = guard.implies(eq)
        currentClosureCallAxioms.add ax
        currentClosureCallAxiomStrs.add $ax
      # RFC-0005 S8ax: a celled capture's write lands in its cell; in the
      # building frame in the local too (the frame's `walk` sees both
      # written to one value).
      let cellDst = cellOf.getOrDefault(nm, "")
      if inFrame or cellDst.len == 0: carried.add (nm, wv)
      if cellDst.len > 0: carried.add (cellDst, wv)
      for ri, er in escapedRaises:
        if inFrame or cellDst.len == 0:
          raiseWrites[ri].add (nm, exitVal(er.path.env))
        if cellDst.len > 0:
          raiseWrites[ri].add (cellDst, exitVal(er.path.env))
    if declined.len > 0:
      closureDegrade(ceCaptureByRefUnmodelled,
        "closure call through " & label & ": the body writes the " &
             "by-reference location(s) " & declined.join(", ") & "; the " &
             "write is not carried back to the caller " &
             "(ceCaptureByRefUnmodelled)")
  for (k, v) in carried: closureEnvWrites.add (k, v)
  # RFC-0005 S8bh: each `var` formal's value where the body raised rides
  # the raise to its actual (beside S8as's by-reference writes).
  for ri, er in escapedRaises:
    var ro: seq[tuple[name: string, val: SymVal]]
    for o in varOuts:
      if o.name in boundOuts: continue   # RFC-0005 S8bu: the cell carries it
      let pn = cb.params[o.param].name
      if er.path.env.hasKey(pn): ro.add (name: o.name, val: er.path.env[pn])
    w.closureRaises.add ClosureRaise(raised: er,
                                     writes: raiseWrites[ri],  ## RFC-0005 S8as
                                     varOuts: ro)
    w.sinks.raiseOrder.add rskClosure   # RFC-0005 S8bb
  # RFC-0005 S8bh: each `var` formal's exit value, merged over the
  # value-bearing exits by their branch conditions (as the exit heaps are,
  # below), for its actual. The caller continues only on those exits (the
  # exit-coverage fact), so the first exit's value is the merge's default.
  for o in varOuts:
    if o.name in boundOuts: continue   # RFC-0005 S8bu: the cell carries it
    let pn = cb.params[o.param].name
    var merged: SymVal
    var have = false
    var exits: seq[tuple[bc: seq[Z3Bool], env: Env]]
    for cp in fallThrough: exits.add (bc: cp.pc, env: cp.env)
    for cp in frame.exits.returnedPaths:
      exits.add (bc: (if cp.pc.len > 0: cp.pc[0 ..< cp.pc.high] else: cp.pc),
                 env: cp.env)
    for ex in exits:
      if not ex.env.hasKey(pn): continue
      let v = ex.env[pn]
      if not have or ex.bc.len == 0:
        merged = v
        have = true
      else:
        var guard = ex.bc[0]
        for k in 1 ..< ex.bc.len: guard = guard and ex.bc[k]
        merged = iteSV(guard, v, merged)
    if have: w.closureVarOuts.add (name: o.name, val: merged)
  # RFC-0005 S7 (closure-descent taint): the descent started from a clean
  # root, so whatever its exit paths picked up (a degrade inside the body)
  # must join the CALLING path -- through the pending-taint drain, the one
  # channel a `lower()` has to its consuming path. Every contribution was
  # recorded by the degrade that produced it. A raise's taint rides its own
  # routed path (`drainClosureRaises`).
  var exitTaint: Taint = {}
  var exitUb: set[UbKind] = {}
  for cp in frame.exits.returnedPaths:
    exitTaint = exitTaint + cp.taint
    exitUb = exitUb + cp.undefined
  for cp in fallThrough:
    exitTaint = exitTaint + cp.taint
    exitUb = exitUb + cp.undefined
  queueDegrade(exitTaint, exitUb)
  # ---- 5. Lift each body return sub-path to a GROUND per-call axiom (D6). ----
  # Two channels yield sub-paths `(branch_conds_i, v_i)`:
  #   (a) EXPLICIT `return EXPR` — `walk(isReturn)` bound the value to the frame
  #       retSym (== funcApp) as the LAST pc constraint (`funcApp == v_i`), under
  #       that path's branch conditions; the delta = `[branch_conds..., retEq]`.
  #   (b) IMPLICIT `result` / fall-through — a value-returning lambda body whose
  #       last statement is `result = EXPR` (Nim's semchecked implicit result)
  #       leaves `cp.env["result"]` holding v_i with the path still live; we
  #       build `funcApp == result_i` ourselves under that path's pc.
  # Each axiom is GROUND (funcApp applied at THIS occurrence, equated to a value)
  # — NEVER `∀env,args` (the G4 hang). The base descent pc is empty, so a path's
  # full pc IS its branch conditions.
  proc assertArm(branchConds: openArray[Z3Bool], eq: Z3Bool) =
    let ax = if branchConds.len == 0:
               eq                          # single, unconditional return
             else:
               var guard = branchConds[0]
               for k in 1 ..< branchConds.len: guard = guard and branchConds[k]
               guard.implies(eq)
    currentClosureCallAxioms.add ax
    currentClosureCallAxiomStrs.add $ax    # stringify while the ctx is live
  var sawValue = false
  # SND-1b (RFC-chapulin-hardening, walker v39): a body sub-path tainted
  # `uncertain` (SND-1's `isUnsupported`/maxCallDepth taint) must NOT be folded
  # into `currentClosureCallAxioms` — that sink is GLOBAL and drained into
  # EVERY subsequent `trySolve` for the rest of the run (unlike the call-cache,
  # which already gates on `not frame.exits.returnedPaths[0].uncertain`, ~5850). Skip
  # axiomatizing that sub-path and record `ceClosureBodyUncertain` (its
  # path taint reaches the caller through `closureDegrade`; the whole-run
  # `closureForcedUnknown` that read it went in RFC-0005 S9) instead of
  # asserting a possibly-wrong value as a permanent ground fact.
  var uncertainDrop = false
  for cp in frame.exits.returnedPaths:                       # (a) explicit return
    # RFC-0005 S8m: the taint check comes first. `completeReturn`'s havoc
    # arm (a bare `return` whose composite result has no zero value) hands
    # back a tainted path with NO binding, and a straight-line body leaves
    # its pc empty: it was skipped here as if it had no value, and the call
    # result stayed free with no taint on the calling path.
    if cp.taint != {}:
      sawValue = true
      uncertainDrop = true
      continue
    if cp.pc.len == 0: continue
    sawValue = true
    # ADR-0012: cp.pc holds ONLY genuine branch conditions now (defect-survivor
    # negations were split into cp.defectSurvivorPc by the drains), so the guard
    # is clean — this is the fix for the C3 unsound witness. cp.pc[^1] is the
    # retEq value binding; cp.pc[0..<high] are the branch selectors.
    assertArm(cp.pc[0 ..< cp.pc.high], cp.pc[^1])
  for cp in fallThrough:                                # (b) implicit result
    if cp.env.hasKey("result"):
      sawValue = true
      if cp.taint != {} or svMentionsUninit(cp.env["result"]):
        # RFC-0005 S8bq: a result holding a `newSeqUninit` seq is not bound
        # (as `completeReturn` declines one): the closure veto taints.
        uncertainDrop = true
        continue
      assertArm(cp.pc, retBindEq(funcApp, cp.env["result"]))
    else:
      # N16 (walker v96): a fallthrough path that never touched `result` at
      # all -- legal Nim, and DISTINCT from the `cp.env.hasKey("result")`
      # branch above. `result` still holds the return type's ZERO VALUE on
      # such a path (Nim zero-initializes every `result` slot before the
      # body runs); pre-fix, `cp` was simply DROPPED here -- no axiom of any
      # kind was asserted for it, so `funcApp` stayed exactly as free as it
      # was before descent, a false-`sxSat` generator with a non-replaying
      # witness. This is the SAME shape R2 (walker v90) fixed for the
      # `isCall` arm's fallthrough (see that arm's `else` twin, above in this
      # file); `applyClosureGround` never got R2's fix even though it is the
      # shared implementation for `lowerClosureCall` AND the C4 HOF inline
      # path (map/filter/fold) -- both now carry the else-twin as of v96.
      # Bind `funcApp` to `defaultZero(cb.retTy, ...)` via the SAME
      # `retBindEq` the assigned branch above uses, instead of leaving it
      # free. `defaultZero`/`retBindEq` both still raise `ValueError` (or
      # `SymexRefUnresolvedError`) for a handful of composite kinds neither
      # is wired for -- for those, classified-decline exactly like R2's own
      # twin does, never bind a value the walker cannot back soundly.
      sawValue = true
      if cp.taint != {}:
        uncertainDrop = true
        continue
      try:
        let zeroVal = defaultZero(cb.retTy, "__closureRet.zerodefault")
        assertArm(cp.pc, retBindEq(funcApp, zeroVal))
      except ValueError:
        # RFC-0005 S7: `feUnsupportedOpHavoc` -- the per-occurrence result is
        # left free on this arm and nothing else is dropped (S6b's composite
        # call-result binding shape); the path carries `{scSpurious}`.
        closureDegrade(feUnsupportedOpHavoc,
          "closure call through " & label &
               ": composite-typed implicit-result fallthrough (untouched-" &
               "result path, retTy kind " & $cb.retTy.kind & ") has no " &
               "sound zero-default (" & getCurrentExceptionMsg() &
               ") — path degraded to sxUnknown (feUnsupportedOp)")
  if uncertainDrop:
    # RFC-0005 S7: `dcFreshSymbol` -- the per-occurrence result is free under
    # the dropped arm; `closureDegrade` joins `{scSpurious}` onto the calling
    # path (the arm's own taint already joined through `exitTaint`).
    closureDegrade(ceClosureBodyUncertain,
      "closure call through " & label &
           " body produced an uncertain sub-path (unmodeled-construct taint or " &
           "nested budget bail) — dropped from the ground-axiom set instead of " &
           "asserting an unsound permanent fact")
  # ADR-0012: thread each exit path's defect-survivor facts onto the CALLER via
  # the exit-pc channel (drained by drainPendingLowerEffects). Each fact is
  # guarded by THAT path's branch conditions — `implies(branchConds_i, neg)` —
  # so a multi-arm body stays sound (the caller commits to "took arm i ⇒ arm i
  # didn't overflow"); for the common straight-line body branchConds is empty and
  # the fact is the bare negation. Collected over ALL exit paths (incl. void
  # fall-through) so a defect on a value-less path is not dropped. NEVER added to
  # currentClosureCallAxioms (global) — that would UNSAT the in-body raise path.
  var mergedDefectPc: seq[Z3Bool]
  proc addGuardedDefects(branchConds: openArray[Z3Bool], dnegs: seq[Z3Bool]) =
    if dnegs.len == 0: return
    if branchConds.len == 0:
      for d in dnegs: mergedDefectPc.add d
    else:
      var guard = branchConds[0]
      for k in 1 ..< branchConds.len: guard = guard and branchConds[k]
      for d in dnegs: mergedDefectPc.add guard.implies(d)
  for cp in frame.exits.returnedPaths:                       # explicit: exclude retEq
    let bc = if cp.pc.len > 0: cp.pc[0 ..< cp.pc.high] else: cp.pc
    addGuardedDefects(bc, cp.defectSurvivorPc)
  for cp in fallThrough:                                # implicit/void: all pc
    addGuardedDefects(cp.pc, cp.defectSurvivorPc)
  for c in mergedDefectPc:
    currentClosureExitPc.add c
    w.sinks.raiseOrder.add rskClosureExit   # RFC-0005 S8bi: logged after the raises
  # RFC-0005 S7: exit COVERAGE. The caller continues past the call only on
  # an execution that left the body through a value-bearing exit, so the
  # continuation is confined to the disjunction of the exits' branch
  # conditions. Before S7 nothing said so: a body path that raised, halted
  # or diverged left the result free, and a caller continuation reality
  # never takes (the body raised) could reach the label -- a false `sxSat`.
  # The raising executions are routed separately (`drainClosureRaises`).
  # Skipped when some exit is unconditional (the disjunction is `true`); a
  # body with no exit at all makes the continuation infeasible (`false`).
  block exitCoverage:
    var arms: seq[Z3Bool]
    proc armOf(bc: openArray[Z3Bool]): Z3Bool =
      result = bc[0]
      for k in 1 ..< bc.len: result = result and bc[k]
    for cp in frame.exits.returnedPaths:
      if cp.pc.len <= 1: break exitCoverage
      arms.add armOf(cp.pc[0 ..< cp.pc.high])
    for cp in fallThrough:
      if cp.pc.len == 0: break exitCoverage
      arms.add armOf(cp.pc)
    var covered = mkBool(false)
    if arms.len > 0:
      covered = arms[0]
      for k in 1 ..< arms.len: covered = covered or arms[k]
    currentClosureExitPc.add covered
    w.sinks.raiseOrder.add rskClosureExit   # RFC-0005 S8bi
  # If the body produced NO value-bearing sub-path AND there are no output paths
  # at all (body diverged / was fully stubbed), mark uncertain so a target
  # reached through this result degrades to sxUnknown.
  # NOTE: void closures (no result, no explicit return) are NOT flagged unknown
  # here — they DO produce fallThrough paths (the body ran to completion without
  # a return value), which is the expected and sound behaviour for a void lambda.
  # The original `if not sawValue: sawUnknown = true` incorrectly caught all
  # void closures, collaterally degrading any UNSAT target after a void closure
  # call (see CR-1 companion fix for the sawUnknown/UNSAT interaction).
  # RFC-0005 S8bn (item 5): a body whose every path RAISED did not
  # diverge: each raise is routed to the caller (`w.closureRaises`,
  # `drainClosureRaises`), which is the call's whole behaviour, and the
  # exit-coverage fact (`false`) leaves no continuation. Only a body with no
  # exit at all, raised or not, is a divergence.
  if not sawValue and fallThrough.len == 0 and frame.exits.returnedPaths.len == 0 and
     escapedRaises.len == 0:
    # RFC-0005 S1b: record the kind (was a kindless run mark). WALK sink, not
    # the closure sink (through S8 `closureForcedUnknown` vetoed a winner on
    # any closure-sink sevError, which this site never did; S9 deleted it).
    # RFC-0005 S7: a HALT (`dcOmitted`) -- the exit-coverage fact
    # above is `false` here, so no caller continuation survives the call.
    w.halted(ceClosureBodyDiverged,
      "closure body produced no value-bearing exit (every body path raised, " &
           "halted or was dropped) — the call's result is unconstrained " &
           "(ceClosureBodyDiverged)")
  # ---- Phase 15 CR-1: merge closure exit heaps back to caller ----------------
  # The exit paths from the closure body may carry heap modifications (e.g.
  # `p[] = 99` inside the body) that must be visible to the CALLER after the
  # call returns.  We merge these exit paths' heap state into the CR-1 exit
  # threadvars; `drainClosureExitHeap` in the enclosing `walk` arm applies them
  # to the survivor caller path (the same mechanism `seedCallerHeapThreadvars` +
  # `drainParseIntRaises` uses for the R1b entry-heap and S10b raises).
  #
  # Merge strategy mirrors the named-proc return-merge (isCall arm ~5443-5463):
  #   * heaps: REPLACEMENT — we take the exit heap directly (the caller's ENTIRE
  #     heap is replaced by the closure's, as for named procs).  For multiple
  #     exit paths we ITE-merge (branch_cond_i ? heap_i : else_heap) per type
  #     key; the single-exit-path case (most common: straight-line bodies) is a
  #     direct assignment with no Z3 ite overhead.
  #   * allocCounters: max-merge — post-closure caller `new T` must not collide
  #     with closure-allocated refs (same invariant as named-proc arm).
  #   * liveRefs: the closure exit's liveRefs is already the UNION of the seeded
  #     caller refs + any refs minted inside the body; replace directly.
  let exitPaths = fallThrough & frame.exits.returnedPaths.contents
  if exitPaths.len > 0:
    currentClosureDidMutateHeap = true   # threadvar fallback
    # Single-exit-path fast path (straight-line body, most common case).
    var mergedHeaps = exitPaths[0].heaps
    var mergedAlloc = exitPaths[0].allocCounters
    var mergedLiveRefs = exitPaths[0].liveRefs
    for i in 1 ..< exitPaths.len:
      # Multiple exit paths (branching inside the closure body): merge heaps
      # with Z3 ITE per type key so the caller sees the correct value on each
      # concrete execution path.  `exitPaths[i].pc` holds the accumulated
      # branch conditions for this sub-path; the ITE guard is their conjunction.
      let ePath = exitPaths[i]
      let ctx = w.z3
      if ePath.pc.len > 0:
        var guard = ePath.pc[0]
        for k in 1 ..< ePath.pc.len: guard = guard and ePath.pc[k]
        # N46 audit (RFC-chapulin-hardening bucket-2): `ePath.heaps` is a
        # plain `Table[string, Z3AnyAst]` -- Nim's Table iteration order
        # follows internal hash-bucket layout, not insertion or content
        # order, and is not part of this codebase's cross-build contract.
        # Every `Z3_mk_ite` call below registers a term with Z3 in CALL
        # order, so an unordered walk here makes the resulting query's
        # term-construction order (and therefore Z3's own order-sensitive
        # search heuristics) depend on the Table's internal layout instead
        # of the program's own semantics -- a genuine reproducibility gap,
        # found while auditing the query-assembly path for N46 (mingw vs
        # MSVC walker divergence on the B5-4 trip-wire). Sort by type-key
        # name for a build-independent, reproducible term order; the heap
        # key set is per-TYPE (not per-allocation), so this sort is
        # negligible cost. (The `else` arm below stays unsorted: it only
        # does plain dictionary assignment, no Z3 builder call, so its
        # iteration order cannot affect query content.)
        var tkeys: seq[string]
        for tkey in ePath.heaps.keys: tkeys.add tkey
        sort(tkeys)
        for tkey in tkeys:
          let exitHeap = ePath.heaps[tkey]
          let prevHeap = mergedHeaps.getOrDefault(tkey, exitHeap)
          let rawIte = checkedIte(ctx, guard.raw, exitHeap.raw, prevHeap.raw)
          mergedHeaps[tkey] = wrap[Z3AnyAst](ctx, rawIte)
      else:
        # Unconditional path (else branch of the last if / the only path):
        # this branch's heap dominates.
        for tkey, exitHeap in ePath.heaps:
          mergedHeaps[tkey] = exitHeap
      # max-merge allocCounters
      for tkey, cnt in ePath.allocCounters:
        if cnt > mergedAlloc.getOrDefault(tkey, 0):
          mergedAlloc[tkey] = cnt
      # re-review S-1: true set-union for liveRefs (dedup by raw AST identity).
      # The earlier "take longest list" heuristic silently dropped equal-length
      # arms (e.g. two exit paths each minting one new T), allowing a caller
      # new T to alias the dropped arm's ref. True set-union appends every ref
      # not already in the merged list (compared by raw Z3 AST pointer identity).
      for tkey, refs in ePath.liveRefs:
        var cur = mergedLiveRefs.getOrDefault(tkey, @[])
        for r in refs:
          var found = false
          for c in cur:
            if c.raw == r.raw: found = true; break
          if not found: cur.add r
        mergedLiveRefs[tkey] = cur
    # Dual-write: threadvar (fallback) + WalkCtx fields (LIVE store).
    # CR-9 Stage 6 Group-4: `w` is always available here (applyClosureGround
    # has `w: var WalkCtx` from the walk-descent call above).
    currentClosureExitHeaps = mergedHeaps              # threadvar fallback
    currentClosureExitAllocCounters = mergedAlloc      # threadvar fallback
    currentClosureExitLiveRefs = mergedLiveRefs        # threadvar fallback
    w.closureDidMutateHeap = true                      # CR-9 Stage 6 Group-4
    w.closureExitHeaps = mergedHeaps                   # CR-9 Stage 6 Group-4
    w.closureExitAllocCounters = mergedAlloc           # CR-9 Stage 6 Group-4
    w.closureExitLiveRefs = mergedLiveRefs             # CR-9 Stage 6 Group-4
  funcApp

# ---- Phase 15 C4: DSL higher-order functions over seq[T] --------------------

proc concreteSeqLen(seqSV: SymVal): Option[int] =
  ## Phase 15 C4. If the seq's length folds (via `simplify`) to a Z3 numeral,
  ## return its concrete value; otherwise `none`. `iekSeqAdd` produces a length
  ## like `0 + 1 + 1` that is NOT a bare numeral until simplified, so we
  ## `simplify` first (decidable, cheap) before inspecting the AST kind.
  let folded = simplify(seqSV.seqLen) # [placeholder-audited]
  if getAstKind(folded) == akNumeral:
    try: some(parseInt(getNumeralString(folded)))
    except CatchableError: none(int)
  else:
    none(int)

proc hofElemAt(seqSV: SymVal; i: int): SymVal =
  ## RFC-0005 S8bq. An inline higher-order call's read of element `i`.
  ## RFC-0005 S8bv: a read that may see an unwritten `newSeqUninit` element
  ## deposits its condition (`uninitReadConds`); the statement's drain forks
  ## the continuation on it, so only the executions that read one are
  ## tainted. S8bq tainted the whole path in-band.
  let u = uninitReadCond(seqSV, mkInt(i))
  if u.isSome:
    syncUninitReadCond(u.get)
  seqElemAt(seqSV, mkInt(i))

proc lowerHofCall(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C4 (ADR-0009). DSL higher-order call `filter`/`map`/`fold` over a
  ## `seq[T]` with a closure arg. INLINE path (concrete length ≤
  ## seqInlineThreshold under a permitting `inlinePolicy`): unroll the closure
  ## per element (quantifier-free). AXIOM path (symbolic length): `map` →
  ## `mapArray` (decidable array-map, NO universal-∀); `fold` → raw `Z3_mk_app`;
  ## `filter` → `ceUnsupportedHof` (Phase-16 deferred). Bounded by
  ## seqInlineThreshold (≤ 8) — no combinatorial fan-out.
  let ctx = requireCurrentContext()
  let seqSV = lower(env, e.hofSeq)
  let hofResTy = if e.hofOp == "fold": e.hofRetElemTy else: tSeq(e.hofRetElemTy)
  if seqSV.kind != svSeq:
    # RFC-0005 S8bw (item 1): a receiver that did not lower to a seq (the
    # stand-in of an earlier in-band decline) declines in-band. This was a
    # `doAssert`, a `weInternalWalkerFault` (`gSeq.map(f)`).
    return degradeAlloc(hofResTy, feUnsupportedExprKind,
      "higher-order call (." & e.hofOp & "): receiver lowered to " &
        plainEnglishSymValKind(seqSV.kind) & ", not a seq -- degraded to " &
        "sxUnknown (feUnsupportedExprKind)", "__hofRecvDegrade")
  if seqSV.isUnsupportedFieldPlaceholder: # [placeholder-audited]
    # N27 (walker v97, D1 verifier finding): decline through the R1
    # chokepoint BEFORE touching `concreteSeqLen`/`seqElemAt`/`seqDataRaw` or
    # even lowering the closure arg. Pre-fix, `concreteSeqLen` read the
    # placeholder's HARD-FORCED-`== 0` `seqLen` directly (no guard anywhere
    # in this proc), folded it to a fabricated concrete 0, `canInline` picked
    # n=0, and every op's result SymVal was built WITHOUT the taint flag —
    # exactly the S1 false-verdict class R1 fixed (iekSeqLen/iekSeqSlice),
    # escaped via this HOF path since `hofDispatch` (dsl_parser.nim) never
    # screens the receiver and this proc never called the chokepoint. This
    # single early guard, placed before ANY placeholder-sensitive read
    # (length, element access, elemTy-driven axiom dispatch), covers every
    # such read in the proc by construction — there is nothing below it left
    # unguarded once it returns first.
    declinePlaceholderInLower(seqSV, "", "higher-order call (." & e.hofOp & ")")
    if e.hofOp == "fold":
      # Result type is the accumulator's scalar type (`hofRetElemTy` holds
      # it for `fold` specifically — see `hofDispatch`'s doc), which need not
      # be seq-shaped at all. Mirrors the axiom path's own
      # `__hofFoldOpaque` decline: a fresh, unconstrained, honestly-typed
      # stub (`lower()` has no `pcOut` to thread a real constraint into, per
      # `declinePlaceholderInLower`'s own doc).
      #
      # N36 (walker v101) reachability verification: if `e.hofRetElemTy.kind
      # == itSeq`, `allocateSym` routes into ITS OWN `itSeq` arm, which
      # guards `not isBackedSeqElemTy(ty.seqElemTy)` BEFORE ever calling
      # `allocateSeqDataRaw` — and `isBackedSeqElemTy` is documented to
      # mirror `allocateSeqDataRaw`'s supported-kind set EXACTLY (see its own
      # doc comment, `types.nim`). So an unbacked nested-seq/composite
      # `hofRetElemTy` here structurally cannot reach `allocateSeqDataRaw`'s
      # `SymexNestedSeqUnsupportedError` raise through THIS call — it is
      # diverted to the itSeq arm's inert placeholder instead. CONFIRMED
      # UNREACHABLE; no guard added.
      var fresh: seq[Z3Bool]
      return allocateSym(e.hofRetElemTy, "__hofFoldPlaceholderDecline", fresh)
    else:
      # `map`/`filter` both still return a seq[hofRetElemTy]. Reuse the
      # receiver's ALREADY-allocated, already-constrained (`== 0`) `seqLen`
      # and inert `seqDataRaw` rather than allocate fresh Z3 symbols here —
      # same "arbitrary sort, structurally never selected from" contract
      # `allocateSym`'s `itSeq` placeholder arm documents, and the same
      # "propagate the flag on the SAME already-asserted symbols" idiom
      # `iekSeqSlice`/`iekSeqAdd` use (`return recv` unchanged) — just
      # retargeting `seqElemTy` to `hofRetElemTy` since `map` may declare a
      # different (still-unbacked) result element type than the receiver.
      return SymVal(kind: svSeq, seqLen: seqSV.seqLen, # [placeholder-audited]
                    seqDataRaw: seqSV.seqDataRaw, seqElemTy: e.hofRetElemTy, # [placeholder-audited]
                    isUnsupportedFieldPlaceholder: true,
                    # N47-followup (walker v110): propagate the reason/kind
                    # too, same "SAME already-asserted symbols" idiom as the
                    # rest of this construction — else a `.map()`/`.filter()`
                    # hop over an operation-level-degraded receiver would
                    # silently drop back to the generic nested-seq message.
                    seqUnsupportedFieldReason: seqSV.seqUnsupportedFieldReason,
                    seqUnsupportedFieldKind: seqSV.seqUnsupportedFieldKind)
  # Build the closure value (svClosure) from the lambda arg (C2a construction:
  # snapshots captures, stashes the body, declares the per-site funcSym).
  let cloSV = lower(env, e.hofClosure)
  if cloSV.kind != svClosure or isNilClosure(cloSV):   # RFC-0016 INT-65: nil
    # RFC-0005 S8bw (item 1): as the receiver above (a proc-typed global
    # read before any write); was a `doAssert`.
    return degradeAlloc(hofResTy, feUnsupportedExprKind,
      "higher-order call (." & e.hofOp & "): its proc argument lowered to " &
        plainEnglishSymValKind(cloSV.kind) & ", not a closure -- degraded " &
        "to sxUnknown (feUnsupportedExprKind)", "__hofClosureDegrade")

  # Settings (via the live WalkCtx, mirroring lowerClosureCall).
  var policy = ipHybrid
  var threshold = 8
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    policy    = wp[].settings.inlinePolicy
    threshold = wp[].settings.budget.seqInlineThreshold

  let lenOpt = concreteSeqLen(seqSV)
  # Decide inline vs axiom. ipAlwaysInline forces inline (requires concrete
  # length to be sound; a symbolic length under ipAlwaysInline degrades to the
  # axiom path with a warning, since we cannot unroll an unknown count).
  let canInline =
    lenOpt.isSome and
    (policy == ipAlwaysInline or
     (policy == ipHybrid and lenOpt.get <= threshold))

  if canInline:
    let n = lenOpt.get
    case e.hofOp
    of "map":
      # Result svSeq of element type hofRetElemTy; elem i = mapper(elem i).
      # Round-6 N37: was an UNGUARDED `allocateSeqDataRaw(e.hofRetElemTy,
      # ...)` call -- N36's own doc note on `allocateSeqDataRaw`'s raise
      # already confirmed this site IS reached walk-time BY CODE-PATH
      # ARGUMENT. A live repro attempt this slice found instead that EVERY
      # inline HOF closure application currently collides with a
      # PRE-EXISTING, UNRELATED defect (N29, HOF lambda Z3 domain-sort
      # mismatch) that fires UPSTREAM of this arm entirely (confirmed via
      # direct instrumentation, reverted before landing -- see
      # `allocateSeqDataRaw`'s own updated doc note and
      # `tests/tsymex_r6_n37_raise_residue.nim`'s item-4 honesty note for
      # the full writeup), so this exact pair of call sites is not
      # independently demonstrable as a live wrong-verdict RED in
      # isolation. Fixed anyway by the MECHANISM argument (N36's own
      # precedent for un-independently-pinnable sites): guard with the SAME
      # `isBackedSeqElemTy` predicate `allocateSym`'s itSeq arm already
      # uses, mirroring the fold/axiom-path siblings below (which route
      # through `allocateSym` and were N36-confirmed unreachable BECAUSE of
      # this exact guard) -- never call the unsafe function at all, rather
      # than catching after the fact (avoids the C-backend exception hazard
      # entirely instead of routing through it, matching B7r2's own finding
      # that even a single non-top-level catch/raise on this backend can
      # misbehave).
      if not isBackedSeqElemTy(e.hofRetElemTy):
        queueDegrade(seNestedSeqUnsupported,
          "seq[seq[T]] / seq[complex] not modeled — element kind " &
               plainEnglishTypeKind(e.hofRetElemTy.kind) &
               " (nested seq element type is not supported)")
        var fresh: seq[Z3Bool]
        return allocateSym(tSeq(e.hofRetElemTy), "__hofMapUnsupportedInline", fresh)
      # RFC-0005 S8bc: one array per leaf of a tree element (either side).
      var arrs = allocateSeqArrs(e.hofRetElemTy, "__hofmap.data")
      for i in 0 ..< n:
        let elemSV = hofElemAt(seqSV, i)
        let mapped = applyClosureGround(cloSV, @[elemSV], "map@" & $i, env)
        if not seqElemFits(mapped, e.hofRetElemTy):
          return seqStoreDecline("map", e.hofRetElemTy, mapped)
        let stored = seqStoreArrs(mkSeqSV(mkInt(i), arrs, e.hofRetElemTy),
                                  mkInt(i), mapped)
        if stored.isNone: return seqStoreDecline("map", e.hofRetElemTy, mapped)
        arrs = stored.get
      mkSeqSV(mkInt(n), arrs, e.hofRetElemTy)
    of "filter":
      # Result svSeq: pack kept elements (predicate true) into running compacted
      # indices. result length = sum ite(pred_i, 1, 0); for each i, if pred_i,
      # store elem_i at the current kept count. Bounded, quantifier-free.
      let elemTy = seqCellTy(e.hofRetElemTy)   ## filter preserves element type (RFC-0005 S8ba: its cell)
      # Round-6 N37: same unguarded-`allocateSeqDataRaw` conversion as the
      # `map` arm immediately above -- see its own comment for the full
      # rationale (identical hazard, identical fix).
      if not isBackedSeqElemTy(elemTy):
        queueDegrade(seNestedSeqUnsupported,
          "seq[seq[T]] / seq[complex] not modeled — element kind " &
               plainEnglishTypeKind(elemTy.kind) &
               " (nested seq element type is not supported)")
        var fresh: seq[Z3Bool]
        return allocateSym(tSeq(elemTy), "__hofFilterUnsupportedInline", fresh)
      # RFC-0005 S8bc: one array per leaf of a tree element.
      var arrs = allocateSeqArrs(elemTy, "__hoffilter.data")
      var keptLen: Z3Int = mkInt(0)
      for i in 0 ..< n:
        let elemSV = hofElemAt(seqSV, i)
        let predSV = applyClosureGround(cloSV, @[elemSV], "filter@" & $i, env)
        doAssert predSV.kind == svBool, "filter predicate did not return Bool"
        # Store elem_i at the CURRENT kept index. Stores past the final kept
        # length are never observed (reads are len-bounded), so an
        # unconditional store at `keptLen` is sound.
        let stored = seqStoreArrs(mkSeqSV(keptLen, arrs, elemTy), keptLen, elemSV)
        if stored.isNone: return seqStoreDecline("filter", elemTy, elemSV)
        arrs = stored.get
        keptLen = keptLen + ite(predSV.bo, mkInt(1), mkInt(0))
      mkSeqSV(simplify(keptLen), arrs, elemTy)
    of "fold":
      # Left-fold: acc = folder(acc, elem_i), from the init accumulator.
      doAssert e.hofInit != nil, "fold inline path requires an init accumulator"
      var acc = lower(env, e.hofInit)
      for i in 0 ..< n:
        let elemSV = hofElemAt(seqSV, i)
        acc = applyClosureGround(cloSV, @[acc, elemSV], "fold@" & $i, env)
      acc
    else:
      raise newException(ValueError, "lowerHofCall: unknown HOF op " & e.hofOp)  # [raise-audited: category-c: parser-controlled op-string invariant (e.hofOp is restricted to map/filter/fold by the parser)]
  else:
    # ---- AXIOM path (symbolic length, or concrete length above threshold). ----
    case e.hofOp
    of "filter":
      # DEFERRED to Phase 16 — no Z3 seqFilter HOF; a quantified filter
      # predicate over a symbolic-length seq is a hang risk. Classify (sevError
      # → sxUnknown) and return a fresh seq so a downstream read does not crash.
      # RFC-0005 S7: `dcSubstituted` -- the predicate is never applied (its
      # raises are dropped) and the stand-in seq is unrelated to the input.
      # `closureDegrade` puts ⊤ on the consuming path, so a hit through
      # `__hofFilterUnsupported` is a candidate, never a clean `sxSat` (the
      # closure veto that also guarded it went in S9).
      closureDegrade(ceUnsupportedHof,
        "filter over a symbolic-length seq is not supported (no Z3 " &
             "seqFilter HOF; axiomatize-filter deferred to Phase 16)")
      # N36 (walker v101) reachability verification: `tSeq(e.hofRetElemTy)`'s
      # OWN `ty.seqElemTy` (= `e.hofRetElemTy`) is exactly the value
      # `allocateSym`'s `itSeq` arm guards with `isBackedSeqElemTy` before
      # ever calling `allocateSeqDataRaw` — same reasoning as
      # `__hofFoldPlaceholderDecline` above. CONFIRMED UNREACHABLE to
      # `allocateSeqDataRaw`'s raise; no guard added.
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(e.hofRetElemTy), "__hofFilterUnsupported", fresh)
    of "map":
      # Axiom path: `mapArray` (Z3_mk_map) — pointwise application of the
      # closure funcSym over the seq's data array. DECIDABLE array-map (no
      # universal quantifier; no G4-style hang). Result is a new seq with the
      # SAME (symbolic) length and a data array `r[i] = f(a[i])`.
      # CR-9 Stage 4: read closureBodies from live WalkerStatics when in a walk.
      let hofSiteKey = (cloSV.closureSite.siteHash, cloSV.closureSite.declOrder)
      let hofBodiesLive =
        if currentLowerSinks != nil:
          currentLowerSinks[].closureBodies
        else:
          currentClosureBodies
      let cb = hofBodiesLive[hofSiteKey]
      # Build a typed unary func_decl from the per-site funcSym. For the axiom
      # map the closure must be capture-free (unit-env) so its funcSym arity is
      # exactly 1 (the element); a captured closure has env-leaf domain args and
      # cannot be a unary array-map function — classify that case.
      var envLeaves = 0
      if cloSV.closureEnv != nil:
        for _ in flattenLeafAsts(cloSV.closureEnv[]): inc envLeaves
      if envLeaves != 0 or e.hofRetElemTy.kind != itInt or
         seqSV.seqElemTy.kind != itInt:
        # Capturing closure or non-int element: the unary-funcdecl array-map
        # shape does not apply. Classify rather than risk an unsound/hang path.
        # RFC-0005 S7: `dcSubstituted`, as the filter decline above.
        closureDegrade(ceUnsupportedHof,
          "map axiom path supports only a capture-free int->int closure " &
               "over a symbolic seq[int]; this shape is deferred")
        # N36 (walker v101) reachability verification: same argument as
        # `__hofFilterUnsupported` above. CONFIRMED UNREACHABLE to
        # `allocateSeqDataRaw`'s raise; no guard added.
        var fresh: seq[Z3Bool]
        return allocateSym(tSeq(e.hofRetElemTy), "__hofMapUnsupported", fresh)
      # mapArray over Z3Array[Z3Int, BV64] using the unary funcSym.
      #
      # RFC-0005 S7: this path recorded NOTHING, yet no axiom ever constrains
      # the funcSym it maps -- the body is never descended here (the comment
      # that stood on `discard cb` claimed "ground axioms still constrain f";
      # none are minted for this symbol), so `ys[i]` was an arbitrary value on
      # a CLEAN path: `xs.map(x * 2)` reached `ys[0] == 3` as a clean `sxSat`
      # (the closure veto never fired: nothing was in its sink). The mapped
      # array keeps the right shape (length, pointwise over one function), but
      # the function is unrelated to the closure and the body's raises are
      # dropped: `ceUnsupportedHof`, `dcSubstituted`.
      closureDegrade(ceUnsupportedHof,
        "map over a symbolic-length seq maps an unconstrained function symbol " &
             "(the closure body is not applied per element)")
      # RFC-0016 CRH-07: `wrapFuncDecl` takes its own reference. Built as an
      # object, `fd` took none, and its `=destroy` released the reference
      # `currentClosureSyms` holds for the run: once the mapped term died the
      # decl was freed while still cached, and the next path to reach this
      # lambda site mapped the freed decl.
      # `wrapFuncDecl` takes the wrapper's own reference. The decl is the
      # closure's run-lifetime decl (`buildClosure` holds one reference for
      # the run), and the wrapper dec_refs on destroy: built from a bare
      # object constructor it gave back a reference it never took, the
      # decl was freed while the closure still named it, and a later
      # translate into an own context read the freed node (RFC-0016 S8ck-r:
      # heap-use-after-free under the ASan libz3; Z3 4.13.4's
      # `ast_translation.cpp` UNREACHABLE on Windows). Masked until nim-z3
      # d86efda bound the Z3Int/Z3Bool hooks: terms never released kept the
      # decl alive through the map decl that names it.
      let fd = wrapFuncDecl[(Z3BitVec[64],), Z3BitVec[64]](
        ctx, cloSV.closureRawFD)
      let srcArr = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
        seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
      let mappedArr = mapArray[Z3Int, Z3BitVec[64], Z3BitVec[64]](fd, srcArr)
      discard cb   ## body stashed but not descended on this path (see above)
      SymVal(kind: svSeq, seqLen: seqSV.seqLen, # [placeholder-audited]
             seqDataRaw: toAnyAst(mappedArr), seqElemTy: seqCellTy(e.hofRetElemTy))   # RFC-0005 S8ba
    of "fold":
      # Axiom path: a raw `Z3_mk_app` of an uninterpreted fold result over the
      # seq's length + data + init (ground, C2b discipline — never a ∀ axiom).
      # The result is an uninterpreted value of the accumulator type; its
      # relation to the elements is left opaque (sound over-approximation —
      # degrades the verdict, never a false sat/unsat).
      # RFC-0005 S7: `dcSubstituted`, as the filter decline above.
      closureDegrade(ceUnsupportedHof,
        "fold over a symbolic-length seq is modeled as an opaque " &
             "ground result (precise symbolic fold deferred)")
      var fresh: seq[Z3Bool]
      return allocateSym(e.hofRetElemTy, "__hofFoldOpaque", fresh)
    else:
      raise newException(ValueError, "lowerHofCall: unknown HOF op " & e.hofOp)  # [raise-audited: category-c: parser-controlled op-string invariant (see above)]

# ---- Public driver ----------------------------------------------------------

proc drainRunTaint[T](dst: var T; drained: openArray[seq[SymexErrorInfo]];
                      extra: Taint = {}) =
  ## RFC-0005 S1 (§2.2 "the run coordinate is derived, not written"). The ONE
  ## writer of a run's drain-time coordinate, for both run entries:
  ## `runSymexImpl` (`WalkCtx.runTaint`, the verdict input) and
  ## `runConcolicFlipImpl` (`ConcolicFlipResult.soundness.runTaint`, RFC-0016
  ## W3-z R4). The union, over every DRAINED `sevError` entry, of
  ## `runTaint(classOf(kind))`; RFC-0005 S1c: nothing else. `extra` is a run
  ## coordinate the entry derived from its own drained record rather than an
  ## error (the flip's reached undefined operations, `scIncomplete`); a walk
  ## site never passes one.
  var t = extra
  for errs in drained:
    t = t + runTaintOf(errs)
  dst.runTaint = t

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings;
                  replay: CandidateReplay): RawResult

when defined(windows) and not defined(symexNoBigStack):
  # Chapulin 0.1.0 re-test triage (catalog #11, CRASH class), walker v64.
  # The walker's recursive lowering + Z3's recursive rewriters are
  # stack-hungry, and a Windows main thread defaults to a 1 MB (MSVC) /
  # 2 MB (MinGW) stack vs 8 MB on Linux — chapulin's depth-2/3 nested-if
  # string twins overflowed and died as a BARE SILENT EXIT (empirically
  # exit code 255 in the toolchain container; the classic 0xC00000FD
  # never surfaces through the CRT), while the identical shapes prove
  # sxUnsat under a 16 MB stack. Fix: execute the whole solve on a FIBER
  # with an explicitly reserved 16 MB stack.
  #
  # A fiber — NOT a thread — is deliberate: a fiber shares the creating
  # thread's identity and TLS, so every threadvar sink the walker relies
  # on (`loweringDegradeErrors`, `extractionErrors`, `currentWalkCtxPtr`,
  # …) stays coherent with zero re-plumbing, and ORC needs no
  # foreign-thread setup (ARC/ORC never scans stacks). Nim's own
  # `createThread` is no alternative: its stack size is the FIXED
  # `ThreadStackMask`-derived ~2 MB on desktop targets — the
  # `-d:nimThreadStackSize` define only applies to embedded targets.
  #
  # Exceptions cannot unwind across `SwitchToFiber`, so the trampoline
  # catches EVERYTHING (including Defect — nothing may escape on a dead
  # fiber) and re-raises on the main fiber, where `runSymex`'s existing
  # arms observe the original dynamic type unchanged.
  #
  # Escape hatch: compile with `-d:symexNoBigStack` to run the solve
  # directly on the calling thread's stack (pre-v64 behaviour).
  type FiberSolveCtx = object
    prog: SymexProgram
    target: SymexTarget
    settings: SymexSettings
    replay: CandidateReplay
    res: RawResult
    exn: ref Exception
    mainFiber: pointer

  const symexFiberStackReserve = 16 * 1024 * 1024
  const symexFiberStackCommit  = 256 * 1024

  proc convertThreadToFiber(param: pointer): pointer
    {.importc: "ConvertThreadToFiber", stdcall, dynlib: "kernel32".}
  proc convertFiberToThread(): int32
    {.importc: "ConvertFiberToThread", stdcall, dynlib: "kernel32".}
  proc createFiberEx(stackCommit, stackReserve: csize_t, flags: uint32,
                     startAddr, param: pointer): pointer
    {.importc: "CreateFiberEx", stdcall, dynlib: "kernel32".}
  proc deleteFiber(f: pointer)
    {.importc: "DeleteFiber", stdcall, dynlib: "kernel32".}
  proc switchToFiber(f: pointer)
    {.importc: "SwitchToFiber", stdcall, dynlib: "kernel32".}

  proc fiberTrampoline(param: pointer) {.stdcall.} =
    when defined(symexFiberTrace): stderr.writeLine "[fiber] trampoline enter"
    let ctx = cast[ptr FiberSolveCtx](param)
    try:
      ctx.res = runSymexImpl(ctx.prog, ctx.target, ctx.settings, ctx.replay)
      when defined(symexFiberTrace): stderr.writeLine "[fiber] impl returned"
    except Exception as e:
      ctx.exn = e
      when defined(symexFiberTrace): stderr.writeLine "[fiber] impl raised " & e.msg
    switchToFiber(ctx.mainFiber)
    # Never reached: the fiber is deleted by the main fiber after the switch.

  proc runSymexWithBigStack(prog: SymexProgram, target: SymexTarget,
                            settings: SymexSettings;
                            replay: CandidateReplay): RawResult =
    # ConvertThreadToFiber returns nil if the thread is ALREADY a fiber (or
    # on failure) — degrade gracefully to a direct call on the current stack
    # (the pre-v64 behaviour) rather than failing the run outright.
    let mainFiber = convertThreadToFiber(nil)
    when defined(symexFiberTrace):
      stderr.writeLine "[fiber] converted mainFiber nil=" & $(mainFiber == nil)
    if mainFiber == nil:
      return runSymexImpl(prog, target, settings, replay)
    var ctx = FiberSolveCtx(prog: prog, target: target, settings: settings,
                            replay: replay,
                            mainFiber: mainFiber)
    # FIBER_FLAG_FLOAT_SWITCH (1): float-state switching — a no-op on x64,
    # required for correctness on x86.
    let fib = createFiberEx(csize_t(symexFiberStackCommit),
                            csize_t(symexFiberStackReserve), 1,
                            cast[pointer](fiberTrampoline), addr ctx)
    when defined(symexFiberTrace):
      stderr.writeLine "[fiber] created nil=" & $(fib == nil)
    if fib == nil:
      discard convertFiberToThread()
      return runSymexImpl(prog, target, settings, replay)
    # Debug-build frame-chain hygiene: Nim's `--stackTrace` machinery links
    # stack-ALLOCATED `TFrame` records through a threadvar chain
    # (`framePtr`), and the trampoline never RETURNS through its Nim
    # epilogue (it switches back and is then deleted) — so its frame would
    # stay linked, pointing into the FREED fiber stack, and the next frame
    # operation on the main fiber would deref freed memory (observed as the
    # same silent 0xFF death this whole fix exists to cure). Save/restore
    # the frame state around the switch — the exact idiom Nim's own
    # coroutines used. No-op in release builds (procs still exist; the
    # chain is simply empty).
    when declared(getFrameState) and declared(setFrameState):
      let savedFrames = getFrameState()
    switchToFiber(fib)
    when declared(getFrameState) and declared(setFrameState):
      setFrameState(savedFrames)
    when defined(symexFiberTrace): stderr.writeLine "[fiber] back on main"
    deleteFiber(fib)
    discard convertFiberToThread()
    if ctx.exn != nil:
      raise ctx.exn
    ctx.res

var paramBoundaryAbort {.threadvar.}: bool
  ## RFC-0005 S8 (§2.5 point 2). Set by `raiseParamAllocIssue` immediately
  ## before it raises, so the `runSymex` boundary can tell a SIGNATURE-scoped
  ## abort (a top-level parameter type that cannot be allocated, before any
  ## walk state exists) from one raised mid-walk. Reset per run by
  ## `runSymexCaught`.

proc abortScope(): DeclineScope =
  ## RFC-0005 S8. The scope of a `runSymex` boundary-abort record: the
  ## param-entry boundary's is `dskSignature`; any other abort was raised by
  ## the walk at the site it was walking (`dskWalkSite`).
  if paramBoundaryAbort: signatureScope() else: walkSite()

proc runSymexCaught(prog: SymexProgram,
               target: SymexTarget,
               settings: SymexSettings;
               replay: CandidateReplay): RawResult =
  ## Phase 14 cycle C4. Wrap the implementation in a `try/except` that
  ## catches `Z3Error` (the abstract base class — all 12 typed
  ## subclasses derive from it). On catch, return `sxUnknown` with
  ## the error structured into `errors`. Walker-level
  ## `ValueError` and `AssertionDefect` are NOT caught — those
  ## are real bugs in the symex layer and must surface.
  paramBoundaryAbort = false   # RFC-0005 S8: see `abortScope`
  try:
    # v64 (catalog #11): on Windows the solve runs on a 16 MB fiber stack —
    # the fiber trampoline re-raises any escaped exception HERE on the main
    # fiber with its dynamic type intact, so the arms below are unaffected.
    when declared(runSymexWithBigStack):
      runSymexWithBigStack(prog, target, settings, replay)
    else:
      runSymexImpl(prog, target, settings, replay)
  except SymexUnsupportedOpError as e:
    # Phase 15 F6: an unmodeled float op (classify/copySign/nextafter/any
    # unmodeled math.<name>) -> sxUnknown + a classified error (Invariant 3:
    # never a silent UNSAT). The op name rides in `msg`. RFC-0005 S6b: the
    # kind is `feUnsupportedOpAborted` (§3.3's boundary-abort class,
    # dcNoAnswer), split off `feUnsupportedOp`'s in-walk substitutions.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: feUnsupportedOpAborted,
                                       severity: severity(feUnsupportedOpAborted), msg: e.msg,
                                       scope: abortScope())])
  # RFC-0016 W4 H1b (HRV-99): the boundary arms for the four string carriers
  # (`SymexUnsupportedStringOpError`, `SymexUnsupportedRegexError`,
  # `SymexZ3VersionMissingError`, `SymexZ3StringIncompleteError`) were
  # removed. Every raise of them is inside `lowerStrArm`'s call graph
  # (`runtime_strings.nim`, whose only exported entry is `lowerStrArm`), and
  # `lowerStrArm`'s one call site (`lower`) catches all four and degrades
  # in-band (`degradeStrArm`, N36), so none reaches this boundary.
  # `tests/tsymex_0016_w4h1b_dead_arms.nim` pins that structure.
  except SymexNotInHandlerError as e:
    # Phase 15 E8: `getCurrentException()` / `getCurrentExceptionMsg()` called
    # outside any `except` handler body (no in-flight exception) -> sxUnknown +
    # eeNotInHandler (Invariant 3 — classified, never a panic). The intrinsic
    # name rides in `msg`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: eeNotInHandler,
                                       severity: severity(eeNotInHandler), msg: e.msg,
                                       scope: abortScope())])
  except SymexOwnershipUnsupportedError as e:
    # Phase 15 R1a (ADR-0010, Breadth-LOW-L4): an `owned T` /
    # `Atomic[T]` formal was allocated -> sxUnknown + heUnsupportedOwnership
    # (Invariant 3 — classified, out of scope for the cluster).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: heUnsupportedOwnership,
                                       severity: severity(heUnsupportedOwnership), msg: e.msg,
                                       scope: abortScope())])
  except SymexNestedSeqUnsupportedError as e:
    # Phase 16 INV: `seq[seq[T]]` / complex-element seq — nested-seq encoding
    # not modeled -> sxUnknown + seNestedSeqUnsupported (Invariant 3 — classified,
    # never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seNestedSeqUnsupported,
                                       severity: severity(seNestedSeqUnsupported), msg: e.msg,
                                       scope: abortScope())])
  except SymexUnsupportedTableValTypeError as e:
    # Phase 16 INV: Table value type not modeled (only Table[string, int] supported)
    # -> sxUnknown + seUnsupportedTableValType (Invariant 3 — classified,
    # never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seUnsupportedTableValType,
                                       severity: severity(seUnsupportedTableValType), msg: e.msg,
                                       scope: abortScope())])
  except SymexUnsupportedSetCharInteropError as e:
    # Phase 16 INV: set[char] / HashSet element type not modeled (only HashSet[int]
    # BV[64] is supported) -> sxUnknown + seUnsupportedSetCharInterop (Invariant 3
    # — classified, never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seUnsupportedSetCharInterop,
                                       severity: severity(seUnsupportedSetCharInterop), msg: e.msg,
                                       scope: abortScope())])
  except SymexClassifiedDegradeError as e:
    # Phase 16 CR-1c (ADR-0020): the single generic classified-degrade carrier's
    # `kind` rides through verbatim -> sxUnknown (Invariant 3). This arm handles
    # any code that DELIBERATELY raises a pre-classified degrade (CR-2b reuses
    # this carrier with its own `kind`). CR-1c's own genuinely-unanticipated
    # native fault does NOT flow here — it is caught by the final `except
    # CatchableError` catch-all below and classified `weInternalWalkerFault`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: e.kind,
                                       severity: severity(e.kind), msg: e.msg,
                                       scope: abortScope())])
  except Z3Error as e:
    # Phase 15 Z3: map the Z3Error subclass name to the closed SymexErrorKind.
    # A caught Z3Error -> sxUnknown, so severity is sevError (invariant 7).
    let ek = case $e.name
             of "Z3MemoryError":   ekZ3MemoryError
             of "Z3InternalError": ekZ3InternalError
             of "Z3SolverError":   ekZ3SolverError
             else:                 ekZ3Error
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: ek, severity: severity(ek), msg: e.msg,
                                       scope: abortScope())])
  except CatchableError as e:
    # Phase 16 CR-1c (RFC-chapulin-hardening, Cluster 2 — Crash-totality,
    # ADR-0020): the genuine last-resort SAFETY NET for the §0 "walker never
    # crashes" invariant. This arm is REACHED ONLY by a `CatchableError` that
    # matched NONE of the specific arms above — i.e. NEITHER one of the 18 known
    # construct-gap `Symex*Error` carriers, NOR `SymexClassifiedDegradeError`,
    # NOR `Z3Error`. By construction that is a genuinely UNANTICIPATED native
    # exception (a stray `KeyError`/`ValueError`/etc.) that escaped the walker
    # from ANY dispatch depth — a walker bug, not an unmodeled SUT construct.
    #
    # It is classified with the DISTINCT `weInternalWalkerFault` kind, NEVER
    # conflated with the ordinary `se*`/`fe*` construct-gap kinds, so CI/
    # telemetry can track "how often we hit the safety net" as a live walker-bug
    # backlog (§0: totality is an audit, not a silently-closed invariant).
    #
    # WHY here (the outermost, pre-existing `try`) and NOT a per-`walk`-frame
    # catch: a `try/except` wrapped around the recursive per-statement dispatch
    # catches-and-re-raises the ANTICIPATED carriers at EVERY frame; on Nim's C
    # backend (ORC + goto exceptions) that repeated catch/re-raise, interacting
    # with the ORC destructor unwind of `walkBlock`'s live `seq[Path]` result
    # (whose `Path` fields hold refcounted Z3 ASTs), corrupted memory into a nil
    # read — a C-backend-only SIGSEGV, invisible on C++ (the same backend-
    # divergence class as the b7258f7 `try/finally` precedent). Placing the ONE
    # catch on the ALREADY-EXISTING `runSymex` try lets an unanticipated native
    # unwind straight through the walk exactly as it did pre-CR-1c (which was
    # sound), while the anticipated carriers are consumed by their specific arms
    # ABOVE and never reach this catch-all. `try/except`, NEVER `try/finally`
    # (b7258f7 hard rule).
    #
    # `Defect`-class raises (the ~63 `doAssert`s and any stray `IndexDefect`/
    # `RangeDefect`/`AssertionDefect`) are NOT `CatchableError` and are NOT
    # caught here — they keep crashing loudly per the §0 crash-doctrine.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: weInternalWalkerFault,
                                       severity: severity(weInternalWalkerFault),
                                       msg: $e.name & ": " & e.msg,
                                       scope: abortScope())])
  except Defect as e:
    # Round-3 crash-doctrine decision (Corey, 2026-08-06 — supersedes the
    # CR-1c "Defects keep crashing loudly" carve-out for CONSUMER-facing
    # totality): with 0.1.0 shipped and chapulin consuming, the ~63
    # doAssert-class internal-invariant failures no longer take down the
    # consumer's process. This ONE outermost arm classifies them
    # `weInternalWalkerFault` — the same telemetry contract as the
    # CatchableError net above: "the walker itself hit a bug here", a live
    # walker-bug backlog kind never conflated with construct gaps. The
    # C-backend corruption hazard that forbade per-frame catching (ADR-0020)
    # does not apply at this locus: the unwind passes through the walk
    # exactly as it did pre-net; only the final destination changes.
    # Caveats (round-3 ledger): under `--panics:on` Defects are not
    # catchable (this arm never fires); stack overflow and libz3 aborts are
    # not exceptions — the v64 fiber-stack work addresses those. On Windows
    # the fiber trampoline ferries Defects across the fiber switch with
    # their dynamic type intact, so they arrive here unchanged.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: weInternalWalkerFault,
                                       severity: severity(weInternalWalkerFault),
                                       msg: $e.name & ": " & e.msg,
                                       scope: abortScope())])


# ---- RFC-0016 K5a: the host half of the build profile ------------------------

type HostGate = object
  read: bool
  host: bprof.HostSemantics
  refusal: Option[bprof.BuildRefusal]

var hostGate: HostGate
  ## The process's host, read once at the first run and admitted once. A plain
  ## global, as `libOverride` (pcre_engine): the walker may run on another thread.
var hostSeam: Option[bprof.HostSemantics]
  ## A test's stand-in for the host (`overrideHostForTest`): not cached.

proc overrideHostForTest*(h: bprof.HostSemantics) =
  ## RFC-0016 K5a. Makes every run read `h` as the host instead of the loaded
  ## libz3 and libpcre (tests); `clearHostOverride` restores them. The seam an
  ## unverified Z3 is tested through, since the suite cannot install another.
  {.cast(gcsafe).}:
    hostSeam = some(h)

proc clearHostOverride*() =
  {.cast(gcsafe).}:
    hostSeam = none(bprof.HostSemantics)

proc currentHost*(): bprof.HostSemantics =
  ## RFC-0016 K5a. The host this run reads: the seam's, else the process's,
  ## read the first time it is asked.
  {.cast(gcsafe).}:
    if hostSeam.isSome: return hostSeam.get
    if not hostGate.read:
      hostGate.host = bprof.readHost(z3FullVersion())
      hostGate.refusal = bprof.admitHost(hostGate.host)
      hostGate.read = true
    hostGate.host

proc hostAdmission*(): Option[bprof.BuildRefusal] =
  ## RFC-0016 K5a (section 8.3, Refusals). `admitHost` of `currentHost()`:
  ## `none` when the host is a verified one. Shared by every run entry
  ## (`runSymex`, the concolic collect), read once.
  {.cast(gcsafe).}:
    if hostSeam.isSome: return bprof.admitHost(hostSeam.get)
    discard currentHost()
    hostGate.refusal

proc stampBuild*(s: var Soundness) =
  ## RFC-0016 K5a. Records on `s` the build this run is: `buildSegment` of the
  ## build and the host, and the row `rowOf` projects them onto.
  let h = currentHost()
  s.buildSegment = bprof.buildSegment(buildSemantics, h)
  let row = bprof.rowOf(buildSemantics, h, bprof.buildProvenance)
  s.buildRow = (if row.isSome: $row.get else: "")

proc hostRefusedError(r: bprof.BuildRefusal): SymexErrorInfo =
  SymexErrorInfo(kind: feHostUnadmitted, severity: severity(feHostUnadmitted),
                 msg: r.reason & " [field: " & $r.field & "] (feHostUnadmitted)",
                 scope: signatureScope())

proc hostRefusedResult(r: bprof.BuildRefusal): RawResult =
  ## The verdict of a run the host half refused: `sxUnknown`, nothing decided.
  result = RawResult(status: sxUnknown, errors: @[hostRefusedError(r)])
  result.soundness.runTaint = runTaintOf(result.errors)
  result.soundness.replay = rsNotNeeded
  stampBuild(result.soundness)

proc dropWitnessPins(r: var RawResult) =
  ## RFC-0016 K10b. The pins are Z3 terms, which keep the run's context alive
  ## (17 MB before a term is made) for as long as any value holding one lives.
  ## Only the run's own tail check reads them, so none leaves the run in a
  ## result: a result that outlives it (the caller's, the cache's) would pin
  ## the context (`tsymex_0016_s8cj_runctx`).
  case r.status
  of sxSat: r.witness.pins = @[]
  of sxRaised: r.raisedWitness.pins = @[]
  else: discard
  for c in r.candidates.mitems: c.input.pins = @[]
  for d in r.diagnostics.mitems: d.raisedWitness.pins = @[]
  for u in r.undefined.mitems: u.witness.pins = @[]

proc runSymex*(prog: SymexProgram,
               target: SymexTarget,
               settings: SymexSettings = defaultSymexSettings();
               replay: CandidateReplay = nil): RawResult =
  ## Phase 14 cycle C4 boundary (`runSymexCaught`), plus RFC-0005 S8
  ## (§13.3, i3): the program's annotation violations ride out on EVERY
  ## verdict branch, including a boundary abort. Verdict-neutral: nothing
  ## reads them to decide `status`.
  ##
  ## RFC-0016 W4 perf: `replay` is the settle's replay of one candidate
  ## (`CandidateReplay`), which only `emitRunSymexReplayed` passes. Nil, no
  ## candidate is replayed in the run, so none is confirmed and no
  ## candidate's tail is walked: each label claim the whole-run gate holds
  ## carries `ubTailUnverified`.
  # RFC-0016 K5a: the host half of the build profile, read once. A host no
  # row covers decides nothing: `sxUnknown` with `feHostUnadmitted`, no raise.
  let hostRefusal = hostAdmission()
  if hostRefusal.isSome:
    result = hostRefusedResult(hostRefusal.get)
    result.annotationViolations = prog.annotationViolations
    result.bounds = settings.budget
    return
  # RFC-0016 S8cj: the run's context must not outlive the run.
  # `resetSymexRunState` makes it the thread's current context (nim-z3's
  # threadvar holds a reference), and nothing put the previous one back, so
  # it lived until the thread's next run, or for ever on a thread that
  # exits. Z3's process-wide allocation count is an input to its default
  # solver's strategy (the `memory` probe: the QF_NIA portfolio skips its
  # bit-blasting stage above 100 MB), so every leaked run moved every later
  # query's spend on every thread (`tsymex_0016_s8cj_runctx`,
  # `docs/rfc/0016-research/S8cj.md`). Restored here, after `runSymexCaught`
  # has returned on every path it catches; `runSymexImpl` cannot do it in a
  # `finally` (CR-13's goto-exception caveat).
  let prevCtx = currentContext()
  # RFC-0016 INT-57: with no run clock the run's solves share one stall
  # deadline (`stallBackstopMs`), and the one it replaces is back after.
  let prevStall = beginStallDeadline(settings.budget.queryTimeoutMs)
  result = runSymexCaught(prog, target, settings, replay)
  endStallDeadline(prevStall)
  dropWitnessPins(result)
  # The caller path-condition stacks hold Z3 terms and are read only by the
  # walk that pushed them. The tail check's walk leaves its last entries in
  # them, and left in the threadvars they kept the run's whole context alive
  # past the run (`tsymex_0016_s8cj_runctx`).
  currentCallerPc = @[]
  closureBodyCallerPc = @[]
  satModels = @[]
  setCurrentContext(prevCtx)
  # RFC-0005 S8m: a run whose Z3 API error never reached the `Z3Error` arm
  # (the C backend loses a raise unwinding through the walk) has no verdict.
  if z3ApiErrorCount > 0:
    var recorded = false
    for e in result.errors:
      if e.kind in {ekZ3Error, ekZ3MemoryError, ekZ3InternalError,
                    ekZ3SolverError}:
        recorded = true
    if not recorded or result.status != sxUnknown:
      result = RawResult(status: sxUnknown, errors: result.errors &
        @[SymexErrorInfo(kind: ekZ3Error, severity: severity(ekZ3Error),
          msg: "Z3 API error (" & z3ApiFirstError & ", " & $z3ApiErrorCount &
               " in the run) was raised inside the walk and never reached " &
               "the run boundary -- no verdict stands behind it " &
               "(RFC-0005 S8m; ekZ3Error)",
          scope: abortScope())])
  result.annotationViolations = prog.annotationViolations
  # RFC-0005 S11 (§8.1). The public run coordinate, DERIVED (§2.2) from the
  # final error list -- after every override above, so a boundary abort and
  # the S8m Z3-API override carry their own error's coordinate too, and an
  # `sxUnknown` never reports `{}` (Invariant-7 extension: every
  # `sxUnknown` carries a `sevError`, and every `sevError` taints the run).
  # It equals the `w.runTaint` the verdict read, plus a winner's witness
  # extraction errors (the one sink `runSymexImpl` drains after deciding).
  result.soundness.runTaint = runTaintOf(result.errors)
  # RFC-0005 0.9.1 (review R1-16). The run settles the verdicts that need no
  # replay: an `sxUnsat` / `sxUnknown`, and a winner on a path no degrade made
  # spurious (the replay pass, which runs after this, re-settles a lossy
  # one). Review R2 (DD5): only those. A claim on an `scSpurious` path is not
  # a winner rules 1-2 ship; should one reach here it stays `rsUnsettled`,
  # never trusted, rather than being promoted to a clean claim.
  if result.soundness.replay == rsUnsettled and
     (result.status in {sxUnsat, sxUnknown} or
      scSpurious notin result.soundness.pathTaint):
    result.soundness.replay = rsNotNeeded
  # RFC-0005 S8bu/S8ca (review R1-07). What of the verdict is this run's, on
  # the result: a save reads it there, never the thread's flags, which the
  # next run resets.
  if queryTimedOutFlag: result.soundness.runDependence.incl rdQueryTimeout
  if nativeStackCutFlag: result.soundness.runDependence.incl rdNativeStack
  # RFC-0005 S11 (§8.2). The bound echo.
  result.bounds = settings.budget
  stampBuild(result.soundness)   # RFC-0016 K5a: the build this verdict is of

proc raiseParamAllocIssue(issue: FieldAllocIssue) =
  ## N40 (round-6 fix round 6, walker v104). The pre-walk PARAMETER-entry
  ## boundary's half of the totality design (see `allocateSym`'s own
  ## doc-comment addendum and `allocDegrade`'s doc comment, above, for the
  ## full writeup). `allocateSym` no longer raises for classifiable input —
  ## it degrades in-band and keeps going. That is the RIGHT behavior for a
  ## nested walk-time allocation (a variant arm field, a heap cell, a
  ## closure return type, ...), where "keep walking, mark the run
  ## degraded" is strictly more informative than aborting the whole run.
  ## It is the WRONG behavior for a TOP-LEVEL SUT parameter: pre-N40, an
  ## unallocatable param type raised IMMEDIATELY, before any walk state
  ## existed, and every existing pin on a param-level classified decline
  ## (CR-2b/CR-2c/N39's own param-boundary carve-out, etc.) expects that
  ## same whole-run, walk-never-started semantics. `runSymexImpl`'s
  ## per-param loop (below) calls `unallocatableFieldIssue` on EVERY
  ## top-level param type before allocating anything and routes a hit
  ## through this proc, which raises the EXACT SAME classified carrier
  ## TYPE, `kind`, and message text `allocateSym` itself used to raise for
  ## the identical shape (byte-for-byte — `unallocatableFieldIssue`'s
  ## messages were audited/fixed to match this slice, types.nim) — so
  ## every pre-N40 pin on a param-level decline stays green unchanged.
  ##
  ## `SymexUnsupportedTableValTypeError`/`SymexUnsupportedSetCharInteropError`/
  ## `SymexOwnershipUnsupportedError` are dedicated carriers whose `kind` is
  ## implied by the exception TYPE itself (see their `except` arms at the
  ## `runSymexImpl` boundary); every other kind (including this slice's new
  ## `seUnsupportedTableKeyType`) reuses the generic `SymexClassifiedDegradeError`
  ## carrier (CR-1c's "no 20th near-identical dedicated exception type"
  ## discipline), which carries `kind` explicitly.
  paramBoundaryAbort = true   # RFC-0005 S8: the abort is signature-scoped
  case issue.kind
  of heUnsupportedOwnership:
    raise (ref SymexOwnershipUnsupportedError)(msg: issue.msg)  # [raise-audited: param-boundary -- allocateSym is total; the param boundary raises by design, before any walk state exists (N40)]
  of seUnsupportedTableValType:
    raise (ref SymexUnsupportedTableValTypeError)(msg: issue.msg)  # [raise-audited: param-boundary -- allocateSym is total; the param boundary raises by design, before any walk state exists (N40)]
  of seUnsupportedSetCharInterop:
    raise (ref SymexUnsupportedSetCharInteropError)(msg: issue.msg)  # [raise-audited: param-boundary -- allocateSym is total; the param boundary raises by design, before any walk state exists (N40)]
  else:
    # feUnsupportedParamType, feUnsupportedWitnessType, seUnsupportedTableKeyType
    # (and any FUTURE `unallocatableFieldIssue` kind that doesn't warrant its
    # own dedicated carrier) ride the generic CR-1c carrier.
    raise (ref SymexClassifiedDegradeError)(kind: issue.kind, msg: issue.msg)  # [raise-audited: param-boundary -- allocateSym is total; the param boundary raises by design, before any walk state exists (N40)]

proc resetSymexRunState(settings: SymexSettings): Z3Context =
  ## RFC-fuzzer-nextgen G1b: factored out of `runSymexImpl`'s preamble
  ## (pure extraction — same statements, same order, no behavior change)
  ## so the new concolic-collection entry (`runConcolicCollectImpl`) can
  ## share the EXACT same per-run resets + fresh Z3 context construction.
  ## Every one of these is a module-level threadvar the lowering layer
  ## (`lower`/`lowerBool`/…) reads and writes regardless of which
  ## `WalkMode` is driving the walk — skipping any of them for the
  ## concolic entry would risk leaking a PRIOR run's stale Z3 asts (bound
  ## to an already-freed context) into a fresh walk.
  #
  # CR-13: clear any stale walk-context pointer left by a previous call that
  # raised. A raise inside walk() propagates through runSymexImpl to the
  # runSymex except handlers WITHOUT clearing currentWalkCtxPtr (the Nim c
  # backend goto-exception model does not re-raise after a finally block when
  # nested try blocks are present, so an inner try/finally cannot be used).
  # Resetting it HERE — before any sync*/allocRef* call that checks
  # `currentWalkCtxPtr != nil` — ensures the stale pointer is never dereffed.
  armThreadStateRelease()  ## RFC-0016 S8ck-r: a Nim thread's state is released when it exits
  resetWalkState(settings.budget.maxSplitParts)  ## RFC-0016 D3c-2: walk_state's threadvars, the sinks pointer included
  let ctx = newContext()
  setCurrentContext(ctx)
  resetWalkSolveState(settings)   ## RFC-0016 INT-34 B5: walk_solve's run state (query and work budget, solve sinks, the winner's heaps)
  # RFC-0005 S8m: count every Z3 API error of the run (`nelliZ3ErrorHandler`).
  Z3_set_error_handler(ctx.raw, nelliZ3ErrorHandler)
  z3ApiErrorCount = 0
  z3ApiFirstError = ""
  resetLowerExprState()   ## RFC-0016 INT-34 B4: lower_expr's run state (arith frames, lowering sinks, global reads)
  resetWalkCtxState()   ## RFC-0016 INT-34 B6a: walk_ctx's run state (the raw status, the heap and closure sinks, the caller and closure-exit heaps)
  resetRuntimeHeapState()   ## RFC-0016 INT-34 B7: runtime_heap's run state (the freshness-cap and ptr-family hint sinks)
  resetLoweringSink()                    ## RFC-0016 D3c-1: symval's threadvars (lowering-degrade sink, pending taint and ub)
  resetWalkExprState()   ## RFC-0016 INT-34 B6b: walk_expr's run state (the caller taint, undefined and pc a closure body is walked under, the drained exit facts)
  resetStringSupport()                   ## RFC-0016 D3c-7: the index-split registry
  resetStringLowering()                  ## RFC-0016 D3c-7: strCharsCounter
  currentClosureCallAxiomStrs = @[]      ## Phase 15 C2b: reset axiom-string hook
  resetHeapModel()                      ## RFC-0016 D3c-6: heap_model's threadvars (the heap-key shapes, container registry, distinct-sort sinks, int bridge)
  ctx

iterator dedupedByMsg(src: seq[SymexErrorInfo]): SymexErrorInfo =
  ## Shared insertion rule behind `drainDedupedByMsg`/`dedupedMsgCount` below:
  ## walks `src` once, yielding each entry the first time its `.msg` AND
  ## `.scope` are seen together, deduplicated WITHIN `src` alone, in its OWN
  ## `HashSet` — never merged with a destination's prior contents or any
  ## sibling sink's own dedup set. Per-sink dedup is deliberate, not an
  ## oversight: a message appearing in two DIFFERENT sinks is vanishingly
  ## unlikely (each sink is written by its own disjoint set of call sites). A
  ## caller that concatenates two sub-sources into one `seq` before calling
  ## (e.g. `w.someField & someThreadvar`) gets THOSE two sub-sources deduped
  ## together, as one sink.
  ##
  ## RFC-0005 S9: the key includes the anchor. Two declines of one kind at
  ## two sites record the same message (the walker's reach record carries the
  ## marker's `reason`, which names the construct, not the site), so a
  ## message-only key kept ONE walk record for both -- and the reach join
  ## (`reachJoinParseErrors`) would have read the second site as never
  ## reached. A `dskWalkSite` record's anchor is the same for every site, so
  ## those still dedup by message alone.
  var seen: HashSet[string]
  for e in src:
    let key = e.msg & "\x00" & $e.scope
    if key notin seen:
      seen.incl key
      yield e

proc rfc0005S8mUncheckedZ3Error*(): tuple[counted: int, code: string] =
  ## RFC-0005 S8m test hook (H1 pattern: `WalkCtx`/contexts are private to
  ## the runtime unit). Makes a fresh symex run context exactly as a run does
  ## (`resetSymexRunState`) and issues an ill-sorted `Z3_mk_eq` WITHOUT
  ## `checkErr` -- the shape of a raise the C backend loses. Reports what
  ## `nelliZ3ErrorHandler` counted, which is what `runSymex` reads.
  let ctx = resetSymexRunState(defaultSymexSettings())
  discard Z3_mk_eq(ctx.raw, mkBool(true).raw, mkBitVec[64](1'i64).raw)  # [s8m-unchecked-probe]
  result = (z3ApiErrorCount, z3ApiFirstError)
  z3ApiErrorCount = 0
  z3ApiFirstError = ""

proc drainDedupedByMsg(dst: var seq[SymexErrorInfo], src: seq[SymexErrorInfo]) =
  ## Round 10 design T4: the one dedup-by-message idiom every hint/error/
  ## warning drain in `runSymexImpl`/`runConcolicCollectImpl` below hand-rolled
  ## separately. Appends each entry of `src` to `dst`, deduplicated per
  ## `dedupedByMsg` above — see its doc for the per-sink-not-cross-sink
  ## dedup contract.
  for e in dedupedByMsg(src):
    dst.add e

proc dedupedMsgCount(src: seq[SymexErrorInfo]): int =
  ## Same per-sink dedup rule as `drainDedupedByMsg` (shared via
  ## `dedupedByMsg` above), for the two `runConcolicCollectImpl` call sites
  ## that only need the count of distinct messages, never the deduped
  ## entries themselves — counts rather than materializing a throwaway seq.
  for e in dedupedByMsg(src):
    inc result

proc reachJoinParseErrors(parseErrors, walkRecords: seq[SymexErrorInfo]):
    seq[SymexErrorInfo] =
  ## RFC-0005 S9 (§2.5 point 1: "Reach-taint then decides the verdict ... and
  ## the `parseErrors` entry becomes purely diagnostic"). A parse-time decline
  ## anchored at a marker (`dskSiteAnchored`) or an unregistered callee key
  ## (`dskCalleeKey`) was reached iff the walk recorded a decline under the
  ## SAME anchor -- the walker records one at every path that reaches the
  ## site, and taints that path. An unreached one is returned as a `sevHint`
  ## (the diagnostic kept, `taintsRun` false: it contributes nothing to the
  ## run coordinate, as it contributed nothing to any path). A reached one,
  ## and every other scope (signature, unplaced), is returned unchanged.
  var reached: seq[DeclineScope]
  for e in walkRecords:
    if taintsRun(e) and e.scope.kind in {dskSiteAnchored, dskCalleeKey} and
       e.scope notin reached:
      reached.add e.scope
  for e in parseErrors:
    var r = e
    if taintsRun(e) and e.scope.kind in {dskSiteAnchored, dskCalleeKey} and
       e.scope notin reached:
      r.severity = demotedSeverity
      r.msg = e.msg & " [never reached on a walked path: diagnostic only " &
              "(RFC-0005 S9)]"
    result.add r

template drainSinkUnion(dst: var seq[SymexErrorInfo]; w: WalkCtx;
                         walkField, threadVarSrc: untyped) =
  ## CR-9 Stage 5 wiring, shared by every sink below that has BOTH a
  ## `WalkCtx` field and a threadvar fallback: `w.walkField` is the LIVE
  ## store, populated during the walk itself; the threadvar is the fallback
  ## for any pre-walk/no-walk/probe caller that writes the sink outside a
  ## walk. Unioning the two and draining (deduped by `.msg`, per
  ## `drainDedupedByMsg` above) covers both the walk and any non-walk caller
  ## uniformly. Each call site below carries a one-line pointer back to this
  ## contract plus whatever is specific to ITS sink (Phase/ADR tag, what it
  ## drains, and why the severity does or doesn't affect the verdict).
  ##
  ## `w` is an explicit parameter (not a free identifier resolved from the
  ## call site's enclosing scope) so the dependency is stated in the
  ## signature rather than implied: every call site must have its own
  ## `WalkCtx` in scope, named whatever it likes, and pass it in. Typed
  ## `WalkCtx` (by value, read-only — this template only ever reads
  ## `w.walkField`) rather than `var WalkCtx` or `untyped`: templates splice
  ## the argument AST into the body instead of copying through a call frame,
  ## so a plain symbol argument (every call site below passes bare `w`)
  ## costs nothing extra over `untyped` here, and the typed parameter still
  ## buys real signature documentation plus type-checking at the call site.
  drainDedupedByMsg(dst, w.walkField & threadVarSrc)

proc verifyTailDefinedKinds(prog: SymexProgram; settings: SymexSettings;
                            ctx: Z3Context; env: Env; initialPC: seq[Z3Bool];
                            pins: seq[Z3Bool]; via: var set[UbKind];
                            viaSites: var seq[string]): set[UbKind] =
  ## RFC-0016 K10b (section 9.1 item 3). The whole-run gate's second walk:
  ## from the entry, in concrete-follow mode under the winner's model `pins`
  ## (`RawWitness.pins`), past the label to a routine exit. The target is a
  ## label no program carries, so `shouldStop` never ends it on a hit; what
  ## ends it is the paths' own exits, a halt, or the run's work budget.
  ## Returns the kinds the run is not shown defined in:
  ##   * each `UbKind` a halt recorded (`haltUndefined` on a side the pins do
  ##     not rule out; `opaqueRaiseForks` at an opaque call whose body may be
  ##     undefined);
  ##   * `ubTailUnverified` for anything else that taints the run: a decline
  ##     reached, an exhausted budget (`beBudgetExhausted` and its siblings),
  ##     the walk work cap (`walkWorkExhausted`), a parse-time decline a path
  ##     reached. Fail closed: a tail the walk could not model is not defined.
  ## Empty: every undefined side was `concretelyInfeasible` under the pins and
  ## nothing declined, so the witness's whole run is defined.
  ##
  ## RFC-0016 W3-z R2/R6: the walk over-approximates the run (`tailGate`),
  ## for the winner and a replay candidate alike. A path may carry a fresh
  ## symbol the pins do not fix (a global havoc, an opaque call's result), so
  ## the walk forks the branches the pins leave open, and a `dcFreshSymbol`
  ## record (the fresh symbol itself) is not a reason the tail is unverified;
  ## every other record still is. RFC-0016 0.10.0 review H2: the undefined
  ## behaviour such a record's token carries (a `{.noinit.}` read's
  ## `ubIndeterminateRead`) is a kind of the result (`WalkCtx.tailUb`).
  ##
  ## RFC-0016 W3-z R9: the walk has its own budget, `tailWalkCappedChecks`
  ## times the rlimit of one of its scratch checks (`concreteBranchRLimit`).
  ## Each check runs under at most what is left of it, and once it is spent
  ## the walk stops (`tailWorkExhausted`, read by `shouldStop`) and the tail
  ## fails closed (`ubTailUnverified`). The forks of open branches multiplied
  ## capped checks, bounded before only by `walkRLimit`.
  ##
  ## RFC-0016 W3-z int4r: that budget is the run's, shared by every tail walk
  ## the run makes (`tailUnitsRun`). Each walk may spend what the walks
  ## before it left, and a walk that starts with nothing left fails closed at
  ## once. A per-walk budget let a run with many candidates spend one budget
  ## per candidate: `tsymex_r6_n36_raise_degrade` walked eleven candidate
  ## tails of a pair loop past 900 s, where the explore walk took seconds.
  ## RFC-0016 W4 perf: a run now walks at most one tail, the winner's or the
  ## replay-confirmed candidate's (R2), so that walk has the whole budget.
  let lowerBase = loweringDegradeErrors.len
  if walkWorkExhausted:
    return {UbKind(ubTailUnverified)}   # no budget left to look with
  let unitsBefore = walkUnitsSpent()
  let tailChecks = settings.budget.tailWalkCappedChecks
  let oneCheck = concreteBranchRLimit(settings)
  if tailChecks > 0 and oneCheck <= uint(high(int) div 2 div tailChecks):
    let left = tailChecks * int(oneCheck) - tailUnitsRun
    if left <= 0:
      return {UbKind(ubTailUnverified)}   # the run's tail budget is spent
    tailUnitsCeil = unitsBefore + left
  else:
    tailUnitsCeil = 0
  tailWorkExhausted = false
  defer:
    tailUnitsRun += max(walkUnitsSpent() - unitsBefore, 0)
    tailUnitsCeil = 0
    tailWorkExhausted = false
    # The K10b perf reading: the tail walk's own units, as a line of the
    # `NELLI_WALK_UNITS_LOG` file beside the explore walk's.
    appendWalkUnits(WalkUnitsLine(
      units: walkUnitsSpent() - unitsBefore, target: "k10b-tail",
      status: $result))
  let exitClock = newExitClock()
  var w = WalkCtx(
    extHardMark: -1,
    exitClock: exitClock, topExits: exitClock.newExits(CallExits),
    frame: initCallFrameCtx(exitClock),
    z3: ctx,
    target: SymexTarget(kind: stkLabel, label: "__nelli_k10b_tail_unreached__"),
    params: prog.params, mode: wmFollowConcrete, tailGate: true,
    found: @[], settings: settings, procs: prog.procs,
    callStack: @[], callStats: initTable[string, CallStat](),
    callCache: initTable[string, seq[CallCacheEntry]](),
    activeCalls: initHashSet[string](), initialEnv: env,
    concreteEq: pins,
    statics: WalkerStatics(exnTable: exnTypeTable,
                           userExnHierarchy: prog.userExnHierarchy,
                           sutRetTy: prog.retTy,
                           globals: globalsTable(prog.globals)),
  )
  for tid, srt in currentRefSorts: w.sinks.refSorts[tid] = srt
  for tid, nc in currentNilConsts: w.sinks.nilConsts[tid] = nc
  for dn, de in currentDistinctSorts:
    if not w.sinks.distinctSorts.hasKey(dn):
      w.sinks.distinctSorts[dn] = de
      w.sinks.distinctSortNames.add dn
  for ck, fd in currentClosureSyms:
    if not w.sinks.closureSyms.hasKey(ck): w.sinks.closureSyms[ck] = fd
  for sk, cb in currentClosureBodies:
    if not w.sinks.closureBodies.hasKey(sk): w.sinks.closureBodies[sk] = cb
  currentLowerSinks = addr w.sinks
  currentWalkCtxPtr = addr w
  let initial = initialWalkPath(initialPC, env)
  discard walk(prog.body, @[initial], w)
  currentLowerSinks = nil
  currentWalkCtxPtr = nil
  stampLoweringPendingLeak(w)
  if walkWorkExhausted or tailWorkExhausted:   # RFC-0016 W3-z R9: or its own
    result.incl UbKind(ubTailUnverified)
  # RFC-0016 0.10.0 review H2: the kinds the walk's degrade tokens put on a
  # path the pins allow. A `dcFreshSymbol` record below carries none itself.
  result.incl w.tailUb
  var errs = w.walkDegradeErrors & w.heapDepthErrors & w.newFieldZeroErrors &
             w.sinks.closureCallErrors
  if loweringDegradeErrors.len > lowerBase:
    errs.add loweringDegradeErrors[lowerBase .. ^1]
  errs.add reachJoinParseErrors(prog.parseErrors, errs)
  for e in errs:
    if ord(e.kind) >= ord(low(UbKind)) and ord(e.kind) <= ord(high(UbKind)):
      result.incl UbKind(e.kind)
    elif taintsRun(e) and classOf(e.kind) != dcFreshSymbol:
      result.incl UbKind(ubTailUnverified)
  # The second walk is a check, not part of the verdict: what it recorded in
  # the lowering sink was read above, and must not reach the explore walk's
  # errors (`tsymex_r6_n13_reassign_seqarm`).
  if loweringDegradeErrors.len > lowerBase:
    loweringDegradeErrors.setLen(lowerBase)
  via = w.tailVia
  viaSites = w.procValueSites

proc verifyTailDefined(prog: SymexProgram; settings: SymexSettings;
                       ctx: Z3Context; env: Env; initialPC: seq[Z3Bool];
                       pins: seq[Z3Bool]):
                       tuple[all, viaOnly: set[UbKind]; sites: seq[string]] =
  ## RFC-0016 W3-z R7. `verifyTailDefinedKinds`, with the kinds an opaque
  ## call added only through the proc-valued variables it calls through
  ## (`WalkCtx.tailVia`) reported apart: `all` is every kind the run is not
  ## shown defined in, `viaOnly` the part of it no other record put there.
  var via: set[UbKind]
  var sites: seq[string]
  let fixed = verifyTailDefinedKinds(prog, settings, ctx, env, initialPC,
                                     pins, via, sites)
  (all: fixed + via, viaOnly: via - fixed, sites: sites)

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings;
                  replay: CandidateReplay): RawResult =
  let ctx = resetSymexRunState(settings)
  setUnionImageProgram(prog.fieldImage)   ## RFC-0016 int6-f, before any allocation
  # RFC-0005 S8as/S8ax: the signed `int` heaps are Int-sorted whenever the
  # run's ints are not exact (`intHeapIsInt`). S8as also required every
  # plain `int` parameter to be an Int: a bit-vector stored into an Int heap
  # and compared with itself after a read is `int2bv(bv2int(v)) != v`, the
  # F5 shape Z3 does not finish. S8ax meets that bit-vector unconverted
  # (`intOfBV`, `storedAt`) and bounds every cell an Int heap is read at by
  # its type (`intCellRangeFacts`).
  # RFC-0005 batch 4: decided here, before any parameter is allocated, not
  # once they are bound. A parameter's leaf-split arrays -- a seq of tuples
  # (S8bc), a table's container values (S8at) -- are built at allocation
  # from `heapLeafTerm` / `heapLeafRaw`, which consult this flag, while
  # every read lifts its select by the flag as it stands then
  # (`liftHeapValue`). Set after binding, the arrays were bit-vector sorted
  # and their reads Int: an ill-sorted term at the first comparison.
  intHeapIsInt = settings.integerSemantics != isExact
  var env: Env
  var initialPC: seq[Z3Bool]
  var log: AbstractionLog
  # ADR-0001 ban scan: variables whose def-use chain contains a
  # bit-twiddling op can't be soundly promoted to Z3Int.
  var intParamNames: HashSet[string]
  for p in prog.params:
    if p.ty.kind == itInt:
      intParamNames.incl p.name
  # ISSUE #161 slice 3. Under UNCHECKED arithmetic (`acOverflow` absent from
  # the build's checks — the `-d:danger` / `--overflowChecks:off` build), signed
  # overflow is not a defect, it WRAPS. Suppressing the raise fork is only
  # half of modelling that: an unbounded `Z3Int` still does not wrap, so a
  # promoted param would report `a * b` as 1.6e19 for a product the program
  # actually computes as a negative int64 — a false NEGATIVE for any path
  # guarded on the wrapped value. (Measured before this fix: `if a*b < 0`
  # over `range[0'i64..4e9]` answered sxUnsat under isOptimised and sxSat
  # under isExact — the two modes contradicting each other, which ADR-0001
  # forbids outright.)
  #
  # There is no dynamic backstop here, unlike the checked case: the thing
  # to catch is not a raise but a defined result. So promotion must be
  # proven statically or declined — which is what finally puts Phase 2's
  # `tryEvalInterval` to work; it has had no caller in `src/` until now.
  #
  # RFC-0016 int6-o: the build's answer, also in a build that checks but holds
  # unchecked regions (`asPushedOff`, `asUnchecked`). The scan is no longer
  # what keeps a wrap sound: every Int it lets a parameter promote to is
  # width-stamped (`promoteSound`, below), and `lowerArith` reads the regime
  # where the walk stands for a stamped Int (the `ubSignedOverflow` halt, or
  # `wrapIntToWidth` where `wrapDefined`), so an unchecked region computes
  # what the bit-vector would and hands its caller an in-window value.
  let wrapScan = settings.integerSemantics == isOptimised and programMayWrap()
  var banPol = BanPolicy(intVars: intParamNames, wrapScan: wrapScan)
  if wrapScan:
    # Narrowest int window among the params: a result must fit the tightest
    # type in play to be provably wrap-free for all of them.
    banPol.window = interval(low(int64), high(int64))
    for p in prog.params:
      if p.ty.kind == itInt:
        let w = bvWindow(p.ty.width, p.ty.signed)
        banPol.window = interval(max(banPol.window.lo, w.lo),
                                 min(banPol.window.hi, w.hi))
        # An int param with no declared range can hold anything its type
        # holds, so its window IS its range — which makes any arithmetic on
        # it unprovable, correctly.
        banPol.ranges[p.name] =
          if p.hasRange: interval(p.rangeLo, p.rangeHi) else: w
  let banned = collectBan(prog.body, banPol)
  # #134: assertion-derived range refinements. Disabled when the
  # user's target is `tAssertionViolation` — the whole point of that
  # search is to find inputs that violate the assertion, so we
  # mustn't fold the assertion into the initial range constraints.
  var assertRanges: Table[string, Interval]
  if target.kind != stkAssertionViolation:
    collectAssertRanges(prog.body, assertRanges)
  if settings.integerSemantics == isLoose:
    emitIsLooseBanner()
  # N40 (round-6 fix round 6, walker v104): pre-walk param-entry boundary
  # totality preservation -- see `raiseParamAllocIssue`'s own doc comment,
  # above, for the full design writeup. `allocateSym` (below) no longer
  # raises for a classified-unallocatable type; this pass restores the
  # SAME whole-run raise semantics every param-level pin expects, before
  # any walk state (or even `currentWalkCtxPtr`) exists.
  for p in prog.params:
    let paramAllocIssue = unallocatableFieldIssue(p.ty)
    if paramAllocIssue.isSome:
      raiseParamAllocIssue(paramAllocIssue.get)
  # RFC-0016 INT-84: what `allocateSym` builds here is the walk's input, so
  # a holey enum in it ranges over its declared values (`allocInputDomain`).
  allocInputDomain = true
  for p in prog.params:
    case p.ty.kind
    of itTuple, itArray, itString, itSeq, itTable, itSet, itMultiVariant, itUninterp, itFloat32, itFloat64, itDistinct, itRef, itPtr, itBitSet:
      # itMultiVariant included here as Phase 14 cycle A1a stub; the
      # `allocateSym` for itMultiVariant raises a clear ValueError
      # (see runtime.nim allocateSym stub). Falling through to the
      # same call site keeps the dispatch surface uniform. itRef/itPtr
      # (Phase 15 R1a) likewise route through `allocateSym`, whose stub
      # raises the classified `heUnresolvedRef` (caught at the runSymex
      # boundary → sxUnknown, Invariant 3).
      # Round-6 B1: `p.isStringBacked` only ever affects the `itSeq` arm;
      # harmless to pass unconditionally for every other kind here.
      env[p.name] = allocateSym(p.ty, p.name, initialPC, p.isStringBacked)
    of itVariant:
      env[p.name] = allocateSym(p.ty, p.name, initialPC)
      # Phase 14 cycle A6 (ADR-0003 D6, mandatory). Under
      # `isOptimised`, promote the variant discriminator to Z3Int
      # so it composes cleanly with other Z3Int-promoted operands
      # (mixed BV/Int comparisons crack the abstraction layer).
      # The BV disc allocated above stays in the Z3 context but
      # becomes unreferenced after the swap; its old disjunction
      # in pcOut is harmless (BV is unused; constraints are
      # tautologies w.r.t. the new svInt disc).
      if settings.integerSemantics == isOptimised and
         p.ty.vDiscTy.kind != itBool:
        # Phase 15 F9c: a `bool` discriminator stays svBool — it is only
        # ever compared to true/false (handled by discEq/isVariantField's
        # svBool arms), never arithmetic, so the Z3Int promotion (which
        # would force `if v.k:` to read an svInt) does not apply.
        # Issue #163 review R12: `discriminatorDomain` (defined beside
        # `allocateSym`, above) is the ONE place that decides this
        # variant's legal discriminator domain -- shared with the BV-path
        # allocator's `itVariant` arm. It folds in the #163 W6
        # range-alias-else-domain guard: a non-enum (range-alias, e.g.
        # `range[lo..hi]`) discriminator with an `else:` arm takes its
        # domain from the disc's own declared range rather than the
        # convex hull of just the explicit `of N:` ordinals (that
        # narrowing made every else-arm value unreachable). An empty
        # `ordSet` signals exactly that case.
        let (minOrd, maxOrd, ordSet) = discriminatorDomain(p.ty)
        let promotedDisc = SymVal(kind: svInt,
          zi: mkIntVar(p.name & "." & p.ty.vDiscName & ".zi"))
        # Tight bound + per-ordinal disjunction on the Z3Int.
        initialPC.add (promotedDisc.zi >= mkZ3IntLit(minOrd))
        initialPC.add (promotedDisc.zi <= mkZ3IntLit(maxOrd))
        # Disjunction over legal ordinals (including else-covered
        # ordinals via vDiscTags when populated). Skipped for a
        # range-alias else-domain: the bounds above already define the
        # legal domain and an equality disjunction over just the
        # explicit `of N:` ordinals would falsely exclude the rest.
        if ordSet.len > 0:
          var clause = promotedDisc.zi == mkZ3IntLit(int64(ordSet[0]))
          for k in 1 ..< ordSet.len:
            clause = clause or
              (promotedDisc.zi == mkZ3IntLit(int64(ordSet[k])))
          initialPC.add clause
        env[p.name].vDisc[] = promotedDisc
        let ivl = interval(minOrd, maxOrd)
        log.add AbstractionEntry(
          name: p.name & "." & p.ty.vDiscName,
          interval: ivl,
          evidence: aeVariantDisc,
          derivation: "variant discriminator promoted to Z3Int " &
                      "over " & $ivl & " (" & $p.ty.vArms.len & " arms)")
    of itInt:
      # Type-derived range takes precedence; otherwise look for
      # assertion-derived ranges (#134).
      var hasRange = p.hasRange
      var rangeLo = p.rangeLo
      var rangeHi = p.rangeHi
      var fromAssert = false
      # RFC-0005 S8q: a scan offset (`IRParam.isScanOffset`) with no
      # declared or asserted range takes its TYPE's full range, so
      # `promoteSound` below allocates it as a width-stamped Z3 Int with
      # that range in `initialPC`: the bit-vector's own value set, and every
      # overflow obligation kept (`overflowCondInt`). As a bit-vector it
      # reached the scan's string query through a signed `bv2int` bridge
      # Z3 did not bound (B7R-3 ran past 300 s under a 10M `rlimit`).
      # RFC-0005 S8t: the same for a B4 accumulating-scan offset
      # (`isIntOffset`), which before S8t promoted UNSTAMPED with no range
      # (arithmetic on it had no overflow obligation), and for either kind
      # under `isExact` (below). Under `isExact` an asserted range is not
      # consulted: the type range is exact, the assertion fold is analysis.
      let isOffsetParam = p.isScanOffset or p.isIntOffset
      var typeRangeForScan = false
      if not hasRange and isOffsetParam and
         p.ty.signed and p.ty.width in [8, 16, 32, 64] and
         (settings.integerSemantics == isExact or
          not assertRanges.hasKey(p.name)):
        hasRange = true
        typeRangeForScan = true
        rangeLo = if p.ty.width == 64: low(int64)
                  else: -(1'i64 shl (p.ty.width - 1))
        rangeHi = if p.ty.width == 64: high(int64)
                  else: (1'i64 shl (p.ty.width - 1)) - 1
      if not hasRange and assertRanges.hasKey(p.name):
        let ai = assertRanges[p.name]
        if not ai.isEmpty:
          hasRange = true
          rangeLo = ai.lo
          rangeHi = ai.hi
          fromAssert = true
      let ivl = interval(rangeLo, rangeHi)
      let promoteLoose = settings.integerSemantics == isLoose
      # Issue #162. An UNSIGNED param never promotes. Nim wraps unsigned
      # arithmetic silently, so wrapping is this type's DEFINED behaviour,
      # and an unbounded `Z3Int` cannot wrap — the same argument #161 slice 3
      # made for signed arithmetic under `-d:danger`. The two cases differ in
      # the remedy available: signed-checked keeps its obligation live via
      # `overflowCondInt`'s raise fork, and unsigned has no raise fork to
      # keep anything live in, so the only sound representation left is the
      # one that wraps by construction. Refused outright rather than made
      # conditional on a wrap proof: before #162 no unsigned param could
      # carry `hasRange` at all (the enum arm in `dsl_typebridge` declines to
      # attach one for exactly this reason), so there is no promotion here to
      # preserve, only one not to introduce.
      # RFC-0005 S8t: under `isExact` a scan offset is promoted too. A Z3
      # Int stamped with its width, over its type's range, with every
      # overflow fork kept, has exactly the bit-vector's values and
      # defects, so `isExact`'s verdicts cannot move except by Z3
      # answering; the bridged form left B7R-3's query `unknown`. Only
      # under checked arithmetic (`acOverflow`): a bit-vector wraps where
      # an unbounded Int does not, and `isExact` runs no wrap scan
      # (`collectBan`'s `wrapScan` is `isOptimised`-only).
      # RFC-0016 int6-o: the build's answer is sound under mixed regions for
      # the same reason (`wrapScan` above): the promoted offset is stamped,
      # so an unchecked region's arithmetic on it is the regime's, and an
      # unchecked build stamps it all the same (`offsetStamp`).
      let offsetExact = settings.integerSemantics == isExact and
                        isOffsetParam and not programMayWrap()
      let promoteSound = (settings.integerSemantics == isOptimised or
                          offsetExact) and
                         hasRange and
                         p.ty.signed and
                         fitsBVWindow(ivl, p.ty) and
                         p.name notin banned
      # Round-6 B4 (ADR-0028 Leg 1, ADR-0027's recorded lift): a param
      # `collectIntOffsetParams` (`dsl_parser.nim`) traced to an
      # accumulating-scan's entry offset promotes UNCONDITIONALLY — it
      # carries no proven range (unlike `promoteSound`), so it must NOT add
      # the range constraints below; it exists purely so `iekStrSubstr`'s
      # strict Int-sortedness requirement (the CR-17 non-termination guard)
      # is met by the closed form's own LOW bound.
      let promote = promoteLoose or promoteSound or p.isIntOffset
      if promote:
        # ISSUE #161 / ADR-0001 amendment: the FLOOR is the proof obligation,
        # not the representation. A `promoteSound` param carries its static
        # Nim width so `lowerArith` keeps pushing `overflowCondInt` for every
        # operation on it — promotion changes the ENCODING, never the defect
        # semantics. Soundness is therefore structural here: it does not
        # depend on any static analysis being complete.
        #
        # This reverses the R3 (S2) scope note that stood here, but ONLY for
        # `promoteSound`. That note recorded a severe regression from
        # stamping (`tsymex_r6_b4_readcstring.nim` went from sub-minute to
        # not finishing within 15+ minutes) — measured on `isIntOffset`
        # params, which promote UNCONDITIONALLY with NO proven range. With no
        # range in the path condition every emitted fork looks satisfiable
        # and Z3 must explore all of them. A `promoteSound` param is the
        # opposite case: its `[rangeLo, rangeHi]` constraints go into
        # `initialPC` immediately below, so the overwhelming majority of its
        # overflow forks are UNSAT at birth and discharged instantly (and
        # slice 2 prunes them before they are ever emitted). The note's
        # conclusion was correct for the case it measured and does not
        # generalise to this one.
        #
        # `promoteLoose` (isLoose) and `isIntOffset`-only promotions stay
        # UNSTAMPED: isLoose is documented-unsound by user opt-in (ADR-0001)
        # and exists as a research baseline. RFC-0005 S8t: an `isIntOffset`
        # param now takes its type's range (above) and goes through
        # `promoteSound`, stamped, like S8q's scan offsets. The blowup the
        # R3 note measured was the stamp WITHOUT a range. What remains on
        # the unstamped arm is an `isIntOffset` param `promoteSound` turns
        # down: banned by the ban scan (a bit-twiddling op, or unprovable
        # arithmetic under unchecked `isOptimised`), unsigned, `isLoose`,
        # or `isExact` with unchecked arithmetic.
        #
        # RFC-0005 S8w: that remainder is closed except for `isLoose`. An
        # `isIntOffset` param `promoteSound` turns down (`offsetStamp`) is
        # stamped with its own width and signedness and confined to its
        # type's window (or its declared range), like a sound promotion:
        #   * checked signed arithmetic keeps its `overflowCondInt` forks;
        #   * unchecked signed arithmetic (`isExact` without `acOverflow`,
        #     or the `isOptimised` wrap scan's unprovable arithmetic) and
        #     unsigned arithmetic wrap (`lowerArith`'s `wrapIntToWidth`),
        #     as the bit-vector would;
        #   * a bit operation bridges through `int2bv`, which is exact, and a
        #     shift -- which the Int has no bit pattern for -- declines in
        #     band (`lower`'s `bShl`/`bShr` arm), scoped to the paths that
        #     reach it.
        # Before S8w the param was an unbounded Int with no stamp: no
        # overflow obligation, no wrap (`start + 1 < start` was `sxUnsat`
        # under unchecked arithmetic although `high(int)` reaches it).
        let offsetStamp = p.isIntOffset and not promoteSound and
                          not promoteLoose and
                          p.ty.width in [8, 16, 32, 64]
        let soundWidth = if promoteSound or offsetStamp: p.ty.width else: 0
        let soundSigned = (promoteSound or offsetStamp) and p.ty.signed
        # Slice 2: the same proven `ivl` that justifies the promotion also
        # seeds the static discharge. It is exactly the pair of constraints
        # added to `initialPC` just below, so the analysis and the path
        # condition cannot disagree about this param's range.
        let offsetWin = if offsetStamp: intWindow(p.ty.width, p.ty.signed)
                        else: default(typeof(intWindow(8, true)))
        let soundIvl =
          if promoteSound: some(ivl)
          elif offsetStamp and p.hasRange: some(interval(p.rangeLo, p.rangeHi))
          elif offsetStamp: offsetWin.ivl
          else: none(Interval)
        env[p.name] = SymVal(kind: svInt, zi: mkIntVar(p.name),
                             ziWidth: soundWidth, ziSigned: soundSigned,
                             ziIvl: soundIvl)
        if offsetStamp and not p.hasRange:
          # The declared-range case is the `elif` arm below, unchanged.
          initialPC.add (env[p.name].zi >= offsetWin.lo)
          initialPC.add (env[p.name].zi <= offsetWin.hi)
          # `uint64`'s window does not fit an `int64` interval; its
          # constraints are in the path condition, the audit entry is not.
          if offsetWin.ivl.isSome:
           log.add AbstractionEntry(
            name: p.name,
            interval: offsetWin.ivl.get,
            evidence: aeTypeRange,
            derivation: "accumulating-scan offset, " & $p.ty &
              " window, width-stamped" &
              (if not p.ty.signed: " (wraps: unsigned)"
               elif programMayWrap():
                 # The build's regime; an unchecked region of a checked
                 # build is the stamped lowering's (RFC-0016 int6-o).
                 " (unchecked arithmetic: overflow is undefined)"
               else: " (overflow forks kept)"))
        if promoteSound:
          initialPC.add (env[p.name].zi >= mkZ3IntLit(rangeLo))
          initialPC.add (env[p.name].zi <= mkZ3IntLit(rangeHi))
          log.add AbstractionEntry(
            name: p.name,
            interval: ivl,
            evidence: if fromAssert: aeNumericFold else: aeTypeRange,
            derivation:
              (if fromAssert: "assertion-derived range "
               elif typeRangeForScan: "scan offset, type range "
               else: "type-derived range ") &
              $ivl & " fits " & $p.ty & " BV window")
        elif p.hasRange and not promoteLoose:
          # isIntOffset-only promotion (not isLoose, not promoteSound) with
          # a DECLARED range (e.g. `range[..]`/`Natural`/`Positive`): unlike
          # isLoose's user-opted unsoundness, `isIntOffset` is a purely
          # internal representation choice the user never asked to be
          # unsound for — carry the same range constraint the BV `else`
          # branch below would have added, just Int-sorted. `lowerBool`
          # dispatches on the now-svInt `env[p.name]`, so this is the exact
          # BV-branch idiom below, sort-adapted.
          initialPC.add lowerBool(env,
            mkBinop(bGe, mkVar(p.name), mkIntLit(p.rangeLo)))
          initialPC.add lowerBool(env,
            mkBinop(bLe, mkVar(p.name), mkIntLit(p.rangeHi)))
        # isLoose (regardless of isIntOffset): no range constraints, no
        # audit entry — by design, the user is told this is unsound and
        # accepts it.
      else:
        env[p.name] = bvVar(p.ty, p.name)
        if p.hasRange:
          # Type-derived range as BV constraints (so `x > 100` is
          # still UNSAT under isExact for range[0..100]).
          initialPC.add lowerBool(env,
            mkBinop(bGe, mkVar(p.name), mkIntLit(p.rangeLo)))
          initialPC.add lowerBool(env,
            mkBinop(bLe, mkVar(p.name), mkIntLit(p.rangeHi)))
    of itBool:
      env[p.name] = SymVal(kind: svBool, bo: mkBoolVar(p.name))
    # RFC-0016 INT-84: a holey enum parameter is one of its declared values
    # (the arms above bound it by `[rangeLo, rangeHi]`, holes included).
    if p.ty.kind == itInt and p.ty.enumOrds.len > 0:
      for c in enumHoleConds(env[p.name], p.ty, zeroLegal = false):
        initialPC.add c
  allocInputDomain = false
  # RFC-0016 INT-82: every parameter's leaves (a ref's address, a seq's or
  # table's backing) are the walk's entry state (`refProvenanceRoots`).
  block:
    var acc: seq[RawZ3Ast]
    for p in prog.params:
      if env.hasKey(p.name): svAsts(env[p.name], acc)
    notePreExistingTerms(ctx, acc)
  let initial = initialWalkPath(initialPC, env)
  let exitClock = newExitClock()
  var w = WalkCtx(
    extHardMark: -1,   ## RFC-0005 S8ax: no depth extension under way
    exitClock: exitClock, topExits: exitClock.newExits(CallExits),
    frame: initCallFrameCtx(exitClock),
    z3: ctx, target: target, params: prog.params,
    mode: wmExplore,   ## RFC-fuzzer-nextgen G1a: explicit for clarity — this
                       ## is also the zero-value, so pre-G1a callers already
                       ## got this behavior with no change required here.
    found: @[],
    settings: settings, procs: prog.procs,
    callStack: @[], callStats: initTable[string, CallStat](),
    callCache: initTable[string, seq[CallCacheEntry]](),
    activeCalls: initHashSet[string](),
    initialEnv: env,
    statics: WalkerStatics(exnTable: exnTypeTable,   ## Phase 15 E4
                           userExnHierarchy: prog.userExnHierarchy,  ## E4a
                           sutRetTy: prog.retTy,  ## RFC-0005 S8p
                           globals: globalsTable(prog.globals)),  ## S8as
  )
  # Phase 15 C2b: publish a pointer to the live WalkCtx so `lowerClosureCall`
  # (running in the `lower` evaluator, no `WalkCtx` parameter) can drive the
  # lambda-body descent through `walk`. `w` is a stack local that lives across
  # the whole walk; the pointer is cleared after.
  currentLowerSinks = addr w.sinks
  currentWalkCtxPtr = addr w
  # CR-13: clear on the normal exit path (see the nil assignment below after
  # walk() returns). On the exception path, the pointer is cleared at the start
  # of the NEXT runSymexImpl call (the `currentWalkCtxPtr = nil` above), so it
  # is never stale when a sync*/allocRef* helper checks it. No inner try/except
  # or try/finally here — Nim's c backend goto-exception model can silently
  # swallow re-raises from nested try blocks, breaking exception propagation.
  # CR-9 Stage 4: sync caches that were already allocated during env setup
  # (lines above; `currentWalkCtxPtr` was nil then so `sync*` were no-ops).
  # This seeds WalkerStatics with any sorts allocated before the walk so that
  # in-walk reads from `w.statics.*` find the expected keys.
  for tid, srt in currentRefSorts:
    w.sinks.refSorts[tid] = srt
  for tid, nc in currentNilConsts:
    w.sinks.nilConsts[tid] = nc
  for dn, de in currentDistinctSorts:
    if not w.sinks.distinctSorts.hasKey(dn):
      w.sinks.distinctSorts[dn] = de
      w.sinks.distinctSortNames.add dn
  for ck, fd in currentClosureSyms:
    if not w.sinks.closureSyms.hasKey(ck):
      w.sinks.closureSyms[ck] = fd
  for sk, cb in currentClosureBodies:
    if not w.sinks.closureBodies.hasKey(sk):
      w.sinks.closureBodies[sk] = cb
  discard walk(prog.body, @[initial], w)
  if walkWorkExhausted:
    # RFC-0016 K7. The one `ckWalkWork` site: the walk's checks spent
    # `walkRLimit` together and `shouldStop` ended it; every path not yet
    # decided is dropped, so the run is `sxUnknown` unless a sound witness
    # was already found (`decideVerdict`, as for `ckFrontier`).
    w.halted(beBudgetExhaustedPrune,
      "walk work cap (walkRLimit=" & $walkRLimitCur & " Z3 units; " &
           $walkUnitsSpent() & " spent) ended the walk -- the paths not yet " &
           "decided are unexplored (beBudgetExhaustedPrune)",
      cap = ckWalkWork)
  if walkStalled:
    # RFC-0016 INT-57. A solve ran past the run's stall deadline with no run
    # clock (`stallBackstopMs`) and `shouldStop` ended the walk: the paths
    # not yet decided are dropped, and the run is `rdQueryTimeout` (not
    # cached). Never a verdict: `sxUnknown` unless a sound witness was found.
    w.halted(beSolverUndef,
      "solver stall backstop (" & $stallBackstopMs & " ms for the run, " &
           "queryTimeoutMs = 0) ended the walk: Z3 had stopped answering a " &
           "solve its step bound had not ended -- the paths not yet decided " &
           "are unexplored (the run's, not the program's)")
  currentLowerSinks = nil
  currentWalkCtxPtr = nil   ## (a) normal-path clear: walk() completed without raising
  stampLoweringPendingLeak(w)  ## RFC-0005 S1: pending-taint leak pin (§2.2)
  # Phase 15 G4 (ADR-0008 D4): CR-9 Stage 4 — `WalkerStatics.distinctSorts`/
  # `.distinctSortNames` are now the LIVE store, populated during the walk by
  # `syncDistinctSortEntry` (called from `allocDistinctSym`). No post-walk
  # mirror needed; `w.sinks.distinctSorts`/`.distinctSortNames` are current.
  # Phase 15 C2a (ADR-0009): CR-9 Stage 4 — `WalkerStatics.closureSyms` is now
  # the LIVE store, populated during the walk by `syncClosureSymEntry` (called
  # from `buildClosure`). No post-walk mirror needed; `w.sinks.closureSyms`
  # already contains the final values.
  # Phase 15 R1 (ADR-0010): CR-9 Stage 4 — `WalkerStatics.refSorts`/`.nilConsts`
  # are now the LIVE store, populated during the walk by `syncRefSortEntry` (called
  # from `allocRefSort` whenever a new sort is allocated). No post-walk mirror copy
  # needed; `w.sinks.refSorts`/`.nilConsts` already contain the final values.
  var statsSeq: CallStats
  for name, st in w.callStats:
    statsSeq.add st
  # Phase 15 E4. Drain the unknown-exn-type warning sink, dedup'd by type name.
  # sevWarning never halts a verdict (Invariant 7), so it is appended to the
  # result's errors regardless of which verdict branch is taken below.
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above.
  var exnWarnings: seq[SymexErrorInfo]
  drainSinkUnion(exnWarnings, w, unknownExnWarnings, unknownExnWarnings)
  # Phase 15 G4. Drain the distinct-bijectivity-skipped hint sink, dedup'd by
  # message (one per distinct type whose base was FP/String). sevHint never
  # changes the verdict (Invariant 7), so it rides every branch alongside
  # exnWarnings — appended to `exnWarnings` so the existing append sites carry
  # it on sat/unsat/unknown uniformly.
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above.
  drainDedupedByMsg(exnWarnings, w.sinks.distinctBijectivityHints & distinctBijectivityHints)
  # Phase 15 R2. Drain the freshness-cap hint sink, dedup'd by message (one per
  # ref type whose per-path distinctness inequalities hit the cap). sevHint
  # never changes the verdict (Invariant 7) — rides every branch via
  # `exnWarnings`, exactly the G4 bijectivity-skip drain above.
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above.
  drainDedupedByMsg(exnWarnings, w.sinks.freshnessCapHints & freshnessCapHints)
  # Phase 15 R8. Drain the ptr-family hint sink, dedup'd by message (one entry
  # per run regardless of how many ptr derefs occurred). sevHint never changes
  # the verdict (Invariant 7) — rides every branch via `exnWarnings`, exactly the
  # R2 freshness-cap drain above. A managed-`ref T`-only run drains NOTHING.
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above.
  drainSinkUnion(exnWarnings, w, ptrFamilyHints, ptrFamilyHints)
  # R16-2: convFloatToIntDomainHints removed (RFC-0005 S8g: a float→int
  # conversion never raises; its out-of-range continuation is a
  # `feConvFloatToIntUndefined`-tainted fork). No hint drain here.
  # Phase 15 R9. Drain the heap-depth-error sink (dedup'd by message). A
  # `heDepthExhausted` is `sevError`, but the verdict is already driven PER-PATH:
  # the exhausting path was halted (returned no survivor) and set `w.sawUnknown`,
  # so a run with NO sat finding degrades to `sxUnknown` carrying this classified
  # kind, while a SHALLOWER path that reached the target still yields its `sxSat`
  # witness (the `w.found` precedence below). Riding `exnWarnings` surfaces the
  # kind on whichever branch is taken (Invariant 3). A run that never exhausts the
  # budget drains NOTHING (no spurious halt). Mirrors the R8 ptr-family drain.
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above.
  drainSinkUnion(exnWarnings, w, heapDepthErrors, heapDepthErrors)
  # v64 (chapulin catalog #5(b), Invariant 7). Drain the budget-bail error
  # sink (dedup'd by message) — mirrors the R9 heap-depth-error drain. A
  # `beBudgetExhausted` is `sevError`; the exhausted/pruned paths already
  # drove the verdict via `w.sawUnknown` — this drain ensures the degraded
  # `sxUnknown` carries the classified WHY instead of an empty errors seq.
  # WalkCtx-field-only (both emitting sites have `w: var WalkCtx`); no
  # threadvar union needed, unlike `drainSinkUnion`'s sites above.
  drainDedupedByMsg(exnWarnings, w.walkDegradeErrors)
  # Cluster H Step C. Drain the isNew-zero-write error sink (dedup'd by
  # message) — mirrors the R9 heap-depth-error drain exactly. A
  # `heNewFieldZeroUnsupported` is `sevError`; the offending path was tainted
  # `uncertain = true` (not halted) so its own downstream sat/raised findings
  # already demote to `sxUnknown` at the `uncertain` chokepoints — this drain
  # only ensures the classified kind rides every verdict branch (Invariant 3).
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above.
  drainSinkUnion(exnWarnings, w, newFieldZeroErrors, newFieldZeroErrors)
  # SND-3 (ADR-0023, walker v58). Drain the lowering-degrade error sink
  # (dedup'd by message) — mirrors the R9 heap-depth-error / Cluster-H
  # newFieldZeroErrors drains exactly. Each entry is `sevError`; the
  # offending path was tainted `uncertain = true` by `drainPendingLowerEffects`
  # (not halted), so its own downstream sat/raised findings already demote to
  # `sxUnknown` at the `uncertain` chokepoints — this drain only ensures the
  # classified kind rides every verdict branch (Invariant 3). Threadvar-only
  # (no WalkCtx-field union): the lowering sites that populate it (`lower`'s
  # `iekBinop`/`iekContains` arms, `cmpString`) have no `w: var WalkCtx` in
  # scope.
  drainDedupedByMsg(exnWarnings, loweringDegradeErrors)
  # Phase 15 C2b. Drain the closure-call error sink (dedup'd by message and
  # anchor). Every entry is recorded by `closureDegrade`, which also put its
  # path taint on the consuming path (RFC-0005 S7); surfaced on every branch.
  # CR-9 Stage 5 union/LIVE-store contract: see `drainSinkUnion`'s doc above
  # (threadvar here is `currentClosureCallErrors`, not a same-named field).
  var closureErrs: seq[SymexErrorInfo]
  drainDedupedByMsg(closureErrs, w.sinks.closureCallErrors & currentClosureCallErrors)
  # RFC-0005 S9 (§2.5) -- the two blanket vetoes are deleted.
  # `capForcedUnknown` forced `sxUnknown` whenever ANY parse-time `sevError`
  # existed, and `closureForcedUnknown` whenever any closure-sink `sevError`
  # did, whatever the path that found the answer had passed. What they
  # insured against is now answered per decline:
  #   * a closure-sink decline taints its consuming path (S7), so it needs no
  #     run-wide switch;
  #   * a parse-time decline anchored at a marker or a callee key (S8) was
  #     REACHED iff a walk record carries the same anchor -- the walker
  #     records one on every path that reaches the site (`isUnsupported`,
  #     `isUnsafeCast`, the missing-callee arm), and taints that path. A
  #     decline no walked path reached contributed nothing to any verdict: it
  #     is kept as a `sevHint` diagnostic and leaves the run coordinate
  #     (`reachJoinParseErrors`). "Reached" means WALKED, not feasible: the
  #     walker forks `if` arms without a feasibility check, so this recovers
  #     `sxUnsat` only behind a decline no path walks at all (a handler no
  #     raise is routed to, a callee never called).
  #   * a signature-scoped decline stays run-wide through its class (§2.5
  #     point 2), as before;
  #   * a decline with NO anchor (`dskUnplaced`, §2.5 point 4) cannot answer
  #     the reach question, so it blocks both directions (`reachUnknown`) --
  #     a walker-completeness defect, pinned empty by the S8 battery.
  let parseErrs = reachJoinParseErrors(prog.parseErrors, exnWarnings)
  # RFC-0005 S1 (§2.2 "the run coordinate is derived, not written"). The run's
  # drain (`drainRunTaint`, the one writer): the walk/heap-depth/
  # new-field-zero/lowering sinks in `exnWarnings`, the reach-joined
  # parse-time errors, the closure sink.
  drainRunTaint(w, [exnWarnings, parseErrs, closureErrs])
  let reachUnknown = unplacedDeclines(exnWarnings).len > 0 or
                     unplacedDeclines(parseErrs).len > 0 or
                     unplacedDeclines(closureErrs).len > 0
  ## RFC-0005 S1c (§2.3): the ordered verdict procedure (`decideVerdict`).
  ## Rules 1-2 keep ADR-0012 D2's unified, target-independent precedence over
  ## `w.found` -- sxSat > sxRaised > the rest, FIRST in discovery order --
  ## now over CLEAN findings only (`w.found` holds nothing else since S1c;
  ## spurious-tainted SATs sit in `w.candidates`). Raise-flavoured targets
  ## only ever accumulate sxRaised in `w.found` (label sxSat is added solely
  ## at isTargetLabel, gated on stkLabel), so first-sxRaised-wins is
  ## bit-identical to the prior `w.found[0]` behaviour for them. Rule 4: any
  ## candidate blocks `sxUnsat`. Rule 5: `sxUnsat` needs only
  ## `scIncomplete notin runTaint` (§0.3's recovered capability; under
  ## all-⊤ that is exactly the old `runTaint == {}`).
  let decision = decideVerdict(w.found, w.candidates, w.runTaint,
                               reachUnknown = reachUnknown)
  rfc0005RawStatus = decision.status
  logWalkUnits(case target.kind
               of stkLabel: "label:" & target.label
               of stkRaisedExn: "raised:" & target.typeFilter
               else: $target.kind, $decision.status)
  let winnerFound = decision.status in {sxSat, sxRaised}
  let winnerIdx   = decision.winnerIdx
  if winnerFound:
    var r = w.found[winnerIdx]
    r.abstractions = log
    r.obligations = obligationLog   ## #161 slice 2
    r.callStats = statsSeq
    ## ADR-0012 D2: collect every non-winning sxRaised into diagnostics.
    ## If winner is sxSat (winnerIdx points to it), ALL sxRaised entries
    ## qualify (none has i==winnerIdx AND is sxRaised). If winner is the
    ## first sxRaised (winnerIdx points to it), all other sxRaised go in.
    var diags: seq[RawDiagnostic]
    for i, f in w.found:
      if f.status == sxRaised and i != winnerIdx:
        diags.add RawDiagnostic(raisedTypeId: f.raisedTypeId,
                                isDefect:     f.isDefect,
                                raisedMsg:    f.raisedMsg,
                                raisedWitness: f.raisedWitness,
                                witnessUnsafe: f.soundness.witnessUnsafe)
    r.diagnostics = diags
    r.undefined = w.undefinedFound   # RFC-0016 K10a-target
    # CR-9 Stage 5: read from WalkCtx.extractionErrors (LIVE store during walk)
    # and union with threadvar fallback. extractionErrors is SAT-branch-only.
    let extractionErrorsLive = w.sinks.extractionErrors & extractionErrors
    if extractionErrorsLive.len > 0:   ## Phase 15 F7: surface any float-extraction failures
      r.errors.add extractionErrorsLive
    r.errors.add exnWarnings       ## Phase 15 E4
    r.errors.add parseErrs         ## Phase 15 G1c; RFC-0005 S9: reach-joined
    r.errors.add closureErrs       ## Phase 15 C2b
    r.candidates = toCandidates(w.candidates)    ## RFC-0005 S1c / S10
    # RFC-0016 K10b (section 9.1 item 3): a clean label `sxSat` is trusted
    # only when the whole run is defined. The explore walk stopped at the
    # hit, so the tail is checked by a second walk under the witness's model
    # pins (`verifyTailDefined`); the kinds it is not shown defined in join
    # `witnessUndefined`, which `trustedSat` requires empty and replay cannot
    # lift (item 4). A verdict already carrying a kind needs no second look;
    # a raise ends the run at the raise, so `sxRaised` is not gated.
    if settings.wholeRunDefinedness and r.status == sxSat and
       target.kind == stkLabel and r.soundness.witnessUndefined == {}:
      let tail = verifyTailDefined(prog, settings, ctx, env, initialPC,
                                   r.witness.pins)
      if tail.all != {}:
        r.soundness.witnessUndefined = ubOrdinals(tail.all)
    r
  elif decision.status == sxUnknown:
    # v64 (chapulin catalog #5(b)): Invariant-7 BACKSTOP. Every sxUnknown
    # must carry at least one classified error. All known degrade sites now
    # classify (budget bails via `beBudgetExhausted`, lowering degrades via
    # `loweringDegradeErrors`, …) — if this fires, some run-marking site
    # escaped classification, which is a walker bug: surface it as
    # `weInternalWalkerFault` so telemetry tracks it, never an empty seq.
    # RFC-0005 S1c: that includes a candidate with nothing recorded behind
    # it -- a spurious-tainted path whose degrade recorded no error (every
    # `Degrade` token comes from a recording funnel, so this is a walker bug).
    # RFC-0005 S11 (§8.1, the Invariant-7 extension): "classified" means a
    # reason that TAINTS the run -- `soundness.runTaint` is derived from
    # these errors and must never be `{}` on an `sxUnknown`. An unknown whose
    # only records are hints / plain warnings has no classified reason
    # either, so the backstop fires on an empty run coordinate, not just on
    # an empty list.
    var unknownErrs = exnWarnings & parseErrs & closureErrs
    if runTaintOf(unknownErrs) == {}:
      unknownErrs.add SymexErrorInfo(
        kind: weInternalWalkerFault, severity: severity(weInternalWalkerFault),
        msg: "sxUnknown produced with no classified reason — an unclassified " &
             "degrade site set sawUnknown bare (walker classification gap; " &
             "weInternalWalkerFault)",
        # RFC-0005 S8 (§2.5 point 4): literally unplaced -- the backstop
        # fires only when no site recorded anything, so there is no site to
        # name. Bucket 4 by construction; the S8 pin enumerates it by name.
        scope: DeclineScope(kind: dskUnplaced))
    # RFC-0016 W4 perf: the settle's replays run here, in its order (`sxSat`
    # claims, then `sxRaised` claims, each in discovery order) up to the
    # first confirmation (RFC-0016 INT-32 item 8: at once, `replayInOrder`), while the run's context and the candidates' model
    # pins are live (`dropWitnessPins` clears them at the boundary). The
    # entry macro settles on what they recorded once the run returns. A run
    # whose Z3 API errors `runSymex` will turn into a bare `sxUnknown`
    # (RFC-0005 S8m) hands out no candidate to settle, so replays none.
    var confirmed = -1
    if replay != nil and z3ApiErrorCount == 0:
      var order: seq[int]
      var cands: seq[SatCandidate]
      for claim in [sxSat, sxRaised]:
        for i, c in w.candidates:
          if c.status == claim:
            order.add i
            cands.add toCandidate(c)
      if order.len > 0:
        let k = replay(order, cands)
        if k >= 0: confirmed = order[k]
    # RFC-0016 W3-z R2 (section 9: replay is no evidence for undefined
    # behaviour). A label candidate a replay confirms is held to the
    # whole-run gate the winner is: its tail is walked under its model pins,
    # and the kinds it is not shown defined in join its `witnessUndefined`,
    # which `settleCandidate` carries onto the confirmed verdict. Its path
    # carries a fresh symbol the pins do not fix, which the walk
    # over-approximates, as it does the winner's.
    #
    # RFC-0016 W4 perf: only the confirmed candidate's tail is walked. A
    # candidate no replay confirms reaches no verdict, so what its tail
    # holds is read by nothing; walking every candidate's tail before any
    # replay spent the run's whole tail budget on the `n36` pair loop, whose
    # verdict stays `sxUnknown`. A candidate whose tail is not walked fails
    # closed (`ubTailUnverified`), so no settle can make it a defined claim.
    # The confirmed tail is the run's only candidate tail walk, so it has
    # the run's whole tail budget and its sites are the only ones joined.
    if settings.wholeRunDefinedness and settings.replay and
       target.kind == stkLabel:
      for i, c in w.candidates.mpairs:
        # RFC-0016 W3-z R7: a candidate whose kinds all came through
        # proc-valued variables (`undefinedViaOnly`) is walked too: a replay
        # may replace those, and then the tail must have been looked at.
        let fixed = c.soundness.witnessUndefined - c.undefinedViaOnly
        if c.status != sxSat or fixed != {}: continue
        if i != confirmed:
          c.soundness.witnessUndefined.incl ubOrdinals({UbKind(ubTailUnverified)})
          continue
        let tail = verifyTailDefined(prog, settings, ctx, env, initialPC,
                                     c.witness.pins)
        let all = c.soundness.witnessUndefined + ubOrdinals(tail.all)
        let allFixed = fixed + ubOrdinals(tail.all - tail.viaOnly)
        c.soundness.witnessUndefined = all
        c.undefinedViaOnly = all - allFixed
        for k in tail.sites:
          if k notin w.procValueSites: w.procValueSites.add k
    RawResult(status: sxUnknown, abstractions: log, obligations: obligationLog,
              callStats: statsSeq, errors: unknownErrs,
              undefined: w.undefinedFound,   # RFC-0016 K10a-target
              procValueSites: w.procValueSites,   # RFC-0016 W3-z R7
              candidates: toCandidates(w.candidates))
  else:
    # RFC-0005 S1c: `decideVerdict` rule 5 -- no solved SAT anywhere (so no
    # candidates to hand out) and `scIncomplete notin runTaint`.
    RawResult(status: sxUnsat, abstractions: log, obligations: obligationLog,
              callStats: statsSeq, undefined: w.undefinedFound,   # K10a-target
              errors: exnWarnings & parseErrs & closureErrs)

# ---- RFC-fuzzer-nextgen G1b: concolic draw-symbolication + concrete-trace --
# ---- constraint collection (mechanism steps 2-3 only; no branch-flip) ------
#
# Design (confirmed against the RFC's §G-concolic before implementing):
#   (a) A recorded `seq[ChoiceNode]` maps cleanly onto the walker's existing
#       symbolic-var machinery: each node already carries BOTH its concrete
#       value and its declared constraint (`IntConstraints`/`BoolConstraints`/
#       …), so "fresh symbolic var + its declared constraint" is exactly
#       `mkIntVar`/`mkBoolVar` + the same `initialPC.add(v >= lo); (v <= hi)`
#       idiom `runSymexImpl` already uses for params — reused verbatim below.
#   (b) There is no walkable form of `generate ∘ property` as ONE typed proc —
#       `Strategy.run` is an opaque runtime closure (`strategy.nim`) with no
#       retrievable AST, confirmed dead-end the RFC itself already names
#       ("Strategy.run/prop are runtime closures with no retrievable AST").
#       The walker's ONLY door stays `fn: typed` (a property proc). So this
#       mechanism does NOT walk the strategy; it treats "which draws feed
#       which property parameter, unmodified vs. through a combinator" as an
#       input the CALLER supplies (`bindings`, below) — matching the RFC's
#       own escape hatch ("anything the walker cannot model is concretized to
#       its observed value"). Classifying a strategy-construction expression
#       as transparent-identity vs. combinator-opaque is a syntactic, macro-
#       level concern (mirrors `fuzzmacro.nim`'s own AST-capture design) that
#       belongs to G1b's caller (ultimately G3's orchestration wiring), not
#       to this mechanism proc.
#   (c) `wmFollowConcrete` fits the existing arm dispatch exactly as G1a
#       shaped it: `walkIfFollowConcrete` (above `isIf`'s wmExplore fork
#       loop) picks the ONE concretely-taken arm using the recorded
#       `ChoiceNode` values (via `concreteEq`, never asserted onto the live
#       path) and reuses `lowerBoolInExpr`/`forkPath` unchanged.
# The mechanism maps cleanly — no escalation needed.

type
  ConcolicBindingKind* = enum
    cbDrawLinked
      ## Transparent identity: this property parameter IS one recorded draw,
      ## unmodified by any strategy combinator — kept symbolic.
    cbConcretized
      ## The draw→parameter link passes through something the walker cannot
      ## see (a `map`/`filter`/`flatMap`/… combinator, or a draw kind G1b
      ## does not yet symbolicate) — bound to its OBSERVED value (a Z3
      ## literal, not a free variable) instead of guessed at.
    cbTransformLinked
      ## RFC-fuzzer-nextgen G6: the parameter's value is `tA*draw + tB`
      ## (still symbolic, `draw` = `trace[tDrawIndex]`), optionally
      ## constrained by extra Z3 conjuncts (`tConjuncts`) — the flattened,
      ## primitive-only twin of `smt/transparency.nim`'s composed
      ## `TransparencyDescriptor` (identity is `tA=1,tB=0`; affine is any
      ## `tA,tB`; predicated/resolved-branching add `tConjuncts`).
      ## `fuzzmacro.nim`'s classifier builds this at macro-expansion time —
      ## this module stays decoupled from the (macro-only) descriptor tree,
      ## seeing only int64/enum data, matching `fuzz.nim`'s own erased-
      ## mirror convention for the bridge result types.

  ConcolicConjunctOp* = enum
    ccoEq, ccoNe, ccoLt, ccoLe, ccoGt, ccoGe

  ConcolicConjunct* = object
    ## `(a*trace[drawIndex] + b) op lit`, asserted as an extra `initialPC`
    ## conjunct. `drawIndex` is independent of the binding's own
    ## `tDrawIndex` — a resolved `branching` guard constrains the
    ## DISCRIMINATOR draw, which is a different index than the value draw
    ## the case it resolved to actually binds.
    drawIndex*: int
    a*, b*: int64
    op*: ConcolicConjunctOp
    lit*: int64

  ConcolicParamBinding* = object
    case kind*: ConcolicBindingKind
    of cbDrawLinked:
      drawIndex*: int   ## index into the trace this parameter equals
    of cbConcretized:
      concreteInt*:  int64   ## read when the parameter's IRType is itInt
      concreteBool*: bool    ## read when the parameter's IRType is itBool
    of cbTransformLinked:
      tDrawIndex*: int
      tA*, tB*: int64
      tConjuncts*: seq[ConcolicConjunct]

  # `ConcolicYieldCounters` moved to the leaf module `./concolictaxonomy`
  # (R28/R29b) — see that module's doc comment. Re-exported above, so this
  # is a pure move.

  ConcolicCollectResult* = object
    pcSatByConcreteInputs*: bool
      ## THE G1b soundness pin (RFC: "collected constraints ARE SATISFIED by
      ## the original concrete input"): every surviving path's collected
      ## `pc`, conjoined with `concreteEq` (the ground equalities pinning
      ## every symbolicated draw to its recorded value), is SAT. G1b never
      ## flips a branch (that's G2), so this can only go false from an
      ## internal bug in `walkIfFollowConcrete`/draw-symbolication — not
      ## from "no solution exists" (there is always one: the original
      ## concrete trace itself). RFC-0005 S8o: the check runs under
      ## `concreteBranchRLimit(settings)`; one that exhausts it is `false`
      ## (not proven).
    counters*: ConcolicYieldCounters
    definedFacts*: seq[ConcolicDefinedFact]
      ## RFC-0016 K10a-concolic. The operations with an undefined side this
      ## replay executed, in encounter order (see `ConcolicDefinedFact`).
    errors*: seq[SymexErrorInfo]
      ## RFC-0016 K7c. The classified degrades and caps the follow walk
      ## recorded, deduplicated as `SymexResult.errors` is (the walk,
      ## heap-depth, new-field and closure-call sinks, and the lowering sink):
      ## a cap such as `ckLoopUnwindFollow` is here by its kind and message,
      ## where only `counters.walkDegradeCount` counted it before. Parse-time
      ## declines stay in `parseErrors`.
    soundBranches*: int
      ## RFC-0016 K7c. How many leading `branchTrace` records are on the
      ## replay's own path: all of them, unless a follow `while` was cut at
      ## `maxLoopUnwind` while the replay was still iterating, when the
      ## records from the cut on belong to a continuation the trace never
      ## takes. A flip of one of those is not a flip of the replay.
    branchTrace*: seq[ConcolicBranchRecord]
      ## RFC-fuzzer-nextgen G2. The `if`-decisions `walkIfFollowConcrete`
      ## resolved along this replay, in encounter order — `runConcolicFlipImpl`
      ## indexes into this by `targetBranchIndex` to build its flip formula.
      ## Empty for a trace with no branching (G1b's own tests never read it).
    drawVars*: seq[SymVal]
      ## RFC-fuzzer-nextgen G2. The fresh symbolic Z3 var built for each of
      ## the first `min(trace.len, maxDraws)` draws, indexed exactly like
      ## `trace` — a default zero-value `SymVal` (never read) for
      ## `ckFloat`/`ckBytes`/`ckString` entries, which G1b's fragment does
      ## not symbolicate (guard on `trace[i].kind`, same as the collection
      ## loop below does, before reading `.zi`/`.bo`). `runConcolicFlipImpl`
      ## reads a solved model's value off these to materialize a new trace.
      ##
      ## Issue #163 review R24: this is the DRAW's own idealized Z3Int
      ## variable, allocated ONCE in Step 2 before any param binding is
      ## decided — it is NOT necessarily the variable a branch predicate
      ## downstream of a `useBV` param binding actually constrains (see
      ## `drawOverrides`, immediately below).
    drawOverrides*: seq[Option[SymVal]]
      ## Issue #163 review R24/R25. R16 (`concolicScalarPromotesSoundly`)
      ## made a `useBV` param binding allocate a FRESH, width/signedness-
      ## faithful BV variable for `env[p.name]` instead of aliasing
      ## `drawVars[i]` directly (the whole point: a BV param must never
      ## share a symbol with the idealized-Z3Int draw var, or it would
      ## reintroduce R16's own wrap-disagreement bug). But that means a
      ## branch predicate reading such a param is written in terms of THAT
      ## fresh BV variable, not `drawVars[i]` — so a flip-solve targeting it
      ## produces a model with no useful assignment for `drawVars[i]` at
      ## all (R24's bug: `materializeConcolicModel` read the wrong,
      ## disconnected variable).
      ##
      ## `drawOverrides[i]` records, PER DRAW INDEX, the actual BV variable
      ## (if any) that stands in for draw `i`'s value in whatever `env`
      ## binding was built from it — `some(bv)` when a `useBV` binding
      ## (cbDrawLinked directly, or cbTransformLinked's own fresh
      ## "represents this draw" BV var — see R25) was built from this draw,
      ## `none` otherwise (the draw kept its plain `drawVars[i]` Z3Int
      ## representation, or was never symbolicated at all).
      ## `materializeConcolicModel` consults this FIRST and falls back to
      ## `drawVars[i]` — never mutates `drawVars` itself, so every OTHER
      ## consumer sharing draw index `i` within this SAME collect call
      ## (`tConjuncts`'s discriminator read, or another binding's own
      ## `tDrawIndex` affine formula — both still genuinely Int-sorted, by
      ## construction of how the macro emits bindings: see `concolic.nim`'s
      ## `bindingExprFor`) keeps working exactly as before, untouched by a
      ## sibling param's own `useBV` choice for the SAME index.
    obligations*: ObligationLog
      ## Issue #163 review R26 (continued). R26's own fix (above,
      ## `concolicScalarLiteral`) stamped `ziWidth`/`ziSigned` onto a
      ## concolic-bound Z3Int param SPECIFICALLY so `overflowCondInt`'s
      ## (#161) signed-overflow obligation would fire on this driver's
      ## `wmFollowConcrete` walk exactly as it already does for `wmExplore`'s
      ## own `promoteSound` route — and `tsymex_163rev_concolic_flip_width.
      ## nim`'s own R26 suite proved that it does fire, but only by reading
      ## the `obligationLog` threadvar DIRECTLY, because this type had no
      ## field to carry it through the public `concolicCollect` macro at
      ## all. This field mirrors `SymexResult.obligations` (`smt/types.nim`
      ## — see its own doc comment for the canonical threadvar-drain
      ## contract; `RawResult.obligations`, just above in this file, is the
      ## same mirror), assigned from the SAME threadvar at the SAME point
      ## `result.counters` is, below. Diagnostics only, exactly like
      ## `counters.walkDegradeCount` (W10/R9): an obligation recorded here
      ## never flips `pcSatByConcreteInputs` or any other verdict-shaped
      ## field on this type, and this type still has no raised-verdict
      ## channel at all (see `drawOverrides`'s own R26 note, and
      ## `tsymex_163rev_concolic_flip_width.nim`'s closing suite, for why
      ## that is a deliberately separate, larger slice this field does not
      ## attempt).
      ##
      ## Round 10 (Design F1/F3, Liveness F1): this seq is a DETAIL view,
      ## not the only surface — the fact "an obligation went live" is what
      ## actually needs to reach the fuzzer, and it does, as
      ## `counters.obligationsLive` (`ConcolicYieldCounters`, `smt/
      ## concolictaxonomy.nim`), folded by `foldFlipResult` into
      ## `Orchestrator.concolicYield`/`CampaignStats.concolicYield` on every
      ## real fuzzing flip via `runConcolicFlipImpl`. This seq stays for the
      ## drill-down (which obligation, what width/signedness) behind that
      ## live count; it was never meant to be, and is not, the only channel.
    annotationViolations*: seq[AnnotationViolation]
      ## RFC-0005 S8 (§13.3, i3). `prog.annotationViolations`, read directly
      ## (same contract as `parseErrors` below). Before S8 a false
      ## `{.symexTransparent.}` claim arrived here as a `parseErrors` entry
      ## (`feTransparentResultUsed`/`feTransparentArgNotInert`) and so was
      ## counted in `counters.parseDeclines`; it is not a decline, so it no
      ## longer is.
    parseErrors*: seq[SymexErrorInfo]
      ## Issue #163 review R26's companion gap: `runConcolicCollectImpl`
      ## drains BOTH degrade sinks (`w.walkDegradeErrors` and the
      ## `loweringDegradeErrors` threadvar, see `counters.walkDegradeCount`'s
      ## own drain immediately below, W10/R9) into a count, but never once
      ## read `prog.parseErrors` — the seq of `SymexErrorInfo` a PARSE-TIME
      ## decline (e.g. `feEnumOrdinalUnresolved`, `feGlobalReadUnmodelled`) is recorded
      ## into, before the walk itself ever starts (`dsl_parser.nim`'s
      ## `ctx.parseErrors`, threaded onto `SymexProgram.parseErrors` by
      ## `parseEntryImplWarned`, the SAME macro-time step `symexFind` and
      ## `concolicCollect` both route through — see `nelli/symex.nim`'s
      ## `concolicCollect` macro body). `runSymexImpl` already unions this
      ## same seq into `r.errors` on every one of its own verdict branches
      ## (`r.errors.add prog.parseErrors`, Phase 15 G1c); a concolic collect
      ## over a program with such a decline used to report "success" with no
      ## indication whatsoever that part of the program was never modelled.
      ## Read directly off `prog.parseErrors` — no threadvar, no drain, no
      ## dedup (a `SymexProgram` is parsed exactly once per macro
      ## invocation, so `prog.parseErrors` cannot accumulate duplicates the
      ## way a threadvar sink written across nested calls could). Diagnostic
      ## only, same contract as `obligations` above.
      ##
      ## Round 10 (Design F1/F3, Liveness F1): same correction as
      ## `obligations` above — this seq is the detail view, not the only
      ## surface. `counters.parseDeclines` (`ConcolicYieldCounters`) counts
      ## the `sevError` entries here (the predicate `capForcedUnknown` used
      ## to force `sxUnknown` on the `wmExplore` path until RFC-0005 S9) and
      ## reaches `Orchestrator.concolicYield`/`CampaignStats.concolicYield`
      ## the same way `obligationsLive` does. A parse decline is counted and
      ## surfaced, never used to reject the materialized seed — see
      ## `parseDeclines`'s own doc comment for why: the seed is still a real
      ## concrete input the fuzzer executes for real against the SUT.

const defaultMaxConcolicDraws* = 256
  ## RFC-fuzzer-nextgen G1b (round-2 breadth fix): bounded trace length. A
  ## recursive/streaming strategy can draw unboundedly many `ChoiceNode`s;
  ## capping the symbolicated-var count keeps draw-symbolication (and the
  ## Z3 formula it seeds) terminating regardless of corpus-entry size.

func concolicIntRepresentable(node: ChoiceNode): bool =
  ## R1: whether a `ckInteger` node is safe to narrow through `toInt64`
  ## anywhere the concolic bridge does so (draw-symbolication bounds,
  ## concrete-equality pins, and later model materialization). `ChoiceInt`
  ## (`Int128`) can hold the full `uint64` range — the stock `uint64`/`uint`
  ## strategy (`derive.nim`) draws exactly that — but the bridge's Z3
  ## integer domain is `int64`-only. `toInt64` silently WRAPS an
  ## out-of-range `Int128` (`int128.nim`'s documented behavior), which would
  ## corrupt the emitted domain (e.g. `[0, high(uint64)]` narrows to the
  ## inverted, unsatisfiable `[0, -1]`) rather than raise. Every field a
  ## call site might narrow — `min`, `max`, `shrinkTowards`, and the
  ## concrete value itself — must independently fit, via `fitsInt64`
  ## (`int128.nim`), the codebase's established narrowing guard.
  node.intC.min.fitsInt64 and node.intC.max.fitsInt64 and
    node.intC.shrinkTowards.fitsInt64 and node.intVal.fitsInt64

proc concolicScalarPromotesSoundly(ty: IRType, settings: SymexSettings): bool =
  ## Issue #163 review finding R16. Whether a concolic-bound `itInt` scalar
  ## parameter may keep the idealized, non-wrapping `Z3Int` representation
  ## `runConcolicCollectImpl` has always used unconditionally, rather than a
  ## width/signedness-faithful bitvector.
  ##
  ## Shares `promoteSound`'s (`runSymexImpl`, above) core argument for the
  ## UNSIGNED case verbatim: Nim wraps unsigned arithmetic silently (defined
  ## behaviour, not a defect), and an unbounded Z3Int cannot wrap by
  ## construction, so an unsigned param never promotes — full stop, exactly
  ## `promoteSound`'s own "An UNSIGNED param never promotes" rule.
  ##
  ## Deliberately NOT a call to `promoteSound` itself, and not merely its
  ## copy: `promoteSound` additionally requires a PROVEN declared range
  ## (`hasRange`) that fits the type's own BV window before a SIGNED param
  ## promotes — necessary there because `wmExplore` forks every arm of every
  ## arithmetic-overflow obligation it emits, and an unranged param leaves
  ## every one of those forks satisfiable, so fork count (and Z3 load)
  ## scales with the search itself (see `promoteSound`'s own comment).
  ## `wmFollowConcrete` does no such forking — `concreteBranchOutcome` is one
  ## bounded scratch SAT check per `if`-decision along a SINGLE concrete
  ## replay — so that path-explosion argument does not transfer here, and
  ## reusing `promoteSound`'s literal formula would force EVERY unranged
  ## scalar int param (an ordinary, unranged `int` included — by far the
  ## common case across this codebase's existing concolic-bound properties:
  ## `tsymex_g1b_concolic.nim`, W10's own fixtures, G6's transform-binding
  ## suite) onto the BV route, a large, unrequested representation and
  ## solver-cost change to the common path that nothing in this finding asks
  ## for.
  ##
  ## What DOES transfer is the actual soundness question: can an unbounded
  ## Z3Int silently disagree with the type's own (truncating) arithmetic? At
  ## the FULL native width (64 bits) — what an ordinary, unranged `int`
  ## declares — it cannot, for exactly the reason `abstraction.nim`'s own
  ## `bvWindow` already documents: this codebase's Z3Int abstraction is
  ## itself capped at `int64`'s own range by convention, so a 64-bit signed
  ## value has nothing narrower to disagree with. The one residual gap
  ## (arithmetic that itself overflows int64) is the SAME pre-existing,
  ## already-flagged limitation this file's own header describes (no
  ## `ziWidth` is stamped on a concolic-bound int at any width, so #161's
  ## live obligation still does not reach one) — not something this fix
  ## introduces, and out of scope for the wrap-disagreement finding it
  ## closes. A signed type NARROWER than 64 bits gets no such exemption:
  ## Z3Int arithmetic on it is exact where the type's own is truncating, so
  ## (matching `promoteSound` exactly for this case) it promotes only when a
  ## declared range is proven to fit the type's own BV window.
  ##
  ## Not gated on `promoteSound`'s `banned` (bit-twiddling-op) exclusion:
  ## that set exists to protect an interval-arithmetic WRAP PROOF (the
  ## `wrapScan`/unchecked-arithmetic case) from a bit op it cannot reason
  ## about — a proof this predicate never attempts (it is a fixed,
  ## type-only decision, not a per-expression static analysis), so there is
  ## nothing here for that exclusion to guard.
  settings.integerSemantics == isOptimised and
  ty.signed and
  (ty.width >= 64 or
   (ty.hasRange and fitsBVWindow(interval(ty.rangeLo, ty.rangeHi), ty)))

proc bvEqConst(v: SymVal, val: int64): Z3Bool =
  ## Issue #163 R16. A ground BV equality pin for a concolic-bound param's
  ## recorded concrete value — the BV-domain twin of Step 2's existing
  ## `concreteEq` `Z3Int` pins on the underlying draw variable. No
  ## `int2bv`/`bv2int` bridge is used anywhere in this fix: the draw's own
  ## Z3Int variable and this fresh BV param variable are two independently
  ## pinned Z3 symbols for the SAME underlying Nim value, and are never
  ## required to agree with each other inside one formula — each is only
  ## ever compared against a ground literal of its own sort. Mirrors
  ## `bvRangeConds`'s own per-width case split, above.
  case v.kind
  of svBV8:  v.bv8  == mkBitVec[8](val)
  of svBV16: v.bv16 == mkBitVec[16](val)
  of svBV32: v.bv32 == mkBitVec[32](val)
  of svBV64: v.bv64 == mkBitVec[64](val)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: BV-only call sites (runConcolicCollectImpl's own useBV guard pre-selects a BV kind)]
      "bvEqConst: not a BV — got " & $v.kind)

proc concolicScalarLiteral(ty: IRType, useBV: bool, val: int64): SymVal =
  ## Issue #163 R16. Ground literal for a concolic-bound scalar `itInt`
  ## param, representation-matched to `useBV`
  ## (`concolicScalarPromotesSoundly`) so a single param never straddles two
  ## representations across this driver's different binding paths
  ## (transparent draw-link vs. out-of-bounds/kind-mismatch concretize
  ## fallback vs. `cbConcretized`).
  ##
  ## Issue #163 review R26: the `svInt` (non-`useBV`) branch is only ever
  ## reached when `concolicScalarPromotesSoundly(ty, ...)` held for this
  ## param (every call site computes `useBV` from exactly that predicate),
  ## which requires `ty.signed` — so stamping `ty.width`/`ty.signed`
  ## unconditionally here is sound. Without this stamp `overflowCondInt`
  ## (issue #161) never fires for a concolic-bound param on ANY path, at
  ## ANY width — the live obligation `promoteSound` (`runSymexImpl`, the
  ## `wmExplore` counterpart) already carries was simply never wired for
  ## `wmFollowConcrete`.
  if useBV: bvConst(ty, val)
  else: SymVal(kind: svInt, zi: mkZ3IntLit(val), ziWidth: ty.width, ziSigned: ty.signed)

proc runConcolicCollectImpl*(prog: SymexProgram, trace: seq[ChoiceNode],
                             bindings: seq[ConcolicParamBinding],
                             settings: SymexSettings = defaultSymexSettings(),
                             maxDraws: int = defaultMaxConcolicDraws
                            ): ConcolicCollectResult =
  ## Concolic mechanism steps 2-3 (RFC §G-concolic) — see the module-section
  ## comment above for the confirmed design. `bindings` has one entry per
  ## `prog.params`, in order; see `ConcolicParamBinding`.
  doAssert bindings.len == prog.params.len,
    "runConcolicCollectImpl: exactly one binding per property parameter " &
    "is required (got " & $bindings.len & " bindings for " &
    $prog.params.len & " params)"
  # RFC-0016 K5a: the host half of the build profile, read once. A host no
  # row covers collects nothing; the refusal rides `parseErrors`, and the
  # empty `branchTrace` makes a flip `cfoUnmodelable`.
  let hostRefusal = hostAdmission()
  if hostRefusal.isSome:
    result.parseErrors = @[hostRefusedError(hostRefusal.get)]
    result.annotationViolations = prog.annotationViolations
    return
  # RFC-0016 S8cj: restore the thread's current context on every exit, as
  # `runSymex` does (this entry has no nested `try`, so CR-13's caveat about
  # a `finally` on the raise path does not apply).
  let prevCtx = currentContext()
  defer:
    satModels = @[]
    setCurrentContext(prevCtx)
  let prevStall = beginStallDeadline(settings.budget.queryTimeoutMs)  ## RFC-0016 INT-57
  defer: endStallDeadline(prevStall)
  let ctx = resetSymexRunState(settings)
  setUnionImageProgram(prog.fieldImage)   ## RFC-0016 int6-f, before any allocation
  var counters: ConcolicYieldCounters
  let cappedLen = min(trace.len, maxDraws)
  if trace.len > maxDraws:
    counters.tracesTruncated = 1

  # ---- Step 2: draw-symbolication ----------------------------------------
  # Each of the first `cappedLen` recorded draws becomes a FRESH symbolic
  # Z3 variable, constrained by its OWN declared `ChoiceNode` constraint —
  # the "drawInteger(min,max) -> symbolic int with min <= v <= max" idea,
  # generalised over `ChoiceKind`. `concreteEq` pins each one to its
  # recorded concrete value, kept SEPARATE from `initialPC` (never asserted
  # onto the live path) so the draws stay free for a later G2 flip-solve.
  var drawVars = newSeq[SymVal](cappedLen)
  var drawOverrides = newSeq[Option[SymVal]](cappedLen)
    ## Issue #163 review R24/R25 — see `ConcolicCollectResult.drawOverrides`'s
    ## own doc comment for the full rationale.
  var initialPC: seq[Z3Bool]
  var concreteEq: seq[Z3Bool]
  for i in 0 ..< cappedLen:
    let node = trace[i]
    case node.kind
    of ckInteger:
      if concolicIntRepresentable(node):
        let v = mkIntVar("nelliConcolicDraw" & $i)
        initialPC.add(v >= mkZ3IntLit(toInt64(node.intC.min)))
        initialPC.add(v <= mkZ3IntLit(toInt64(node.intC.max)))
        concreteEq.add(v == mkZ3IntLit(toInt64(node.intVal)))
        drawVars[i] = SymVal(kind: svInt, zi: v)
        inc counters.drawsSymbolicated
      else:
        # R1: e.g. the stock `uint64`/`uint` strategy's full-range draw —
        # narrowing `min`/`max`/`intVal` through `toInt64` here would wrap
        # and emit a corrupt (possibly inverted/unsatisfiable) Z3 domain.
        # Not modelable this run: leave `drawVars[i]` at its zero value
        # (never read — same convention `ckFloat`/`ckBytes`/`ckString`
        # use below) and let any linked parameter binding concretize.
        inc counters.nonInt64Draws
    of ckBoolean:
      let v = mkBoolVar("nelliConcolicDraw" & $i)
      if node.boolC.p <= 0.0:
        initialPC.add(v == false)
      elif node.boolC.p >= 1.0:
        initialPC.add(v == true)
      concreteEq.add(v == node.boolVal)
      drawVars[i] = SymVal(kind: svBool, bo: v)
      inc counters.drawsSymbolicated
    of ckFloat, ckBytes, ckString:
      # Walker-boundary concretization: G1b's fragment does not yet
      # symbolicate these kinds. Any parameter bound to this draw index
      # concretizes below (`paramsConcretized`) — no crash, no symbolic var.
      inc counters.unsupportedDrawKinds

  # ---- Bind property parameters per `bindings` ---------------------------
  proc concretizeFromChoiceNode(ty: IRType, node: ChoiceNode, useBV: bool): SymVal =
    case ty.kind
    of itBool: SymVal(kind: svBool, bo: mkBool(node.kind == ckBoolean and node.boolVal))
    else:
      # R1: guard the narrowing — an int64-unrepresentable concrete value
      # (e.g. the upper half of a uint64 draw) falls back to the same
      # `0'i64` ground literal the non-ckInteger case already uses. Sound
      # under this bridge's own contract (RFC §G-concolic: "a wrong model
      # wastes one candidate", every candidate is re-verified concretely
      # before admission) — never a crash. Issue #163 R16: representation
      # (`useBV`) is decided by the PARAM's own declared type, same as
      # every other binding path below, so this fallback never straddles a
      # different representation than the transparent path would have used.
      let v = if node.kind == ckInteger and node.intVal.fitsInt64:
                toInt64(node.intVal)
              else: 0'i64
      concolicScalarLiteral(ty, useBV, v)

  var env: Env
  for i, p in prog.params:
    let b = bindings[i]
    # Issue #163 review finding R16. Every concolic-bound scalar `itInt`
    # param used to bind as an idealized, non-wrapping Z3Int regardless of
    # its declared width/signedness — `concreteBranchOutcome` then evaluated
    # arithmetic under EXACT semantics even for a type whose real Nim
    # arithmetic wraps (unsigned) or truncates before it ever reaches
    # int64's own bounds (a narrower signed width with no proven range),
    # producing a branch decision that can disagree with the real concrete
    # execution the trace claims to record (see this file's Section D for
    # the measured repro). `useBV` decides, once per param, which
    # representation `lowerArith`/`lowerBool` — shared, unmodified, between
    # `wmExplore` and `wmFollowConcrete` — will use for every occurrence of
    # this param below.
    let useBV = p.ty.kind == itInt and
                not concolicScalarPromotesSoundly(p.ty, settings)
    case b.kind
    of cbDrawLinked:
      let transparentAndInBounds =
        b.drawIndex >= 0 and b.drawIndex < cappedLen and
        ((p.ty.kind == itInt and trace[b.drawIndex].kind == ckInteger and
          concolicIntRepresentable(trace[b.drawIndex])) or
         (p.ty.kind == itBool and trace[b.drawIndex].kind == ckBoolean))
      if transparentAndInBounds:
        if useBV:
          # R16: the draw's own symbolic var (`drawVars[b.drawIndex]`) stays
          # an unbounded Z3Int (Step 2 symbolicates every draw the same way,
          # independent of which param it may be linked to) — aliasing it
          # directly here, as the sound branch below still does, would
          # reintroduce exactly this finding's bug. Bind a FRESH,
          # width/signedness-faithful BV variable instead, and pin it to
          # the trace's own recorded concrete value directly (no
          # `int2bv`/`bv2int` bridge to the draw var — see `bvEqConst`).
          #
          # Issue #163 review R24: a `concolicFlip` targeting a decision
          # that reads THIS param builds its flip formula from `env[p.name]`
          # (this fresh `bv`, since that's what the walker actually lowers a
          # reference to this param through) — so record `bv` in
          # `drawOverrides[b.drawIndex]` for `materializeConcolicModel` to
          # read back from, instead of the disconnected, never-referenced
          # `drawVars[b.drawIndex]` Z3Int. Also carry the draw's OWN
          # declared `[min, max]` onto `bv` (Step 2 gives `drawVars[i]` the
          # same bound over its Z3Int representation) — a BV's bit width
          # alone bounds it no tighter than the type's full range, which can
          # be far wider than the strategy's own declared draw range, and an
          # un-narrowed flip target only gets clamped back down at
          # materialization (same accepted "clamp can undo the flip" cost
          # the optimistic-relaxation path already documents), not rejected.
          let bv = bvVar(p.ty, p.name)
          let node = trace[b.drawIndex]
          concreteEq.add bvEqConst(bv, toInt64(node.intVal))
          # [range-invariant: concolic-trace-interval -- bounds come from the
          # TRACE node's recorded per-draw interval (`node.intC`), not from the
          # type's declared range, so `rangeCondsIfNeeded` (which reads
          # `ty.rangeLo`/`ty.rangeHi`) is not the applicable helper. The value
          # is a BV by construction (`bvVar` always yields a BV kind).]
          for c in bvRangeConds(bv, toInt64(node.intC.min),  # [range-invariant: concolic-trace-interval]
                                toInt64(node.intC.max), p.ty.signed):
            initialPC.add c
          drawOverrides[b.drawIndex] = some(bv)
          env[p.name] = bv
        else:
          # Issue #163 review R26: stamp the param's static Nim width/
          # signedness onto a FRESH copy (never mutate the shared
          # `drawVars[b.drawIndex]` itself — `tConjuncts`/another binding's
          # own affine formula may still read that SAME draw index in its
          # bare, unstamped form within this same collect call) so
          # `overflowCondInt` (#161) can fork for a concolic-bound Z3Int
          # param exactly as it already does for `wmExplore`'s own
          # `promoteSound` route. Only meaningful for `itInt` — an `itBool`
          # binding takes this same branch (a bool param is never `useBV`)
          # and keeps its plain `svBool` `drawVars` entry untouched.
          if p.ty.kind == itInt:
            env[p.name] = SymVal(kind: svInt, zi: drawVars[b.drawIndex].zi,
                                 ziWidth: p.ty.width, ziSigned: p.ty.signed)
          else:
            env[p.name] = drawVars[b.drawIndex]
      else:
        # Truncated past the cap (still a real draw, just not symbolicated
        # this run) or a kind mismatch — concretize to the recorded value
        # rather than crash; still sound (a ground literal).
        inc counters.paramsConcretized
        if b.drawIndex >= 0 and b.drawIndex < trace.len:
          env[p.name] = concretizeFromChoiceNode(p.ty, trace[b.drawIndex], useBV)
        elif p.ty.kind == itBool:
          env[p.name] = SymVal(kind: svBool, bo: mkBool(false))
        else:
          env[p.name] = concolicScalarLiteral(p.ty, useBV, 0'i64)
    of cbConcretized:
      inc counters.paramsConcretized
      case p.ty.kind
      of itBool: env[p.name] = SymVal(kind: svBool, bo: mkBool(b.concreteBool))
      else:      env[p.name] = concolicScalarLiteral(p.ty, useBV, b.concreteInt)
    of cbTransformLinked:
      # RFC-fuzzer-nextgen G6. Only itInt parameters are transform-linked
      # (the transparency descriptor's affine/predicated categories are
      # int-only — `smt/transparency.nim`'s own doc); `p.ty.kind == itBool`
      # bound this way is a classifier bug, not a runtime possibility, so
      # it degrades the same as an out-of-range/kind-mismatched draw would.
      let transparentAndInBounds =
        b.tDrawIndex >= 0 and b.tDrawIndex < cappedLen and
        p.ty.kind == itInt and trace[b.tDrawIndex].kind == ckInteger and
        concolicIntRepresentable(trace[b.tDrawIndex])
      if transparentAndInBounds:
        if useBV:
          # Issue #163 review R25 (was: concretize to a ground literal,
          # sacrificing this param's flip-ability — see the historical note
          # this replaces, in git blame, for the original R16 reasoning).
          #
          # The `int2bv`/`bv2int` hazard this originally avoided is real
          # (`runtime_floats.nim`'s F5 note), but it is specifically about
          # BRIDGING one Z3 AST between the Int and BV sorts mid-formula —
          # it says nothing against building the affine expression NATIVELY
          # in BV theory from a FRESH BV variable that independently stands
          # in for the draw, the same move R24 already makes for a direct
          # `cbDrawLinked` binding. `bvDraw` is that variable: pinned to the
          # draw's own recorded concrete value via `bvEqConst` (a ground
          # equality against a same-sort literal — never a bridge), then
          # combined with `tA`/`tB` (also lifted to the SAME BV sort) via
          # ordinary same-width BV `+`/`*` (`binBV`). No Int-sorted AST is
          # ever touched. `env[p.name]` stays genuinely symbolic (a flip can
          # find it a new value), and `drawOverrides[b.tDrawIndex] = bvDraw`
          # lets `materializeConcolicModel` read the solved DRAW value back
          # (not the transformed param value) — mirroring R24 exactly.
          #
          # Deliberately UNCHANGED for a draw index also carrying its own
          # `tConjuncts` (the `dkPredicated`/filter case, which reuses this
          # SAME `tDrawIndex` as each conjunct's own `drawIndex` — see
          # `concolic.nim`'s `bindingExprFor`): those conjuncts still read
          # `drawVars[c.drawIndex].zi` below, unaffected by `bvDraw` (a
          # SEPARATE, independently-pinned symbol for the same underlying
          # value, exactly `bvEqConst`'s own established convention) — a
          # flip may therefore land `bvDraw` on a value the ORIGINAL filter
          # predicate would have rejected, which is sound-but-wasteful
          # (Track E re-verifies concretely downstream), not unsound, and
          # matches this driver's existing "a dropped/inapplicable
          # constraint only ever widens the solution set" contract.
          let node = trace[b.tDrawIndex]
          let bvDraw = bvVar(p.ty, "nelliConcolicTransformDraw" & $b.tDrawIndex)
          concreteEq.add bvEqConst(bvDraw, toInt64(node.intVal))
          # [range-invariant: concolic-trace-interval -- as above: the trace
          # node's recorded interval, not the type's declared range.]
          for c in bvRangeConds(bvDraw, toInt64(node.intC.min),  # [range-invariant: concolic-trace-interval]
                                toInt64(node.intC.max), p.ty.signed):
            initialPC.add c
          drawOverrides[b.tDrawIndex] = some(bvDraw)
          let tABV = bvConst(p.ty, b.tA)
          let tBBV = bvConst(p.ty, b.tB)
          env[p.name] = binBV(binBV(bvDraw, tABV, `*`), tBBV, `+`)
        else:
          let dv = drawVars[b.tDrawIndex].zi
          # Issue #163 review R26: stamp width/signedness on this route too
          # — see the `cbDrawLinked` non-`useBV` arm's own comment above for
          # the full rationale (identical here, just a computed rather than
          # a bare `svInt`).
          env[p.name] = SymVal(kind: svInt, zi: mkZ3IntLit(b.tA) * dv + mkZ3IntLit(b.tB),
                               ziWidth: p.ty.width, ziSigned: p.ty.signed)
        # Extra conjuncts (the filter/branching-guard predicate) — each
        # independently bounds-checked: a conjunct naming a draw outside
        # the symbolicated fragment is DROPPED rather than crashing or
        # concretizing the whole binding — dropping a constraint only
        # widens the solution set (sound: Track E re-verifies every
        # candidate concretely downstream, so a wasted candidate is the
        # only possible cost, never a false claim). A conjunct naming an
        # int64-unrepresentable draw (R1) is dropped the same way — that
        # draw was never symbolicated, so `drawVars[c.drawIndex]` would not
        # hold a real Z3 var. Unaffected by `useBV`: these conjuncts
        # constrain OTHER draws' Int-sorted symbolic vars, never this
        # param's own env binding.
        for c in b.tConjuncts:
          if c.drawIndex >= 0 and c.drawIndex < cappedLen and
             trace[c.drawIndex].kind == ckInteger and
             concolicIntRepresentable(trace[c.drawIndex]):
            let cv = drawVars[c.drawIndex].zi
            let lhs = mkZ3IntLit(c.a) * cv + mkZ3IntLit(c.b)
            let rhsLit = mkZ3IntLit(c.lit)
            let conj =
              case c.op
              of ccoEq: lhs == rhsLit
              of ccoNe: lhs != rhsLit
              of ccoLt: lhs <  rhsLit
              of ccoLe: lhs <= rhsLit
              of ccoGt: lhs >  rhsLit
              of ccoGe: lhs >= rhsLit
            initialPC.add(conj)
      else:
        inc counters.paramsConcretized
        if b.tDrawIndex >= 0 and b.tDrawIndex < trace.len:
          env[p.name] = concretizeFromChoiceNode(p.ty, trace[b.tDrawIndex], useBV)
        else:
          env[p.name] = concolicScalarLiteral(p.ty, useBV, 0'i64)

  # ---- Step 3: follow the concrete trace, collecting modelable constraints
  let exitClock = newExitClock()
  var w = WalkCtx(
    extHardMark: -1,   ## RFC-0005 S8ax: no depth extension under way
    exitClock: exitClock, topExits: exitClock.newExits(CallExits),
    frame: initCallFrameCtx(exitClock),
    z3: ctx,
    target: SymexTarget(kind: stkLabel, label: "__nelli_concolic_unreached__"),
    params: prog.params, mode: wmFollowConcrete,
    found: @[], settings: settings, procs: prog.procs,
    callStack: @[], callStats: initTable[string, CallStat](),
    callCache: initTable[string, seq[CallCacheEntry]](),
    activeCalls: initHashSet[string](), initialEnv: env,
    concreteEq: concreteEq,
    statics: WalkerStatics(exnTable: exnTypeTable,
                           userExnHierarchy: prog.userExnHierarchy,
                           sutRetTy: prog.retTy,
                           globals: globalsTable(prog.globals)),  ## S8as
  )
  currentLowerSinks = addr w.sinks
  currentWalkCtxPtr = addr w
  let initial = initialWalkPath(initialPC, env)
  # RFC-0005 S8j: a path that left through the SUT's own `return` is a
  # normal exit too; its constraints join the soundness pin below.
  let resultPaths =
    walk(prog.body, @[initial], w) & w.topExits.returnedPaths.contents
  currentLowerSinks = nil
  currentWalkCtxPtr = nil
  # RFC-0005 S1c: the walk-end pending-taint leak pin, exactly as
  # `runSymexImpl` runs it. This driver used to skip it, so a lowering
  # degrade whose path taint was never drained stayed in the
  # lowering queue threadvar after the collect returned (reset only at
  # the NEXT run's entry) and went uncounted. The stamp records a classified
  # `weInternalWalkerFault` into `w.walkDegradeErrors`, which the
  # `walkDegradeCount` read below picks up, and clears the residue.
  stampLoweringPendingLeak(w)
  counters.ambiguousBranches = w.concolicAmbiguousBranches
  counters.ambiguousByConstruct = w.concolicAmbiguousByConstruct
  # Issue #163 audit finding W10: this driver used to read neither
  # `w.walkDegradeErrors` nor `w.sawUnknown` — `runSymexImpl` names the
  # opaque call that cost the answer via `exnWarnings` (below), but a
  # concolic collect silently discarded the same classified degrade. Diagnostics
  # only (never a verdict here); dedup by message, exactly the `exnWarnings`
  # drain's own rule.
  #
  # #163 review R9: `runSymexImpl` drains TWO parallel sinks into
  # `exnWarnings` -- `w.walkDegradeErrors` (WalkCtx-field, written by walker
  # sites with a `w: var WalkCtx` in scope) AND `loweringDegradeErrors` (a
  # THREADVAR, written by lowering sites with no `WalkCtx` in local scope,
  # e.g. `cmpString`'s string-ordering degrade) -- each deduped by message in
  # its OWN `HashSet` (mirrored below, not merged into one set: a message
  # appearing in both sinks is vanishingly unlikely in practice, since the two
  # sinks are written by disjoint call sites, and this keeps the exact
  # per-sink dedup rule `runSymexImpl` already uses rather than introducing a
  # new cross-sink one). This counter used to read ONLY `w.walkDegradeErrors`
  # -- `resetSymexRunState` resets `loweringDegradeErrors` at this driver's
  # own entry, so the threadvar sink IS live during a concolic walk, but its
  # contents were never read back here. An unmodelled lowering-site op (e.g.
  # string ordering, S3-pending) therefore reported `walkDegradeCount == 0`,
  # indistinguishable from a genuinely clean collect.
  counters.walkDegradeCount = dedupedMsgCount(w.walkDegradeErrors) +
                              dedupedMsgCount(loweringDegradeErrors)
  # Issue #163 round 10 (Design F1/F3, Liveness F1): `obligationLog` and
  # `prog.parseErrors` were already read into `ConcolicCollectResult.
  # obligations`/`.parseErrors` below, but those two fields had no consumer
  # anywhere on the production path (`runConcolicFlipImpl` forwards only
  # `.counters`, never `.obligations`/`.parseErrors`). Fold each into a
  # counter HERE, alongside `walkDegradeCount` above, so it rides the SAME
  # already-live `counters` -> `ConcolicFlipResult.collectCounters` ->
  # `foldFlipResult` -> `Orchestrator.concolicYield` chain every other
  # counter on this object already travels — see `ConcolicYieldCounters.
  # obligationsLive`/`.parseDeclines` (`smt/concolictaxonomy.nim`) for the
  # full rationale, including why a parse decline counts but never gates
  # admission.
  for o in obligationLog:
    if o.disposition == odLive: inc counters.obligationsLive
  for e in prog.parseErrors:
    if e.severity == sevError: inc counters.parseDeclines

  # ---- Soundness pin: the collected constraints ARE satisfied by the
  # original concrete draws (RFC: "feed them back to Z3 ... check
  # directly") — checked here so callers/tests get a plain bool. ----------
  # RFC-0005 S8o: bounded like the branch-outcome solves beside it
  # (`concreteBranchRLimit`), with their `random_seed`. It had no bound at
  # all. An exhausted bound is `zsUnknown`, reported `false`: not proven,
  # never a claim.
  # RFC-0005 S8by: in a context of its own (`concreteScratchCheck`).
  var pinned = initialPC & concreteEq
  for p in resultPaths:
    for c in p.pc: pinned.add c
  # RFC-0005 S8ag: a split's Int is free without its axioms.
  result.pcSatByConcreteInputs = concreteScratchCheck(ctx,
    pinned & indexSplitRoots(ctx, pinned), settings) == zsSat
  result.counters = counters
  result.branchTrace = w.branchTrace
  result.soundBranches =
    if w.followCut: w.followCutAt else: w.branchTrace.len
  drainDedupedByMsg(result.errors, w.walkDegradeErrors)
  drainDedupedByMsg(result.errors, w.heapDepthErrors)
  drainDedupedByMsg(result.errors, w.newFieldZeroErrors)
  drainDedupedByMsg(result.errors, w.sinks.closureCallErrors)
  drainDedupedByMsg(result.errors, loweringDegradeErrors)
  result.definedFacts = w.definedFacts
  result.drawVars = drawVars
  result.drawOverrides = drawOverrides
  # Issue #163 review R26 (continued) + the parse-error gap. Both fields'
  # own doc comments (`ConcolicCollectResult`, above) give the full
  # rationale; the short version: `obligationLog` is the SAME per-run
  # threadvar `resetSymexRunState` (this proc's own entry, above) resets and
  # `runSymexImpl` drains into `RawResult.obligations` on every verdict
  # branch, so reading it here reflects only THIS collect, not a stale one
  # from an earlier call. `prog.parseErrors` needs no draining at all — it
  # is a plain field on the `SymexProgram` this call was handed, populated
  # once at parse time.
  result.obligations = obligationLog
  result.parseErrors = prog.parseErrors
  result.annotationViolations = prog.annotationViolations   # RFC-0005 S8

# ---- RFC-fuzzer-nextgen G2: branch-flip solve + materialization -----------
#
# Builds on `runConcolicCollectImpl` (G1b) unchanged — this section adds RFC
# §G-concolic steps 4-5 on top of its `branchTrace`/`drawVars` output:
#   4. formula = (prefix constraints up to the target branch) AND (negated
#      target predicate); ask Z3 for a model. UNSAT/timeout falls back to a
#      BOUNDED optimistic relaxation (drop prefix conjuncts in a fixed,
#      deterministic, reverse-collection order — never a 2^n subset search —
#      each attempt capped by the SAME per-query Z3 timeout as the exact
#      attempt). `maxRelaxationAttempts` bounds total attempts regardless of
#      how large the prefix is: termination is by construction (a fixed loop
#      count over one-shot bounded Z3 checks), not a property of the formula.
#   5. A SAT model's per-draw value, read off `drawVars` and CLAMPED back into
#      that draw's OWN declared constraints, reconstructs a `ChoiceNode` via
#      the SAME constructors (`integerChoice`/`booleanChoice`) the original
#      draw used — structurally valid by construction. A draw the model
#      didn't need to move (or one past the collection cap) keeps its
#      original concrete value verbatim.
# The clamp in step 5 is why "solved" does not imply "the intended edge is
# actually covered": an optimistic attempt may have solved by dropping a
# draw's OWN range bound, and clamping the result back into that range can
# silently undo the very flip the solve found. That is exactly the case the
# RFC's soundness argument covers ("Track E re-verifies concretely — a bad
# seed is discarded downstream, never trusted") — so this module re-verifies
# cheaply itself, by re-collecting on the materialized seed and checking
# whether the SAME decision now took the previously-untaken arm, and reports
# the outcome as part of the yield taxonomy rather than silently trusting it.

# `ConcolicFlipOutcome`/`ConcolicCoverageOutcome`/`ConcolicFlipCounters`/
# `ConcolicFlipResult` moved to the leaf module `./concolictaxonomy`
# (R28/R29b) — see that module's doc comment. Re-exported above, so this is
# a pure move; every arm/field name is unchanged.

const defaultMaxRelaxationAttempts* = 8
  ## RFC-fuzzer-nextgen G2 (round-2 feasibility fix): a FIXED bound on
  ## optimistic-relaxation attempts — the mechanism that keeps a
  ## pathological/fully-unsolvable case from hanging or enumerating a `2^n`
  ## conjunct-subset search. Each attempt is one bounded Z3 check.

const maxConcolicUndefined* = 8
  ## RFC-0016 K10a-concolic. The most undefined-behaviour reaches one flip
  ## solve reports (and so the most extra bounded checks it adds).

const defaultZ3TimeoutMs* = 2000'u
  ## RFC-fuzzer-nextgen G2: per-attempt Z3 wall-clock timeout (Z3's own
  ## `timeout` solver param, milliseconds) — applied to EVERY flip-solve
  ## attempt (exact included, not just the optimistic ones): Z3
  ## non-termination is the central hazard this slice exists to bound, and
  ## an exact attempt on an adversarial formula is exactly as capable of
  ## hanging as a relaxed one.
  ##
  ## R26: this bound alone is wall-clock, hence machine/load-dependent —
  ## whether it actually fires before Z3 decides depends on how fast the
  ## host is, so it cannot be used to deterministically PROVE `cfoTimedOut`
  ## in a test. Callers who need a bound that exhausts identically on every
  ## machine set `settings.budget.queryRLimit` instead (or in addition):
  ## `flipCheck` applies it the same way `trySolve` and
  ## `concreteBranchOutcome` do (see `concreteBranchRLimit`'s doc). RFC-0016
  ## INT-33: this timeout caps the solve's `queryTimeoutMs`.

proc flipCheck(ctx: Z3Context; conjuncts: seq[Z3Bool]; target: Z3Bool;
               settings: SymexSettings; z3TimeoutMs: uint):
               tuple[status: Z3Status, m: Z3Model] =
  ## RFC-0016 INT-33 (R1-27, PRC-25). One flip solve, as a walker query:
  ## `conjuncts` and `target` with the run-wide facts every walker query
  ## asserts (`globalRoots`: the closure-call axioms, the entry values' type
  ## facts, the containers' cardinality, the string decompositions and the
  ## `str.indexof` splits), decided by `checkCapped` (the `maxSeqLen` caps,
  ## `seqQueryRLimit`, the regex limit sites) under `queryRLimit` and a
  ## `queryTimeoutMs` capped at the flip's own `z3TimeoutMs`. The bespoke
  ## solve this replaced asserted neither: a closure call's result was free
  ## there, so a flip set it to the flipped value and left the draws where
  ## they were. `queryRLimit` is one budget with the collect pass (G1b), so
  ## a caller wanting a deterministic `cfoTimedOut` needs one that starves
  ## this query and still lets the collect's concrete-pinned checks finish
  ## (`tests/tsymex_g2_flip.nim`'s R26 suite).
  ## The collect that built the formula restored the thread's context on its
  ## way out; the pools `globalRoots` drains are still its run's.
  var s = settings
  if z3TimeoutMs != 0'u and (s.budget.queryTimeoutMs == 0'u or
                             s.budget.queryTimeoutMs > z3TimeoutMs):
    s.budget.queryTimeoutMs = z3TimeoutMs
  let prevCtx = currentContext()
  let savedTimeout = queryTimeoutMsCur
  defer:
    setCurrentContext(prevCtx)
    queryTimeoutMsCur = savedTimeout
  setCurrentContext(ctx)
  queryTimeoutMsCur = s.budget.queryTimeoutMs
  var q = conjuncts
  q.add target
  let roots = q & globalRoots(q)
  inc symexZ3CallCount
  let r = checkCapped(ctx, roots, s, s.budget.queryRLimit)
  (r.status, r.m)

proc evalConcolicDrawInt64(m: Z3Model, sv: SymVal): int64 =
  ## Issue #163 review R24/R25. Evaluate a concolic draw's ACTUAL Z3
  ## representation — the idealized `svInt` Step 2 always allocates, or a
  ## `useBV` binding's own fresh BV variable (`drawOverrides`) — to its
  ## int64 value under a solved model. Unsigned BV kinds read via
  ## `evalUint` (not `evalInt`, which reads the top bit as a sign, wrong for
  ## e.g. a `uint8` value >= 128): mirrors `extractFromSymVal`'s own
  ## `sv.signed`-keyed split (above) for exactly the same reason. Every
  ## value this ever sees was, by construction of what put it in
  ## `drawVars`/`drawOverrides` in the first place, already proven to fit
  ## `int64` (`concolicIntRepresentable`), so the `uint64 -> int64`
  ## conversion for an unsigned BV never wraps.
  case sv.kind
  of svBV8:  (if sv.signed: int64(m.evalInt(sv.bv8))  else: int64(m.evalUint(sv.bv8)))
  of svBV16: (if sv.signed: int64(m.evalInt(sv.bv16)) else: int64(m.evalUint(sv.bv16)))
  of svBV32: (if sv.signed: int64(m.evalInt(sv.bv32)) else: int64(m.evalUint(sv.bv32)))
  of svBV64: (if sv.signed: int64(m.evalInt(sv.bv64)) else: int64(m.evalUint(sv.bv64)))
  of svInt:  m.evalInt(sv.zi)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: draw-representation-only reachability (drawVars/drawOverrides entries for a ckInteger draw are always svInt or a BV kind — see runConcolicCollectImpl's own construction sites)]
      "evalConcolicDrawInt64: not an int-representable SymVal — got " & $sv.kind)

proc materializeConcolicModel(m: Z3Model, trace: seq[ChoiceNode],
                              drawVars: seq[SymVal],
                              drawOverrides: seq[Option[SymVal]],
                              cappedLen: int
                             ): seq[ChoiceNode] =
  ## RFC §G-concolic step 5: each symbolicated draw's solved value, IN DRAW
  ## ORDER, reconstructed as a `ChoiceNode` via the SAME constructor (and
  ## therefore the SAME declared constraints) the original draw used — the
  ## result is a structurally-valid choice sequence BY CONSTRUCTION, not by
  ## post-hoc validation. The solved value is CLAMPED into the draw's own
  ## `[min, max]` first: a model is free to assign any value to a draw whose
  ## own range bound an optimistic attempt dropped, and `integerChoice`/
  ## `booleanChoice` would raise on an out-of-range value otherwise — clamping
  ## keeps construction total. A draw the model didn't touch (unsupported
  ## kind, int64-unrepresentable range/value — R1, `concolicIntRepresentable`
  ## — or past `cappedLen`) keeps its ORIGINAL concrete value verbatim.
  ##
  ## Issue #163 review R24: `drawOverrides[i]`, when set, names the variable
  ## a `useBV` param binding ACTUALLY built `env[p.name]` from for this draw
  ## — the one a flip formula's branch predicate genuinely constrains — and
  ## is read here IN PREFERENCE to `drawVars[i]`'s plain, disconnected
  ## Z3Int. See `ConcolicCollectResult.drawOverrides`'s own doc comment.
  result = trace
  for i in 0 ..< cappedLen:
    case trace[i].kind
    of ckInteger:
      if concolicIntRepresentable(trace[i]):
        let lo = toInt64(trace[i].intC.min)
        let hi = toInt64(trace[i].intC.max)
        let src = if i < drawOverrides.len and drawOverrides[i].isSome:
                    drawOverrides[i].get
                  else: drawVars[i]
        let solved = clamp(evalConcolicDrawInt64(m, src), lo, hi)
        result[i] = integerChoice(solved, lo, hi, toInt64(trace[i].intC.shrinkTowards))
      else:
        discard   ## R1: not symbolicated (int64-unrepresentable range or
                  ## concrete value — see `concolicIntRepresentable`), so
                  ## `drawVars[i]` holds no real Z3 var to evaluate; keep
                  ## the ORIGINAL concrete value verbatim, same as the
                  ## unsupported-kind case below.
    of ckBoolean:
      let solved = m.evalBool(drawVars[i].bo)
      result[i] = booleanChoice(solved, trace[i].boolC.p)
    of ckFloat, ckBytes, ckString:
      discard   ## not symbolicated by G1b; `result[i]` already holds the
                ## original node from the `result = trace` copy above.

proc runConcolicFlipImpl*(prog: SymexProgram, trace: seq[ChoiceNode],
                          bindings: seq[ConcolicParamBinding],
                          targetBranchIndex: int,
                          settings: SymexSettings = defaultSymexSettings(),
                          maxDraws: int = defaultMaxConcolicDraws,
                          maxRelaxationAttempts: int = defaultMaxRelaxationAttempts,
                          z3TimeoutMs: uint = defaultZ3TimeoutMs
                         ): ConcolicFlipResult =
  ## RFC-fuzzer-nextgen G2 steps 4-5, built entirely on `runConcolicCollectImpl`
  ## (G1b, called once here — no re-implementation of draw-symbolication or
  ## concrete-trace following). `targetBranchIndex` is the caller-supplied
  ## designator (G2 scope — G3 wires frontier-stall selection on top of this
  ## later): an index into the collected `branchTrace`, i.e. the Nth `if`
  ## decision encountered along the concrete replay.
  let collected = runConcolicCollectImpl(prog, trace, bindings, settings, maxDraws)
  result.collectCounters = collected.counters
  result.annotationViolations = collected.annotationViolations   # RFC-0016 K8-0

  template finish(o: ConcolicFlipOutcome, c: ConcolicCoverageOutcome) =
    result.outcome = o
    result.coverage = c
    result.soundness = Soundness(replay: rsNotNeeded)
    drainRunTaint(result.soundness, [collected.parseErrors, collected.errors],
      extra = (if result.undefinedReached.len > 0: {scIncomplete} else: {}))
    for u in result.undefinedReached:
      result.soundness.witnessUndefined.incl ubOrdinals({u.kind})
    inc result.flipCounters.byOutcome[o]
    inc result.flipCounters.byCoverage[c]
    return result

  # RFC-0016 K7c: a decision past a follow cut is on a continuation the
  # trace never takes; it is not offered as a flip target.
  if targetBranchIndex < 0 or targetBranchIndex >= collected.soundBranches:
    finish(cfoUnmodelable, ccoNotApplicable)

  let target = collected.branchTrace[targetBranchIndex]
  let ctx = target.observedTruth.ctx   ## any Z3 AST carries its own context —
                                        ## no need to thread `Z3Context` separately.
  # RFC-0016 K10a-concolic (section 9.1 item 1). The flip's input is a native
  # run's, so it must keep every operation on the prefix and in the target's
  # own condition DEFINED: those facts (`definedFacts`, `at <= target`) are in
  # EVERY attempt, the optimistic ones included, which drop only prefix
  # conjuncts. The other disjunct, an input that makes one of the target
  # condition's operations undefined, is solved after the seed and reported
  # (never used as a seed).
  var definedNow: seq[Z3Bool]
  var targetOps: seq[ConcolicDefinedFact]
  for f in collected.definedFacts:
    if f.at <= targetBranchIndex:
      definedNow.add(not f.cond)
      if f.at == targetBranchIndex: targetOps.add f
  let negatedTarget = mkAnd(@[not target.observedTruth] & definedNow)

  # ---- Attempt 0: exact — prefix AND negated-target, same bound as every
  # optimistic attempt (an exact query can hang just as easily as a relaxed
  # one — see the module-section comment). --------------------------------
  var model: Z3Model
  var solved = false
  var sawTimeout = false
  let (exactStatus, exactModel) = flipCheck(ctx, target.prefixPc, negatedTarget,
                                             settings, z3TimeoutMs)
  case exactStatus
  of zsSat:
    model = exactModel
    solved = true
  of zsUnknown:
    sawTimeout = true
  of zsUnsat:
    discard

  # ---- Bounded optimistic fallback: drop prefix conjuncts in REVERSE-
  # COLLECTION order (deterministic, linear, never a 2^n subset search) —
  # attempt k drops the LAST k conjuncts. Stops at `maxRelaxationAttempts`
  # OR once the prefix is fully drained, whichever is smaller: EITHER bound
  # alone guarantees this loop runs a bounded, fixed number of one-shot
  # timed-out-capped Z3 checks and then gives up. -------------------------
  var attemptsUsed = 0
  if not solved:
    let n = target.prefixPc.len
    var k = 1
    while k <= maxRelaxationAttempts and k <= n:
      let relaxed = target.prefixPc[0 ..< (n - k)]
      inc attemptsUsed
      let (r, m) = flipCheck(ctx, relaxed, negatedTarget, settings, z3TimeoutMs)
      case r
      of zsSat:
        model = m
        solved = true
      of zsUnknown:
        sawTimeout = true
      of zsUnsat:
        discard
      if solved: break
      inc k
  result.flipCounters.relaxationAttemptsUsed = attemptsUsed

  # The second disjunct: each operation of the target's condition whose
  # undefined side the prefix allows. The prefix is NOT relaxed here (an
  # undefined side reached only by dropping a constraint is no finding).
  # The walk already put each operation's defined side into the path it
  # continued on (`drainArithTraps`), so the prefix would exclude the very
  # side asked for: the operation's own defined side, and the later ones
  # (an undefined operation ends the path before they run), are taken out.
  var seenUb: seq[(UbKind, string)]
  for i, f in targetOps:
    if result.undefinedReached.len >= maxConcolicUndefined: break
    if (f.kind, f.site) in seenUb: continue
    var reach: seq[Z3Bool]
    for c in target.prefixPc:
      var own = false
      for g in targetOps[i .. ^1]:
        if astEqual(c, not g.cond) or astEqual(not c, g.cond): own = true
      if not own: reach.add c
    let (st, sm) = flipCheck(ctx, reach, f.cond, settings, z3TimeoutMs)
    if st == zsSat:
      seenUb.add (f.kind, f.site)
      result.undefinedReached.add ConcolicUndefined(
        kind: f.kind, site: f.site,
        input: materializeConcolicModel(sm, trace, collected.drawVars,
          collected.drawOverrides, min(trace.len, maxDraws)))
      inc result.flipCounters.undefinedReached

  if solved:
    let cappedLen = min(trace.len, maxDraws)
    result.materialized = materializeConcolicModel(model, trace, collected.drawVars,
                                                   collected.drawOverrides, cappedLen)
    let outcome = if attemptsUsed == 0: cfoSolvedExact else: cfoSolvedOptimistic
    # ---- Coverage split: re-collect on the materialized seed and check
    # whether the SAME decision index now took a DIFFERENT arm. -----------
    let replay = runConcolicCollectImpl(prog, result.materialized, bindings, settings, maxDraws)
    let coverage =
      if targetBranchIndex < replay.soundBranches and
         replay.branchTrace[targetBranchIndex].armTaken != target.armTaken:
        ccoIntendedCovered
      else:
        ccoUnrelatedCoverage
    finish(outcome, coverage)
  elif sawTimeout:
    finish(cfoTimedOut, ccoNotApplicable)
  else:
    finish(cfoUnsat, ccoNotApplicable)

# ---- Raw → typed witness ----------------------------------------------------
#
# Per-width readers used by the macro's tuple-construction. The macro
# selects the right reader based on the param's IRType.

proc readBool*(w: RawWitness, name: string): bool =
  w.boolVals[name]

# Phase 15 F7: bit-exact float witness readers. Index the float tables
# populated by `extractLeaf`'s `evalFloat64Opt`/`evalFloat32Opt` path; the
# stored value round-trips every IEEE-754 bit pattern (NaN, ±Inf, ±0).
proc readFloat*(w: RawWitness, name: string): float = w.float64Vals[name]
proc readFloat32*(w: RawWitness, name: string): float32 = w.float32Vals[name]

proc readHeapSnapshot*(w: RawWitness): seq[HeapSnapshotEntry] = w.heapSnapshot
  ## Phase 15 R12. Public accessor for the heap-snapshot witness (RawWitness is
  ## not an exported type, so the `symexFind` macro reaches the field through
  ## this proc). Empty for a SUT with no ref/ptr params.

# Signed widths return the matching Nim signed type.
proc readInt*(w: RawWitness,   name: string): int   = int(  w.intVals[name])
proc readInt8*(w: RawWitness,  name: string): int8  = int8( w.intVals[name])
proc readInt16*(w: RawWitness, name: string): int16 = int16(w.intVals[name])
proc readInt32*(w: RawWitness, name: string): int32 = int32(w.intVals[name])
proc readInt64*(w: RawWitness, name: string): int64 =       w.intVals[name]

# Unsigned widths.
proc readUInt*(w: RawWitness,   name: string): uint   = uint(  w.uintVals[name])
proc readUInt8*(w: RawWitness,  name: string): uint8  = uint8( w.uintVals[name])
proc readChar*(w: RawWitness, name: string): char =
  ## RFC-0005 S8am (S8z's remainder, item 3). A Nim `char` witness: the SAME
  ## `uintVals` cell `readUInt8` reads (`char`/`byte`/`uint8` share one
  ## `itInt(width=8, signed=false)` Z3 representation -- `IRType.isChar`
  ## only distinguishes them at render-SITE selection, in `primTyAndReader`;
  ## the underlying model value is identical), reinterpreted as `char`.
  char(w.uintVals[name])
proc readUInt16*(w: RawWitness, name: string): uint16 = uint16(w.uintVals[name])
proc readUInt32*(w: RawWitness, name: string): uint32 = uint32(w.uintVals[name])
proc readUInt64*(w: RawWitness, name: string): uint64 =        w.uintVals[name]

proc readString*(w: RawWitness, name: string): string = w.strVals[name]

var cstringWitnessBufs {.threadvar.}: seq[ref string]
  ## RFC-0016 INT-87. The buffers `readCString` handed out, kept alive for
  ## the thread: a witness `cstring` addresses one, and the tuple holding it
  ## may outlive any scope the reader runs in.

proc readCString*(w: RawWitness, name: string): cstring =
  ## RFC-0016 INT-87. A `cstring` witness (`tCString`): nil, or a fresh
  ## buffer holding the model's bytes and the terminating NUL (a Nim string
  ## keeps one past its length).
  if not w.boolVals[name & ".nonNil"]: return nil
  let buf = new string
  buf[] = w.strVals[name & ".bytes"]
  cstringWitnessBufs.add buf
  cstring(buf[])

# ---- RFC-0005 S8h: ref witnesses built from the model's input heap ---------
#
# A `ref`/`ptr` position of the typed witness (a param, a field of a by-value
# param, a container element, a field of another cell) is resolved through
# the heap snapshot `buildHeapSnapshot` wrote: nil, the cell of another
# position (aliasing -- one Nim object per model address, bound to every
# position that holds it), or a cell of its own. A cell is allocated ONCE, and
# its fields are filled from the leaves the snapshot wrote under the cell's
# name (`<cell>.<field>`, or `<cell>` for a scalar pointee). The fill is a
# generic over the SUT's own Nim type (`fieldPairs`), so a recursive field, a
# cycle, a case object reached through a field and a ref inside a by-value
# field render the same way a top-level param does -- the IR never has to
# spell the pointee's fields out (a recursive field's IR pointee is an empty
# placeholder by construction).

type
  WitnessCellBuild* = proc (c: RefWitness; cell, leaves: string;
                            dst: pointer) {.nimcall.}
    ## RFC-0016 INT-81. Builds the cell `cell` as one Nim type (`buildCellAs`)
    ## into the ref slot `dst`, whatever the slot's static type is: the
    ## object is the cell's dynamic type, and a slot of an ancestor type
    ## holds it upcast.
  WitnessCellType = object
    ## RFC-0016 INT-81. A dynamic type a cell may have: its run-type tag
    ## codes at depths `1 ..` (`inheritTagCode` of each type of its chain
    ## below the root), and its builder (nil: no witness can name it).
    chain: seq[int64]
    build: WitnessCellBuild
  RefWitness* = ref object
    ## RFC-0005 S8h. One per rendered witness tuple, shared by every position
    ## in it: the snapshot's position -> cell map, and the cells built so far.
    w: RawWitness
    cellOf: Table[string, string]   ## position -> its cell's name ("" = nil)
    cells: Table[string, pointer]   ## cell name -> the object built for it
    types: seq[WitnessCellType]     ## RFC-0016 INT-81: `registerCellType`
    sortOf: Table[string, string]   ## RFC-0016 INT-88: position -> its sort
    sortSize: Table[string, int]    ## RFC-0016 INT-88: `registerPtrSize`
    rawCells: Table[string, pointer]  ## RFC-0016 INT-88: a cross-sort cell's
                                      ## allocation, made by a view of it
                                      ## before its owner filled it

proc newRefWitness*(w: RawWitness): RefWitness =
  ## RFC-0005 S8h. A position absent from the snapshot is nil: a nil field is
  ## rendered inline and gets no entry, and a field whose heap the winning
  ## path never materialised was never observed.
  result = RefWitness(w: w)
  for e in w.heapSnapshot:
    result.sortOf[e.name] = e.sort   # RFC-0016 INT-88
    result.cellOf[e.name] =
      if e.value == "nil": ""
      elif e.aliasRef.isSome: e.aliasRef.get
      else: e.name
  # RFC-0005 S8bh (item 2). A position aliasing a `ptr` cell that is itself
  # a field's address (`"&<cell>.<field>"`) aliases that address; S8bn
  # (item 2): likewise one aimed at a variable (`"@aim:<name>"`).
  var positions: seq[string]
  for pos in result.cellOf.keys: positions.add pos
  for pos in positions:
    let cell = result.cellOf[pos]
    if cell.len > 0 and cell != pos and result.cellOf.hasKey(cell) and
       (result.cellOf[cell].startsWith("&") or
        result.cellOf[cell].startsWith(ptrAimPrefix)):
      result.cellOf[pos] = result.cellOf[cell]

proc refElemPos*(container: string; i: int): string =
  ## RFC-0005 S8h. The position of element `i` of a `seq`/`array` of refs.
  container & "[" & $i & "]"

proc cellInt(c: RefWitness; path: string; v: var int64): bool =
  if c.w.intVals.hasKey(path): (v = c.w.intVals[path]; true) else: false
proc cellUInt(c: RefWitness; path: string; v: var uint64): bool =
  if c.w.uintVals.hasKey(path): (v = c.w.uintVals[path]; true) else: false
proc cellBool(c: RefWitness; path: string; v: var bool): bool =
  if c.w.boolVals.hasKey(path): (v = c.w.boolVals[path]; true) else: false
proc cellF32(c: RefWitness; path: string; v: var float32): bool =
  if c.w.float32Vals.hasKey(path): (v = c.w.float32Vals[path]; true) else: false
proc cellF64(c: RefWitness; path: string; v: var float64): bool =
  if c.w.float64Vals.hasKey(path): (v = c.w.float64Vals[path]; true) else: false

# Non-generic accessors: the generics below are instantiated in the caller's
# module, so they never touch `RefWitness`'s private fields directly.
proc cellNameOf(c: RefWitness; pos: string): string = c.cellOf.getOrDefault(pos, "")
# RFC-0005 S8ap: a string and a leaf-split seq / Table / HashSet cell field
# (`renderHeapCompound`), read under the same leaf names a by-value param
# of the type uses.
proc cellStr(c: RefWitness; path: string; v: var string): bool =
  if c.w.strVals.hasKey(path): (v = c.w.strVals[path]; true) else: false
proc cellSeqLen(c: RefWitness; path: string): int =
  c.w.seqLens.getOrDefault(path, -1)
proc cellTabKeys(c: RefWitness; path: string): seq[string] =
  c.w.tabKeys.getOrDefault(path)
proc cellHasTab(c: RefWitness; path: string): bool = c.w.tabKeys.hasKey(path)
proc cellSetMembers(c: RefWitness; path: string): seq[int64] =
  c.w.setMembers.getOrDefault(path)
proc cellBuilt(c: RefWitness; cell: string): pointer = c.cells.getOrDefault(cell, nil)
proc cellRecord(c: RefWitness; cell: string; p: pointer) = c.cells[cell] = p

proc registerPtrSize*(c: RefWitness; sort: string; size: int) =
  ## RFC-0016 INT-88. The byte size of the pointee of the `ptr` sort `sort`
  ## (`Ref_<type id>`); the witness tuple registers every `ptr` type its
  ## positions may hold (`emitWitnessTuple`), so a cell held at two sorts is
  ## allocated for the larger.
  c.sortSize[sort] = max(size, c.sortSize.getOrDefault(sort, 0))

proc cellBytes(c: RefWitness; cell: string; own: int): int =
  ## RFC-0016 INT-88. The bytes the `ptr` cell `cell` is allocated with: its
  ## position's own pointee size `own`, or the largest registered pointee
  ## of any position holding it.
  result = own
  for pos, cl in c.cellOf:
    if cl == cell:
      result = max(result, c.sortSize.getOrDefault(c.sortOf.getOrDefault(pos), 0))

proc cellForeignView(c: RefWitness; pos, cell: string): bool =
  ## RFC-0016 INT-88. The position `pos` holds the cell `cell` at another
  ## sort than the cell's owner does (`cast[ptr float](addr x)` beside
  ## `addr x`): it is a typed view of the owner's allocation, which the
  ## owner fills.
  let ps = c.sortOf.getOrDefault(pos)
  let cs = c.sortOf.getOrDefault(cell)
  pos != cell and ps.len > 0 and cs.len > 0 and ps != cs

proc cellAlloc(c: RefWitness; cell: string; own: int): pointer =
  ## RFC-0016 INT-88. The allocation of the `ptr` cell `cell`: the one a
  ## view made before its owner was built, or a fresh zeroed one of
  ## `cellBytes`. Unmanaged memory the witness owns for the rest of the
  ## process (nothing frees what a SUT is handed as a raw pointer).
  result = c.rawCells.getOrDefault(cell, nil)
  if result == nil:
    result = alloc0(cellBytes(c, cell, own))
    c.rawCells[cell] = result

proc registerCellType*(c: RefWitness; chain: seq[int64];
                       build: WitnessCellBuild) =
  ## RFC-0016 INT-81. A dynamic type a cell of this witness may have (see
  ## `cellDynBuild`); the witness tuple registers every type of the
  ## hierarchies its positions hold (`emitWitnessTuple`).
  c.types.add WitnessCellType(chain: chain, build: build)

proc cellDynBuild(c: RefWitness; leaves: string): WitnessCellBuild =
  ## RFC-0016 INT-81. The builder of the cell whose leaves are under
  ## `leaves`, as the dynamic type the model chose for it, or nil (build it
  ## as the position's static type). The snapshot writes the cell's run-type
  ## tag at each depth (`<cell>.@lvl<j>`) and the depth of the deepest
  ## static type among the positions that hold it (`<cell>.@floor`,
  ## `cellDynamicType`). The type is the deepest registered one whose chain
  ## the tags spell, no shallower than that floor: so it is a descendant of
  ## (or is) every position's static type, and a slot of any of them holds
  ## it. A tag the registered types do not spell is a type no test of the
  ## path named (the walk compares tags with the codes of the types it
  ## names), which the deepest spelled type stands for. A type the witness
  ## cannot name (nil builder) is skipped for the deepest nameable one;
  ## `witnessFidelity` classifies such a witness lossy.
  var floor = 0'i64
  if not cellInt(c, leaves & ".@floor", floor): return nil
  var lvls: seq[int64]
  var v: int64
  while cellInt(c, leaves & ".@lvl" & $(lvls.len + 1), v): lvls.add v
  var best = -1
  for i, t in c.types:
    if t.build == nil or int64(t.chain.len) < floor or
       t.chain.len > lvls.len:
      continue
    if t.chain != lvls[0 ..< t.chain.len]: continue
    if best < 0 or t.chain.len > c.types[best].chain.len: best = i
  if best < 0: nil else: c.types[best].build

var ptrAims {.threadvar.}: Table[pointer, string]
  ## RFC-0005 S8bn (item 2). Each `ptr` witness cell built for a position
  ## aimed at a variable (`"@aim:<name>"`), and that variable's IR name. A
  ## cell is unmanaged memory never freed, so its address names it for the
  ## rest of the process.

proc ptrAimRecord(cell: string; p: pointer) =
  if cell.startsWith(ptrAimPrefix): ptrAims[p] = cell[ptrAimPrefix.len .. ^1]

proc ptrAimsAt*(p: pointer; name: string): bool =
  ## RFC-0005 S8bn (item 2). The witness pointer `p` was aimed at the
  ## variable `name` (a global, or a `var` parameter of the SUT): the
  ## replay's splat (`emitWitnessSplat`) then hands it the address of the
  ## variable itself, which no witness cell can be.
  p != nil and ptrAims.getOrDefault(p, "") == name

proc ptrAimPath*(p: pointer; name: string): tuple[hit: bool; path: seq[string]] =
  ## RFC-0005 S8bn (item 4). The witness pointer `p` was aimed at a part of
  ## the variable `name` (`@aim:<name>/<step>/...`): the steps, each a field
  ## position, an element index, or a table key (`k<hex>`), for
  ## `ptrAimInto`.
  if p == nil: return
  let a = ptrAims.getOrDefault(p, "")
  if not a.startsWith(name & "/"): return
  result.path = a[name.len + 1 .. ^1].split('/')
  result.hit = true

{.push fieldChecks: off.}   # RFC-0005 S8bw (item 3): see `ptrAimByName`
proc ptrAimInto*[T; U](x: var T; path: seq[string]; i: int): ptr U =
  ## RFC-0005 S8bn (item 4). The address of the part of `x` the steps
  ## `path[i ..]` name (a field's position, an element's index, a table
  ## key), or nil.
  when T is U:
    if i == path.len: return addr x
  elif T is SomeInteger and U is SomeInteger and sizeof(T) == sizeof(U):
    # RFC-0005 S8bz (item 6): the other signedness at the same bytes
    # (`svMayHold` lists it).
    if i == path.len: return cast[ptr U](addr x)
  if i >= path.len: return nil
  when T is Table:
    if path[i].len >= 1 and path[i][0] == 'k':
      let key = try: parseHexStr(path[i][1 .. ^1]) except ValueError: ""
      when compiles(x.hasKey(key)):
        if x.hasKey(key):
          return ptrAimInto[typeof(x[key]), U](x[key], path, i + 1)
    return nil
  else:
    let n = try: parseInt(path[i]) except ValueError: -1
    when T is tuple or (T is object and not (T is ref)):
      # RFC-0005 S8bw (item 3): a case object's step names its field
      # (`f<name>`): `fieldPairs` walks only the active branch, so a
      # position is not one field (`ptrAimByName`). A discriminator is not
      # addressable (`when compiles`).
      if path[i].len >= 1 and path[i][0] == 'f':
        when T is object:
          let fname = path[i][1 .. ^1]
          ptrAimByName(x, fname):
            when compiles(ptrAimInto[typeof(it), U](it, path, i + 1)):
              return ptrAimInto[typeof(it), U](it, path, i + 1)
        return nil
      var k = 0
      for _, f in fieldPairs(x):
        when compiles(ptrAimInto[typeof(f), U](f, path, i + 1)):
          if k == n:
            return ptrAimInto[typeof(f), U](f, path, i + 1)
        inc k
    elif T is array or T is seq:
      var k = 0
      for e in x.mitems:
        if k == n:
          return ptrAimInto[typeof(e), U](e, path, i + 1)
        inc k
    nil
{.pop.}

proc storeOrdinal[F](f: var F; v: int64) =
  ## RFC-0005 S8cl (item 5; factored out of S8s's `validDefault`). `f = F(v)`,
  ## range-checked, written through its bytes: `F` can be an imported type whose
  ## C++ assignment is deleted. `std/atomics`' `Atomic[T]` on cpp holds `value:
  ## AtomicInt8`, an ordinal alias imported as `std::atomic<NI8>`, and an
  ## assignment there emitted a use of the deleted `std::atomic::operator=` (a
  ## cpp compile error in every SUT whose cell holds an `Atomic`,
  ## `tsymex_r6_n43_parity`).
  if v < int64(ord(low(F))) or v > int64(ord(high(F))):
    raise newException(RangeDefect, "value out of range: " & $v)  # [raise-audited: category-c: the check `F(v)` made implicitly, in reading a witness back, outside the walk]
  when sizeof(F) == 1:
    var lo = int8(v)
  elif sizeof(F) == 2:
    var lo = int16(v)
  elif sizeof(F) == 4:
    var lo = int32(v)
  else:
    var lo = v
  static: doAssert sizeof(lo) == sizeof(F)
  copyMem(addr f, addr lo, sizeof(F))

proc readCellField[F](c: RefWitness; path: string; f: var F)

{.push fieldChecks: off.}   # RFC-0005 S8bw (item 3): see `ptrAimByName`
proc cellRecordBranches[T](c: RefWitness; prefix: string; x: var T) =
  ## RFC-0005 S8bz (item 6). Each field's address under `prefix`, every
  ## branch's: a pointer the snapshot aims at a field of an inactive branch
  ## addresses that field's bytes all the same. `fieldPairs` walks only the
  ## active one. A discriminator is not addressable (`when compiles`).
  ptrAimEachField(x):
    when compiles(addr it):
      cellRecord(c, prefix & "." & itName, cast[pointer](addr it))
{.pop.}

proc validDefault[F](f: var F) =
  ## RFC-0005 S8h. A cell comes from `new`/`alloc0`, so every field starts
  ## zeroed, and zero need not lie inside a field's declared range
  ## (`range[10..20]`, an enum whose low is not 0). A field the model never
  ## observed does not affect the path, so any in-range value is faithful:
  ## `low(F)`. By-value aggregates are walked recursively, since a nested
  ## ranged subfield is zeroed too.
  when F is object or F is tuple:
    {.cast(uncheckedAssign).}:
      for _, fv in fieldPairs(f): validDefault(fv)
  elif F is array:
    for x in f.mitems: validDefault(x)
  elif F is SomeUnsignedInt or F is bool or F is char:
    discard
  elif F is Ordinal:
    if ord(f) < ord(low(F)) or ord(f) > ord(high(F)):
      storeOrdinal(f, int64(ord(low(F))))   # RFC-0005 S8s: not `f = low(F)`
  else:
    discard

proc fillCell[T: ref | ptr](c: RefWitness; cell, leaves: string; x: var T)

proc viewLeavesInto[V](c: RefWitness; path: string; x: var V) =
  ## RFC-0016 INT-90. The scalar leaves rendered under `path` for a typed
  ## view (`renderCrossSortViews`), each written into `x` in place; a leaf
  ## the snapshot did not render leaves its bytes as they are.
  when V is object or V is tuple:
    for fname, fv in fieldPairs(x):
      when typeof(fv) is SomeNumber:
        readCellField(c, path & "." & fname, fv)
  elif V is SomeNumber:
    readCellField(c, path, x)

proc resolveRef*[T: ref | ptr](c: RefWitness; pos: string): T =
  ## RFC-0005 S8h. The witness value of the `ref`/`ptr` position `pos`.
  var cell = cellNameOf(c, pos)
  if cell.len == 0: return nil
  when T is ptr:
    # RFC-0016 INT-88. A position holding the cell at another sort than its
    # owner is a typed view of the owner's one allocation, not a cell of its
    # own: `cast[ptr float](addr x)` beside `addr x`. RFC-0016 INT-90: the
    # leaves the snapshot rendered for the view (`renderCrossSortViews`) are
    # written into it at their own bytes, before or after the owner's (the
    # bytes they share agree): a view wider than its owner, or over its
    # padding, holds the model's bytes there, not the allocation's zeros.
    if not cell.startsWith("&") and not cell.startsWith(ptrAimPrefix) and
       cellForeignView(c, pos, cell):
      let p = cellAlloc(c, cell, sizeof(result[]))
      viewLeavesInto(c, pos, cast[T](p)[])
      return cast[T](p)
  let built = cellBuilt(c, cell)
  if built != nil: return cast[T](built)
  # RFC-0005 S8bh (item 2). A pointer to a field (`"&<cell>.<field>"`) is
  # that field's address, recorded when its object was built. The typed
  # witness builds every pointer position after the others (S8bn, item 1:
  # `emitWitnessTuple`), so its object is built first; one that is still not
  # (a pointer in a cell's field) leaves the pointer its own cell, read from
  # the leaves the snapshot wrote under the position's name.
  # RFC-0005 S8bn (item 2): a pointer aimed at a variable (`"@aim:<name>"`)
  # is a cell of its own, recorded for the splat (`ptrAimsAt`), and shared by
  # every position aimed alike.
  var leaves = cell
  if cell.startsWith("&"):
    cell = pos
    leaves = pos
  elif cell.startsWith(ptrAimPrefix):
    leaves = pos
  when T is ref:
    # RFC-0016 INT-81. A cell is built ONCE, as the dynamic type the model
    # gave its address (its run-type tags), not as the static type of the
    # position that reaches it first; every position holding it gets that
    # one object, upcast. Built as the position's type, a descendant the
    # verdict needs (a method override, `of`, a down-conversion) replayed as
    # its ancestor, and a cell a base-typed position reached first was too
    # small for a descendant-typed one.
    let dyn = cellDynBuild(c, leaves)
    if dyn != nil:
      dyn(c, cell, leaves, addr result)
      return
  fillCell(c, cell, leaves, result)

proc buildCellAs*[T: ref](c: RefWitness; cell, leaves: string; dst: pointer) =
  ## RFC-0016 INT-81. The `WitnessCellBuild` of the type `T`: the cell built
  ## as a `T`, stored into the ref slot `dst` (a slot of `T` or an ancestor;
  ## it holds nil).
  fillCell(c, cell, leaves, cast[ptr T](dst)[])

proc fillCell[T: ref | ptr](c: RefWitness; cell, leaves: string; x: var T) =
  ## RFC-0005 S8h (factored out of `resolveRef` at RFC-0016 INT-81). Allocate
  ## the cell `cell` as a `T`, record it before its fields are read (so a
  ## cycle back to it finds it), and fill each field from the leaves under
  ## `leaves`.
  when T is ref:
    new(x)
  else:
    # A `ptr` witness cell is unmanaged memory the witness owns for the rest
    # of the process: nothing frees what a SUT is handed as a raw pointer.
    # RFC-0016 INT-88: one allocation per address, sized for the largest
    # pointee any position holding it has (`cellAlloc`).
    x = cast[T](cellAlloc(c, cell, sizeof(x[])))
    ptrAimRecord(cell, cast[pointer](x))
  cellRecord(c, cell, cast[pointer](x))
  when x[] is object:
    # A case object's discriminator is assigned in field order, before the
    # branch fields `fieldPairs` then yields for the branch it selected.
    {.cast(uncheckedAssign).}:
      for fname, fv in fieldPairs(x[]):
        readCellField(c, leaves & "." & fname, fv)
        # RFC-0005 S8bh (item 2): the field's address, for a pointer the
        # snapshot aims at it (`aliasRef = "&<cell>.<field>"`).
        cellRecord(c, "&" & leaves & "." & fname, cast[pointer](addr fv))
    when compiles(cellRecordBranches(c, "&" & leaves, x[])):
      cellRecordBranches(c, "&" & leaves, x[])
  else:
    readCellField(c, leaves, x[])

proc readCellSeq[E](c: RefWitness; path: string; f: var seq[E]) =
  ## RFC-0005 S8ap. A seq cell field: `seqLens[path]` elements, each the leaf
  ## `<path>.<i>`, a ref/ptr element the position `<path>[<i>]`. Absent (a
  ## field no path materialised) keeps the empty seq.
  let n = cellSeqLen(c, path)
  if n < 0: return
  f = newSeq[E](n)
  for i in 0 ..< n:
    when E is ref or E is ptr:
      f[i] = resolveRef[E](c, refElemPos(path, i))
    else:
      readCellField(c, path & "." & $i, f[i])
      # RFC-0005 S8bn (item 4): the element's address, for a pointer the
      # snapshot aims at it (`aliasRef = "&<cell>.<field>.<index>"`).
      if path.len > 0 and path[0] != '&':
        cellRecord(c, "&" & path & "." & $i, cast[pointer](addr f[i]))

proc cellRecordParts[T](c: RefWitness; prefix: string; x: var T) =
  ## RFC-0005 S8bz (item 2). The address of each part of the aggregate `x`,
  ## under `prefix`, by position and by name (`f<name>`), for a pointer the
  ## snapshot aims at it.
  when T is object or T is tuple:
    var k = 0
    {.cast(uncheckedAssign).}:
      for fname, fv in fieldPairs(x):
        cellRecord(c, prefix & "." & $k, cast[pointer](addr fv))
        cellRecord(c, prefix & ".f" & fname, cast[pointer](addr fv))
        cellRecordParts(c, prefix & "." & $k, fv)
        cellRecordParts(c, prefix & ".f" & fname, fv)
        inc k
  elif T is array:
    var k = 0
    for e in x.mitems:
      cellRecord(c, prefix & "." & $k, cast[pointer](addr e))
      cellRecordParts(c, prefix & "." & $k, e)
      inc k

proc readCellTable[K, V](c: RefWitness; path: string; f: var Table[K, V]) =
  ## RFC-0005 S8ap. A `Table[string, V]` cell field: the keys of
  ## `tabKeys[path]`, each value the leaf `<path>.<key>` (`intVals`, a bool
  ## value as 0/1 -- `extractTableEntries`'s layout). RFC-0005 S8ar: every
  ## backed key and value type (`witnessTabKey` / `witnessTabVal`); a value
  ## type the model does not back keeps its zero, and `witnessFidelity`
  ## classifies such a pointee lossy.
  if not cellHasTab(c, path): return
  f = initTable[K, V]()
  for k in cellTabKeys(c, path):
    var v: V
    when compiles(witnessTabVal(c.w, "", v)):
      discard witnessTabVal(c.w, path & "." & k, v)
    when compiles(witnessTabKey[K](k)):
      f[witnessTabKey[K](k)] = v
  # RFC-0005 S8bn (item 4): each value's address, once every key is in (a
  # later insertion may move them), for a pointer the snapshot aims at it
  # (`aliasRef = "&<cell>.<field>.<key>"`).
  if path.len > 0 and path[0] != '&':
    for k in cellTabKeys(c, path):
      when compiles(witnessTabKey[K](k)):
        cellRecord(c, "&" & path & "." & k,
                   cast[pointer](addr f[witnessTabKey[K](k)]))
        # RFC-0005 S8bz (item 2): and its parts' (`readCellField`'s spelling).
        when V is object or V is tuple or V is array:
          cellRecordParts(c, "&" & path & "." & k, f[witnessTabKey[K](k)])

proc readCellSet[E](c: RefWitness; path: string; f: var HashSet[E]) =
  ## RFC-0005 S8ap. A `HashSet[E]` cell field: `setMembers[path]`, whose
  ## members are integers. Only an integer-like `E` is backed
  ## (`isBackedSetElemTy`); any other keeps the empty set, and
  ## `witnessFidelity` classifies its pointee lossy.
  f = initHashSet[E]()
  when E is SomeInteger or E is enum or E is char or E is bool:
    for v in cellSetMembers(c, path): f.incl E(v)

proc readCellField[F](c: RefWitness; path: string; f: var F) =
  ## RFC-0005 S8h. One field of a cell (or a scalar pointee). The kinds the
  ## logical heap models (`liftHeapValue`: int, bool, float, ref, ptr) read
  ## the snapshot's leaf; a leaf that is absent was never observed and keeps
  ## `validDefault`. RFC-0005 S8ap: a string, seq, `Table[string, V]` and
  ## `HashSet` field too (`renderHeapCompound`). Every other kind keeps
  ## `validDefault` too: a read of it
  ## degrades the path (`heUnsupportedPointeeRead`), so no clean verdict
  ## rests on it, and `witnessFidelity` classifies such a pointee lossy.
  when F isnot ref and F isnot ptr:
    validDefault(f)
  when F is distinct:
    # RFC-0005 S8ar: a `distinct` cell value is its base's leaf.
    var b: typetraits.distinctBase(F)
    readCellField(c, path, b)
    when compiles(F(b)): f = F(b)
  elif F is ref:
    f = resolveRef[F](c, path)
  elif F is ptr:
    when typeof(f[]) is object or typeof(f[]) is SomeNumber or
         typeof(f[]) is bool or typeof(f[]) is enum or typeof(f[]) is char or
         typeof(f[]) is ref or typeof(f[]) is ptr or
         typeof(f[]) is string:   ## RFC-0005 S8bn
      f = resolveRef[F](c, path)
  elif F is bool:
    var b: bool
    if cellBool(c, path, b): f = b
  elif F is float32:
    var x: float32
    if cellF32(c, path, x): f = x
  elif F is SomeFloat:
    var x: float64
    if cellF64(c, path, x): f = F(x)
  elif F is SomeUnsignedInt or F is char:
    var u: uint64
    var i: int64
    if cellUInt(c, path, u): f = F(u)
    elif cellInt(c, path, i): f = F(uint64(i))
  elif F is Ordinal:
    var i: int64
    var u: uint64
    if cellInt(c, path, i): storeOrdinal(f, i)   # RFC-0005 S8cl
    elif cellUInt(c, path, u): storeOrdinal(f, int64(u))
  elif F is string:
    # RFC-0005 S8ap: a string field is read from the heap and rendered.
    var x: string
    if cellStr(c, path, x): f = x
  elif F is seq:
    readCellSeq(c, path, f)
  elif F is Table:
    when compiles(readCellTable(c, path, f)): readCellTable(c, path, f)
  elif F is HashSet:
    readCellSet(c, path, f)
  elif F is object or F is tuple:
    # RFC-0005 S8ar: a by-value object / tuple field, each part the leaf
    # `<path>.<name>` (`renderHeapValue`; an anonymous tuple's `FieldN`).
    # RFC-0005 S8bz (item 1): each part's address, for a pointer the snapshot
    # aims at it by position or name (`&<cell>.<field>.<index>.<step>`).
    var k = 0
    {.cast(uncheckedAssign).}:
      for fname, fv in fieldPairs(f):
        readCellField(c, path & "." & fname, fv)
        if path.len > 0 and path[0] != '&':
          cellRecord(c, "&" & path & "." & $k, cast[pointer](addr fv))
          cellRecord(c, "&" & path & ".f" & fname, cast[pointer](addr fv))
          cellRecord(c, "&" & path & "." & fname, cast[pointer](addr fv))
        inc k
  elif F is array:
    # RFC-0005 S8ar: an array field, element `i` (from 0) the leaf `<path>.<i>`.
    var i = 0
    for x in f.mitems:
      readCellField(c, path & "." & $i, x)
      if path.len > 0 and path[0] != '&':
        cellRecord(c, "&" & path & "." & $i, cast[pointer](addr x))
      inc i
  else:
    discard

proc resolvePointer*(c: RefWitness; pos: string): pointer =
  ## RFC-0016 INT-83. The witness value of the `pointer` position `pos`:
  ## nil, the cell of the typed position the snapshot aliases it to, or a
  ## cell of its own, of the scalar sort the snapshot gave it (the sort a
  ## `cast[ptr T]` of it reads; `pointerViewPos`), filled from its leaf, or
  ## sixteen zero bytes for an address no read looks through.
  ## Defined after `readCellField`'s body: an instantiation of that generic
  ## made before its body is compiled is empty, and every later use of the
  ## same instantiation (a `bool` or `int` field of any witness cell) would
  ## read nothing.
  let cell = cellNameOf(c, pos)
  if cell.len == 0: return nil
  let built = cellBuilt(c, cell)
  if built != nil: return built
  var srt = ""
  for e in c.w.heapSnapshot:
    if e.name == cell: srt = e.sort
  template scalar(T: typedesc; ty: IRType) =
    if srt == "Ref_" & refPointeeTypeId(ty):
      let q = cast[ptr T](alloc0(max(sizeof(T), 16)))
      readCellField(c, cell, q[])
      cellRecord(c, cell, cast[pointer](q))
      return cast[pointer](q)
  scalar(int, tInt(64, signed = true))
  scalar(int32, tInt(32, signed = true))
  scalar(int16, tInt(16, signed = true))
  scalar(int8, tInt(8, signed = true))
  scalar(uint64, tInt(64, signed = false))
  scalar(uint32, tInt(32, signed = false))
  scalar(uint16, tInt(16, signed = false))
  scalar(uint8, tInt(8, signed = false))
  scalar(bool, tBool())
  # A cell no read looks through as a scalar: its own address only. Never
  # freed (the witness's cells live for the process, as a `ptr` cell does).
  result = alloc0(16)
  cellRecord(c, cell, result)

proc readSeqLen*(w: RawWitness, name: string): int =
  ## Phase 15 R3 (ADR-0010). The model length of a seq witness leaf — used by
  ## the `seq[ref T]` reader to size a default-cell seq (the per-element pointee
  ## values are not individually rendered at R3; the full per-element
  ## heap-snapshot witness lands R11b/R12).
  if w.seqLens.hasKey(name): w.seqLens[name] else: 0

proc readSeqInt*(w: RawWitness, name: string): seq[int] =
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int(w.intVals[path])

proc readSeqInt8*(w: RawWitness, name: string): seq[int8] =
  ## RFC-chapulin-hardening M1: fixed-width-int seq element reader.
  ## Analogous to `readSeqInt` (the int64 case) but narrowing each leaf to
  ## `int8` — the value was already range-correct at extraction time
  ## (`extractSeqElements`'s `itInt`/width==8 arm evaluates the model's BV8
  ## and stores the sign-correct int64 in `intVals`), so the narrowing here
  ## is a lossless truncation, not a re-interpretation.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int8](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int8(w.intVals[path])

proc readSeqInt16*(w: RawWitness, name: string): seq[int16] =
  ## RFC-chapulin-hardening M1. See `readSeqInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int16](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int16(w.intVals[path])

proc readSeqInt32*(w: RawWitness, name: string): seq[int32] =
  ## RFC-chapulin-hardening M1. See `readSeqInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int32](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int32(w.intVals[path])

proc readSeqUInt8*(w: RawWitness, name: string): seq[uint8] =
  ## RFC-chapulin-hardening M1: fixed-width-int seq element reader. Covers
  ## both `seq[byte]` and `seq[uint8]` (`byte` is a Nim alias for `uint8`;
  ## `classifyType` maps either to the same unsigned-width-8 `IRType`, so the
  ## reader cannot distinguish the two — nor does it need to, the return
  ## type is structurally identical). Reads from `uintVals` — the unsigned
  ## twin of `readSeqInt8`'s `intVals`.
  ##
  ## Round-6 B4: a `seq[byte]` param B1 marked `isStringBacked` allocates via
  ## the itString machinery (`allocateSym`), so its model value lands in
  ## `RawWitness.strVals` (one whole-string leaf) instead of `seqLens`/
  ## `uintVals` (per-index array leaves) — B1's own flagged gap, since the
  ## GENERATED reader glue picks `readSeqUInt8` off the param's DECLARED
  ## type (`seq[byte]`), unaware of the allocation representation, and
  ## previously degraded to an empty seq no matter what the model held.
  ## Route through `strVals` first, byte-per-char, before falling back to
  ## the array representation — the two representations are mutually
  ## exclusive per param (`extractLeaf`'s `svString`/array split populates
  ## exactly one), so checking `strVals` first never shadows a genuine
  ## array-backed witness.
  if w.strVals.hasKey(name):
    let s = w.strVals[name]
    result = newSeq[uint8](s.len)
    for i in 0 ..< s.len:
      result[i] = uint8(s[i])
    return
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint8](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = uint8(w.uintVals[path])

proc readSeqUInt16*(w: RawWitness, name: string): seq[uint16] =
  ## RFC-chapulin-hardening M1. See `readSeqUInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint16](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = uint16(w.uintVals[path])

proc readSeqUInt32*(w: RawWitness, name: string): seq[uint32] =
  ## RFC-chapulin-hardening M1. See `readSeqUInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint32](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = uint32(w.uintVals[path])

proc readSeqUInt64*(w: RawWitness, name: string): seq[uint64] =
  ## RFC-chapulin-hardening M1. See `readSeqUInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint64](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = w.uintVals[path]

proc readSeqFloat64*(w: RawWitness, name: string): seq[float] =
  ## Phase 15 F9b: reconstruct a `seq[float]` from the per-element
  ## float64Vals subtable, analogous to readSeqInt.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[float](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.float64Vals.hasKey(path):
      result[i] = w.float64Vals[path]

proc readSeqFloat32*(w: RawWitness, name: string): seq[float32] =
  ## Phase 15 F9b: reconstruct a `seq[float32]` from float32Vals.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[float32](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.float32Vals.hasKey(path):
      result[i] = w.float32Vals[path]

proc readSeqBool*(w: RawWitness, name: string): seq[bool] =
  ## RFC-0005 S8ar: a `seq[bool]` witness, from `boolVals` (an element absent
  ## from the model is `false`, Nim's zero).
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[bool](n)
  for i in 0 ..< n:
    result[i] = w.boolVals.getOrDefault(name & "." & $i, false)

proc readSeqString*(w: RawWitness, name: string): seq[string] =
  ## RFC-0005 S8ar: a `seq[string]` witness, from `strVals`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[string](n)
  for i in 0 ..< n:
    result[i] = w.strVals.getOrDefault(name & "." & $i, "")

proc readTableStrInt*(w: RawWitness, name: string): Table[string, int] =
  ## Phase 5 cycle 5: build a `Table[string, int]` populated with the
  ## key-value pairs the SUT accessed (static string literals).
  result = initTable[string, int]()
  if not w.tabKeys.hasKey(name):
    return
  for k in w.tabKeys[name]:
    let p = name & "." & k
    if w.intVals.hasKey(p):
      result[k] = int(w.intVals[p])

proc readSetInt*(w: RawWitness, name: string): HashSet[int] =
  ## Phase 5 cycle 8: build a `HashSet[int]` from collected members.
  result = initHashSet[int]()
  if not w.setMembers.hasKey(name): return
  for v in w.setMembers[name]:
    result.incl int(v)

proc witnessIntAs*[T](v: int64): T =
  ## RFC-0005 S8z. A container cell's witness value (`cellModelValue`) as
  ## the element type `T`: a 64-bit unsigned value keeps its bits.
  when T is uint64 or T is uint: cast[T](v)
  else: T(v)

proc witnessTabKey*[K](k: string): K =
  ## RFC-0005 S8ar. A rendered table key (`extractTableEntries`) as `K`: a
  ## string as itself, a cell key from its decimal.
  ## RFC-0005 S8at: a float key from its IEEE bit pattern (`floatKeyCell`).
  when K is string: k
  elif K is float32: cast[float32](uint32(parseBiggestInt(k) and 0xFFFF_FFFF'i64))
  elif K is SomeFloat: K(cast[float64](parseBiggestInt(k)))
  else: witnessIntAs[K](parseBiggestInt(k))

proc readBitSetAs*[T](w: RawWitness, name: string): set[T] =
  ## RFC-0005 S8bq. A builtin `set[T]` from its collected members.
  privateAccess(RawWitness)  # instantiated in callers' modules (see walk_types)
  if not w.setMembers.hasKey(name): return
  for v in w.setMembers[name]:
    result.incl witnessIntAs[T](v)

proc readSetIntAs*[T](w: RawWitness, name: string): HashSet[T] =
  ## RFC-0005 S8z. `readSetInt` for any fixed-width int element type.
  privateAccess(RawWitness)  # instantiated in callers' modules (see walk_types)
  result = initHashSet[T]()
  if not w.setMembers.hasKey(name): return
  for v in w.setMembers[name]:
    result.incl witnessIntAs[T](v)

proc readSeqAs*[T](c: RefWitness, name: string): seq[T] =
  ## RFC-0005 S8bl (item 4). A witness `seq[T]` of a tree element holding a
  ## ref part, read through the witness tuple's ONE `RefWitness` (its
  ## positions, `collectTreeRefPositions`), so a cell two positions share --
  ## two elements, an element and a param -- is one object.
  privateAccess(RawWitness)  # instantiated in callers' modules (see walk_types)
  let n = c.w.seqLens.getOrDefault(name, 0)
  result = newSeq[T](n)
  for i in 0 ..< n:
    readCellField(c, name & "." & $i, result[i])

proc readSeqAs*[T](w: RawWitness, name: string): seq[T] =
  ## RFC-0005 S8at. A witness `seq[T]` of any renderable element type, at
  ## `name` (`extractFromSymVal`'s `seqLens` + `.<i>` element leaves): a
  ## `Table`'s seq value, which the table reader reaches generically.
  ## RFC-0005 S8bc: also a by-value `seq[char]` / `seq[Enum]` (the fixed
  ## width readers return `seq[uint8]`, not the declared type). A `char` or
  ## enum element converts by value (`cast` from the 64-bit leaf is a
  ## byte-order-dependent reinterpretation), and a string-backed `seq[char]`
  ## (one whole-string leaf, as `readSeqUInt8` reads it) is read per byte.
  privateAccess(RawWitness)  # instantiated in callers' modules (see walk_types)
  when T is char:
    if w.strVals.hasKey(name):
      let s = w.strVals[name]
      result = newSeq[T](s.len)
      for i in 0 ..< s.len: result[i] = s[i]
      return
  let n = w.seqLens.getOrDefault(name, 0)
  result = newSeq[T](n)
  for i in 0 ..< n:
    let p = name & "." & $i
    when T is string: result[i] = w.strVals.getOrDefault(p, "")
    elif T is bool: result[i] = w.boolVals.getOrDefault(p, false)
    elif T is float32:
      if w.float32Vals.hasKey(p): result[i] = w.float32Vals[p]
    elif T is SomeFloat:
      if w.float64Vals.hasKey(p): result[i] = T(w.float64Vals[p])
    elif T is char or T is enum:
      if w.uintVals.hasKey(p): result[i] = T(w.uintVals[p])
      elif w.intVals.hasKey(p): result[i] = T(w.intVals[p])
    elif T is object or T is tuple or T is array or T is distinct or T is seq:
      # RFC-0005 S8bc (item 3): a tree element, written in the heap's cell
      # layout (`extractTreeValue`), read as a by-value cell field is.
      # RFC-0016 PRC-23: and a seq element of a seq of seqs, whose length
      # is `seqLens[<path>.<i>]` (`readCellSeq`).
      readCellField(newRefWitness(w), p, result[i])
    else:
      if w.uintVals.hasKey(p): result[i] = cast[T](w.uintVals[p])
      elif w.intVals.hasKey(p): result[i] = witnessIntAs[T](w.intVals[p])

proc readTableAs*[K, V](w: RawWitness, name: string): Table[K, V]

proc witnessTabVal*[V](w: RawWitness; p: string; v: var V): bool =
  ## RFC-0005 S8ar. The rendered table value at leaf `p`, as `V`.
  ## RFC-0005 S8at: a container value (`isTableContainerValTy`), read as a
  ## by-value param of its type is; every rendered key has one.
  privateAccess(RawWitness)  # instantiated in callers' modules (see walk_types)
  when V is seq:
    v = readSeqAs[typeof(items(default(V)))](w, p)
    return true
  elif V is HashSet:
    v = readSetIntAs[typeof(items(default(V)))](w, p)
    return true
  elif V is Table:
    v = readTableAs[typeof(keys(default(V))), typeof(values(default(V)))](w, p)
    return true
  elif V is object or V is tuple or V is array:
    # RFC-0005 S8bz (item 2): an aggregate value, in the heap's cell layout.
    readCellField(newRefWitness(w), p, v)
    return true
  elif V is string:
    if w.strVals.hasKey(p): (v = w.strVals[p]; return true)
  elif V is float32:
    if w.float32Vals.hasKey(p): (v = w.float32Vals[p]; return true)
  elif V is SomeFloat:
    if w.float64Vals.hasKey(p): (v = V(w.float64Vals[p]); return true)
  elif V is bool:
    if w.intVals.hasKey(p): (v = w.intVals[p] != 0; return true)
  else:
    if w.intVals.hasKey(p): (v = witnessIntAs[V](w.intVals[p]); return true)
  false

proc readTableAs*[K, V](w: RawWitness, name: string): Table[K, V] =
  ## RFC-0005 S8ar. A witness `Table[K, V]` of any backed key and value type
  ## (`isRenderableTableTy`).
  privateAccess(RawWitness)  # instantiated in callers' modules (see walk_types)
  result = initTable[K, V]()
  if not w.tabKeys.hasKey(name):
    return
  for k in w.tabKeys[name]:
    var v: V
    if witnessTabVal(w, name & "." & k, v):
      result[witnessTabKey[K](k)] = v

# ---- Phase 15 Cluster C (C2a): closure-construction test hooks ---------------
#
# These hooks let a test introspect the CONSTRUCTED `svClosure` (env snapshot +
# per-site funcSym) WITHOUT a full `symexFind` body descent (`f(3)` would hit
# an `iekClosureCall` application). They set up a fresh context, reset the
# closure-funcSym memo, build the construction-time env at the `let f = …`
# binding point, and lower an `iekLambda` against it via the real
# `lower(env, e)` / `buildClosure` path. The probe returns a plain record so the
# non-exported `Env`/`SymVal`/`symValHash`/`lower` stay encapsulated.

type C2aClosureProbe* = object  ## Phase 15 C2a test hook.
  isClosure*:                       bool
  siteHash*:                        int64
  declOrder*:                       int
  envIsTuple*:                      bool
  envFieldNames*:                   seq[string]
  envFieldCount*:                   int
  capturedFieldMatchesOffset*:      bool
  funcDeclIsLive*:                  bool
  closureSymsLen*:                  int
  assertionCountDuringConstruction*: int

proc c2aClosureProbe*(): C2aClosureProbe =
  ## Construct the reference closure (per RFC §C2a) and return an introspectable
  ## probe. Models the `let f = proc(y: int): int = y + offset` binding point of
  ##   proc sut(x: int): int =
  ##     let offset = x * 2
  ##     let f = proc(y: int): int = y + offset
  ##     f(3)
  ## with `offset` (== x*2) and an `unrelated` local in the construction env.
  let ctx = newContext()
  setCurrentContext(ctx)
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()
  let offsetSV = SymVal(kind: svBV64, bv64: mkBitVec[64](14'i64), signed: true)
  var env: Env = initOrderedTable[string, SymVal]()
  env["offset"] = offsetSV
  env["unrelated"] = SymVal(kind: svBV64, bv64: mkBitVec[64](99'i64),
                            signed: true)
  let body = mkReturnVal(mkBinop(bAdd, mkVar("y"), mkVar("offset")))
  let lam = mkLambda(siteHash = 4242'i64, declOrder = 0,
                     params = @[IRParam(name: "y", ty: tInt(64, true))],
                     body = body, captures = @["offset"], retTy = tInt(64, true))
  let clo = lower(env, lam)
  result.isClosure = clo.kind == svClosure
  if result.isClosure:
    result.siteHash = clo.closureSite.siteHash
    result.declOrder = clo.closureSite.declOrder
    if clo.closureEnv != nil:
      let envRec = clo.closureEnv[]
      result.envIsTuple = envRec.kind == svTuple
      result.envFieldNames = envRec.fieldNames
      result.envFieldCount = envRec.fields.len
      if result.envFieldCount == 1:
        result.capturedFieldMatchesOffset =
          envRec.fields[0].kind == svBV64 and
          symValHash(envRec.fields[0]) == symValHash(offsetSV)
    result.funcDeclIsLive = not clo.closureRawFD.isNil
  result.closureSymsLen = currentClosureSyms.len
  # Construction touches no solver — there is no solver in this probe and
  # `buildClosure` only DECLARES a funcSym (no assertion). Deterministically 0.
  result.assertionCountDuringConstruction = 0

proc c2aClosureProbeRelowered*(): C2aClosureProbe =
  ## Lower the SAME site against the SAME env/param sorts TWICE; assert the
  ## funcSym memo holds exactly one entry (the get-or-create reuse).
  let ctx = newContext()
  setCurrentContext(ctx)
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()
  let offsetSV = SymVal(kind: svBV64, bv64: mkBitVec[64](14'i64), signed: true)
  var env: Env = initOrderedTable[string, SymVal]()
  env["offset"] = offsetSV
  let body = mkReturnVal(mkBinop(bAdd, mkVar("y"), mkVar("offset")))
  let lam = mkLambda(siteHash = 7'i64, declOrder = 1,
                     params = @[IRParam(name: "y", ty: tInt(64, true))],
                     body = body, captures = @["offset"], retTy = tInt(64, true))
  let c1 = lower(env, lam)
  let c2 = lower(env, lam)
  result.isClosure = c1.kind == svClosure and c2.kind == svClosure
  result.closureSymsLen = currentClosureSyms.len
  result.assertionCountDuringConstruction = 0

# RFC-0016 review D3c-2. The upward verbs the include files call through
# `lowerHooks` (`walk_state.nim`): filled once, here, after every one of them is
# defined and before any walk can run. `tsymex_0016_d3_hooks` pins that no
# field is left nil.
lowerHooks = LowerHooks(
  lower: lower, lowerClosureCall: lowerClosureCall,
  currentFrameId: currentFrameId,
  registerCapCell: registerCapCell,
  depositStrIndexOob: depositStrIndexOob,
  depositUndefinedOob: depositUndefinedOob)
# RFC-0016 INT-34 B3b: `walk_path`'s own typed hook, filled beside it.
pathHooks = PathHooks(noteUbAtFork: noteUbAtFork)
# RFC-0016 INT-34 B4: `lower_expr`'s own typed hook, filled beside them.
lowerExprHooks = LowerExprHooks(lowerHofCall: lowerHofCall)
# RFC-0016 INT-34 B6b: `walk_expr`'s own typed hook, filled beside them.
walkExprHooks = WalkExprHooks(routeRaise: routeRaise)

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(cstringWitnessBufs,   # RFC-0016 INT-87
    z3ApiErrorCount, z3ApiFirstError,
    currentClosureCallAxiomStrs, paramBoundaryAbort, ptrAims)

registerThreadStateRelease(releaseThreadState)
