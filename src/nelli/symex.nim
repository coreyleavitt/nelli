## nelli/symex — public-API entry for the symbolic-execution capability.
##
## See:
##   * docs/SYMEX_PLAN.md     — build plan + scope
##   * docs/symex/ADR-0001-integer-semantics.md
##   * docs/symex/ADR-0002-dsl-factoring.md
##
## Phase 1 supports a small Nim fragment: int/bool params + locals,
## arithmetic + comparison + boolean, `if` / `elif` / `else`, the
## three body markers below. Each later phase widens the fragment.
##
## Body markers — `symexTarget`/`symexAssert`/`symexAssume` are
## `proc {.inline.}`, not templates, so the same SUT is simultaneously
## walkable by symex AND runnable under random PBT without source
## duplication. They are defined in `src/nelli/engine/markers.nim` and
## merely re-exported here by name (see :145-153) for `import nelli/symex`
## callers; they are also reachable from a bare `import nelli` via the
## `engine` export chain (RFC-z3-optional S1c), so a marker-annotated SUT
## survives the 0.7.0 break without importing this Z3-bound module.
## Outside symex:
##
##   * `symexTarget(name)`  — usually a no-op, but calls
##                            `symexCaptureRecord`, which feeds the
##                            `{.threadvar.}` capture context backing
##                            `assertCoveredBy`; a no-op only when no
##                            capture is active on this thread
##   * `symexAssert(cond)`  — `doAssert cond` (it's a stated invariant)
##   * `symexAssume(cond)`  — no-op; Phase 1 recognizes it in the parser
##                            but does not yet restrict the SUT's
##                            normal-run input domain
##
## Layout (RFC-0016 D6). This module is the public facade: the user-facing
## macros (their signatures and documentation), `symexForAll`, the DB macro
## forms, and the re-exports. The implementation lives in `nelli/smt/`:
##
##   * `witness_render`   -- a witness as a `seq[ChoiceNode]`
##   * `symex_cache`      -- the DB record codecs (soundness, gaps, notes,
##                           witness / verdict / raised entries)
##   * `witness_emit`     -- the typed witness reader emitters
##   * `witness_fidelity` -- how faithful a rebuilt witness is; the splat
##   * `replay_footprint` -- replay eligibility and the footprint scan
##   * `routine_table`    -- the routine table a replay child carries
##   * `heldset`          -- the held-set walk (proc-valued globals)
##   * `replay_emit`      -- the code a replay emits (`emitReplayWitness`)
##   * `replay_settle`    -- the verdict-side settle of replay results
##   * `proc_lift`        -- the proc-value lift
##   * `run_replayed`     -- the replayed-search body of the entry macros
##   * `entry_parse`      -- what every entry macro does first
##   * `find_emit`, `findall_emit`, `cover_emit` -- the macro bodies

import std/[macros, sets, tables, options, strutils, macrocache]
# RFC-0016 W1-c1b: the build is admitted (or refused, by name) BEFORE `z3` is
# imported. Under `--mm:refc` nim-z3's `=destroy` hooks do not compile, and
# that error names `z3/ast.nim`, not the build; this one names the field.
from ./smt/buildprofile import buildSemantics, admitBuild, refusalMessage
const buildAdmission = admitBuild(buildSemantics)
when buildAdmission.isSome:
  {.error: refusalMessage(buildAdmission.get).}
import z3
export z3.z3FullVersion
import ./choice
export choice
import ./smt/dsl
export dsl
import ./smt/replayproc   ## RFC-0005 S8ct
import ./smt/replayresult ## RFC-0005 0.9.1 (review R1-06, R1-14)
export replayExecutions
export replayresult.ReplayOutcome, replayresult.ReplayResult,
       replayresult.outcome, replayresult.child,
       replayresult.detail, replayresult.runDependence
import ./engine/types as engineTypes
import ./smt/witness_render   ## RFC-0016 D6: the witness -> choices bridge
export witness_render.renderAsChoices
export engineTypes.SymexFinding, engineTypes.SymexFindingStatus,
       engineTypes.FindingGap, engineTypes.FindingUndefined, engineTypes.trusted   ## RFC-0005 S11


# ---- assertCoveredBy capture context ----------------------------------------
#
# RFC-z3-optional S1c: `SymexCaptureCtx`, the `symexCapture` threadvar and
# `symexCaptureBegin`/`End`/`Record` now live in `engine/markers.nim`,
# alongside the `symexTarget`/`symexAssert`/`symexAssume` markers they
# serve. All of it is Z3-free, and putting it behind the walker's import
# meant a marker-annotated SUT could not compile under bare `import nelli`
# once the umbrella stopped re-exporting symex. Re-exported by name below,
# so `import nelli/symex` callers are unchanged.

import ./engine/markers as symexMarkers
export symexMarkers.SymexCaptureCtx,
       symexMarkers.symexCapture,
       symexMarkers.symexCaptureBegin,
       symexMarkers.symexCaptureEnd,
       symexMarkers.symexCaptureRecord,
       symexMarkers.symexTarget,
       symexMarkers.symexAssert,
       symexMarkers.symexAssume

# Review R1-10: the thread-local `SymexFinding` sink (`recordSymexFinding` /
# `consumeSymexFindings`) is gone. Only `symexForAll` drained it, so findings
# from an earlier call on the thread leaked into its report. A finding now
# belongs to the call that made it: `assertCoveredBy` returns it (or carries
# it on its `SymexCoverageDefect`), `symexFindAllWitnesses` returns them, and
# a run's report holds its own.


# ---- Content-addressed DB persistence ---------------------------------------
#
# Symex witnesses persist under a content-addressed key derived from
# (canonical SUT IR, target, witness-relevant settings, Z3 version,
# Nim version, walker version). Identical inputs → identical key;
# any change to *anything that affects the witness* rotates the key
# so stale entries become invisible. See docs/symex/determinism.md
# and nelli/smt/canonicalize.nim for the canonical-encoding
# contract and the proof obligations on each input.
import ./db
export db
import ./strategy
import ./engine
import ./engine/phases
import ./engine/pipeline
import ./optbox
import ./smt/canonicalize
export canonicalize.symexCacheKey, canonicalize.symexCacheKeyPrefix,
       canonicalize.symexWalkerVersion,
       canonicalize.renderAsChoicesVersion, canonicalize.canonicalize,
       canonicalize.cacheKeySat, canonicalize.cacheKeyUnsat,
       canonicalize.cacheKeyUnknown, canonicalize.cacheKeyRaised,
       canonicalize.verdictCacheMaxEntries
import ./smt/witness_emit   ## RFC-0016 D6: the witness reader emitters
export witness_emit.emitTyAndReader
import ./smt/replay_footprint   ## RFC-0016 D6: replay eligibility + the footprint scan
export replay_footprint.replayEligible, replay_footprint.replayInScope,
       replay_footprint.replayReached
import ./smt/replay_emit   ## RFC-0016 D6: the replay child emitter
export replay_emit.wireTarget, replay_emit.readTarget, replay_emit.targetLabelOf,
       replay_emit.emitReplayWitness
import ./smt/replay_settle   ## RFC-0016 D6: the verdict-side replay settle
export replay_settle.candidateLossy
import ./smt/entry_parse   ## RFC-0016 D6: what every entry macro does first
export entry_parse.describeTarget
import ./smt/cover_emit   ## RFC-0016 D6: the assertCoveredBy body
export cover_emit.SymexCoverageDefect
import ./smt/find_emit   ## RFC-0016 D6: the symexFind / concolic bodies
import ./smt/findall_emit   ## RFC-0016 D6: the symexFindAllWitnesses body
import ./smt/symex_cache   ## RFC-0016 D6: the DB record codecs
export symex_cache.saveSymexNotesImpl, symex_cache.loadSymexNotesImpl,
       symex_cache.saveSymexWitnessImpl, symex_cache.loadSymexWitnessesImpl,
       symex_cache.saveSymexVerdictImpl, symex_cache.loadSymexVerdictImpl,
       symex_cache.saveSymexRaisedImpl, symex_cache.loadSymexRaisedImpl,
       symex_cache.toFindingStatus, symex_cache.CachedWitness,
       symex_cache.CachedVerdict, symex_cache.CachedRaised, symex_cache.CachedNotes



# ---- Layer 2 — forAllWithSymexSeeds ----------------------------------------
#
# The engine entry that lifts symex witnesses into the random-PBT
# loop as forced seeds. `symexSeedPhase` is slotted between
# `explicit` (user-pinned regression seeds, no shrinking) and
# `random` (fresh exploration). Seeds that falsify carry their
# choice sequence forward to `shrinkPhase` for minimisation —
# Z3 returns *some* satisfying assignment, not a minimal one.

proc forAllWithSymexSeeds*[T](seeds: seq[seq[ChoiceNode]],
                              s: Strategy[T], prop: proc(x: T),
                              settings: Settings = Settings()
                             ): Report[T] =
  ## Run `prop` against `s` with `seeds` as forced replays before
  ## the random phase. Falsifications discovered from a seed flow
  ## through the same `shrinkPhase → finalizePhase` chain a random
  ## falsification would. Returns the terminal `Report[T]`.
  let phases = @[
    Phase[T](name: "dbReuse",   run: dbReusePhase[T]),
    Phase[T](name: "explicit",  run: explicitExamplesPhase[T]),
    symexSeedPhase[T](seeds),
    Phase[T](name: "random",    run: randomPhase[T]),
    Phase[T](name: "targeted",  run: targetedPhase[T]),
    Phase[T](name: "shrink",    run: shrinkPhase[T]),
    Phase[T](name: "explain",   run: explainPhase[T]),
    Phase[T](name: "finalize",  run: finalizePhase[T]),
  ]
  runForAllPipelineWithPhases(
    inMemoryDatabase(), dbEnabled = false,
    s, prop, settings, toExamples[T](@[]), phases)

# ---- Layer 3 — symexForAll sugar -------------------------------------------
#
# One-call entry: `symexForAll(strategy, fn, db)` discovers all
# auto-targets in `fn`, runs symex per target (Layer 1), seeds the
# random-PBT loop with the SAT witnesses (Layer 2), and threads
# the per-target findings into the resulting Report's
# `symexFindings` field for caller-side auditing.
#
# The SUT proc `fn` plays both roles: it is the property the
# engine runs against random + symex-seeded draws, AND the body
# the IR scan inspects for `symexTarget` / `symexAssert` / `arr[i]`
# / variant-field reads.

macro symexForAll*(s: typed, fn: typed,
                   db: ExampleDatabase,
                   symexSettings: static SymexSettings =
                     defaultSymexSettings(),
                   forAllSettings: Settings = Settings(),
                   excludeTargets: seq[SymexTarget] = @[]
                  ): untyped =
  ## Run symex against every auto-discovered target in `fn`, then
  ## drive the random PBT loop on `s` with the symex-derived
  ## witnesses as forced seeds. The terminal Report carries both
  ## the random-run verdict and the per-target symex findings.
  ##
  ## Returns `untyped` matching the `symexFind` macro shape; the
  ## emitted expression has type `Report[T]` where `T` is the
  ## strategy's element type.
  # Inspect `fn`'s formal-param count at macro time to decide
  # whether to pass `fn` directly as the property (single-arg) or
  # wrap it in a tuple-splatting lambda (multi-arg). The strategy
  # `s`'s element type comes from `getTypeInst(s)[1]` — for
  # `Strategy[T]` that's `T` (`int` for `integers()`,
  # `(int, bool)` for `map(integers(), booleans())`).
  # RFC-parser-normalization N1: routes through the shared nil-core's
  # hard-error wrapper. `symexForAll` DELIBERATELY never parses `impl` —
  # it defers entirely to `symexFindAllWitnesses`'s own parse/expansion
  # below. Do not "fix" this into a second `parseEntryImpl` call; that
  # would double-parse the same SUT.
  let impl = resolveEntryImpl(fn, "symexForAll")
  if impl[2].kind != nnkEmpty:
    error("symexForAll: generic procs are not supported as `fn` " &
          "(witness reconstruction has no type to bind generics to)",
          fn)
  let formalParams = impl[3]
  # [0] is the return type. Count names, not IdentDefs: `x, a, b: int` is one
  # IdentDefs holding three parameters (a name list, a type, a default).
  var nParams = 0
  for i in 1 ..< formalParams.len:
    nParams += formalParams[i].len - 2
  let prop =
    if nParams == 1:
      fn      # single-arg: `fn` IS the property
    else:
      # Multi-arg: emit `proc(t: T) = fn(t[0], t[1], …)`. Type
      # comes from `getTypeInst(s)[1]` — the strategy's element
      # type. Nim verifies field-types vs param-types when the
      # emitted call compiles, so a mismatch surfaces as a typed
      # error at the splat site rather than buried inside the
      # macro.
      let sTypeNode = newCall(bindSym"getTypeInst", s)
      # `sTypeNode` evaluates to a NimNode at *macro-time*; we
      # however need a `typedesc` *at call site* so the wrapper's
      # param type is a real type. Use a type alias via `type X =
      # typeof((default(...)))` — no, simpler — extract the
      # element-type expression directly from `s.getTypeInst` at
      # macro time and splice it as a type.
      let sTypeInst = s.getTypeInst
      if sTypeInst.kind != nnkBracketExpr or not sTypeInst[0].eqIdent("Strategy"):
        error("symexForAll: expected `s` to have type Strategy[T] " &
              "(got " & $sTypeInst.repr & ")", s)
      # An empty element type reflects back as `()`, a value, not a type
      # node; spell it `tuple[]`.
      let elemTy =
        if sTypeInst[1].kind == nnkTupleConstr and sTypeInst[1].len == 0:
          newTree(nnkTupleTy)
        else: sTypeInst[1]
      # Reject named-field tuples — `map(s1, s2)` produces an
      # anonymous positional tuple (nnkTupleConstr). Named-field
      # tuple strategies are deferred to a future cycle.
      # (A zero-parameter `fn` takes the strategy's element, ignores it, and
      # calls `fn()`; its element type may be the empty `tuple[]`.)
      if nParams > 1 and elemTy.kind == nnkTupleTy:
        error("symexForAll: named-field tuple strategies are not " &
              "supported as `s` for multi-arg `fn`; use the " &
              "anonymous `map(s1, s2, …)` form", s)
      let tId = genSym(nskParam, "t")
      var splat = newCall(fn)
      for i in 0 ..< nParams:
        splat.add nnkBracketExpr.newTree(tId, newLit(i))
      let lam = newProc(
        params = @[ident"void",
                   newIdentDefs(tId, elemTy)],
        body = splat, procType = nnkLambda)
      lam

  result = quote do:
    block:
      let findings = symexFindAllWitnesses(`fn`, `db`, `symexSettings`,
                                            `excludeTargets`)
      var seeds: seq[seq[ChoiceNode]] = @[]
      for f in findings:
        # RFC-0005 S11 (§8.1 "the seed filter"). A seed is only an input --
        # the property itself judges it -- so an untrusted sfSat is seeded
        # too: since 0.9.1 (WA-9) that is a lossy witness no replay confirmed
        # (`rsUnconfirmed`), which may or may not reach the target, and the
        # finding's `trusted()` says which it is (review R1-15). But a seed
        # runs `prop` in this process: a witness whose replay ended or hung
        # its child (`witnessUnsafe`, WA-2, review R2) would end or hang it.
        # `hostRunnable` refuses those.
        if f.status == sfSat and hostRunnable(f.soundness):
          seeds.add f.witnessChoices
      var report = forAllWithSymexSeeds(seeds, `s`, `prop`,
                                         `forAllSettings`)
      # Review R1-10: Layer 1's findings, then the sfNotApplicable entries
      # the seed phase recorded on this run (already on `report`). Nothing
      # from another call on the thread.
      report.symexFindings = findings & report.symexFindings
      report


# ---- Body markers -----------------------------------------------------------

## Body markers are procs (not templates) so semcheck doesn't elide
## the call site before the symex parser sees it. The parser
## recognizes the call by callee name; outside symex these run as
## ordinary procs whose body provides the dual-mode semantics.

# ---- Extension pragma -------------------------------------------------------

## Phase 9 user-extension hook. Attach to a proc the walker should
## not enter: `proc readSensor(): int {.symexOpaque.} = ...`.
## Inside symex, a call to the proc returns a fresh symbolic value and
## records `feOpaqueCallUnmodelled` (class `dcSubstituted`: the analysis
## put a free value where the real one goes). That gap is `scSpurious` on
## the paths through the call and `scIncomplete` on the run (RFC-0005), so:
##
## - a witness found past the call is reported `sxSat` only after replay
##   has run the real proc on it and reproduced the target
##   (`soundness.replay == rsConfirmed`) -- otherwise `sxUnknown`;
## - an `sxUnsat` is not `trusted()` while the gap is on the run.
##
## `gaps()` on the result names the call and its class, which is the lever
## (model the callee, or prove it irrelevant with `{.symexTransparent.}`).
## Outside symex the pragma is a no-op and the proc executes normally.
template symexOpaque*() {.pragma.}

## Issue #163 user-extension hook, and the one to reach for first for a
## logging/metrics/tracing call: attach to a VOID proc that cannot change
## anything the code under test observes — no result, nothing written through
## an argument, no state the SUT reads back — and symex DELETES the call
## instead of modelling it:
##
## ```nim
## proc trace(msg: string) {.symexTransparent.} = stderr.writeLine msg
## ```
##
## `{.symexOpaque.}` would also keep the walker out of `trace`'s body, but it
## additionally records a `dcSubstituted` gap on every path through the call,
## so a target behind it is `sxSat` only if replay confirms the witness and is
## never a trusted `sxUnsat`. That is the right price for `readSensor()`, whose
## result the SUT branches on, and the wrong price for a trace line. Use `symexOpaque`
## when the call's result or effects matter and cannot be modelled; use
## `symexTransparent` when the honest answer is that they do not matter.
##
## The promise is honoured only in statement position, and even there only
## when every argument is provably inert (a plain value — never a `var`
## formal, `ref`, `ptr`, or an object that might carry one). Two ways to
## over-claim it, and both fail the same safe way:
##
## - the result IS used (expression position) — `avResultUsed`;
## - a statement-position argument is NOT provably inert (e.g. `var x: int`
##   passed to a callee that writes through it) — `avArgNotInert`.
##
## Either way the call falls back to `symexOpaque` handling (its gap, with the
## consequences above), and the broken promise is reported on its own
## channel: an `AnnotationViolation` on `SymexResult.annotationViolations` and
## `SymexFinding.annotationViolations`, naming the pragma, the callee and the
## site. The channel is verdict-neutral -- it never changes a status -- and
## every report format renders it (GitHub output as an `::error`), because it
## is a defect in the annotated code, not in the analysis. An over-claimed
## pragma therefore costs precision, never soundness (never a false witness).
## Outside symex it is a no-op.
##
## One asymmetry worth knowing: the pragma is matched purely BY NAME (any
## module may declare its own private `{.pragma.}` template spelled the same
## — deliberate, and how `nelli/coverage` stays Z3-free), so an accidental
## name collision is possible. The risk is not symmetric between the two
## pragmas: colliding on `symexOpaque` fails SAFE (at worst one more
## `dcSubstituted` gap), but colliding on `symexTransparent` would fail UNSAFE — the
## call vanishes outright — so name this pragma with care in any module that
## does not import it from here.
template symexTransparent*() {.pragma.}

# RFC-z3-optional S1c: `symexTarget`/`symexAssert`/`symexAssume` moved to
# `engine/markers.nim` and are re-exported by name near the top of this
# file. They are Z3-free annotations that belong in production code, so
# they must not sit behind the walker's import.


macro replayWitness*(fn: typed; witness: typed; target: SymexTarget;
                     pathTaint: Taint): untyped =
  ## RFC-0005 §4.2: execute `witness` (a `SymexResult.witness`, or
  ## `.raisedWitness`, of a `symexFind(fn, …)` run) against the REAL `fn`
  ## and report whether it reaches `target`, as a `ReplayResult`: its
  ## `outcome`, and how the child ended (`detail`). Target-shaped, so the
  ## raise-flavoured targets §2.3 puts in scope are expressible: a `sxRaised`
  ## candidate is replayed with `tRaisedExn(r.raisedTypeId)` -- the claim
  ## that exact type ESCAPES `fn`, whatever the search target was (under E6 a
  ## non-excluded Defect surfaces as `sxRaised` under ANY target).
  ## `pathTaint` is the candidate's `RawResult.pathTaint`, the input to the
  ## eligibility gate (`replayEligible`).
  ##
  ## Returns `roInconclusive` (`replayNotRun`) WITHOUT running `fn` for an
  ## ineligible taint, a
  ## witness shape outside the faithfully-renderable fragment (`emitTyAndReader`
  ## placeholders -- permanently), or a target kind outside
  ## `replayInScope`. Otherwise runs `fn` once, inside its own nested capture
  ## frame, catching whatever escapes.
  ##
  ## It takes no `SymexSettings`, and uses the defaults: the macro-time parse
  ## of `fn` (which reads only its parameters, to type the witness) runs under
  ## `defaultSymexSettings()`'s `maxInstantiationsPerProc`, and the child is
  ## killed at `SymexSettings().replayTimeoutMs` (10_000 ms). Why: this is the
  ## direct-call form of the replay the entry macros run, and they do not
  ## call it -- they splice `emitReplayWitness` with their own settings'
  ## timeout (`emitRunSymexReplayed`). A caller who needs another bound, or
  ## `replay = false`, goes through `symexFind` with its settings.
  # RFC-0016 PRC-02b: register the methods `fn` calls in the caller's scope
  # first, so a replay's footprint reads the overrides the entry can see.
  when hasMethodTable:
    let pre = methodPrelude(fn)
    if pre != nil:
      return newTree(nnkStmtListExpr, pre,
                     newCall(bindSym"replayWitness", fn, witness, target,
                             pathTaint))
  let parsed = parseEntryImpl(fn, "replayWitness",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  emitReplayWitness(fn, parsed.params, witness, target, pathTaint)

macro symexFind*(fn: typed,
                 target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): untyped =
  ## Symbolically execute `fn` searching for an input that reaches `target`.
  ## Returns `SymexResult[ParamTuple]` where `ParamTuple` is the proc's
  ## parameter list as a Nim tuple.
  symexFindImpl(bindSym"symexFind", fn, target, settings)

# ---- concolicCollect (RFC-fuzzer-nextgen G1b) -------------------------------

macro concolicCollect*(fn: typed, trace, bindings: typed,
                       settings: static SymexSettings = defaultSymexSettings(),
                       maxDraws: static int = defaultMaxConcolicDraws
                      ): ConcolicCollectResult =
  ## The G1b concolic entry: draw-symbolication + concrete-trace constraint
  ## collection (RFC §G-concolic steps 2-3 — no branch-flipping, that's G2).
  ##
  ## `fn` is the property proc (named or an inline `proc(x: T) = …` literal,
  ## same capture contract as `symexFind` — routes through the SAME
  ## `parseEntryImplWarned` helper, so `fn` becomes a walkable
  ## `SymexProgram` exactly as it does there, AND an incoherent `settings`
  ## warns exactly as it does there. `trace` is the recorded concrete draw
  ## sequence (`seq[ChoiceNode]`) the corpus entry replays; `bindings` says,
  ## per `fn` parameter, whether it's a direct (symbolic) draw or a
  ## concretized (opaque-combinator) value — see `ConcolicParamBinding`.
  concolicCollectImpl(bindSym"concolicCollect", fn, trace, bindings, settings, maxDraws)

# ---- concolicFlip (RFC-fuzzer-nextgen G2) -----------------------------------

macro concolicFlip*(fn: typed, trace, bindings: typed,
                    targetBranchIndex: typed,
                    settings: static SymexSettings = defaultSymexSettings(),
                    maxDraws: static int = defaultMaxConcolicDraws,
                    maxRelaxationAttempts: static int = defaultMaxRelaxationAttempts,
                    z3TimeoutMs: static uint = defaultZ3TimeoutMs
                   ): ConcolicFlipResult =
  ## The G2 entry: branch-flip solve + choice-sequence materialization (RFC
  ## §G-concolic steps 4-5), with the bounded optimistic fallback. Same
  ## macro-capture contract as `concolicCollect` (routes through
  ## `parseEntryImplWarned`) — `fn`/`trace`/`bindings` are exactly G1b's. G2 adds
  ## `targetBranchIndex`: which recorded `if`-decision (occurrence order
  ## along the concrete replay, i.e. an index into the collected
  ## `branchTrace`) to flip — a caller-supplied designator at G2; G3 wires
  ## frontier-stall selection on top of this later.
  concolicFlipImpl(bindSym"concolicFlip", fn, trace, bindings, targetBranchIndex, settings, maxDraws, maxRelaxationAttempts, z3TimeoutMs)

# ---- allRaiseFindings -------------------------------------------------------

proc allRaiseFindings*[T](r: SymexResult[T]): seq[DefectFinding[T]] =
  ## ADR-0012 D2. Returns the complete set of raise findings for a result:
  ## when `r.status == sxRaised`, prepends a `DefectFinding[T]` built from
  ## the winning branch fields to `r.diagnostics`; otherwise returns
  ## `r.diagnostics` unchanged (which may be non-empty for sxSat results
  ## where incidental raises were discovered before the label was hit).
  ## `isDefect` is derived from the type id suffix; `raisedMsg` is not
  ## available at the public-type level and is always `none`.
  if r.status == sxRaised:
    let winning = DefectFinding[T](
      raisedTypeId: r.raisedTypeId,
      defectKind:   typeIdToDefectKind(r.raisedTypeId),
      isDefect:     r.raisedTypeId.endsWith("Defect"),
      raisedMsg:    none(string),
      witness:      r.raisedWitness,
      heapSnapshot: r.heapSnapshot,
      witnessUndefined: r.soundness.witnessUndefined,   # W3-z R5 (U7)
      witnessUnsafe:    r.soundness.witnessUnsafe)
    @[winning] & r.diagnostics
  else:
    r.diagnostics

macro assertCoveredBy*(fn: typed,
                       target: static SymexTarget,
                       testFn: typed = nil,
                       settings: static SymexSettings = defaultSymexSettings()
                      ): untyped =
  ## Prove that `testFn`, invoked on the symex witness for `target`
  ## inside `fn`, actually exercises that target. Raises
  ## `SymexCoverageDefect` (an `AssertionDefect`) when symex found a
  ## trusted witness (`sxSat` / `sxRaised`, `trusted()`) but the testFn
  ## run did not observe the target. UNSAT vacuously passes; UNKNOWN
  ## raises unless `acceptUnknownAsCovered`. An untrusted witness that
  ## misses is reported as unconfirmed, the way UNKNOWN is, never as
  ## testFn's failure (review R1-15).
  ##
  ## Returns the call's `SymexFinding` (discardable); on failure the
  ## `SymexCoverageDefect` carries it in `findings` (review R1-10).
  ## Inside a `forAll` (nested ones included), the finding is also on the
  ## run's `Report.symexFindings`: one entry per call site and target, the
  ## latest (review R2 DD3, R3 E2, E3). Outside one (a plain test body, a
  ## fuzz or concolic harness, a thread of the property's own) the return
  ## value and the defect are its only channel.
  ##
  ## `testFn` defaults to `fn` itself — the common shape where the
  ## same code under symex is the same code under random PBT.
  ##
  ## Known cosmetic duplicate (RFC-0010 review round 2, finding R2-06): an
  ## incoherent `settings` here prints the `warnIncoherentSettings` warning
  ## TWICE — once as `assertCoveredBy: ...` (this macro's own
  ## `parseEntryImplWarned` call below) and once as `symexFind: ...`,
  ## because the block this macro expands to calls the public `symexFind`
  ## macro internally (see `symexFind(\`fn\`, ...)` a little further down),
  ## which independently re-validates the SAME `settings` through its own
  ## `parseEntryImplWarned` call. Both warnings resolve to the same
  ## compile-time `warning()` statement (`warnIncoherentSettings`, above
  ## `parseEntryImplWarned`); the compiler's instantiation trace for both
  ## points back to this exact call site, so nothing here is misattributed
  ## -- it is genuinely one incoherent `settings` value producing two
  ## printed lines for one user call. This is INTENTIONAL, not a bug to
  ## silence: routing this macro's internal `symexFind` call through raw
  ## `parseEntryImpl` to skip the re-validation was evaluated and rejected
  ## -- it would reopen the exact bypass this RFC closed, for the sole
  ## benefit of quieter output. A `{.compileTime.}`-set dedup keyed on the
  ## call-site `NimNode`'s `lineInfoObj` was also evaluated (round 2
  ## follow-up) and rejected: measured experimentally, the `fn` NimNode
  ## seen INSIDE the nested `symexFind` expansion does not carry this
  ## call site's line info -- it carries the fixed source position of the
  ## `quote do:` block below that constructs the nested call, which is
  ## IDENTICAL for every `assertCoveredBy` call anywhere in the program.
  ## Deduping on it would not merely fail to suppress this pair; it would
  ## silently cross-suppress the SECOND warning from every OTHER, unrelated
  ## incoherent `assertCoveredBy` call in the whole compilation after the
  ## first one -- a correctness regression far worse than double-printed
  ## noise. Two harmless corollaries worth knowing: (1) the multi-target
  ## `assertCoveredBy` overload below dispatches each target to THIS macro,
  ## so an N-target call with incoherent `settings` prints this pair N
  ## times, once per target; (2) a caller invoking `symexFind` directly
  ## never sees the duplicate -- it is specific to routing through
  ## `assertCoveredBy`.
  assertCoveredByImpl(bindSym"assertCoveredBy", fn, target, testFn, settings)

macro assertCoveredBy*(fn: typed,
                       targets: static openArray[SymexTarget],
                       testFn: typed = nil,
                       settings: static SymexSettings = defaultSymexSettings()
                      ): untyped =
  ## Multi-target form: prove `testFn` covers every target. Each
  ## target is dispatched through the single-target `assertCoveredBy`;
  ## failures are accumulated and reported as one aggregate message.
  ## Returns every target's `SymexFinding` (discardable); on failure the
  ## one `SymexCoverageDefect` carries them all (review R1-10).
  let failuresId = genSym(nskVar, "failures")
  let findingsId = genSym(nskVar, "findings")
  result = newStmtList()
  result.add quote do:
    var `failuresId`: seq[string] = @[]
    var `findingsId`: seq[SymexFinding] = @[]
  for t in targets:
    let tNode =
      case t.kind
      of stkLabel:              newCall(bindSym"tLabel", newLit(t.label))
      of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
      of stkIndexError:         newCall(bindSym"tIndexError")
      of stkFieldDefect:        newCall(bindSym"tFieldDefect")
      of stkRaisedExn:          newCall(bindSym"tRaisedExn", newLit(t.typeFilter))
      of stkNilAccess:          newCall(bindSym"tNilAccess")   ## Phase 15 R5
      of stkUndefined:          newCall(bindSym"tUndefined", newLit(t.ubKinds))
    let settingsNode = newLit(settings)
    let inner = newCall(ident"assertCoveredBy", fn, tNode, testFn, settingsNode)
    result.add quote do:
      try:
        `findingsId`.add `inner`
      except SymexCoverageDefect as e:
        `findingsId`.add e.findings
        `failuresId`.add e.msg
  let totalLit = newLit(targets.len)
  let outcomesSym = bindSym"coverageOutcomes"
  result.add quote do:
    `outcomesSym`(`findingsId`, `failuresId`, `totalLit`)
  result = nnkBlockStmt.newTree(newEmptyNode(), result)

# ---- Macro forms for the content-addressed DB API ---------------------------
#
# These macros parse the typed SUT to a SymexProgram (so the IR hash
# in the cache key reflects the same IR the walker will see), then
# delegate to the runtime impl. The pure (testable) part of the key
# derivation lives in nelli/smt/canonicalize.

proc rebuildTargetNode(target: SymexTarget): NimNode =
  ## Macro-time fresh constructor call for `target`. Splicing a
  ## `static SymexTarget` of a non-stkLabel kind directly via
  ## `quote do` triggers Nim to materialise an nnkObjConstr that
  ## names every field — invalid for variants. Rebuilding via the
  ## `t*` constructors is always well-formed.
  case target.kind
  of stkLabel:              newCall(bindSym"tLabel", newLit(target.label))
  of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
  of stkIndexError:         newCall(bindSym"tIndexError")
  of stkFieldDefect:        newCall(bindSym"tFieldDefect")
  of stkRaisedExn:          newCall(bindSym"tRaisedExn", newLit(target.typeFilter))
  of stkNilAccess:          newCall(bindSym"tNilAccess")   ## Phase 15 R5
  of stkUndefined:          newCall(bindSym"tUndefined", newLit(target.ubKinds))

macro symexCacheKeyForFn*(fn: typed,
                           target: static SymexTarget,
                           settings: static SymexSettings =
                             defaultSymexSettings()
                          ): string =
  ## Phase 13 cycle 2 — test helper. Emits a runtime expression
  ## that evaluates to the bare content-addressed key (no
  ## `:sat`/`:unsat`/`:unk` suffix) for `fn` + `target` + `settings`
  ## under the current Z3 / Nim / walker / rendering versions.
  ##
  ## Tests use this to probe `db.loadPrimary` directly without
  ## reconstructing `SymexProgram` by hand, while still pinning the
  ## suffix participation contract. NOT intended for production
  ## consumers — they should use `saveSymexWitness` /
  ## `loadSymexWitnesses` which encapsulate the suffix.
  # Review R1-11: `entryParse`, as every walking entry parses, so the key is
  # the one `symexFindAllWitnesses` writes; no settings warning (no walk here).
  let e = entryParse(fn, "symexCacheKeyForFn", settings,
    newCall(bindSym"symexCacheKeyForFn", fn, targetLit(target), newLit(settings)),
    warn = false)
  if e.again != nil: return e.again
  let progExpr = e.prog
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = `progExpr`
      symexCacheKey(prog, `targetExpr`, `settings`,
                    z3Version        = z3FullVersion(),
                    nimVersion       = NimVersion,
                    walkerVersion    = symexWalkerVersion,
                    renderingVersion = renderAsChoicesVersion)

macro saveSymexWitness*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings,
                        finding: SymexFinding,
                        maxEntries: int = 64): untyped =
  ## Persist `finding`'s witness under the content-addressed cache
  ## key derived from `fn`'s IR, the target, the witness-relevant
  ## subset of `settings`, and the current Z3/Nim/walker versions.
  ## Non-Sat findings are skipped.
  # Review R1-11: `entryParse`, as every walking entry parses, so the key is
  # the one `symexFindAllWitnesses` writes; no settings warning (no walk here).
  let e = entryParse(fn, "saveSymexWitness", settings,
    newCall(bindSym"saveSymexWitness", db, fn, targetLit(target), newLit(settings), finding, maxEntries),
    warn = false)
  if e.again != nil: return e.again
  let progExpr = e.prog
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = `progExpr`
      var dbErrors: seq[string] = @[]
      saveSymexWitnessImpl(`db`, prog, `targetExpr`, `settings`,
                            `finding`, dbErrors, `maxEntries`)
      # RFC-0005 S8av: route through the SAME thread-local sink
      # `symexFindAllWitnesses` drains into `Report.dbErrors` (Phase 14
      # cycle C2), so a caller of this standalone macro sees a save
      # failure via `consumeSymexDbErrors()` instead of it being
      # silently swallowed (was: declared `{.used.}` and discarded —
      # S11's own note on `db.nim`'s "errors flow to Report.dbErrors"
      # promise, left unwired since Phase 13 cycle 7).
      for dbErr in dbErrors:
        recordSymexDbError(dbErr)

macro loadSymexWitnesses*(db: ExampleDatabase, fn: typed,
                          target: static SymexTarget,
                          settings: static SymexSettings
                         ): untyped =
  ## Load previously-persisted witnesses for *exactly* this
  ## SUT/target/settings/Z3/Nim/walker combination, each with its
  ## stored `Soundness` (`seq[CachedWitness]`, RFC-0005 S11).
  ## Mismatched key → empty seq.
  # Review R1-11: `entryParse`, as every walking entry parses, so the key is
  # the one `symexFindAllWitnesses` writes; no settings warning (no walk here).
  let e = entryParse(fn, "loadSymexWitnesses", settings,
    newCall(bindSym"loadSymexWitnesses", db, fn, targetLit(target), newLit(settings)),
    warn = false)
  if e.again != nil: return e.again
  let progExpr = e.prog
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = `progExpr`
      var dbErrors: seq[string] = @[]
      let witnesses = loadSymexWitnessesImpl(`db`, prog, `targetExpr`,
                                              `settings`, dbErrors)
      # RFC-0005 S8av: see `saveSymexWitness`'s identical comment.
      for dbErr in dbErrors:
        recordSymexDbError(dbErr)
      witnesses

# ---- Verdict macro forms (Phase 13 cycle 10) -------------------------------
#
# Mirror `saveSymexWitness` / `loadSymexWitnesses` for non-SAT
# verdicts. `status: SymexFindingStatus` is a runtime value, not
# static — the suffix (`:unsat` vs `:unk`) is dispatched at
# runtime inside `saveSymexVerdictImpl`. RFC-0005 S8av: error
# accumulation routes through `recordSymexDbError`/
# `consumeSymexDbErrors` (the same sink `symexFindAllWitnesses`
# drains into `Report.dbErrors`), so a caller of the standalone
# macro form sees a save/load failure there instead of it being
# silently swallowed; callers wanting a locally-scoped `errors` seq
# instead use the `*Impl` procs directly.

macro saveSymexVerdict*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings,
                        status: SymexFindingStatus,
                        soundness: Soundness): untyped =
  ## Persist a non-SAT verdict (sfUnsat / sfUnknown) for `fn`'s
  ## content-addressed key, with the `soundness` it was decided under
  ## (RFC-0005 S11). No-op for sfSat (use `saveSymexWitness`) and
  ## sfNotApplicable.
  # Review R1-11: `entryParse`, as every walking entry parses, so the key is
  # the one `symexFindAllWitnesses` writes; no settings warning (no walk here).
  let e = entryParse(fn, "saveSymexVerdict", settings,
    newCall(bindSym"saveSymexVerdict", db, fn, targetLit(target), newLit(settings), status, soundness),
    warn = false)
  if e.again != nil: return e.again
  let progExpr = e.prog
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = `progExpr`
      var dbErrors: seq[string] = @[]
      saveSymexVerdictImpl(`db`, prog, `targetExpr`, `settings`,
                            `status`, `soundness`, dbErrors)
      # RFC-0005 S8av: see `saveSymexWitness`'s identical comment.
      for dbErr in dbErrors:
        recordSymexDbError(dbErr)

macro loadSymexVerdict*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings
                       ): untyped =
  ## Load a previously-persisted non-SAT verdict for `fn`'s
  ## content-addressed key. Checks `:unsat` then `:unk`
  ## (UNSAT-first load-order tie-break). Returns
  ## `Option[CachedVerdict]`: the status, its stored `Soundness`
  ## (RFC-0005 S11) and `gaps` (RFC-0005 S8av).
  # Review R1-11: `entryParse`, as every walking entry parses, so the key is
  # the one `symexFindAllWitnesses` writes; no settings warning (no walk here).
  let e = entryParse(fn, "loadSymexVerdict", settings,
    newCall(bindSym"loadSymexVerdict", db, fn, targetLit(target), newLit(settings)),
    warn = false)
  if e.again != nil: return e.again
  let progExpr = e.prog
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = `progExpr`
      var dbErrors: seq[string] = @[]
      let verdict = loadSymexVerdictImpl(`db`, prog, `targetExpr`,
                                          `settings`, dbErrors)
      # RFC-0005 S8av: see `saveSymexWitness`'s identical comment.
      for dbErr in dbErrors:
        recordSymexDbError(dbErr)
      verdict

# ---- Layer 1 — symexFindAllWitnesses ---------------------------------------
#
# Phase 12 cycle 7. The Layer-1 primitive: given a SUT and an
# `ExampleDatabase`, run symex against every auto-discovered target
# in the SUT's IR and return one `SymexFinding` per (review R1-10: as a
# value only; `symexForAll` puts them on its report).
#
# Cycle 7 covers `tLabel` only — `symexTarget("name")` markers
# extracted via `irCollectLabels` (cycle 4) walking transitively
# through `parseProc`'s callee table. Cycles 8-10 add the three
# auto-included defect targets. Cycle 11 adds `excludeTargets`.
# Cycle 12 wires the DB cache.

macro symexFindAllWitnesses*(fn: typed,
                              db: ExampleDatabase,
                              symexSettings: static SymexSettings =
                                defaultSymexSettings(),
                              # Constructor-form list of targets to suppress
                              # from auto-discovery. Comparison is by
                              # `SymexTargetKind` (label-by-name suppression
                              # is out of scope). Not `static` because Nim 2.2
                              # rejects every viable default expression for a
                              # `static seq[T]` parameter; instead the macro
                              # inspects the call-site AST directly via the
                              # NimNode it receives.
                              excludeTargets: seq[SymexTarget] = @[]
                             ): seq[SymexFinding] =
  ## Run symex against every auto-discovered target in `fn`. Returns
  ## one `SymexFinding` per target, in IR-traversal order.
  symexFindAllWitnessesImpl(bindSym"symexFindAllWitnesses", fn, db, symexSettings, excludeTargets)

# =============================================================================
# RFC-0005 S8ah -- build-time wiring of the compile-time VM let-aliasing
# guard (`smt/vm_alias_guard.nim`) onto the REAL symex compile path, opt-in
# behind `-d:nelliVmAliasAudit` so an ordinary `import nelli/symex` compile
# (every user who is not running this repo's own CI) pays nothing: the
# `when defined` condition is false, so this whole block -- including the
# `import` itself -- is never semantically checked, only parsed as a
# skipped statement. Measured (S8ah's own note in the RFC): with the define
# OFF, compiling `tests/tsymex_phase15_F8_smoke.nim` (a small, representative
# symex test) shows no measurable difference against the pre-S8ah baseline;
# with it ON, the guard's own reflection walk adds a few seconds (the same
# order of cost `tsymex_rfc0005_s8ab_letaudit.nim` itself already pays every
# `nimble test`/`dt-bounded.sh` run) -- acceptable for CI, not for every
# user's build, hence opt-in rather than unconditional.
#
# `vm_alias_guard.nim` audits the OTHER 15 files in scope (14 directly via
# `{.all.}}` imports, plus itself covers none of symex.nim -- see its own
# header for why `concolic.nim` is ALSO excluded there, to avoid an import
# cycle). This block covers the 16th: symex.nim's OWN top-level routines,
# self-audited (no `{.all.}}` import needed to reflect on your own module).
when defined(nelliVmAliasAudit):
  import ./smt/vm_alias_guard
  import ./smt/witness_render {.all.}
  import ./smt/symex_cache {.all.}
  import ./smt/witness_emit {.all.}
  import ./smt/replay_footprint {.all.}
  import ./smt/routine_table {.all.}
  import ./smt/witness_fidelity {.all.}
  import ./smt/heldset {.all.}
  import ./smt/replay_emit {.all.}
  import ./smt/replay_settle {.all.}
  import ./smt/proc_lift {.all.}
  import ./smt/run_replayed {.all.}
  import ./smt/entry_parse {.all.}
  import ./smt/cover_emit {.all.}
  import ./smt/find_emit {.all.}
  import ./smt/findall_emit {.all.}

  # RFC-0016 D6: the implementation `symex.nim` used to hold lives in these
  # modules now. They are audited here, by the same mechanism and under their
  # own file tag, so a move out of this file never takes code out of the audit.
  const symexSmtDir = currentSourcePath().parentDir / "smt"
  const symexMovedFiles = ["witness_render.nim", "symex_cache.nim", "witness_emit.nim", "replay_footprint.nim", "routine_table.nim", "witness_fidelity.nim", "heldset.nim", "replay_emit.nim", "replay_settle.nim", "proc_lift.nim", "run_replayed.nim", "entry_parse.nim", "cover_emit.nim", "find_emit.nim", "findall_emit.nim"]

  template auditMoved(fname: string) =
    const movedPath = symexSmtDir / fname
    const movedNames = extractTopLevelNames(movedPath)
    vmGuardAuditNames(movedNames, fname)

  auditMoved "witness_render.nim"
  auditMoved "symex_cache.nim"
  auditMoved "witness_emit.nim"
  auditMoved "replay_footprint.nim"
  auditMoved "routine_table.nim"
  auditMoved "witness_fidelity.nim"
  auditMoved "heldset.nim"
  auditMoved "replay_emit.nim"
  auditMoved "replay_settle.nim"
  auditMoved "proc_lift.nim"
  auditMoved "run_replayed.nim"
  auditMoved "entry_parse.nim"
  auditMoved "cover_emit.nim"
  auditMoved "find_emit.nim"
  auditMoved "findall_emit.nim"

  const symexSelfNames = extractTopLevelNames(currentSourcePath())
  vmGuardAuditNames(symexSelfNames, "symex.nim")

  proc symexOwnTag(h: string): bool =
    ## A hit key is `<file>:<routine>...`: this module's own or a moved one's.
    if h.startsWith("symex.nim:"): return true
    for f in symexMovedFiles:
      if h.startsWith(f & ":"): return true
    false

  const symexSelfLetHits = block:
    var dedup: seq[string]
    for h in vmGuardLetHits:
      if symexOwnTag(h) and h notin dedup: dedup.add h
    dedup

  const symexSelfParamHits = block:
    var dedup: seq[string]
    for h in vmGuardParamHits:
      if symexOwnTag(h) and h notin dedup: dedup.add h
    dedup

  const symexSelfReachHits = block:
    var dedup: seq[string]
    for h in vmGuardReachHits:
      if symexOwnTag(h) and h notin dedup: dedup.add h
    dedup

  # The one historical hazard S8x/S8ab/S8af already reviewed and allowlisted
  # in symex.nim's own scope: `emitTyAndReaderShared`'s nested
  # `emitMVBranch`, reading a `VariantAxis`/`VariantArm` element with
  # nothing written while the binding is live (the `types.nim:==` twin of
  # this same finding is allowlisted in `vm_alias_guard.nim`'s own block).
  const symexSelfLetAllowlist = [
    "witness_emit.nim:emitTyAndReaderShared: let ax : VariantAxis (ntyObject) <- ty.mvAxes[axisIdx]",
    "witness_emit.nim:emitTyAndReaderShared: let elseArm : VariantArm (ntyObject) <- ax.arms[elseArmIx]",
  ]

  # RFC-0005 S8ah: symex.nim's own macros (`symexFindAllWitnesses`) call
  # `traceOneCallBoundary[seq[NimNode]]` directly (unquoted) -- but forcing
  # that instantiation for audit needs `{.all.}}` visibility into
  # `dsl_parser.nim`'s private symbol, which symex.nim does not have (and
  # should not need just to self-audit). `vm_alias_guard.nim`'s own
  # 14-file self-audit already forces and audits that exact instantiation
  # as a side effect of the `import` above (module-level code runs once,
  # at import time) and records it in the GLOBAL `vmGuardForcedGenerics`
  # list -- the completeness check below reads THAT, not a local
  # symex.nim-only copy, so it sees the forcing regardless of which module
  # performed it.
  static:
    doAssert vmGuardWalkErrs.len == 0,
      "symex.nim self-audit: getImpl/audit-machinery error:\n" & vmGuardWalkErrs.join("\n")
    var unexpectedLets: seq[string]
    for h in symexSelfLetHits:
      if h notin symexSelfLetAllowlist: unexpectedLets.add h
    doAssert unexpectedLets.len == 0,
      "symex.nim self-audit: unallowlisted compile-time VM let-aliasing " &
      "hazard (RFC-0005 S8ab/S8x) -- fix it or add a reviewed allowlist " &
      "entry with a justification:\n" & unexpectedLets.join("\n")
    doAssert symexSelfParamHits.len == 0,
      "symex.nim self-audit: unallowlisted compile-time VM param-aliasing " &
      "hazard:\n" & symexSelfParamHits.join("\n")
    var reachableGenerics: seq[string]
    for h in symexSelfReachHits:
      let genericKey = h.split(" -> ")[^1]
      if genericKey notin reachableGenerics: reachableGenerics.add genericKey
    var unforced: seq[string]
    for g in reachableGenerics:
      if g notin vmGuardForcedGenerics: unforced.add g
    doAssert unforced.len == 0,
      "symex.nim self-audit: a macro directly (unquoted) calls a generic " &
      "with no forced-instantiation audit (RFC-0005 S8ah item 1/3):\n" &
      unforced.join("\n")

