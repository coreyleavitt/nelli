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

import std/[macros, sets, tables, algorithm, options, strutils, importutils, macrocache]
from std/os import extractFilename
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
import ./smt/scan
import ./smt/scan_kinds   ## RFC-0016 K2F-3: the shared scan kind lists
import ./smt/impl_digest   ## RFC-0005 review R1-09
import ./smt/replayproc   ## RFC-0005 S8ct
import ./smt/replaywire   ## RFC-0005 S8ct
import ./smt/replayresult ## RFC-0005 0.9.1 (review R1-06, R1-14)
export replayExecutions
export replayresult.ReplayOutcome, replayresult.ReplayResult,
       replayresult.outcome, replayresult.child,
       replayresult.detail, replayresult.runDependence
from ./smt/scoped_names import isModuleGlobal, isRoutineGlobal, globalIRName   ## RFC-0005 S8bn
import ./engine/types as engineTypes
from ./engine/frame import recordSymexFinding, FindingOrigin   ## review R2 (DD3)
import ./smt/sha256   ## review R5 (3d): `fnIdLit` hashes a non-symbol `fn`
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

proc describeTarget*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "label(\"" & t.label & "\")"
  of stkAssertionViolation: "assertion-violation"
  of stkIndexError:         "index-error"
  of stkFieldDefect:        "field-defect"
  of stkRaisedExn:                                       ## Phase 15 E2a
    if t.typeFilter.len == 0: "raised-exn(any)"
    else:                     "raised-exn(" & t.typeFilter & ")"
  of stkNilAccess:          "nil-access"                 ## Phase 15 R5
  of stkUndefined:                                       ## RFC-0016 K10a-target
    if t.ubKinds == allUbKinds: "undefined(all)"
    else:
      var names: seq[string]
      for k in t.ubKinds: names.add $k
      "undefined(" & names.join(",") & ")"

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
import ./smt/routine_table   ## RFC-0016 D6: the routine table a replay child carries
import ./smt/witness_fidelity   ## RFC-0016 D6: witness fidelity + the splat
import ./smt/heldset   ## RFC-0016 D6: the held-set walk
import ./smt/symex_cache   ## RFC-0016 D6: the DB record codecs
export symex_cache.saveSymexNotesImpl, symex_cache.loadSymexNotesImpl,
       symex_cache.saveSymexWitnessImpl, symex_cache.loadSymexWitnessesImpl,
       symex_cache.saveSymexVerdictImpl, symex_cache.loadSymexVerdictImpl,
       symex_cache.saveSymexRaisedImpl, symex_cache.loadSymexRaisedImpl,
       symex_cache.toFindingStatus, symex_cache.CachedWitness,
       symex_cache.CachedVerdict, symex_cache.CachedRaised, symex_cache.CachedNotes


type
  SymexCoverageDefect* = object of AssertionDefect
    ## Review R1-10. What `assertCoveredBy` raises when coverage is not
    ## proven, carrying the finding(s) the call made: a finding belongs to
    ## the call that produced it, on failure as on success (it was a
    ## thread-local sink that leaked into later callers).
    findings*: seq[SymexFinding]

proc coverageOutcome(origin: FindingOrigin; f: SymexFinding;
                     failure: string): SymexFinding {.discardable.} =
  ## Review R1-10. The end of a single-target `assertCoveredBy`: its finding,
  ## or a `SymexCoverageDefect` carrying it when `failure` says why coverage
  ## is not proven. Review R2 (DD3): inside a property, the finding also
  ## goes on the run's report (`recordSymexFinding`), on success or failure;
  ## review R3 (E2): as the latest of its call site `site` for its target.
  ## Outside any property, the return and the defect are its only channel.
  recordSymexFinding(origin, f)
  if failure.len > 0:
    var e = newException(SymexCoverageDefect, failure)
    e.findings = @[f]
    raise e
  f

proc coverageOutcomes(fs: seq[SymexFinding]; failures: seq[string];
                      total: int): seq[SymexFinding] {.discardable.} =
  ## Review R1-10. The end of a multi-target `assertCoveredBy`: every
  ## target's finding, or one `SymexCoverageDefect` carrying them all.
  if failures.len > 0:
    var msg = "assertCoveredBy (multi): " & $failures.len &
              " of " & $total & " targets uncovered:"
    for f in failures:
      msg.add "\n  - " & f
    var e = newException(SymexCoverageDefect, msg)
    e.findings = fs
    raise e
  fs


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

proc wireTarget*(w: var WireWriter; t: SymexTarget) =
  ## RFC-0005 S8ct. A case object, so outside the generic encoding.
  wirePut(w, t.kind)
  case t.kind
  of stkLabel: wirePut(w, t.label)
  of stkRaisedExn: wirePut(w, t.typeFilter)
  of stkUndefined: wirePut(w, t.ubKinds)   ## RFC-0016 K10a-target
  else: discard

proc readTarget*(r: var WireReader): SymexTarget =
  ## RFC-0005 S8ct. See `wireTarget`.
  var k: SymexTargetKind
  wireGet(r, k)
  case k
  of stkLabel:
    var s: string
    wireGet(r, s)
    SymexTarget(kind: stkLabel, label: s)
  of stkRaisedExn:
    var s: string
    wireGet(r, s)
    SymexTarget(kind: stkRaisedExn, typeFilter: s)
  of stkAssertionViolation: SymexTarget(kind: stkAssertionViolation)
  of stkIndexError: SymexTarget(kind: stkIndexError)
  of stkFieldDefect: SymexTarget(kind: stkFieldDefect)
  of stkNilAccess: SymexTarget(kind: stkNilAccess)
  of stkUndefined:
    var ks: set[UbKind]
    wireGet(r, ks)
    SymexTarget(kind: stkUndefined, ubKinds: ks)

func targetLabelOf*(t: SymexTarget): string =
  ## RFC-0005 S8ct. The label a child reports as it is hit, or none.
  if t.kind == stkLabel: t.label else: ""

type ChildWitness = object
  ## RFC-0005 S8ct. How a re-executed child comes by its witness, where it is not
  ## the rendered tuple itself: the entry macros marshal the solver's model
  ## (`blob`, of type `blobTy`), and the child renders it as the host does:
  ## `decl` binds `witId` from `blobId`.
  blob, blobTy, blobId, decl, witId: NimNode

var replaySiteCounter {.compileTime.}: int

proc paramsFidelity(params: seq[IRParam]): WitnessFidelity =
  ## How faithfully a witness of `params` renders: the worst parameter's
  ## `witnessFidelity`.
  var noms: Table[string, IRType]
  var seenNoms: HashSet[string]
  for p in params: collectNominals(p.ty, noms, seenNoms)
  result = wfFaithful
  for p in params: result = max(result, witnessFidelity(p.ty, noms))

proc emitReplayWitness*(fn: NimNode; params: seq[IRParam];
                        witness, target, pathTaint: NimNode;
                        extraLossy: NimNode = newLit(false);
                        nilDeref: NimNode = newLit(false);
                        timeoutMs: NimNode = newLit(
                          SymexSettings().replayTimeoutMs);
                        child: ChildWitness = ChildWitness()): NimNode =
  ## RFC-0005 S2: the macro-time half of `replayWitness`, spliced by S10 into
  ## the entry macros' shared replay emitter (`emitRunSymexReplayed`). Emits
  ## an expression of type `ReplayResult`. `witness` is the typed witness
  ## tuple (the output of `emitTyAndReader`), `target` a `SymexTarget`
  ## expression, `pathTaint` a `Taint` expression (the candidate's).
  ## `extraLossy` (RFC-0005 S10) is a runtime `bool`: true when the model
  ## behind this witness is known NOT to be the rendered value even though
  ## its shape renders faithfully -- a candidate whose extraction recorded
  ## `feExtractionFailed` (a float leaf substituted by `0.0`). It demotes a
  ## miss from `roRefuted` to `roInconclusive`; a hit still confirms.
  ## `nilDeref` (RFC-0005 S8k) is a runtime `bool`: true when the witness's
  ## path went through the walker's nil-dereference edge
  ## (`SatCandidate.nilDerefOnPath`). Order of refusal, each one WITHOUT
  ## executing `fn`: ineligible taint, unexecutable witness shape, out-of-scope
  ## target kind, a nil-dereference path.
  ## `timeoutMs` (RFC-0005 S8be) is an `int` expression bounding the run;
  ## past it the child is killed and the outcome is `roTimedOut`.
  ## RFC-0005 S8ct: the run itself happens in a child process
  ## (`replayproc.nim`), never in this one.
  let fidelity = paramsFidelity(params)
  if fidelity == wfUnexecutable:
    # Decided at macro time: the splat is not even emitted, so a placeholder
    # (a nil proc, a nil ptr) can never be called.
    return newCall(bindSym"replayNotRun")
  let paramTys = formalParamTypes(fn)
  if paramTys.len != params.len:
    return newCall(bindSym"replayNotRun")   # not a plain proc type: never run it
  let witId = genSym(nskLet, "replayWit")
  let tgtId = genSym(nskLet, "replayTarget")
  let escId = genSym(nskVar, "replayEscaped")
  let boundId = genSym(nskVar, "replayArgsBound")
  let hitsId = genSym(nskLet, "replayHits")       # RFC-0005 S8be
  let childRes = genSym(nskLet, "replayChild")    # RFC-0005 S8ct
  # RFC-0005 S8bn (item 2): the module-level `var`s `fn` can reach, which a
  # `ptr` parameter's witness may be aimed at.
  var globals: seq[NimNode]
  for g in calleeOuterSyms(fn):
    if isModuleGlobal(g) and g.symKind == nskVar: globals.add g
  # The run: a statement list whose value is the `ReplayReport`, spliced into
  # the child's half on whichever side declares it. §4.2 "Capture reentrancy":
  # a nested frame, so an enclosing user capture (`assertCoveredBy`) keeps its
  # hits and does not see ours.
  proc runBody(childWitId, childTgtId: NimNode): NimNode =
    let splat = emitWitnessSplat(fn, params.len, childWitId, paramTys,
                                 newAssignment(boundId, newLit(true)),
                                 params, globals)
    result = quote do:
      var `escId`: ref Exception = nil
      var `boundId` = false
      symexCaptureBegin()
      armReplayHit(targetLabelOf(`childTgtId`))
      try:
        `splat`
      except Exception as e:
        `escId` = e
      let `hitsId` = symexCaptureEnd()
      ReplayReport(reached: replayReached(`childTgtId`, `hitsId`, `escId`),
                   bound: `boundId`)
  let lossy = newLit(fidelity == wfLossy)
  # RFC-0005 S10. The rendered witness type is not always the parameter
  # type (a `Rune` renders as `int`, a `distinct` as its base, a table as
  # the reader's own instantiation). `convertible` is a COMPILE-TIME check
  # that every argument converts; a witness that does not is never run
  # (`roInconclusive`, permanently -- the same as a placeholder shape).
  # `converted` marks a run whose arguments went through a conversion: its
  # hit still confirms (it is a real execution of `fn` on a concrete input),
  # but a miss only demotes to `roInconclusive`, because a conversion may
  # round (`float32`) and so the input run need not be the model.
  var convertible = newLit(true)
  var converted = newLit(false)
  for i in 0 ..< params.len:
    let elem = nnkBracketExpr.newTree(witId, newLit(i))
    let ty = paramTys[i]
    convertible = infix(convertible, "and",
                        newCall(bindSym"compiles", newCall(ty, elem)))
    converted = infix(converted, "or", infix(elem, "isnot", ty))
  var preamble = newStmtList()
  var runChild: NimNode
  when replayForks:
    let body = runBody(witId, tgtId)
    runChild = quote do:
      runReplayForked(proc (): ReplayReport {.closure, gcsafe.} =
        {.cast(gcsafe).}:
          result = (block:
            `body`), `timeoutMs`)
  elif replayReexecs:
    # What the SUT may reach must be handed over, or it does not run.
    var refuse = ""
    let fp = replayFootprint(fn)
    if fp.open:
      refuse = fp.why
    else:
      for g in fp.globals:
        if not isWireableType(g.getTypeInst):
          refuse = "`" & g.strVal & "`, of a type the wire cannot carry"
          break
    let blobTy =
      if child.blobTy != nil: child.blobTy
      else: newCall(bindSym"typeof", witness)
    if refuse.len == 0 and child.blobTy == nil and
       not isWireableType(witness.getTypeInst):
      refuse = "the witness, of a type the wire cannot carry (a ref " &
               "to an inheritable object, an imported C struct, a proc)"
    if refuse.len > 0:
      let msg = newLit(refuse)
      runChild = quote do:
        refusedNotMarshallable(`msg`)
    else:
      inc replaySiteCounter
      let info = lineInfoObj(fn)
      let site = newLit(info.filename.extractFilename & ":" & $info.line & ":" &
                        $info.column & "#" & $replaySiteCounter)
      let rd = genSym(nskVar, "replayReader")
      let wr = genSym(nskVar, "replayWriter")
      let payload = genSym(nskParam, "payload")
      # Named by the site's count, which no other expansion shares (a symbol
      # made here would trip the N2 audit's routine-kind scan).
      let childProc = ident("nelliReplayChildBody" & $replaySiteCounter)
      let regId = genSym(nskVar, "replayChildRegistered")
      let stackId = genSym(nskVar, "replayStack")
      let blobId = if child.blobId != nil: child.blobId
                   else: genSym(nskVar, "replayBlob")
      # The child's own symbols, never the host side's: a genSym'd symbol declared
      # twice has one owner, and a child proc nested in a routine would then be
      # capturing the routine's local.
      let wid = if child.witId != nil: child.witId
                else: genSym(nskLet, "childWitness")
      let childTgt = genSym(nskLet, "childTarget")
      let decl =
        if child.decl != nil: child.decl
        else:
          let b = blobId
          quote do:
            let `wid` {.used.} = `b`
      let body = runBody(wid, childTgt)
      # RFC-0016 PRC-02. The routines a proc value may name, in one order for
      # both ends (the child is this binary): a slot a routine cannot fill
      # (one whose address cannot be taken) holds nil, which no value matches.
      # RFC-0016 W3-z R10: held in a `{.global.}` beside the child's entry, so
      # both ends take a nested routine's address where it can be taken
      # (module-level code, `nestedRoutineAddrs`), the child before it runs.
      let table = emitRoutineTable(fp)
      let tableExpr = table.procs
      let envOkExpr = table.envOk
      let envBenignExpr = table.envBenign
      let envPutExpr = table.envPut
      let envGetExpr = table.envGet
      let envWhyExpr = table.envWhy
      let registry = genSym(nskVar, "replayRoutines")
      var getGlobals = newStmtList()
      var putGlobals = newStmtList()
      for g in fp.globals:
        getGlobals.add quote do:
          wireGet(`rd`, cast[ptr typeof(`g`)](unsafeAddr `g`)[])
        # RFC-0016 W3-z R10 follow-up: the decline names the variable whose
        # value cannot cross, as a forked run's unlifted hint does.
        let gName = newLit("`" & g.strVal & "` holds ")
        putGlobals.add quote do:
          try:
            wirePut(`wr`, `g`)
          except WireError as e:
            raise newException(WireError, `gName` & e.msg)
      let blob = if child.blob != nil: child.blob else: witId
      # RFC-0016 PRC-02b. The child is this binary, so the toolchain's table of
      # what each method dispatcher can run says what it would run: a body no
      # scan read declines. Empty (nothing to ask) without a method in the scan.
      var dispatchCheck = newLit("")
      when hasMethodTable:
        if fp.dispatched.len > 0:
          var names = nnkBracket.newTree()
          var calls = nnkBracket.newTree()
          var addrs = nnkBracket.newTree()
          for m in fp.dispatched:
            names.add newLit(m.strVal)
            calls.add quote do: cast[pointer](`m`)
          for m in fp.methods:
            addrs.add quote do: cast[pointer](`m`)
          dispatchCheck = newCall(bindSym"methodDispatchRefusal",
                                  nnkPrefix.newTree(ident"@", names),
                                  nnkPrefix.newTree(ident"@", calls),
                                  nnkPrefix.newTree(ident"@", addrs))
      # The host runs no child for a witness that does not convert (`convertible`
      # below); the child's splat must not be compiled for one either.
      var childConvertible = newLit(true)
      for i in 0 ..< params.len:
        let elem = nnkBracketExpr.newTree(wid, newLit(i))
        childConvertible = infix(childConvertible, "and",
          newCall(bindSym"compiles", newCall(paramTys[i], elem)))
      let guarded = quote do:
        when `childConvertible`:
          `body`
        else:
          ReplayReport()
      let slotsTy = bindSym"RoutineSlots"
      preamble = quote do:
        var `registry` {.global.}: `slotsTy`
        proc `childProc`(`payload`: string): ReplayReport {.nimcall.} =
          var `rd` = initWireReader(`payload`, `registry`)
          `rd`.envGet = `envGetExpr`
          var `stackId`: int64
          wireGet(`rd`, `stackId`)
          let `childTgt` = readTarget(`rd`)
          var `blobId`: `blobTy`
          wireGet(`rd`, `blobId`)
          `getGlobals`
          readHostHooks(`rd`)
          `decl`
          result = (block:
            `guarded`)
        # The table is filled by the entry's own initialiser, so whenever
        # that runs (in the child, before the SUT), it is filled first.
        var `regId` {.global, used.} = (block:
          `registry` = `tableExpr`
          replayChildEntry(`site`, `childProc`))
      runChild = quote do:
        block:
          var `wr`: WireWriter
          `wr`.procs = `tableExpr`
          `wr`.envOk = `envOkExpr`
          `wr`.envBenign = `envBenignExpr`
          `wr`.envPut = `envPutExpr`
          `wr`.envWhy = `envWhyExpr`
          var refused = ""
          try:
            wirePut(`wr`, int64(callerStackSize()))
            wireTarget(`wr`, `tgtId`)
            wirePut(`wr`, `blob`)
            `putGlobals`
          except WireError as e:
            refused = e.msg
          if refused.len > 0: refusedNotMarshallable(refused)
          else:
            # RFC-0005 batch 11: what the host installed at run time, which the
            # child would start without (`putHostHooks`: RFC-0016 INT-13 hands
            # it the ones it can). RFC-0005 0.9.1 (WA-7): set at this moment
            # only, so the decline is not cached.
            let hook = putHostHooks(`wr`)
            let dispatch = `dispatchCheck`
            if hook.len > 0: refusedHostHook(hook)
            elif dispatch.len > 0: refusedNotMarshallable(dispatch)
            else: runReplayReexec(`site`, `wr`.data, `timeoutMs`)
  else:
    runChild = quote do:
      refusedStatically("this platform has no way to run a replay outside " &
                        "the host process")
  result = quote do:
    block:
      `preamble`
      let `tgtId`: SymexTarget = `target`
      if not replayEligible(`pathTaint`) or not replayInScope(`tgtId`) or
         `nilDeref`:
        replayNotRun()
      else:
        let `witId` {.used.} = `witness`
        when not (`convertible`):
          replayNotRun()
        else:
          # RFC-0005 S8ct: the run is in a child: the host learns how it ended.
          let `childRes` = `runChild`
          replayResultOf(`childRes`, `lossy` or `extraLossy` or `converted`)

proc methodPrelude(fn: NimNode): NimNode

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

# ---- Replay wired into the verdict (RFC-0005 S10, §2.3 rule 3) ---------------
#
# `runSymex` ends at `decideVerdict`, which cannot apply rule 3 (replay needs
# `fn`, and `runSymex` is runtime code with none -- §4.2 "Plumbing"). So a run
# whose only SAT lies on an `scSpurious`-tainted path returns `sxUnknown` with
# its SOLVED models in `RawResult.candidates` (`SatCandidate`), and the entry
# macro settles them here, after `runSymex` returns and BEFORE any
# `SymexResult`/`SymexFinding` is built or anything is persisted.
#
# CANDIDACY IS UNSPELLABLE AS SAT. A `SatCandidate` is not a `RawResult` and
# has no witness branch; its model is the private `input` field. This module
# alone reads it (`privateAccess`), through the two procs below, both
# private and reached from generated code only via `bindSym` inside
# `emitRunSymexReplayed`:
#   * `candidateInput` -- the model, for rendering the witness to REPLAY;
#   * `settleCandidate` -- the ONLY constructor of a `sxSat`/`sxRaised`
#     `RawResult` from a candidate, and only on `roConfirmed`.
# And `emitRunSymexReplayed` is the only place in this module that emits a
# `runSymex` call (pinned by `tsymex_rfc0005_s10_replay_verdict`), so an entry
# macro cannot obtain a `RawResult` that skipped the settle: forgetting replay
# is not expressible, and even a hand-rolled caller of `runSymex` elsewhere
# can only ever see a candidate's metadata, never a witness to report.
#
# REPLAY HAZARDS (§4.2), as contained here:
#   * Contract change -- `symexFind`/`symexFindAllWitnesses`/`symexForAll` now
#     EXECUTE `fn` at verdict time, on solver-chosen inputs, whenever a run's
#     only SAT is a replay-eligible candidate. Its side effects happen for
#     real, in the caller's process (a `scSpurious` path is tainted precisely
#     because it ran through something unmodelled, often an effect). Nothing
#     runs for a clean verdict, an `sxUnsat`, or an ineligible candidate.
#   * Link/load -- because the settle references `fn`, `fn` and its callees
#     are code-generated, linked and loaded into the caller's binary even
#     when no candidate is ever replayed (an undefined `importc`, a missing
#     `dynlib` such as `std/re`'s PCRE, now fails the build or start-up).
#     Not containable at runtime; `SymexSettings.replay = false` (static)
#     emits no reference to `fn` at all -- the pre-S10 verdict.
#   * Non-termination -- bounded by the eligibility gate, which never runs a
#     `dcFabricated` (k-unroll survivor) witness, and by `replayTimeoutMs`: the
#     replay's child is killed past it (`roTimedOut`).
#   * Defects -- caught by the replay frame and classified; under
#     `--panics:on` nothing is replayed (`replayInScope`); a raw-`ptr`
#     witness is never executed (`witnessFidelity`); a candidate whose path
#     went through the walker's nil-dereference edge, escaping or caught,
#     is never executed (RFC-0005 S8k: `nilDerefOnPath`, and a
#     `NilAccessDefect` raise target is out of `replayInScope`) -- the
#     walker models that edge as a raise, the default build SIGSEGVs.
#   * Crashes -- RFC-0005 S8ct: whatever else the real `fn` does on the witness
#     (SIGSEGV, stack overflow, `quit`, `abort`, memory corruption) ends its
#     child and is reported (`roCrashed`, `feReplayCrashed`), never `sxUnsat`.
#   * Capture reentrancy -- each replay runs in its own nested capture frame
#     (`engine/markers.nim`), so a user's enclosing `assertCoveredBy`
#     capture neither loses hits nor sees replay's.
#   * Bounded replays -- candidates are replayed in discovery order, `sxSat`
#     claims before `sxRaised` claims (ADR-0012 D2's precedence, as rules
#     1-2), and the settle STOPS at the first `roConfirmed`: at most one
#     confirming execution, plus one per earlier refuted/declined candidate.
#
# THE TWO BLANKET VETOES (§2.5) are not consulted: they distrust the MODEL
# (a cap or closure decline anywhere), and a confirmed replay is a fact about
# the REAL `fn` -- it reached the target on a concrete input -- that no model
# defect can make false. Rules 1-2 still precede rule 3 (a clean winner means
# the raw status is already `sxSat`/`sxRaised`, and the settle is skipped).
#
# RFC-0005 0.9.1 (WA-9) -- ONE exception: a clean winner whose witness renders
# lossily (`winnerLossy`). Its path reaches the target, but the witness it
# reports is not the model's, so it is replayed as the pass's one job and
# settled by `settleWinner`: `rsConfirmed` on a confirmation, else
# `rsUnconfirmed` (status unchanged, not `trusted()`, with a hint).

privateAccess(SatCandidate)

proc candidateInput(c: SatCandidate): auto =
  ## RFC-0005 S10. The candidate's model, for the replay codegen to render
  ## into `fn`'s parameter tuple. Private: see the section comment.
  c.input

func candidateLossy*(c: SatCandidate): bool =
  ## RFC-0005 S10. True when the candidate's own extraction substituted a
  ## value (`feExtractionFailed`: a float leaf that did not resolve to a
  ## numeral was rendered `0.0`), so the rendered witness is not the model
  ## even where its shape is faithful -- replay's `extraLossy`.
  for e in c.errors:
    if e.kind == feExtractionFailed: return true
  false

type ProcValueLift = object
  ## RFC-0016 W3-z R7. What the replayed run's proc-valued variables held
  ## (`emitProcValueLift`): `named`, every variable the walk reported
  ## (`RawResult.procValueSites`) held, when the run started, a routine of
  ## the replay's footprint, and no code the run may execute writes it but
  ## with a routine named there, while every proc value the run's state holds
  ## is one of the footprint's routines (so no code the scan did not read can
  ## run); `kinds`, what those routines' bodies may reach
  ## (`routineUndefinedKinds`). Not `named`: nothing is replaced.
  named: bool
  kinds: set[UbKind]
  why: string
    ## RFC-0016 W3-z R10. Not `named`: why, naming what (the hint a confirmed
    ## claim whose kinds stay carries, `procValueUnliftedHint`).

func liftedUndefined(c: SatCandidate; lift: ProcValueLift): set[UbOrdinal] =
  ## RFC-0016 W3-z R7. The confirmed claim's `witnessUndefined`: the kinds only
  ## a call through a proc-valued variable put there
  ## (`witnessUndefinedViaOnly`, "may be undefined": the variable may hold any
  ## routine of its type) are replaced by what the routines the replayed run's
  ## variables held reach. Run-dependent by construction: it reads the state
  ## the replay ran from.
  if not lift.named or c.witnessUndefinedViaOnly == {}:
    return c.witnessUndefined
  (c.witnessUndefined - c.witnessUndefinedViaOnly) + ubOrdinals(lift.kinds)

func procValueUnliftedHint(c: SatCandidate; lift: ProcValueLift): SymexErrorInfo =
  ## RFC-0016 W3-z R10. A confirmed claim whose kinds a call through a
  ## module-level proc-valued variable put there (`witnessUndefinedViaOnly`)
  ## stay: the settle could not name the routine the variable held
  ## (`ProcValueLift.why`). The re-executed child's decline is the same kind.
  var kinds: seq[string]
  for o in c.witnessUndefinedViaOnly: kinds.add $UbKind(ord(low(UbKind)) + int(o))
  let why = if lift.why.len > 0: lift.why else: "no reason was recorded"
  SymexErrorInfo(kind: feReplayDeclined, severity: sevHint,
    msg: "replay confirmed the claim, but did not name the routine a " &
         "proc-valued variable held, so what the call through it may reach " &
         "stays (" & kinds.join(", ") & "): " & why & " (" &
         $feReplayDeclined & ")")

proc settleCandidate(raw: RawResult; c: SatCandidate;
                     replayed: ReplayResult; input: string;
                     lift: ProcValueLift): RawResult =
  ## RFC-0005 S10 (§2.3 rule 3). Applies ONE candidate's replay to the
  ## `sxUnknown` result `raw`, by its `outcome`:
  ##   * `roConfirmed` -- the verdict becomes the candidate's claim
  ##     (`sxSat`/`sxRaised`) carrying its model as the witness, its
  ##     `pathTaint` (still `scSpurious`, with RFC-0005 S11's `replay =
  ##     rsConfirmed` beside it -- the one writer of `rsConfirmed`) and its
  ##     own extraction errors after the run's. RFC-0005 0.9.1 (WA-2): a child
  ##     that ended or hung after the target sets `witnessUnsafe`, with a
  ##     `feReplayCrashed`/`feReplayTimedOut` hint (`confirmedEnding`). No
  ##     `diagnostics`: every other finding is either a candidate nobody
  ##     confirmed or a clean one an unplaced decline suppressed
  ##     (`decideVerdict`'s `reachUnknown`, RFC-0005 S9).
  ##   * any other -- stays `sxUnknown` (a refuted candidate too, by rule 4:
  ##     the enlarged program reaches the target; never `sxUnsat`), with the
  ##     replay's hint (`candidateHint`): none for `roInconclusive`.
  ## Either way the replay's run-dependence joins the verdict's (WA-7).
  ## Private (the only candidate -> verdict constructor); see the section
  ## comment.
  result = raw
  if replayed.outcome != roConfirmed:
    result.errors.add candidateHint(replayed, c.status, c.raisedTypeId, input)
    result.soundness.runDependence.incl replayed.runDependence
    return
  case c.status
  of sxSat:
    result = RawResult(status: sxSat, witness: c.input)
  of sxRaised:
    result = RawResult(status: sxRaised, raisedTypeId: c.raisedTypeId,
                       isDefect: c.isDefect, raisedMsg: c.raisedMsg,
                       raisedWitness: c.input)
  of sxUnsat, sxUnknown:
    return raw    ## not a claim; `toCandidate` never builds one
  result.abstractions = raw.abstractions
  result.obligations  = raw.obligations
  result.callStats    = raw.callStats
  let ended = confirmedEnding(replayed, c.status, c.raisedTypeId, input)
  result.errors       = raw.errors & c.errors & ended   # RFC-0005 0.9.1 WA-2
  # RFC-0016 W3-z R10: kinds a call through a proc-valued variable put there,
  # which the settle could not replace, say why (never a bare kind).
  if not lift.named and c.witnessUndefinedViaOnly != {}:
    result.errors.add procValueUnliftedHint(c, lift)
  # RFC-0005 S11: the claim's soundness -- its own path, the run's
  # coordinate (re-derived: the candidate's extraction errors are now part
  # of this result's error list), and the replay that confirmed it.
  result.soundness    = Soundness(pathTaint: c.pathTaint,
                                  buildSegment: raw.soundness.buildSegment,   # RFC-0016 K5a
                                  buildRow: raw.soundness.buildRow,
                                  witnessUndefined: liftedUndefined(c, lift),   # RFC-0016 W1-d3, W3-z R7
                                  runTaint: runTaintOf(result.errors),
                                  replay: replayed.replayStatus,
                                  witnessUnsafe: c.witnessUnsafe or replayed.endsChild,   # RFC-0016 WA-B (S4)
                                  runDependence: raw.soundness.runDependence +
                                                 replayed.runDependence)
  result.bounds       = raw.bounds
  result.undefined    = raw.undefined   # RFC-0016 W3-z R3: the run's own findings
  result.candidates   = raw.candidates
  result.annotationViolations = raw.annotationViolations   # RFC-0005 S8

func winnerLossy(raw: RawResult; staticLossy: bool): bool =
  ## RFC-0005 0.9.1 (WA-9). A clean winner (rules 1-2 decided `sxSat` or
  ## `sxRaised` without replay) whose witness renders lossily: the shape is
  ## `wfLossy` (`staticLossy`, decided at macro time), or the run's extraction
  ## substituted a value (`feExtractionFailed`). The winner's path reaches the
  ## target, but the witness reported for it is not the model's, so nothing
  ## yet says that witness reaches it.
  if raw.status notin {sxSat, sxRaised} or raw.soundness.replay != rsNotNeeded or
     scSpurious in raw.soundness.pathTaint:
    return false
  if staticLossy: return true
  for e in raw.errors:
    if e.kind == feExtractionFailed: return true
  false

proc winnerCandidate(raw: RawResult): SatCandidate =
  ## RFC-0005 0.9.1 (WA-9). A lossy clean winner as the one job of the replay
  ## pass, so it is replayed by the same codegen a candidate is. Its path is
  ## clean (replay-eligible); its extraction errors make `candidateLossy` true
  ## where the run substituted a value. Settled by `settleWinner`, never by
  ## `settleCandidate`.
  result = SatCandidate(status: raw.status, pathTaint: {},
                        nilDerefOnPath: raw.nilDerefOnPath)
  for e in raw.errors:
    if e.kind == feExtractionFailed: result.errors.add e
  case raw.status
  of sxSat: result.input = raw.witness
  of sxRaised:
    result.input = raw.raisedWitness
    result.raisedTypeId = raw.raisedTypeId
    result.isDefect = raw.isDefect
    result.raisedMsg = raw.raisedMsg
  of sxUnsat, sxUnknown: discard

func rawClaimText(raw: RawResult): string =
  claimText(raw.status, (if raw.status == sxRaised: raw.raisedTypeId else: ""))

proc settleWinner(raw: RawResult; replayed: ReplayResult;
                  input: string): RawResult =
  ## RFC-0005 0.9.1 (WA-9). Applies the replay of a lossy clean winner's
  ## witness. The status stands either way: the clean path reaches the
  ## target. `roConfirmed` makes it `rsConfirmed` (with WA-2's ending); any
  ## other outcome leaves it `rsUnconfirmed`, not `trusted()`, with a hint
  ## saying why (`winnerHint`). The replay's run-dependence joins the
  ## verdict's (WA-7).
  result = raw
  result.soundness.replay = replayed.replayStatus
  result.soundness.runDependence.incl replayed.runDependence
  # Review R2 (DD1): a child that did not finish makes the witness unsafe to
  # run in the host, confirmed or not, as a typed fact the cache stores.
  # RFC-0016 WA-B (S4): the claim's own flag (a crash claim's) is not the
  # replay's to clear.
  result.soundness.witnessUnsafe = raw.soundness.witnessUnsafe or replayed.endsChild
  if replayed.outcome == roConfirmed:
    let tid = if raw.status == sxRaised: raw.raisedTypeId else: ""
    result.errors.add confirmedEnding(replayed, raw.status, tid, input)
  else:
    result.errors.add winnerHint(replayed, rawClaimText(raw), input)

proc gateLossyWinner(raw: RawResult; staticLossy: bool;
                     settings: SymexSettings): RawResult =
  ## RFC-0016 K10b (section 9.1 item 3). The second walk needs the model's
  ## pins, not the rendered value, so a lossy winner (`winnerLossy`: the
  ## shape renders lossily, or the run substituted a value) is tail-checked
  ## like any other (`verifyTailDefined`) and stays trusted when its tail is
  ## defined. It "cannot be followed" only where a pin is genuinely missing
  ## (`RawWitness.pinsComplete` false: a parameter or leaf the pins skipped),
  ## and then it fails closed: `ubTailUnverified` joins `witnessUndefined`,
  ## the status stands, the verdict is not `trusted()` and the replay that
  ## follows cannot lift it. Gate off: `raw` unchanged.
  result = raw
  if settings.wholeRunDefinedness and raw.status == sxSat and
     not raw.witness.pinsComplete and winnerLossy(raw, staticLossy):
    result.soundness.witnessUndefined.incl ubOrdinals({UbKind(ubTailUnverified)})

proc markLossyWinnerUnreplayed(raw: RawResult; staticLossy: bool): RawResult =
  ## RFC-0005 0.9.1 (WA-9). `SymexSettings.replay = false`: a lossy clean
  ## winner cannot be confirmed, so it is `rsUnconfirmed`.
  result = raw
  if winnerLossy(raw, staticLossy):
    result.soundness.replay = rsUnconfirmed
    result.errors.add winnerUnreplayedHint(rawClaimText(raw))

proc procValueCode[T: proc](x: T): pointer =
  ## RFC-0016 W3-z R7. The routine a proc value names, as the address the
  ## replay's routine table holds; nil for a nil value. RFC-0016 W3-z R10: a
  ## closure with a captured environment names its routine too (a nested
  ## one, `ReplayFootprint.nested`); what the environment holds was checked
  ## by the scratch wire (`envRefusal`, `WireWriter.envOk`).
  if x.isNil: return nil
  when sizeof(T) > sizeof(pointer):
    rawProc(x)
  else:
    cast[pointer](x)

var routineUndefinedMemo {.compileTime.}: Table[string, set[UbKind]]

proc routineUndefinedMemoised(r: NimNode): set[UbKind] =
  ## RFC-0016 W3-z R7. `routineUndefinedKinds`, once per routine.
  let key = routineKey(r)
  if key notin routineUndefinedMemo:
    routineUndefinedMemo[key] = routineUndefinedKinds(r)
  routineUndefinedMemo[key]

proc formalsShape(t: NimNode): string =
  ## RFC-0016 W3-z R7. A proc type's formals and result, without its calling
  ## convention: a nimcall routine converts to a closure type of the same
  ## shape, so the two hold the same routines.
  if t.kind == nnkProcTy and t.len > 0 and t[0].kind == nnkFormalParams:
    var parts: seq[string]
    for i in 0 ..< t[0].len:
      let d = t[0][i]
      if d.kind == nnkIdentDefs:
        for _ in 0 ..< d.len - 2: parts.add d[^2].repr
      else: parts.add d.repr
    parts.join("|")
  else: "?" & t.repr

proc emitProcValueLift(fn: NimNode; keys: seq[string]; sites: NimNode): NimNode =
  ## RFC-0016 W3-z R7. An expression of type `ProcValueLift`: which routine
  ## each proc-valued variable the walk reported (`sites`, the run's
  ## `RawResult.procValueSites`) held when the replay ran, read in the host
  ## before the child starts (a forked child copies the host; a re-executed
  ## one is handed these values), and what the routine's body may reach.
  ##
  ## A variable's value at the run's start is the routine a call through it
  ## runs when no code the run may execute writes it otherwise: the code is
  ## the replay's footprint (`replayFootprint`; open, nothing is named), every
  ## use of the variable in it is a call, a comparison, or an assignment of a
  ## routine's symbol (`procValueUses`), whose routine joins the variable's,
  ## and the run cannot reach code the footprint did not read, which holds
  ## when every proc value the run's state holds names a routine of the
  ## footprint: the state is written to a scratch wire whose routine table is
  ## the footprint's (`replaywire.nim`, the check a re-executed child's hand-
  ## over makes), and a value it cannot carry (a closure with an
  ## environment, a routine the code does not name) names nothing. `keys`
  ## are the variables the SUT's IR names (`irCollectProcValueSites`); a
  ## reported variable with no reading here names nothing either.
  let liftT = bindSym"ProcValueLift"
  proc unnamed(why: string): NimNode =
    nnkObjConstr.newTree(bindSym"ProcValueLift",
                         nnkExprColonExpr.newTree(ident"why", newLit(why)))
  if keys.len == 0:
    return unnamed("the program names no proc-valued variable the run calls through")
  let fp = replayFootprint(fn)
  if fp.open:
    return unnamed("the replayed code is open: " & fp.why)
  for g in fp.globals:
    if not isWireableType(g.getTypeInst):
      return unnamed("`" & g.strVal & "`, of a type the wire cannot carry")
  let okId = genSym(nskVar, "procValuesNamed")
  let whyId = genSym(nskVar, "procValuesWhy")
  let ksId = genSym(nskVar, "procValueKinds")
  let siteId = genSym(nskForVar, "procValueSite")
  let codeId = genSym(nskLet, "procValueCode")
  let wr = genSym(nskVar, "procValueWire")
  let tabId = genSym(nskLet, "procValueTable")
  # RFC-0016 W3-z R10: the table names nested routines too (a closure's code),
  # where module-level code can take their addresses (`nestedRoutineAddrs`).
  let table = emitRoutineTable(fp)
  let tableExpr = table.procs
  let envOkExpr = table.envOk
  let envBenignExpr = table.envBenign
  let slots = fp.routines & fp.nested
  var putGlobals = newStmtList()
  for g in fp.globals:
    let gLit = newLit("`" & g.strVal & "` holds ")
    putGlobals.add quote do:
      if `okId`:
        try: wirePut(`wr`, `g`)
        except WireError as e:
          `okId` = false
          `whyId` = `gLit` & e.msg
  let codeOf = bindSym"procValueCode"
  let setOf = bindSym"ubSetOf"
  var caseStmt = nnkCaseStmt.newTree(siteId)
  for key in keys:
    if key notin procValueSites: continue
    let g = procValueSites[key]
    var assigned: seq[NimNode]
    var understood = true
    for r in fp.userRoutines:
      let impl =
        try: r.getImpl
        except CatchableError: newEmptyNode()
      if impl.kind in RoutineNodes and impl.len > 6 and
         not procValueUses(impl[6], g, assigned):
        understood = false
        break
    if not understood: continue
    # RFC-0016 W3-z R8: what the variable may hold AT its calls, in the
    # order the run executes, not every routine stored in it anywhere.
    let held = heldAtCalls(fn, g, fp.userRoutines, assigned)
    var staticKinds: set[UbKind]
    for a in held.routines: staticKinds = staticKinds + routineUndefinedMemoised(a)
    let staticMask = newLit(ubMaskOf(staticKinds))
    if not held.start:
      # No call runs the value the variable held as the run began: what it
      # held then is not read, and need not name a routine.
      caseStmt.add nnkOfBranch.newTree(newLit(key), quote do:
        `ksId` = `ksId` + `setOf`(`staticMask`))
      continue
    let gName = newLit("`" & g.strVal & "`")
    var chain = nnkIfStmt.newTree(nnkElifBranch.newTree(
      infix(codeId, "==", newNilLit()),
      quote do:
        `okId` = false
        `whyId` = `gName` & " is nil when the run starts"))
    # A value of `g`'s type names a routine of its shape (a cast to another
    # is undefined already); only those are asked about, and read.
    let shape = formalsShape(g.getTypeImpl)
    for i, r in slots:
      if formalsShape(r.getTypeImpl) != shape: continue
      let mask = newLit(ubMaskOf(routineUndefinedMemoised(r)))
      let at = newLit(i)
      chain.add nnkElifBranch.newTree(
        quote do: `codeId` == `tabId`[`at`],
        quote do:
          `ksId` = `ksId` + `setOf`(`mask`))
    let notFound = newLit(" holds a routine the replayed code does not " &
      "name, or names only nested in a routine where the settle cannot " &
      "take its address (it runs inside a routine, not at module level)")
    chain.add nnkElse.newTree(quote do:
      `okId` = false
      `whyId` = `gName` & `notFound`)
    caseStmt.add nnkOfBranch.newTree(newLit(key), quote do:
      `ksId` = `ksId` + `setOf`(`staticMask`)
      let `codeId` = `codeOf`(`g`)
      `chain`)
  if caseStmt.len == 1:
    return unnamed("no proc-valued variable the run calls through is read " &
                   "only by calls, comparisons and stores of a routine")
  let unread = newLit(" is called through by the run, but a use of it is " &
    "not a call, a comparison or a store of a routine")
  caseStmt.add nnkElse.newTree(quote do:
    `okId` = false
    `whyId` = "`" & `siteId` & "`" & `unread`)
  result = quote do:
    block:
      var `okId` = `sites`.len > 0
      var `whyId` = ""
      var `ksId`: set[UbKind]
      let `tabId` = `tableExpr`
      if `okId`:
        var `wr`: WireWriter
        `wr`.procs = `tabId`
        `wr`.envOk = `envOkExpr`
        # RFC-0016 W3-z R11: a scratch wire, whose environments are not
        # written: an environment whose destructor runs no user code is named.
        `wr`.envBenign = `envBenignExpr`
        `wr`.scratch = true
        `putGlobals`
        if `okId`:
          let hook = putHostHooks(`wr`)
          if hook.len > 0:
            `okId` = false
            `whyId` = "the host set a runtime hook the replayed code does " &
                      "not name: " & hook
      if `okId`:
        for `siteId` in `sites`:
          `caseStmt`
          if not `okId`: break
      `liftT`(named: `okId`, kinds: `ksId`, why: `whyId`)

proc emitRunSymexReplayed(fn: NimNode; params: seq[IRParam];
                          prog, target, settings: NimNode;
                          replayOn: bool;
                          procValueKeys: seq[string] = @[]): NimNode =
  ## RFC-0005 S10. THE `runSymex` call of every entry macro (`symexFind`,
  ## and `symexFindAllWitnesses` -- hence `symexForAll`): emits a block
  ## expression of type `RawResult` that runs the walker and then settles
  ## its candidates by replay (rule 3), so neither consumer can see a raw
  ## result that skipped the settle. `prog`/`target`/`settings` are the
  ## `SymexProgram`, `SymexTarget` and `SymexSettings` expressions the
  ## caller would have passed to `runSymex`.
  ##
  ## `replayOn` is the caller's STATIC `SymexSettings.replay`. Off, the
  ## emitted expression is the bare `runSymex` call: no reference to `fn` is
  ## generated at all, so `fn` and its callees need not link or load (the
  ## opt-out for a SUT that is analysable but not executable in the test
  ## binary), and every candidate stays `sxUnknown` -- the pre-S10 verdict.
  ##
  ## Settles an `sxUnknown` (rules 1-2 already produced any clean
  ## verdict; `sxUnsat` has no candidates), and (RFC-0005 0.9.1, WA-9) a clean
  ## winner with a lossy witness (`winnerLossy`, `settleWinner`). For each
  ## candidate, in
  ## discovery order, `sxSat` claims first: renders its model through the
  ## same `emitTyAndReader` readers the verdict uses, replays it
  ## (`emitReplayWitness`) against the search target (an `sxSat` claim) or
  ## `tRaisedExn(<its raised type>)` (an `sxRaised` claim -- the claim that
  ## exact type escapes `fn`), and hands the `ReplayResult` it returns to
  ## `settleCandidate`; stops at the first confirmation. Nothing about a
  ## replay is read off the thread (review R1-06): what the settle and a
  ## later save need of it, the run-dependence included, is on the value.
  let rawId     = genSym(nskLet, "rawPreReplay")
  # RFC-0005 0.9.1 (WA-9): whether every witness of `fn` renders lossily.
  let staticLossy = newLit(paramsFidelity(params) == wfLossy)
  # RFC-0016 K10b: a lossy witness cannot be followed past the label, so under
  # the whole-run gate it fails closed (`ubTailUnverified`) before any replay.
  let gateLossySym = bindSym"gateLossyWinner"
  let runCall = quote do:
    `gateLossySym`(runSymex(`prog`, `target`, `settings`), `staticLossy`,
                   `settings`)
  if not replayOn:
    let markSym = bindSym"markLossyWinnerUnreplayed"
    return quote do:
      `markSym`(`runCall`, `staticLossy`)
  let witId  = genSym(nskLet, "candRawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(params, witId)
  let settledId = genSym(nskVar, "settled")
  let tgtId     = genSym(nskLet, "searchTarget")
  let candId    = genSym(nskForVar, "cand")
  let claimId   = genSym(nskForVar, "claim")
  let typedId   = genSym(nskLet, "candWitness")
  let replayedId = genSym(nskLet, "replayed")
  let replayTgt = genSym(nskLet, "replayTarget")
  let inputSym  = bindSym"candidateInput"
  let settleSym = bindSym"settleCandidate"
  let winnerSettleSym = bindSym"settleWinner"
  let lossyWinSym = bindSym"winnerLossy"
  let winnerCandSym = bindSym"winnerCandidate"
  let lossyWinId = genSym(nskLet, "lossyWinner")
  let jobsId = genSym(nskLet, "replayJobs")
  let liftId = genSym(nskLet, "procValueLift")   # RFC-0016 W3-z R7
  let liftExpr = emitProcValueLift(fn, procValueKeys,
                                   newDotExpr(rawId, ident"procValueSites"))
  # A zero-param `fn` has the empty tuple `()` as its witness, which is a
  # value but not a type annotation -- so annotate only a non-empty one.
  let typedDecl =
    if params.len == 0:
      quote do:
        let `typedId` {.used.} = `witnessTup`
    else:
      quote do:
        let `typedId` {.used.}: `tupleTy` = `witnessTup`
  # RFC-0005 S8ct: a re-executed child is handed the solver's model, and renders
  # it as this process does, with no aliasing to carry across.
  var child = ChildWitness()
  when replayReexecs:
    let childRaw = genSym(nskVar, "childRaw")
    let childWit = genSym(nskLet, "childWitness")
    let (childTy, childTup) = emitWitnessTuple(params, childRaw)
    child = ChildWitness(blob: witId, blobTy: newCall(bindSym"typeof", witId),
                         blobId: childRaw, witId: childWit,
                         decl:
                           if params.len == 0:
                             quote do:
                               let `childWit` {.used.} = `childTup`
                           else:
                             quote do:
                               let `childWit` {.used.}: `childTy` = `childTup`)
  let replay = emitReplayWitness(fn, params, typedId, replayTgt,
    newDotExpr(candId, ident"pathTaint"),
    newCall(bindSym"candidateLossy", candId),
    newDotExpr(candId, ident"nilDerefOnPath"),
    newDotExpr(settings, ident"replayTimeoutMs"),   # RFC-0005 S8be
    child)
  result = quote do:
    block:
      let `rawId` = `runCall`
      var `settledId` = `rawId`
      # RFC-0005 0.9.1 (WA-9): a lossy clean winner is the pass's one job.
      let `lossyWinId` = `lossyWinSym`(`rawId`, `staticLossy`)
      if (`rawId`.status == sxUnknown and `rawId`.candidates.len > 0) or
         `lossyWinId`:
        let `tgtId`: SymexTarget = `target`
        let `jobsId` =
          if `lossyWinId`: @[`winnerCandSym`(`rawId`)]
          else: `rawId`.candidates
        let `liftId` = `liftExpr`
        block replayPass:
          for `claimId` in [sxSat, sxRaised]:
            for `candId` in `jobsId`:
              if `candId`.status != `claimId`: continue
              let `replayTgt`: SymexTarget =
                if `claimId` == sxSat: `tgtId`
                else: tRaisedExn(`candId`.raisedTypeId)
              let `witId` {.used.} = `inputSym`(`candId`)
              `typedDecl`
              let `replayedId` = `replay`
              let shown = (when compiles($`typedId`): $`typedId` else: "")
              `settledId` =
                if `lossyWinId`:
                  `winnerSettleSym`(`settledId`, `replayedId`, shown)
                else: `settleSym`(`settledId`, `candId`, `replayedId`, shown,
                                  `liftId`)
              if `replayedId`.outcome == roConfirmed: break replayPass
      `settledId`

# ---- The driver macro -------------------------------------------------------

proc warnIncoherentSettings(settings: SymexSettings, entry: string) =
  ## RFC-0010 C3a. `validateSymexSettings` is exported and unit-tested and was
  ## called by nothing in `src/` -- a validator that never runs on a real
  ## configuration, which is this RFC's own pattern sitting inside the RFC that
  ## exists to end it. §5 required a decision: wire it in or delete it.
  ##
  ## Wire it in. (Its warning for an empty `arithChecks` -- the defect round B
  ## found in the ten const literals -- went with that setting in RFC-0016
  ## K10d: the build alone decides which checks run.) The mechanism that could
  ## have caught that defect was already written; it was simply never called.
  ##
  ## RFC-0010 review round 2: this proc is no longer called directly from
  ## any entry macro. Every macro that reaches the walker under a
  ## caller-chosen `settings` calls `parseEntryImplWarned` below instead
  ## of `dsl_parser.parseEntryImpl` directly, and that wrapper is the one
  ## call site left that invokes this. That makes coverage true BY
  ## CONSTRUCTION rather than by each macro author remembering to add the
  ## call: a future entry macro gets the check for free by reusing the
  ## helper it already needs for parsing, not by a separate step that can
  ## be forgotten the way the original four call sites were.
  ##
  ## Known duplicate (RFC-0010 review round 2, finding R2-06): an
  ## incoherent `settings` passed to `assertCoveredBy` reaches THIS `for`
  ## loop twice for one user call -- once with `entry == "assertCoveredBy"`
  ## from its own `parseEntryImplWarned` call, once with
  ## `entry == "symexFind"` from the `symexFind` macro that
  ## `assertCoveredBy`'s expansion calls internally. See the long comment
  ## on `assertCoveredBy` (below) for why this is intentional and why a
  ## `{.compileTime.}` dedup here was tried and rejected as unsafe.
  for w in validateSymexSettings(settings):
    warning(entry & ": " & w)

proc parseEntryImplWarned(fn: NimNode, apiName: string,
                          settings: SymexSettings): ParseResult =
  ## The chokepoint referenced above. Parses `fn` exactly like
  ## `dsl_parser.parseEntryImpl` (it delegates to that proc for the parse
  ## itself) and, before doing so, unconditionally emits a `warning()` via
  ## `warnIncoherentSettings` when `settings` looks incoherent. That is ALL
  ## it does: nothing here rejects, fixes up, or substitutes a corrected
  ## `settings` -- a caller who ignores the compiler warning gets back
  ## exactly the same `ParseResult` as one who heeds it. Despite the RFC's
  ## review-round comments (kept verbatim below) using the word "validates",
  ## this is not validation in the gating sense; it is parse-plus-warn. The
  ## name was corrected from `parseEntryImplValidated` to
  ## `parseEntryImplWarned` in a later review round (finding R2-08) for
  ## exactly this reason.
  ##
  ## `dsl_parser.parseEntryImpl` (owned by RFC-parser-normalization N1,
  ## outside this file) takes only the derived `maxInst: int`, not
  ## `settings` itself -- its signature has no `static` settings value to
  ## inspect, so the warning cannot live inside it without changing that
  ## signature. This wrapper is the closest genuine chokepoint reachable
  ## from `symex.nim` alone: every macro that runs the WALKER under a
  ## caller-chosen `settings` (`symexFind`, `concolicCollect`,
  ## `concolicFlip`, `assertCoveredBy`, `symexFindAllWitnesses` — and,
  ## transitively, `symexForAll`, which itself emits a call to
  ## `symexFindAllWitnesses`) calls THIS instead of `parseEntryImpl`
  ## directly, so parsing and warning can never drift apart again for
  ## that set. The five cache/DB helper macros
  ## (`symexCacheKeyForFn`/`saveSymexWitness`/`loadSymexWitnesses`/
  ## `saveSymexVerdict`/`loadSymexVerdict`) parse through the same
  ## `entryParse` with `warn = false`: they don't run the walker
  ## themselves, they key or persist results computed elsewhere, so a
  ## warning at a cache lookup would be noise pointing at the wrong call
  ## site. (Review R1-11: they once called `parseEntryImpl`
  ## directly and so skipped `methodPrelude` too.)
  ##
  ## `settings` is `static SymexSettings` at every call site (an entry
  ## macro's own `static` parameter), so this whole call resolves at macro
  ## time: zero runtime cost, and `warnIncoherentSettings`'s `warning()`
  ## lands on the user's call site, not inside the library.
  warnIncoherentSettings(settings, apiName)
  parseEntryImpl(fn, apiName, settings.budget.maxInstantiationsPerProc)

proc methodPrelude(fn: NimNode): NimNode =
  ## RFC-0005 S8bn (item 6). nil when every method `fn` calls (transitively)
  ## is registered (`dsl_parser.methodRegistry`); otherwise the statements
  ## that register them, emitted into the CALLER's scope, where each name
  ## resolves to every overload visible there. The entry macro then expands
  ## again after them, and its parse dispatches each method call over the
  ## overrides (`methodDispatchStmt`). A name not visible at the caller is
  ## recorded as such, and its calls stay declined.
  let names = unregisteredMethodNames(fn)
  if names.len == 0: return nil
  result = newStmtList()
  for nm in names:
    let id = ident(nm)
    let reg = newCall(bindSym"symexRegisterMethods", newLit(nm), id)
    let none = newCall(bindSym"symexRegisterNoMethods", newLit(nm))
    result.add quote do:
      when declared(`id`): `reg`
      else: `none`

proc targetLit(t: SymexTarget): NimNode =
  ## RFC-0005 S8bn. A static `SymexTarget` as an expression, for an entry
  ## macro's re-expansion (`methodPrelude`).
  case t.kind
  of stkLabel: newCall(bindSym"tLabel", newLit(t.label))
  of stkRaisedExn: newCall(bindSym"tRaisedExn", newLit(t.typeFilter))
  of stkUndefined: newCall(bindSym"tUndefined", newLit(t.ubKinds))
  else: nnkObjConstr.newTree(bindSym"SymexTarget",
                             newColonExpr(ident"kind", newLit(t.kind)))

type EntryParse = object
  ## RFC-0005 review R1-11. What an entry macro starts from (`entryParse`).
  again: NimNode      ## non-nil: return this (the methods' registration, then
                      ## the macro again)
  parsed: ParseResult
  prog: NimNode       ## the `SymexProgram` constructor, keyed and walked

proc entryParse(fn: NimNode; apiName: string; settings: SymexSettings;
                again: NimNode; warn = true): EntryParse =
  ## RFC-0005 review R1-11. Every entry macro's parse of `fn`, the cache and DB
  ## helpers' among them, so what they key cannot drift from what the walking
  ## entries write. First the methods `fn` calls are registered in the
  ## caller's scope (`methodPrelude`): `again` is the macro's own call, which
  ## then expands once more, after them. Before this the five cache/DB macros
  ## parsed without it, and keyed the undispatched program wherever no other
  ## entry had registered the methods yet.
  ##
  ## `warn`: the walking entries warn on an incoherent `settings`
  ## (`parseEntryImplWarned`); the cache/DB macros run no walk and do not.
  ## `prog` carries the source digest of the routines `fn` calls
  ## (`implDigest`, R1-09).
  let pre = methodPrelude(fn)
  if pre != nil:
    result.again = newTree(nnkStmtListExpr, pre, again)
    return
  result.parsed =
    if warn: parseEntryImplWarned(fn, apiName, settings)
    else: parseEntryImpl(fn, apiName, settings.budget.maxInstantiationsPerProc)
  var p = result.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)
  let paramsExpr = p.paramsNimNode
  let bodyExpr = p.bodyNimNode
  let procsExpr = p.procsNimNode
  let glExpr = p.globalsNimNode
  let rtExpr = p.retTyNimNode
  let uxhExpr = p.userExnHierarchyNimNode
  let peExpr = p.parseErrorsNimNode
  let avExpr = p.annotationViolationsNimNode
  let digest = newLit(implDigest(fn))
  result.prog = quote do:
    SymexProgram(params: `paramsExpr`, body: `bodyExpr`, procs: `procsExpr`,
                 globals: `glExpr`, retTy: `rtExpr`,
                 userExnHierarchy: `uxhExpr`, parseErrors: `peExpr`,
                 annotationViolations: `avExpr`, implDigest: `digest`)

macro symexFind*(fn: typed,
                 target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): untyped =
  ## Symbolically execute `fn` searching for an input that reaches `target`.
  ## Returns `SymexResult[ParamTuple]` where `ParamTuple` is the proc's
  ## parameter list as a Nim tuple.
  # RFC-parser-normalization N1: routes through `parseEntryImpl` like
  # `symexFindAllWitnesses` — `parsed` is consumed at macro time here
  # (`.params` below) via the same helper, not a different shape.
  # RFC-0010 review round 2: goes through `parseEntryImplWarned`
  # (below `warnIncoherentSettings`), which warns on an incoherent
  # `settings` and THEN calls `parseEntryImpl` — a single call site both
  # entries share.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s.
  let e = entryParse(fn, "symexFind", settings, newCall(bindSym"symexFind",
    fn, targetLit(target), newLit(settings)))
  if e.again != nil: return e.again
  var parsed = e.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)
  let progExpr = e.prog

  # Build the tuple type and witness-construction tuple. We genSym a
  # local name for the RawWitness so the witness-constructor calls
  # share an identity-equal NimNode with the `let` that binds it.
  let witId = genSym(nskLet, "rawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(parsed.params, witId)

  # ADR-0012 D2: a SEPARATE gensym for the per-diagnostic RawWitness
  # binding inside the diagnostics loop. Using a distinct name avoids any
  # shadowing concern with the outer `witId` binding.
  let diagWitId = genSym(nskLet, "diagRawWit")
  let (_, diagWitnessTup) = emitWitnessTuple(parsed.params, diagWitId)
  # RFC-0016 K10a-target: the same reader for each `UndefinedFinding`.
  let undefWitId = genSym(nskLet, "undefRawWit")
  let (_, undefWitnessTup) = emitWitnessTuple(parsed.params, undefWitId)

  # `(int,)` is a syntactic 1-tuple; nnkTupleConstr with one child
  # renders correctly for both the type and the value.


  # RFC-0005 S10: the walker run AND the rule-3 replay settle of its
  # candidates, in one emitted expression (`emitRunSymexReplayed`) -- the
  # `case raw.status` below only ever sees a settled result.
  let progId = genSym(nskLet, "prog")
  let runReplayed = emitRunSymexReplayed(fn, parsed.params, progId,
                                         newLit(target), newLit(settings),
                                         settings.replay,
                                         irCollectProcValueSites(parsed.body,
                                                                 parsed.procs))

  result = quote do:
    block:
      let `progId` = `progExpr`
      let raw = `runReplayed`
      ## ADR-0012 D2: type each RawDiagnostic into DefectFinding[T] by
      ## rebinding diagWitId per entry and running the same witnessTup reader.
      let diagResult = block:
        var diagSeq: seq[DefectFinding[`tupleTy`]]
        for diagEntry in raw.diagnostics:
          let `diagWitId` = diagEntry.raisedWitness
          diagSeq.add DefectFinding[`tupleTy`](
            raisedTypeId: diagEntry.raisedTypeId,
            defectKind:   typeIdToDefectKind(diagEntry.raisedTypeId),
            isDefect:     diagEntry.isDefect,
            raisedMsg:    diagEntry.raisedMsg,
            witness:      `diagWitnessTup`,
            heapSnapshot: readHeapSnapshot(`diagWitId`),
            witnessUnsafe:    diagEntry.witnessUnsafe)
        diagSeq
      let undefResult = block:
        var undefSeq: seq[UndefinedFinding[`tupleTy`]]
        for undefEntry in raw.undefined:
          let `undefWitId` = undefEntry.witness
          undefSeq.add UndefinedFinding[`tupleTy`](
            kind: undefEntry.kind, site: undefEntry.site,
            witness: `undefWitnessTup`)
        undefSeq
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               heapSnapshot: readHeapSnapshot(`witId`),
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)
      of sxRaised:
        # Phase 15 E2b. The walker reached a reachable `raise`; surface the
        # raised type id PLUS the reconstructed witness that reaches it (solved
        # from the raise-path condition). `witId` binds `raw.raisedWitness` so
        # the shared `witnessTup` reader reconstructs the SUT input tuple exactly
        # as on the `sxSat` path.
        let `witId` = raw.raisedWitness
        SymexResult[`tupleTy`](status: sxRaised,
                               raisedTypeId: raw.raisedTypeId,
                               raisedWitness: `witnessTup`,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               heapSnapshot: readHeapSnapshot(`witId`),
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)

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
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s.
  let e = entryParse(fn, "concolicCollect", settings,
    newCall(bindSym"concolicCollect", fn, trace, bindings, newLit(settings),
            newLit(maxDraws)))
  if e.again != nil: return e.again
  let progExpr = e.prog
  result = quote do:
    block:
      let prog = `progExpr`
      runConcolicCollectImpl(prog, `trace`, `bindings`, `settings`, `maxDraws`)

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
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s.
  let e = entryParse(fn, "concolicFlip", settings,
    newCall(bindSym"concolicFlip", fn, trace, bindings, targetBranchIndex,
            newLit(settings), newLit(maxDraws), newLit(maxRelaxationAttempts),
            newLit(z3TimeoutMs)))
  if e.again != nil: return e.again
  let progExpr = e.prog
  result = quote do:
    block:
      let prog = `progExpr`
      runConcolicFlipImpl(prog, `trace`, `bindings`, `targetBranchIndex`,
                         `settings`, `maxDraws`, `maxRelaxationAttempts`,
                         `z3TimeoutMs`)

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

# ---- assertCoveredBy --------------------------------------------------------

proc hostRefusalReason(s: Soundness): string =
  ## Why `hostRunnable(s)` is false, as the reason `assertCoveredBy` gives for
  ## not running a witness: the actual cause, not one guessed for all of them.
  if s.replay == rsUnsettled:
    "its record was never settled"
  elif s.witnessUndefined != {}:
    var names: seq[string] = @[]
    for k in undefinedKinds(s): names.add $k
    "its path ran past undefined behaviour (" & names.join(", ") & ")"
  elif s.witnessUnsafe:
    "its witness ends or hangs the process that runs it (a crash claim, " &
      "or a replay that ended or hung its child)"
  else:
    "it is not host-runnable"

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
  # RFC-parser-normalization N1: routes through `parseEntryImpl`, same as
  # `symexFind` above — `parsed` is consumed at macro time via the same
  # helper `symexFindAllWitnesses` uses.
  # RFC-0010 review round 2: via `parseEntryImplWarned`, so an
  # incoherent `settings` warns here too.
  let parsed = parseEntryImplWarned(fn, "assertCoveredBy", settings)

  let actualTestFn =
    if testFn.kind == nnkNilLit: fn else: testFn

  # Splat the witness tuple into testFn's positional params.
  # Phase 14 A7b: wrap each param in a fresh `var` local before the
  # call so `var T` parameters receive an addressable lvalue.
  # Pre-A7b this emitted `testFn(wit[0], wit[1], ...)` which fails
  # to compile for SUTs that take any `var T`. The wrapping is
  # zero-cost for non-var params and idiomatic for var params.
  # (RFC-0005 S2: the splat is `emitWitnessSplat`, shared with replay.)
  let witId = genSym(nskLet, "wit")
  let splatBlock = emitWitnessSplat(actualTestFn, parsed.params.len, witId)

  # gensym shared identifiers used across the cover-check sub-quote
  # and the main quote — quote-do hygiene would otherwise mint
  # fresh symbols per block.
  let hitsId           = genSym(nskLet, "hits")
  let assertionRaisedId = genSym(nskVar, "assertionRaised")
  let indexRaisedId     = genSym(nskVar, "indexRaised")
  let fieldRaisedId     = genSym(nskVar, "fieldRaised")
  let anyRaisedId       = genSym(nskVar, "anyRaised")        ## Phase 15 E2a

  # We dispatch on `target.kind` at macro time so that only the
  # branch-appropriate field is referenced in the emitted code.
  # Splicing a `static SymexTarget` of a non-stkLabel kind via
  # quote-do would otherwise force Nim to materialise an
  # nnkObjConstr that names every field — but a variant-object's
  # `label` field is invalid under `stkAssertionViolation`.
  let coveredExpr =
    case target.kind
    of stkLabel:
      let labelLit = newLit(target.label)
      quote do: (`labelLit` in `hitsId`)
    of stkAssertionViolation:
      quote do: `assertionRaisedId`
    of stkIndexError:
      quote do: `indexRaisedId`
    of stkFieldDefect:
      quote do: `fieldRaisedId`
    of stkRaisedExn:
      quote do: `anyRaisedId`   ## Phase 15 E2a: covered iff the SUT raised
    of stkNilAccess:
      quote do: `anyRaisedId`   ## Phase 15 R5: covered iff the SUT nil-derefed
    of stkUndefined:
      quote do: false           ## RFC-0016 K10a-target: never run in the host
  let failMsg =
    case target.kind
    of stkLabel:
      newLit("assertCoveredBy: testFn did not reach symexTarget(\"" &
             target.label & "\") on the symex witness")
    of stkAssertionViolation:
      newLit("assertCoveredBy: testFn did not raise AssertionDefect " &
             "on the symex witness (target was tAssertionViolation)")
    of stkIndexError:
      newLit("assertCoveredBy: testFn did not raise IndexDefect " &
             "on the symex witness (target was tIndexError)")
    of stkFieldDefect:
      newLit("assertCoveredBy: testFn did not raise FieldDefect " &
             "on the symex witness (target was tFieldDefect)")
    of stkRaisedExn:
      newLit("assertCoveredBy: testFn did not raise an exception " &
             "on the symex witness (target was tRaisedExn)")
    of stkNilAccess:
      newLit("assertCoveredBy: testFn did not raise NilAccessDefect " &
             "on the symex witness (target was tNilAccess)")
    of stkUndefined:
      newLit("assertCoveredBy: a tUndefined witness reaches undefined " &
             "behaviour and is never run in the host")
  let targetDescLit = newLit(describeTarget(target))

  # Rebuild the target node from its kind so the spliced AST is
  # always well-formed for the variant.
  let targetExpr =
    case target.kind
    of stkLabel:           newCall(bindSym"tLabel", newLit(target.label))
    of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
    of stkIndexError:      newCall(bindSym"tIndexError")
    of stkFieldDefect:     newCall(bindSym"tFieldDefect")
    of stkRaisedExn:       newCall(bindSym"tRaisedExn", newLit(target.typeFilter))
    of stkNilAccess:       newCall(bindSym"tNilAccess")
    of stkUndefined:       newCall(bindSym"tUndefined", newLit(target.ubKinds))

  let gapsSym = bindSym"findingGaps"   ## RFC-0005 S11 (private helper)
  let hintsSym = bindSym"findingHints"         ## RFC-0005 W1 (private helper)
  let diagsSym = bindSym"findingDiagnostics"   ## RFC-0005 W1 (private helper)
  let undefSym = bindSym"findingUndefined"     ## RFC-0016 K10a-target
  # RFC-0005 0.9.1 (WA-2). A witness whose confirming replay ended its child
  # after the target (`witnessUnsafe`) is never splatted here: it would end or
  # hang this process. With no `testFn`, the replay already ran `fn` on it and
  # saw the target reached, which is the coverage this checks (an `sxSat`
  # claim is replayed against the search target). Otherwise nothing runs it,
  # and the check fails, saying why.
  #
  # Review R1-15. The arm reads `trusted()`, not `status` alone. A trusted
  # claim's witness reaches the target in `fn`, so a `testFn` that does not
  # reach it on that witness is to blame. An untrusted one (`rsUnconfirmed`: a
  # lossy witness no replay confirmed) proves no witness exists: it is run
  # (unless its replay ended its child, `hostRunnable`), and a hit
  # proves coverage, but a miss proves nothing about `testFn`. It is reported
  # as unconfirmed, as an UNKNOWN is, and `acceptUnknownAsCovered` downgrades
  # it the same way.
  #
  # Review R1-10. The finding is the call's own: returned (discardable), or
  # carried by the `SymexCoverageDefect` the call raises.
  let sameFn = newLit(testFn.kind == nnkNilLit)
  let unsafeMsg = newLit("assertCoveredBy: the symex witness is known to " &
    "end or hang the process that runs it after reaching the target (its " &
    "replay's child did not finish); it is not run in this process, so " &
    "testFn's coverage of it is not checked")
  let unconfirmedMsg = newLit("assertCoveredBy: symex claims " &
    describeTarget(target) & " is reachable, but the claim is not trusted " &
    "(its witness renders lossily and no replay of the real fn confirmed " &
    "it), so no witness is known to reach the target. ")
  let unconfirmedTail = newLit("Coverage is unconfirmed, and testFn is not " &
    "blamed (set acceptUnknownAsCovered = true to downgrade)")
  let runnableSym = bindSym"hostRunnable"
  let refusalSym = bindSym"hostRefusalReason"
  let outcomeSym = bindSym"coverageOutcome"
  # Review R3 (E2): the call site the run's report keys this finding by. The
  # multi-target form hands its own `fn` node on, so its targets share it.
  let siteLit = newLit(fn.lineInfo)
  # Review R4 (U1): and the `fn` itself, since a template or helper shares one
  # call site among several `fn`s, and a generic one among its instantiations.
  # Review R5 (3d): a routine is told apart as `routineKey` tells routines
  # apart (name and body hash; `signatureHash` is the same for every routine
  # of one parameter list). `parseEntryImplWarned` above has already resolved
  # `fn` through `getImpl`, which rejects anything that is not a routine
  # symbol (a lambda, a call, a template, a macro, a proc-typed variable), so
  # only a symbol `resolveRoutineImpl` accepts gets here. Asked of that
  # resolver, not of a symbol-kind set, so the two cannot drift (the N2 kind
  # gate audit forbids a bare kind gate outside it).
  if fn.kind != nnkSym or resolveRoutineImpl(fn).isNil:
    error("assertCoveredBy: a non-routine symbol reached the finding key", fn)
  let fnIdText = routineKey(fn)
  let fnIdLit = newLit(fnIdText & "@" & fn.getTypeInst.repr)
  let originLit = nnkObjConstr.newTree(bindSym"FindingOrigin",
    nnkExprColonExpr.newTree(ident"site", siteLit),
    nnkExprColonExpr.newTree(ident"fnId", fnIdLit))
  let trustedSym = bindSym"trusted"
  # Shared by the arm bodies below and the block they are spliced into.
  let rId = genSym(nskLet, "r")
  let findingId = genSym(nskVar, "finding")
  let failureId = genSym(nskVar, "failureMsg")
  # One body for the two arms that carry a witness: `sxSat` (`r.witness`) and
  # `sxRaised` (`r.raisedWitness`). `sameFnOk` says whether, with no `testFn`,
  # an unsafe witness's replay already established the coverage: true for
  # `sxSat` (replayed against this target), false for `sxRaised` (replayed
  # against the raise).
  let acceptUnknown = newLit(settings.acceptUnknownAsCovered)
  proc claimArm(witField: NimNode; status: NimNode;
                sameFnOk: bool): NimNode =
    let unsafeCovers = newLit(sameFnOk)
    quote do:
      let `witId` = `witField`
      let trustedClaim = `trustedSym`(`rId`)
      let runIt = `runnableSym`(`rId`.soundness)
      symexCaptureBegin()
      var `assertionRaisedId` = false
      var `indexRaisedId` = false
      var `fieldRaisedId` = false
      var `anyRaisedId` = false   ## Phase 15 E2a: any exception raised
      try:
        if runIt:
          `splatBlock`
      except AssertionDefect:
        `assertionRaisedId` = true
        `anyRaisedId` = true
      except IndexDefect:
        `indexRaisedId` = true
        `anyRaisedId` = true
      except FieldDefect:
        `fieldRaisedId` = true
        `anyRaisedId` = true
      except NilAccessDefect:                       ## Phase 15 R5
        `anyRaisedId` = true
      except CatchableError:
        `anyRaisedId` = true
      except Defect:
        # RFC-0016 W1-c3 (W-26): any other Defect (overflow, range, div by
        # zero, ...) is a raise like the arms above, not the host's end.
        # Under --panics:on a Defect is not catchable (W1-c2 owns that).
        `anyRaisedId` = true
      let `hitsId` = symexCaptureEnd()
      let reached = runIt and `coveredExpr`
      var covered = false
      var failure = ""
      if `rId`.soundness.witnessUnsafe and trustedClaim:
        if `sameFn` and `unsafeCovers`: covered = true
        else: failure = `unsafeMsg`
      elif reached:
        covered = true
      elif trustedClaim:
        failure = `failMsg`
      else:
        if not `acceptUnknown`:
          failure = `unconfirmedMsg` &
            (if runIt: "Running it did not reach the target. "
             else: "It was not run here: " & `refusalSym`(`rId`.soundness) &
                   ". ") & `unconfirmedTail`
      `findingId` = SymexFinding(
        targetDesc:     `targetDescLit`,
        status:         `status`,
        covered:        covered,
        witnessChoices: renderAsChoices(`witId`),
        z3Version:      z3FullVersion(),
        soundness:      `rId`.soundness,              ## RFC-0005 S11
        bounds:         `rId`.bounds,                 ## review R1-17
        gaps:           `gapsSym`(`rId`.errors),
        annotationViolations: `rId`.annotationViolations,
        hints: `hintsSym`(`rId`.errors),                 ## RFC-0005 W1
        diagnostics: `diagsSym`(`rId`.diagnostics),
        undefined: `undefSym`(`rId`.undefined))
      `failureId` = failure
  let satArm = claimArm(newDotExpr(rId, ident"witness"), bindSym"sfSat", true)
  # Phase 16 D1a: defect targets (tAssertionViolation, tIndexError,
  # tFieldDefect, tNilAccess) return sxRaised with a populated
  # `raisedWitness` (the path-constrained witness that triggers the raise),
  # replayed through testFn exactly as an `sxSat` witness is.
  let raisedArm = claimArm(newDotExpr(rId, ident"raisedWitness"),
                           bindSym"sfRaised", false)
  result = quote do:
    block:
      let `rId` = symexFind(`fn`, `targetExpr`, `settings`)
      var `findingId`: SymexFinding
      var `failureId` = ""
      case `rId`.status
      of sxSat:
        `satArm`
      of sxUnsat:
        `findingId` = SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnsat, covered: true,
          z3Version:  z3FullVersion(),
          soundness:  `rId`.soundness,                  ## RFC-0005 S11
          bounds:     `rId`.bounds,                     ## review R1-17
          gaps:       `gapsSym`(`rId`.errors),
          annotationViolations: `rId`.annotationViolations,
          hints: `hintsSym`(`rId`.errors),                 ## RFC-0005 W1
          diagnostics: `diagsSym`(`rId`.diagnostics),
        undefined: `undefSym`(`rId`.undefined))
        # A vacuous pass.
      of sxUnknown:
        `findingId` = SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnknown, covered: false,
          z3Version:  z3FullVersion(),
          soundness:  `rId`.soundness,                  ## RFC-0005 S11
          bounds:     `rId`.bounds,                     ## review R1-17
          gaps:       `gapsSym`(`rId`.errors),
          annotationViolations: `rId`.annotationViolations,
          hints: `hintsSym`(`rId`.errors),                 ## RFC-0005 W1
          diagnostics: `diagsSym`(`rId`.diagnostics),
        undefined: `undefSym`(`rId`.undefined))
        let s: SymexSettings = `settings`
        if not s.acceptUnknownAsCovered:
          `failureId` = "assertCoveredBy: symex returned UNKNOWN; cannot " &
            "prove coverage (set acceptUnknownAsCovered = true to downgrade)"
      of sxRaised:
        `raisedArm`
      `outcomeSym`(`originLit`, `findingId`, `failureId`)

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
  # Phase 14 A7b: the Phase-12 `var T` guard is lifted. Witness
  # semantics: the walker reports the INITIAL value of each `var`
  # param (via `initialEnv`), which the test runtime invokes the
  # SUT with. Mutations are walker-internal symbolic operations
  # with no caller-side identity tracking.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  # RFC-0010 review round 2: via `parseEntryImplWarned`, so an
  # incoherent `symexSettings` warns here — and, transitively, for
  # `symexForAll`, which emits a call to this macro rather than routing
  # through `symexFind`/`assertCoveredBy` (its own settings never touched
  # `warnIncoherentSettings` before this).
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s, as the cache
  # and DB macros' are, so their keys are the ones written here.
  let e = entryParse(fn, "symexFindAllWitnesses", symexSettings,
    newCall(bindSym"symexFindAllWitnesses", fn, db, newLit(symexSettings),
            excludeTargets))
  if e.again != nil: return e.again
  var parsed = e.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)
  let progExpr = e.prog

  let labels = irCollectLabels(parsed.body, parsed.procs)

  # Macro-time filter set: any target kind appearing in
  # `excludeTargets` is dropped, regardless of `label` (per plan:
  # comparison is by kind). Label-by-name suppression is
  # out-of-scope for v1 — the deferrals table tracks it.
  # `excludeTargets` is a NimNode at macro time (the call-site
  # expression). The user writes one of:
  #   * `@[tIndexError(), tLabel("x")]`   — nnkPrefix("@", nnkBracket(...))
  #   * the default `@[]`                  — empty bracket
  # We inspect the AST and translate each constructor call to the
  # corresponding `SymexTargetKind`. Comparison is by kind per the
  # plan: any call to `tIndexError` excludes ALL tIndexError
  # auto-discoveries; any call to `tLabel(...)` excludes ALL labels
  # regardless of name. Label-by-name suppression is a documented
  # deferral.
  # Phase 14 B67: `tLabel("name")` excludes ONLY the named label
  # (previously excluded ALL labels regardless of name).
  # `tAssertionViolation/tIndexError/tFieldDefect` continue to
  # exclude by kind. This is a documented breaking change for
  # users who relied on `tLabel(...)` to mean "all labels."
  var excludedKinds: set[SymexTargetKind]
  var excludedLabels: seq[string]
  proc collectKinds(n: NimNode) =
    case n.kind
    of nnkPrefix:
      if n.len == 2: collectKinds(n[1])
    of nnkBracket:
      for child in n: collectKinds(child)
    of nnkCall, nnkCommand:
      if n.len >= 1 and n[0].kind in {nnkIdent, nnkSym}:
        case n[0].strVal
        of "tLabel":
          if n.len >= 2 and n[1].kind in {nnkStrLit..nnkTripleStrLit}:
            excludedLabels.add n[1].strVal
        of "tAssertionViolation": excludedKinds.incl stkAssertionViolation
        of "tIndexError":         excludedKinds.incl stkIndexError
        of "tFieldDefect":        excludedKinds.incl stkFieldDefect
        of "tRaisedExn":          excludedKinds.incl stkRaisedExn
        of "tUndefined":          excludedKinds.incl stkUndefined
        else: discard
    else: discard
  collectKinds(excludeTargets)

  # Build the witness-renderer for this proc's parameter tuple
  # exactly as `symexFind` does — the witness reconstruction must
  # produce a typed Nim value so `renderAsChoices` can serialise it
  # into the choice IR for the example DB and report.
  let witId = genSym(nskLet, "rawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(parsed.params, witId)
  # RFC-0005 W1: the per-diagnostic reader, as `symexFind` builds it (a
  # distinct gensym so it never shadows `witId`).
  let diagWitId = genSym(nskLet, "diagRawWit")
  let (_, diagWitnessTup) = emitWitnessTuple(parsed.params, diagWitId)
  # A zero-parameter `fn` has the empty tuple `()` as its witness: a value,
  # not a type annotation, so annotate only a non-empty one.
  proc witnessDecl(name, tup: NimNode): NimNode =
    if parsed.params.len == 0:
      quote do:
        let `name` {.used.} = `tup`
    else:
      quote do:
        let `name`: `tupleTy` = `tup`
  let undefWitId = genSym(nskLet, "undefRawWit")   # RFC-0016 K10a-target
  let (_, undefWitnessTup) = emitWitnessTuple(parsed.params, undefWitId)
  let typedUndefWitId = genSym(nskLet, "typedUndefWit")
  let typedDiagWitId = genSym(nskLet, "typedDiagWit")
  let typedWitId = genSym(nskLet, "typedWit")
  let typedRaisedWitId = genSym(nskLet, "typedRaisedWit")
  let typedDiagWitDeclNode = witnessDecl(typedDiagWitId, diagWitnessTup)
  let typedUndefWitDeclNode = witnessDecl(typedUndefWitId, undefWitnessTup)
  let typedWitDeclNode = witnessDecl(typedWitId, witnessTup)
  let typedRaisedWitDeclNode = witnessDecl(typedRaisedWitId, witnessTup)


  # Compile-time list of target constructors. We materialise them
  # at runtime as a `seq[SymexTarget]` so the runtime loop is a
  # single straight-line walk regardless of label count.
  # Build the runtime target list as a typed `newSeq[SymexTarget]()`
  # plus per-target `.add` calls. Avoids the "cannot infer element
  # type" trap when the SUT exposes zero targets — that case
  # (which cycle 18 promotes to `sfNotApplicable`) still needs to
  # compile cleanly.
  let tsId = genSym(nskVar, "targets")
  var targetsBuild = newStmtList()
  targetsBuild.add quote do:
    var `tsId` = newSeq[SymexTarget]()
  var nTargets = 0
  # Phase 14 B67: per-label exclusion.
  for lbl in labels:
    if lbl in excludedLabels: continue
    let call = newCall(bindSym"tLabel", newLit(lbl))
    targetsBuild.add newCall(bindSym"add", tsId, call)
    inc nTargets
  if stkAssertionViolation notin excludedKinds and
     irHasAssert(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tAssertionViolation"))
    inc nTargets
  if stkIndexError notin excludedKinds and
     irHasIndex(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tIndexError"))
    inc nTargets
  if stkFieldDefect notin excludedKinds and
     irHasVariantField(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tFieldDefect"))
    inc nTargets
  # Phase 15 E6. A raw `assert cond, msg` lowers to an implicit
  # `AssertionDefect` raise; auto-discover it as a `tRaisedExn("AssertionDefect")`
  # target so the reachable defect surfaces in `Report.symexFindings`.
  if stkRaisedExn notin excludedKinds and
     irHasAssertDefect(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tRaisedExn", newLit("AssertionDefect")))
    inc nTargets

  # Zero-targets fallback: the SUT has no symex-relevant constructs
  # (no markers, no asserts, no indexing, no variant arm-field
  # reads) — or `excludeTargets` ruled them all out. Skip Z3
  # entirely; deposit one `sfNotApplicable` audit entry so the
  # eventual Report still carries an honest "we looked, there was
  # nothing to look at" record. The runtime loop falls through
  # cleanly because `tsId` is empty.
  # Zero-targets fallback assembled at macro time: when nothing
  # was discovered (after `excludeTargets` filtering), the macro
  # emits a single `sfNotApplicable` deposit and skips the entire
  # `runSymex` loop — Z3 isn't called, the per-target cache isn't
  # touched. Otherwise the emitted body iterates `tsId` and runs
  # cache-then-symex per target.
  # gensym shared between the outer prog-binding quote and the
  # inner runtime body so they refer to the same NimNode (each
  # `quote do:` mints its own hygienic identifiers otherwise).
  let progId     = genSym(nskLet, "prog")
  let findingsId = genSym(nskVar, "findings")
  let dbErrorsId = genSym(nskVar, "dbErrors")
  let loopTarget = genSym(nskForVar, "t")  ## the runtime loop variable below
  let runReplayed = emitRunSymexReplayed(fn, parsed.params, progId,
                                         loopTarget, newLit(symexSettings),
                                         symexSettings.replay,
                                         irCollectProcValueSites(parsed.body,
                                                                 parsed.procs))
  let gapsSym = bindSym"findingGaps"   ## RFC-0005 S11 (private helper)
  let hintsSym = bindSym"findingHints"   ## RFC-0005 W1 (private helper)
  let stampSym = bindSym"stampBuild"     ## RFC-0016 K5a
  let runtimeBody =
    if nTargets == 0:
      # RFC-0005 W1 (§8.1, S11: every finding carries soundness, gaps and
      # annotation violations). Nothing ran, so the run's error list is the
      # parse-time one; its coordinate is derived from it as `runSymex`
      # derives a run's (`runTaintOf`), so the gaps' class join is the
      # `runTaint`, and there is no winning path or replay.
      quote do:
        let noTargetsFinding = SymexFinding(
          targetDesc: "no-targets-discovered",
          status:     sfNotApplicable,
          covered:    false,
          z3Version:  z3FullVersion(),
          # Review R1-16: settled by construction -- nothing ran, so there
          # is no claim to replay.
          soundness:  Soundness(runTaint: runTaintOf(`progId`.parseErrors),
                                replay: rsNotNeeded),
          bounds:     `symexSettings`.budget,       ## review R1-17
          gaps:       `gapsSym`(`progId`.parseErrors),
          hints:      `hintsSym`(`progId`.parseErrors),
          annotationViolations: `progId`.annotationViolations)
        `findingsId`.add noTargetsFinding
    else:
      quote do:
        for `loopTarget` in `tsId`:
          var f = SymexFinding(
            targetDesc: describeTarget(`loopTarget`),
            covered:    false,
            z3Version:  z3FullVersion(),
            fromCache:  false,
            # Review R1-17: the budget; a cache hit's key was derived from
            # it (every field is keyed), so the stored verdict ran under it.
            bounds:     `symexSettings`.budget,
            # RFC-0005 S11: parse-time facts, so a cache hit has them too.
            annotationViolations: `progId`.annotationViolations)
          # Phase 13 cycle 7. Three-level cascade:
          #   1. SAT cache hit → load witness, fromCache=true.
          #   2. Verdict cache hit → load sfUnsat/sfUnknown,
          #      fromCache=true.
          #   3. Cold path → runSymex; save witness or verdict.
          # `findingsId.add f` stays outside the if-else tree so EVERY
          # path returns a finding.
          let cached = loadSymexWitnessesImpl(`db`, `progId`, `loopTarget`,
                                              `symexSettings`, `dbErrorsId`)
          if cached.len > 0:
            f.status = sfSat
            f.witnessChoices = cached[0].choices
            f.soundness = cached[0].soundness   ## RFC-0005 S11: served unchanged
            f.gaps = cached[0].gaps             ## RFC-0005 S8az
            f.fromCache = true
          else:
            let cachedVerdict = loadSymexVerdictImpl(`db`, `progId`, `loopTarget`,
                                                     `symexSettings`,
                                                     `dbErrorsId`)
            # The raised slot is read only when the verdict missed; the
            # cascade is witness, then verdict, then raised.
            let cachedRaised =
              if cachedVerdict.isNone:
                loadSymexRaisedImpl(`db`, `progId`, `loopTarget`,
                                    `symexSettings`, `dbErrorsId`)
              else: @[]
            if cachedVerdict.isSome:
              f.status = cachedVerdict.get.status
              f.soundness = cachedVerdict.get.soundness   ## RFC-0005 S11
              f.gaps = cachedVerdict.get.gaps             ## RFC-0005 S8av
              f.fromCache = true
            elif cachedRaised.len > 0:
              # Phase 15 E2a. A reachable raise was persisted for this target;
              # serve it from cache without Z3. RFC-0005 W1: as the cold arm
              # below builds it -- the `raised(<type>)` descriptor, the
              # defect type and the witness the sentinel stores.
              let hit = cachedRaised[0]
              f.status = sfRaised
              f.targetDesc = "raised(" & hit.raw.raisedTypeId & ")"
              if hit.raw.isDefect:
                f.defectTypeId = hit.raw.raisedTypeId
              f.witnessChoices = hit.choices
              f.soundness = hit.raw.soundness   ## RFC-0005 S11
              f.gaps = hit.gaps                 ## RFC-0005 S8az
              f.fromCache = true
            else:
              # RFC-0005 S10: run + rule-3 replay settle; persisted below
              # only AFTER the settle (replay precedes persist, §7).
              let raw = `runReplayed`
              f.status = toFindingStatus(raw.status)
              # RFC-0005 S11: the settled soundness (persisted below with the
              # verdict) and the per-cause view of this run.
              f.soundness = raw.soundness
              f.bounds = raw.bounds   ## review R1-17
              f.gaps = `gapsSym`(raw.errors)
              # RFC-0005 W1: what `gaps` leaves out (the replay outcomes
              # among it) and the raises that did not decide the verdict,
              # the latter rendered as `symexFind` types them.
              f.hints = `hintsSym`(raw.errors)
              for diagEntry in raw.diagnostics:
                let `diagWitId` {.used.} = diagEntry.raisedWitness
                `typedDiagWitDeclNode`
                f.diagnostics.add FindingDiagnostic(
                  raisedTypeId:   diagEntry.raisedTypeId,
                  isDefect:       diagEntry.isDefect,
                  raisedMsg:      diagEntry.raisedMsg.get(""),
                  witnessChoices: renderAsChoices(`typedDiagWitId`),
                  witnessUnsafe:    diagEntry.witnessUnsafe)
              # RFC-0016 K10a-target: the undefined behaviours reached, with
              # the witness that reaches each, rendered the same way.
              for undefEntry in raw.undefined:
                let `undefWitId` {.used.} = undefEntry.witness
                `typedUndefWitDeclNode`
                f.undefined.add FindingUndefined(
                  kind: $undefEntry.kind, site: undefEntry.site,
                  witnessChoices: renderAsChoices(`typedUndefWitId`))
              var verdictSaved = false
              case raw.status
              of sxSat:
                let `witId` {.used.} = raw.witness
                `typedWitDeclNode`
                f.witnessChoices = renderAsChoices(`typedWitId`)
                verdictSaved = saveSymexWitnessImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                      f, `dbErrorsId`)
              of sxUnsat, sxUnknown:
                verdictSaved = saveSymexVerdictImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                      f.status, f.soundness, `dbErrorsId`,
                                      f.gaps)   ## RFC-0005 S8av
              of sxRaised:
                # Phase 16 D1a. The defect fork is now unconditional;
                # `routeRaise` populates `raisedWitness`. Carry it as
                # `witnessChoices` so callers can replay the input.
                # Use a DISTINCT `targetDesc` ("raised(<TypeId>)") so
                # sfSat filter loops in tests don't double-match on the
                # same base descriptor.
                let `witId` {.used.} = raw.raisedWitness
                `typedRaisedWitDeclNode`
                f.witnessChoices = renderAsChoices(`typedRaisedWitId`)
                f.targetDesc = "raised(" & raw.raisedTypeId & ")"
                # Phase 15 E6. Carry the defect type id onto the finding for
                # display when the raised type is a `Defect` subtype.
                if raw.isDefect:
                  f.defectTypeId = raw.raisedTypeId
                verdictSaved = saveSymexRaisedImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                    @[raw], `dbErrorsId`, @[f.gaps],  ## RFC-0005 S8az
                                    @[f.witnessChoices])               ## RFC-0005 W1
              # RFC-0005 W1: beside whichever slot the arm above wrote.
              # Review R4 (W2), R5 (D4a): only when that arm saved the verdict
              # (its own return, not a copy of its skip rules).
              if verdictSaved:
                saveSymexNotesImpl(`db`, `progId`, `loopTarget`,
                                   `symexSettings`, f.hints, f.diagnostics,
                                   f.undefined, `dbErrorsId`)
          if f.fromCache:
            # RFC-0005 W1: every hit above serves the cold run's hints and
            # diagnostics too, from the `:notes` record the cold arm wrote.
            let notes = loadSymexNotesImpl(`db`, `progId`, `loopTarget`,
                                           `symexSettings`, `dbErrorsId`)
            f.hints = notes.hints
            f.diagnostics = notes.diagnostics
            f.undefined = notes.undefined   # RFC-0016 K10a-target
          `stampSym`(f.soundness)   ## RFC-0016 K5a: a cache hit's too
          `findingsId`.add f

  result = quote do:
    block:
      let `progId` {.used.} = `progExpr`
      `targetsBuild`
      var `findingsId`: seq[SymexFinding] = @[]
      var `dbErrorsId` {.used.}: seq[string] = @[]
        # Phase 13 cycle 3 — accumulator for DB save/load failures.
        # Phase 14 cycle C2: drained into `engineSymexDbErrors`
        # thread-local sink so `finalizePhase` can append into
        # `Report.dbErrors` at end-of-run.
      `runtimeBody`
      # Phase 14 C2: deposit accumulated DB errors into the
      # engine-side thread-local sink. `recordSymexDbError` is a
      # tiny append; safe to call from any phase.
      for dbErr in `dbErrorsId`:
        recordSymexDbError(dbErr)
      `findingsId`

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

  const symexSelfNames = extractTopLevelNames(currentSourcePath())
  vmGuardAuditNames(symexSelfNames, "symex.nim")

  const symexSelfLetHits = block:
    var dedup: seq[string]
    for h in vmGuardLetHits:
      if h.startsWith("symex.nim:") and h notin dedup: dedup.add h
    dedup

  const symexSelfParamHits = block:
    var dedup: seq[string]
    for h in vmGuardParamHits:
      if h.startsWith("symex.nim:") and h notin dedup: dedup.add h
    dedup

  const symexSelfReachHits = block:
    var dedup: seq[string]
    for h in vmGuardReachHits:
      if h.startsWith("symex.nim:") and h notin dedup: dedup.add h
    dedup

  # The one historical hazard S8x/S8ab/S8af already reviewed and allowlisted
  # in symex.nim's own scope: `emitTyAndReaderShared`'s nested
  # `emitMVBranch`, reading a `VariantAxis`/`VariantArm` element with
  # nothing written while the binding is live (the `types.nim:==` twin of
  # this same finding is allowlisted in `vm_alias_guard.nim`'s own block).
  const symexSelfLetAllowlist = [
    "symex.nim:emitTyAndReaderShared: let ax : VariantAxis (ntyObject) <- ty.mvAxes[axisIdx]",
    "symex.nim:emitTyAndReaderShared: let elseArm : VariantArm (ntyObject) <- ax.arms[elseArmIx]",
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

