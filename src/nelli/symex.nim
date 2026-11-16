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
import ./smt/replay_emit   ## RFC-0016 D6: the replay child emitter
export replay_emit.wireTarget, replay_emit.readTarget, replay_emit.targetLabelOf,
       replay_emit.emitReplayWitness
import ./smt/replay_settle   ## RFC-0016 D6: the verdict-side replay settle
export replay_settle.candidateLossy
import ./smt/proc_lift   ## RFC-0016 D6: the proc-value lift
import ./smt/run_replayed   ## RFC-0016 D6: the replayed-search body
import ./smt/entry_parse   ## RFC-0016 D6: what every entry macro does first
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

