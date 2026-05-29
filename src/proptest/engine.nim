## The property runner.
##
## `forAll` generates up to `maxExamples` values from a strategy and checks the
## property against each, classifying every example as pass, falsified, or
## rejected (`assume`/filter). It returns a `Report` rather than raising, so it
## composes; the test-framework adapter (`dsl.nim`) turns a falsified report
## into a single unittest failure.
##
## **Targeted PBT.** A property can call `target(score, label = "")` zero or
## more times per example. The engine tracks a bounded Pareto front of
## non-dominated examples across all labels and, after the random phase,
## explores around the front with two phases:
## * **Pareto-aware greedy hill-climb** — try ±{1, 10, 100, 1000} perturbations
##   on each integer choice; a perturbation is accepted iff its score-tuple is
##   not dominated by any current front member.
## * **Simulated-annealing escape** — from each front member, do K Cauchy-
##   distributed proposals. Acceptance uses random-weight Tchebycheff
##   scalarization (reaches the full Pareto front, including non-convex
##   regions, unlike weighted-sum). Falsifications discovered during either
##   phase are shrunk and reported as falsifications.
##
## **Cross-run resumption** — the secondary corpus persists the full Pareto
## front (label-keyed score tables) so a follow-up run seeds its targeted
## phase from where the last one left off.

import std/[math, tables, sets, options, hashes, times, monotimes, algorithm,
            strutils]
export options
import ./strategy, ./datasource, ./rng, ./choice, ./shrinker, ./db, ./int128
# Settings, Report[T], Outcome, Necessity, ParetoEntry, EventStats,
# ScoreMap, NumericSummary, FalsifiedError, DeadlineExceeded,
# defaultSettings — all extracted to engine/types.nim so the new
# pipeline phases (#119) can reference them without a circular
# import on engine.nim itself.
import ./engine/types
export types
import ./engine/frame
export frame
import ./engine/eval
export eval
import ./engine/render
export render
import ./engine/pipeline
export pipeline
import ./engine/targeting
export targeting

# Forward declarations: `runForAllPipeline` (defined alongside `forAll`
# in the middle of this file) calls `defaultPhases[T]()`, which is defined
# at the bottom alongside the phase implementations. Forward-declare so
# the middle of the file compiles without reordering the layout.
proc defaultPhases*[T](): seq[Phase[T]]



proc runForAllPipeline[T](db: ExampleDatabase, dbEnabled: bool,
                          s: Strategy[T], prop: proc(x: T),
                          settings: Settings,
                          explicit: seq[T]): Report[T] =
  ## The new pipeline-based runner. Constructs an `EngineSpec[T]`,
  ## pushes a fresh `EngineFrame`, applies the deadline-wrapping to
  ## `prop`, then iterates `defaultPhases[T]()` via `runPipeline`.
  ##
  ## Replaces the legacy `runForAllImpl`. The behavior is identical
  ## from the caller's perspective — the same `Report[T]` shape comes
  ## out — but every previously-monolithic step (DB reuse, explicit,
  ## random, targeted, shrink, explain, finalize) is now an
  ## independently-testable phase.
  var settings = settings
  if settings.derandomize:
    if settings.testId.len == 0:
      raise newException(ValueError,
        "Settings.derandomize=true requires a non-empty Settings.testId")
    settings.seed = cast[uint64](hash(settings.testId))
  engineStack.add EngineFrame()
  defer: discard engineStack.pop()
  let originalProp = prop
  let deadline = settings.deadline
  let hasDeadline = deadline.inNanoseconds > 0
  let prop =
    if hasDeadline:
      proc(x: T) =
        let start = getMonoTime()
        originalProp(x)
        let elapsed = getMonoTime() - start
        if elapsed.inNanoseconds > deadline.inNanoseconds:
          raise newException(DeadlineExceeded,
            "deadline exceeded: " & $elapsed & " > " & $deadline)
    else:
      originalProp
  let spec = EngineSpec[T](
    s: s, prop: prop, settings: settings,
    db: db, dbEnabled: dbEnabled, explicit: explicit)
  var state = initEngineState(spec)
  runPipeline(state, defaultPhases[T]())

proc forAll*[T](s: Strategy[T], prop: proc(x: T),
                settings = defaultSettings()): Report[T] =
  ## Check `prop` against values drawn from `s`. Deterministic in
  ## `settings.seed`. When `settings.testId` and `settings.dbPath` are
  ## both set, the reuse phase replays any DB-stored failure first; a
  ## fresh falsification is saved back to the directory-based DB.
  let db = directoryBasedDatabase(settings.dbPath)
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, @[])

proc forAllUsing*[T](db: ExampleDatabase, s: Strategy[T], prop: proc(x: T),
                     settings = defaultSettings()): Report[T] =
  ## Variant of `forAll` that runs against an explicitly-supplied DB
  ## backend. DB is enabled whenever `settings.testId` is non-empty.
  let dbEnabled = settings.testId.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, @[])

proc forAllWithExamples*[T](explicit: openArray[T], s: Strategy[T],
                            prop: proc(x: T),
                            settings = defaultSettings()): Report[T] =
  ## Run each value in `explicit` through `prop` before the random phase.
  ## Explicit examples are user-pinned regression seeds — the user said
  ## "this exact input matters," so we don't shrink them (no choice
  ## sequence to shrink) and report `choices: @[]` on failure.
  let db = directoryBasedDatabase(settings.dbPath)
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, @explicit)


# ============================================================================
# Pipeline phases (toward #119 — engine redesign as pluggable phase pipeline)
# ============================================================================
# Phases consume / mutate `EngineState[T]` (defined in engine/pipeline.nim).
# For session 1 of #119, only `finalizePhase` is implemented as a working
# phase; subsequent sessions add `randomPhase`, `shrinkPhase`, etc., and
# eventually switch `forAll` / `forAllUsing` to use `runPipeline` instead of
# the legacy `runForAllImpl`.
#
# Phases live in engine.nim for now because they need access to engine
# internals (`snapshotEvents`, `renderDisplayed`, `evalReplay`, `perturbations`).
# Once those internals are also extracted into sub-modules, phases move into
# their own files (`engine/phase_finalize.nim`, `engine/phase_random.nim`, …).

proc dbReusePhase*[T](state: var EngineState[T]): PhaseAction =
  ## Replay primary DB entries for `state.spec.settings.testId`. On the
  ## first entry that reproduces a falsification, set
  ## `state.output.rawFalsification` (with `fromPhase = "dbReuse"`) and
  ## `pcContinue` so `shrinkPhase` minimizes it. Stale entries (those
  ## that no longer falsify) are batched + pruned in one
  ## removeMany call to avoid N writes.
  ##
  ## Self-gates on rawFalsification.isNone (skips when an upstream
  ## source phase already produced one — though dbReuse is the first
  ## source phase, so in practice this guard is defense in depth).
  if state.output.rawFalsification.isSome: return pcContinue
  if not state.spec.dbEnabled: return pcContinue
  var primaryEntries: seq[seq[ChoiceNode]]
  try:
    primaryEntries = state.spec.db.loadPrimary(state.spec.settings.testId)
  except DbError as e:
    state.acc.dbErrors.add("loadPrimary: " & e.msg)
    if state.spec.settings.strictDb:
      state.output.finalReport = some(Report[T](
        outcome: otFalsified, examples: 0,
        message: "DB: loadPrimary: " & e.msg,
        seed: state.spec.settings.seed,
        dbReplays: 0,
        events: snapshotEvents(),
        printEvents: state.spec.settings.printEvents,
        dbErrors: state.acc.dbErrors))
      return pcTerminate
    return pcContinue

  var staleEntries: seq[seq[ChoiceNode]]
  for entry in primaryEntries:
    inc state.acc.dbReplays
    let r = evalReplay(state.spec.s, state.spec.prop, entry)
    case r.kind
    of ekFalsified:
      if staleEntries.len > 0:
        try: state.spec.db.removeMany(state.spec.settings.testId, staleEntries)
        except DbError as e: state.acc.dbErrors.add("removeMany: " & e.msg)
      state.output.rawFalsification = some(RawFalsification[T](
        value: r.fValue, choices: r.fChoices,
        message: r.fMsg, notes: r.fNotes,
        fromPhase: "dbReuse"))
      return pcContinue
    of ekPassed, ekRejected:
      staleEntries.add entry
  if staleEntries.len > 0:
    try: state.spec.db.removeMany(state.spec.settings.testId, staleEntries)
    except DbError as e: state.acc.dbErrors.add("removeMany: " & e.msg)
  pcContinue

proc explicitExamplesPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Run user-pinned regression seeds from `state.spec.explicit` before
  ## the random phase. An explicit failure short-circuits with
  ## `choices: @[]` (no shrinking on user-pinned values — the user said
  ## "this exact input matters") and a "from explicit example" message.
  ## Skips if a prior source phase (e.g. dbReuse) already produced a
  ## falsification.
  if state.output.rawFalsification.isSome: return pcContinue
  if state.spec.explicit.len == 0: return pcContinue
  for i, ex in state.spec.explicit:
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    template fail(reason: string): untyped =
      state.output.finalReport = some(Report[T](
        outcome: otFalsified, examples: i,
        counterexample: some(ex), choices: @[],
        message: "from explicit example #" & $i & " " & reason,
        seed: state.spec.settings.seed,
        dbReplays: state.acc.dbReplays,
        events: snapshotEvents(),
        printEvents: state.spec.settings.printEvents,
        dbErrors: state.acc.dbErrors))
      return pcTerminate
    try:
      state.spec.prop(ex)
    except Rejection:
      continue
    except FalsifiedError as e:
      fail(": " & e.msg)
    except CatchableError as e:
      fail("raised " & $e.name & ": " & e.msg)
    except Defect as e:
      fail("crashed: " & $e.name & ": " & e.msg)
  pcContinue

proc randomPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Self-gates: skip if an upstream source phase (dbReuse, explicit)
  ## already produced a falsification.
  if state.output.rawFalsification.isSome: return pcContinue
  ## Generate random inputs from `state.spec.s`, run the property, and
  ## either accumulate (passing examples, with their scores feeding the
  ## Pareto front) or short-circuit:
  ## - On falsification: set `state.output.rawFalsification` and
  ##   `pcContinue` so `shrinkPhase` processes it.
  ## - On rejection-budget exhaustion: set the final `otExhausted`
  ##   Report and `pcTerminate`.
  while state.acc.examplesDone < state.spec.settings.maxExamples:
    var ds = newDataSource(initSplitMix64(state.acc.master.next))
    var rejected = false
    var failMessage = ""
    var falsified = false
    var valueOpt: Option[T]
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    try:
      let x = state.spec.s.generate(ds)
      valueOpt = some(x)
      state.spec.prop(x)
    except Rejection:
      rejected = true
    except FalsifiedError as e:
      falsified = true; failMessage = e.msg
    except CatchableError as e:
      falsified = true; failMessage = "raised " & $e.name & ": " & e.msg
    except Defect as e:
      falsified = true; failMessage = "crashed: " & $e.name & ": " & e.msg
    if falsified:
      state.output.rawFalsification = some(RawFalsification[T](
        value: valueOpt, choices: ds.recorded,
        message: failMessage, notes: currentFrame().notes,
        fromPhase: "random"))
      return pcContinue
    if rejected:
      inc state.acc.rejections
      if state.acc.rejections > state.spec.settings.maxRejections:
        state.output.finalReport = some(Report[T](
          outcome: otExhausted, examples: state.acc.examplesDone,
          seed: state.spec.settings.seed,
          paretoFront: state.acc.paretoFront,
          dbReplays: state.acc.dbReplays,
          events: snapshotEvents(),
          printEvents: state.spec.settings.printEvents,
          dbErrors: state.acc.dbErrors))
        return pcTerminate
      continue
    if currentFrame().scores.len > 0:
      let entry = ParetoEntry(scores: currentFrame().scores, choices: ds.recorded)
      insertPareto(state.acc.paretoFront, entry)
      updateRefPoint(state.acc.refPoint, entry.scores)
    inc state.acc.examplesDone
  pcContinue

proc shrinkPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Process `state.output.rawFalsification` if set:
  ## 1. Pre-shrink flaky retry pass (settings.flakyRetries iterations).
  ## 2. Shrinker to minimize the failing choice sequence.
  ## 3. Re-evalReplay on shrunk choices to capture the shrunk-example
  ##    note context (matches `Report.notes` semantics).
  ## 4. Post-shrink flaky check from `shrink.flaky`.
  ## 5. Persist to DB (when enabled and not flaky).
  ## Mutates `state.output` with the shrink results.
  ##
  ## No-op (returns `pcContinue`) when there's no falsification to process.
  if state.output.rawFalsification.isNone: return pcContinue
  let raw = state.output.rawFalsification.get

  # Step 1: pre-shrink flaky detect.
  var flakyRetryPassed = false
  for _ in 0 ..< state.spec.settings.flakyRetries:
    let e = evalReplay(state.spec.s, state.spec.prop, raw.choices)
    if e.kind == ekPassed:
      flakyRetryPassed = true
      break
  if flakyRetryPassed:
    state.output.isFlaky = true
    state.output.shrunkChoices = some(raw.choices)
    state.output.shrunkExample = raw.value
    state.output.shrunkNotes = raw.notes
    return pcContinue

  # Step 2-3: shrink + capture shrunk notes.
  let shrunk = shrink(state.spec.s, state.spec.prop, raw.choices,
                       state.spec.settings.maxShrinks)
  let shrunkEval = evalReplay(state.spec.s, state.spec.prop, shrunk.choices)
  let shrunkNotes = if shrunkEval.kind == ekFalsified: shrunkEval.fNotes
                    else: @[]

  state.output.shrunkChoices = some(shrunk.choices)
  state.output.shrunkExample = shrunk.example
  state.output.shrunkNotes = shrunkNotes
  state.output.isFlaky = shrunk.flaky

  # Step 5: DB persistence on the successfully-shrunk failure.
  if state.spec.dbEnabled and not shrunk.flaky:
    try:
      state.spec.db.save(state.spec.settings.testId, shrunk.choices)
    except DbError as e:
      state.acc.dbErrors.add("save: " & e.msg)
      if state.spec.settings.strictDb:
        state.output.finalReport = some(Report[T](
          outcome: otFalsified, examples: state.acc.examplesDone,
          counterexample: none(T), choices: @[],
          message: "DB: save: " & e.msg,
          seed: state.spec.settings.seed,
          dbReplays: state.acc.dbReplays,
          events: snapshotEvents(),
          printEvents: state.spec.settings.printEvents,
          dbErrors: state.acc.dbErrors))
        return pcTerminate
  pcContinue

proc targetedPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Hill-climb + simulated-annealing over the Pareto front built by
  ## `randomPhase`. Cross-run resumption: loads secondary corpus first
  ## to seed the front from prior runs.
  ##
  ## Implementation: wraps the existing `runTargetedPhase` with a
  ## capture-only callback that stores any falsification into
  ## `state.output.rawFalsification` for downstream `shrinkPhase` to
  ## process. The callback returns a placeholder Report that
  ## `runTargetedPhase` discards as `some(...)`; we ignore that and
  ## use the captured raw falsification instead.
  ##
  ## Self-gates: skip if a prior phase already falsified.
  if state.output.rawFalsification.isSome: return pcContinue

  # Cross-run resumption: seed the front from the secondary corpus
  # *before* the empty-front check — a saved Pareto front from a
  # previous run is reason to run targeting even if this run's random
  # phase didn't produce any scored examples (e.g., maxExamples = 0).
  if state.spec.dbEnabled:
    var secondaryEntries: seq[ScoredEntry]
    try:
      secondaryEntries = state.spec.db.loadSecondary(state.spec.settings.testId)
    except DbError as e:
      state.acc.dbErrors.add("loadSecondary: " & e.msg)
    for entry in secondaryEntries:
      var scores: ScoreMap
      if entry.scores.len > 0: scores = entry.scores
      else: scores[""] = entry.score
      insertPareto(state.acc.paretoFront,
                   ParetoEntry(scores: scores, choices: entry.choices))
      updateRefPoint(state.acc.refPoint, scores)

  if state.acc.paretoFront.len == 0: return pcContinue

  var captured: Option[RawFalsification[T]]
  proc captureCb(value: Option[T], choices: seq[ChoiceNode],
                 msg, prefix: string, ex: int,
                 originalNotes: seq[(string, string)]): Report[T] =
    captured = some(RawFalsification[T](
      value: value, choices: choices,
      message: msg, notes: originalNotes,
      fromPhase: "targeted"))
    Report[T](outcome: otFalsified)  # placeholder; not consumed

  let _ = runTargetedPhase(
    state.spec.s, state.spec.prop, state.spec.settings,
    state.spec.db, state.spec.dbEnabled,
    state.acc.master, state.acc.paretoFront, state.acc.refPoint,
    state.acc.examplesDone, captureCb)

  if captured.isSome:
    state.output.rawFalsification = captured
  pcContinue

proc explainPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Run the explain pass (per-choice necessity) when we have a
  ## non-flaky shrunken falsification. Skips when flaky (the shrunk
  ## example doesn't reliably reproduce, so necessity wouldn't be
  ## meaningful).
  if state.output.shrunkChoices.isNone or state.output.isFlaky:
    return pcContinue
  let raw = state.output.rawFalsification.get
  state.output.necessity = explain(state.spec.s, state.spec.prop,
                                    state.output.shrunkChoices.get,
                                    raw.message)
  pcContinue

proc finalizePhase*[T](state: var EngineState[T]): PhaseAction =
  ## Terminal phase: build the final Report from accumulated state.
  ## When upstream phases already set `finalReport` (e.g.,
  ## `randomPhase` on exhaustion, `shrinkPhase` on strict-DB error),
  ## this phase is a no-op.
  ##
  ## When a shrunken falsification is present, builds an `otFalsified`
  ## (or `otFlaky`) Report. Otherwise builds `otPassed`.
  ## See also `defaultPhases[T]()` for the canonical pipeline.
  if state.output.finalReport.isSome: return pcContinue
  if state.output.shrunkChoices.isSome and
     state.output.rawFalsification.isSome:
    let raw = state.output.rawFalsification.get
    let outcome = if state.output.isFlaky: otFlaky else: otFalsified
    let prefix =
      case raw.fromPhase
      of "dbReuse": "from DB"
      of "explicit": "from explicit example"
      of "targeted": "via target"
      else: ""
    let msgPrefix =
      if state.output.isFlaky:
        (if prefix.len > 0: "flaky (post-shrink) " & prefix & ": "
         else: "flaky (post-shrink): ")
      else:
        (if prefix.len > 0: prefix & ": " else: ": ")
    state.output.finalReport = some(Report[T](
      outcome: outcome,
      examples: state.acc.examplesDone,
      counterexample: state.output.shrunkExample,
      choices: state.output.shrunkChoices.get,
      message: msgPrefix & raw.message,
      seed: state.spec.settings.seed,
      paretoFront: state.acc.paretoFront,
      dbReplays: state.acc.dbReplays,
      notes: state.output.shrunkNotes,
      necessity: state.output.necessity,
      displayed: renderDisplayed(state.spec.s, state.output.shrunkExample),
      events: snapshotEvents(),
      printEvents: state.spec.settings.printEvents,
      dbErrors: state.acc.dbErrors))
    return pcContinue
  # Default: otPassed
  state.output.finalReport = some(Report[T](
    outcome: otPassed,
    examples: state.acc.examplesDone,
    seed: state.spec.settings.seed,
    paretoFront: state.acc.paretoFront,
    dbReplays: state.acc.dbReplays,
    events: snapshotEvents(),
    printEvents: state.spec.settings.printEvents,
    dbErrors: state.acc.dbErrors))
  pcContinue

proc defaultPhases*[T](): seq[Phase[T]] =
  ## The canonical PBT pipeline. Each entry is one phase, run in
  ## order; phases self-gate on state so the same list works for
  ## every kind of run (passing, falsifying, flaky, exhausted,
  ## DB-replayed, explicit-pinned, targeted).
  @[
    Phase[T](name: "dbReuse",  run: dbReusePhase[T]),
    Phase[T](name: "explicit", run: explicitExamplesPhase[T]),
    Phase[T](name: "random",   run: randomPhase[T]),
    Phase[T](name: "targeted", run: targetedPhase[T]),
    Phase[T](name: "shrink",   run: shrinkPhase[T]),
    Phase[T](name: "explain",  run: explainPhase[T]),
    Phase[T](name: "finalize", run: finalizePhase[T]),
  ]
