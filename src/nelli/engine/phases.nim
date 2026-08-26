## Phase implementations for the engine pipeline.
##
## Each phase is a deep module by Ousterhout's criterion: tiny interface
## (`run(state) → PhaseAction`), substantial implementation, independently
## testable, self-gating on `EngineState`.
##
## Pipeline order (from `defaultPhases[T]()`):
##   dbReuse → explicit → random → targeted → shrink → explain → finalize
##
## Source phases (dbReuse / explicit / random / targeted) self-gate on
## `state.output.rawFalsification.isNone` so they don't overwrite each
## other. Downstream phases (shrink / explain) gate on the inverse —
## they only act when there's a falsification to process. `finalize`
## constructs the terminal Report from accumulated state.

import std/[options, tables, times, monotimes, hashes]
import ../strategy, ../datasource, ../rng, ../choice, ../shrinker, ../db, ../int128, ../optbox
import ./types, ./frame, ./eval, ./render, ./targeting, ./pipeline
import ../coverage

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
        fromPhase: "dbReuse", crash: r.fCrash))
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
    template fail(reason: string; crashInfo = none(CrashInfo)): untyped =
      state.output.finalReport = some(Report[T](
        outcome: otFalsified, examples: i,
        counterexample: box(ex), choices: @[],
        message: "from explicit example #" & $i & " " & reason,
        seed: state.spec.settings.seed,
        dbReplays: state.acc.dbReplays,
        events: snapshotEvents(),
        printEvents: state.spec.settings.printEvents,
        dbErrors: state.acc.dbErrors,
        crash: crashInfo))
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
      # RFC-fuzzer-nextgen U0: same in-process crash-isolation boundary as
      # `evalReplay`/`fuzz.observeInProcess` — a Defect on an explicit
      # (user-pinned) example is caught and reported with typed CrashInfo
      # rather than aborting; explicit examples still aren't shrunk (no
      # choice sequence to shrink), matching the pre-U0 contract.
      let msg = "crashed: " & $e.name & ": " & e.msg
      fail(msg, some(CrashInfo(kind: ckException, defect: $e.name, message: msg)))
  pcContinue

proc symexSeedPhase*[T](seeds: seq[seq[ChoiceNode]]): Phase[T] =
  ## Phase 12 cycle 14. Replays a list of symex-derived choice
  ## sequences against the live strategy + property. Each seed is
  ## fed to `evalReplay`, which catches `Overrun` / `Rejection`
  ## internally and surfaces them as `ekRejected`. Successful
  ## falsifications carry forward as `RawFalsification` with
  ## `fromPhase = "symexSeed"`, so `shrinkPhase` can minimise the
  ## witness — Z3 returns *some* satisfying assignment, not a
  ## minimal one. Self-gates on prior falsifications (e.g., from
  ## `dbReusePhase`) so warm-run regression catches still take
  ## priority — see deferral #4 for the documented warm-run note.
  ##
  ## Closure-capturing the seeds requires `Phase[T].run` to be
  ## `{.closure.}` — flipped in Phase 12 cycle 2.
  Phase[T](name: "symexSeed",
    run: proc(state: var EngineState[T]): PhaseAction =
      # Phase 14 cycle B2: `forcePhases` override. When `phSymexSeed`
      # is in the set, the phase runs even after a prior phase
      # falsified; its findings are deposited into the sink and the
      # existing `rawFalsification` is left intact (not overwritten).
      let forced = phSymexSeed in state.spec.settings.forcePhases
      if state.output.rawFalsification.isSome and not forced:
        return pcContinue
      for seed in seeds:
        let r = evalReplay(state.spec.s, state.spec.prop, seed)
        case r.kind
        of ekFalsified:
          # `r.fChoices` is the trace evalReplay actually consumed
          # (may differ from `seed` if the property short-circuited
          # mid-draw). Carrying *that* forward gives the shrinker
          # the exact sequence to minimise.
          # Phase 14 B2: when forced, preserve any prior falsification
          # (the existing one wins) — symexSeed still finishes
          # iterating so its findings flow to the sink, but doesn't
          # overwrite an already-found counterexample.
          if state.output.rawFalsification.isNone:
            state.output.rawFalsification = some(RawFalsification[T](
              value: r.fValue, choices: r.fChoices,
              message: r.fMsg, notes: r.fNotes,
              fromPhase: "symexSeed", crash: r.fCrash))
            return pcContinue
        of ekRejected:
          # The seed's shape doesn't match the current strategy
          # (Overrun) or the property called `reject` / `assume`
          # (Rejection). Either way it's not a falsification —
          # record an `sfNotApplicable` finding so the eventual
          # report carries an honest audit trail and continue.
          recordSymexFinding(SymexFinding(
            targetDesc: "<seed-shape-mismatch-or-rejected>",
            status:     sfNotApplicable,
            covered:    false))
        of ekPassed:
          discard
      pcContinue)

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
    # #103 follow-up: thread the user's distribution-bias policy onto
    # the per-example DataSource so `Settings.integerBias` is observed
    # by every `drawInteger` call in this example's draw sequence.
    ds.integerBias = resolved(state.spec.settings.integerBias)
    var rejected = false
    var failMessage = ""
    var falsified = false
    var valueOpt: Opt[T]
    var crashInfo = none(CrashInfo)
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    try:
      let x = state.spec.s.generate(ds)
      valueOpt = box(x)
      state.spec.prop(x)
    except Rejection:
      rejected = true
    except FalsifiedError as e:
      falsified = true; failMessage = e.msg
    except CatchableError as e:
      falsified = true; failMessage = "raised " & $e.name & ": " & e.msg
    except Defect as e:
      # RFC-fuzzer-nextgen U0: same in-process crash-isolation boundary as
      # `evalReplay` — the random phase is `forAll`'s highest-traffic
      # source phase, so this is the site the RFC's "coverageGuided forAll
      # path is crash-fatal" ground truth centers on.
      falsified = true
      failMessage = "crashed: " & $e.name & ": " & e.msg
      crashInfo = some(CrashInfo(kind: ckException, defect: $e.name,
                                 message: failMessage))
    if falsified:
      state.output.rawFalsification = some(RawFalsification[T](
        value: valueOpt, choices: ds.recorded,
        message: failMessage, notes: currentFrame().notes,
        fromPhase: "random", crash: crashInfo))
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
    state.output.shrunkCrash = raw.crash
    return pcContinue

  # Step 2-3: shrink + capture shrunk notes.
  let shrunk = shrink(state.spec.s, state.spec.prop, raw.choices,
                       state.spec.settings.maxShrinks)
  let shrunkEval = evalReplay(state.spec.s, state.spec.prop, shrunk.choices)
  let shrunkNotes = if shrunkEval.kind == ekFalsified: shrunkEval.fNotes
                    else: @[]
  # RFC-fuzzer-nextgen U0: re-derived from the SHRUNK candidate's own
  # re-`evalReplay` (mirrors `shrunkNotes`'s own re-derivation), not carried
  # verbatim from `raw` — the minimal example is what's actually reported,
  # so its own crash classification is authoritative (in the rare case
  # shrinking lands on a differently-classified failure of the same
  # `ChoiceSeq` neighborhood).
  let shrunkCrash = if shrunkEval.kind == ekFalsified: shrunkEval.fCrash
                    else: none(CrashInfo)

  state.output.shrunkChoices = some(shrunk.choices)
  state.output.shrunkExample = shrunk.example
  state.output.shrunkNotes = shrunkNotes
  state.output.shrunkCrash = shrunkCrash
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
          counterexample: empty[T](), choices: @[],
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
  proc captureCb(value: Opt[T], choices: seq[ChoiceNode],
                 msg, prefix: string, ex: int,
                 originalNotes: seq[(string, string)],
                 crash: Option[CrashInfo]): Report[T] =
    captured = some(RawFalsification[T](
      value: value, choices: choices,
      message: msg, notes: originalNotes,
      fromPhase: "targeted", crash: crash))
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
      dbErrors: state.acc.dbErrors & consumeSymexDbErrors(),
      coverageHits: (if state.spec.settings.coverageGuided:
                       currentCoverage() else: 0),
      crash: state.output.shrunkCrash))
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
    dbErrors: state.acc.dbErrors,
    coverageHits: (if state.spec.settings.coverageGuided:
                     currentCoverage() else: 0)))
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
