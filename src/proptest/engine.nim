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
import ./engine/phases
export phases
import ./coverage
export coverage

const coverageScoreLabel* = "__coverage__"
  ## Reserved label under which the coverage-guided wrap (`#107`) writes
  ## the per-example coverage delta into `currentFrame().scores`. The
  ## `__` prefix is in the engine-owned namespace enforced by `target()`,
  ## so user code can't collide with it.

# Forward declarations: `runForAllPipeline` (defined alongside `forAll`
# in the middle of this file) calls `defaultPhases[T]()`, which is defined
# at the bottom alongside the phase implementations. Forward-declare so
# the middle of the file compiles without reordering the layout.



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
  let deadlineProp =
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
  # #107 — coverage-as-PBT-target. When `coverageGuided` is on, flip the
  # thread's coverage mode to `cmRecording` for the duration of the run,
  # zero the bitmap so cumulative counts reflect this run, and wrap the
  # property so each call records the per-example *delta* under the
  # reserved label `coverageScoreLabel` directly in the frame's score
  # table. The targeted phase then treats coverage as another Pareto
  # objective with no other changes.
  let priorCoverageMode = currentCoverageMode()
  if settings.coverageGuided:
    setCoverageMode(cmRecording)
    resetCoverage()
  defer:
    if settings.coverageGuided:
      setCoverageMode(priorCoverageMode)
  let prop =
    if settings.coverageGuided:
      proc(x: T) =
        let before = currentCoverage()
        deadlineProp(x)
        let delta = currentCoverage() - before
        # Bypass `target()` validation: the engine owns this label.
        currentFrame().scores[coverageScoreLabel] = float(delta)
    else:
      deadlineProp
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


