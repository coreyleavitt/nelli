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
import ./autolabel
export autolabel

when compileOption("panics"):
  {.warning: "nelli: under --panics:on, property *crashes* (Defects — " &
    "IndexDefect, nil-deref, overflow, doAssert/failed assert) are fatal and " &
    "uncatchable, so the engine cannot report them as shrunk counterexamples — " &
    "a crashing property aborts the whole run. Clean `ensure`/`assume` " &
    "falsification is unaffected. Build test binaries with --panics:off to " &
    "enable crash-as-falsification (and shrinking through a crash).".}

proc engineAutoLabelSink(label: string) {.nimcall.} =
  ## The sink the engine installs for `Settings.autoLabels=true`. Routes
  ## strategies' `autoLabel(...)` calls into the current frame's
  ## categorical events table. Safe to call from inside any strategy
  ## run during a forAll: the frame is guaranteed non-empty by
  ## `runForAllPipeline`'s push/pop discipline.
  if engineStack.len == 0: return
  inc engineStack[^1].eventsCategorical.mgetOrPut(label, 0)

const coverageScoreLabel* = "__coverage__"
  ## Reserved label under which the coverage-guided wrap (`#107`) writes
  ## the per-example coverage delta into `currentFrame().scores`. The
  ## `__` prefix is in the engine-owned namespace enforced by `target()`,
  ## so user code can't collide with it.

# Forward declarations: `runForAllPipeline` (defined alongside `forAll`
# in the middle of this file) calls `defaultPhases[T]()`, which is defined
# at the bottom alongside the phase implementations. Forward-declare so
# the middle of the file compiles without reordering the layout.



proc runForAllPipelineWithPhases*[T](db: ExampleDatabase, dbEnabled: bool,
                                      s: Strategy[T], prop: proc(x: T),
                                      settings: Settings,
                                      explicit: Examples[T],
                                      phases: seq[Phase[T]]): Report[T] =
  ## Pipeline-based runner with an injectable phase list. The default
  ## phase ordering (DB reuse → explicit → random → targeted → shrink
  ## → explain → finalize) lives behind the `runForAllPipeline`
  ## wrapper below; Phase 12 cycle 15 uses this entry point to slot
  ## `symexSeedPhase` in between `explicit` and `random` without
  ## duplicating any of the preamble (deadline wrap, autoLabel sink,
  ## coverage init, derandomize-seed derivation).
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
  # #108 — strategy distribution auto-labels. When `autoLabels` is on,
  # install a sink that routes each strategy's `autoLabel(...)` call into
  # the frame's `eventsCategorical` table; save/restore the prior sink
  # so a nested forAll's discipline composes. The sink is a top-level
  # `{.nimcall.}` proc (closures aren't compatible with the sink type),
  # which is why it lives at file scope and reads engineStack directly.
  let priorAutoLabelSink = currentAutoLabelSink()
  if settings.autoLabels:
    setAutoLabelSink(engineAutoLabelSink)
  defer:
    if settings.autoLabels:
      setAutoLabelSink(priorAutoLabelSink)
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
  runPipeline(state, phases)

proc runForAllPipeline[T](db: ExampleDatabase, dbEnabled: bool,
                          s: Strategy[T], prop: proc(x: T),
                          settings: Settings,
                          explicit: Examples[T]): Report[T] =
  ## Thin wrapper that fixes the phase list at `defaultPhases[T]()`.
  ## Behavior identical to the pre-cycle-13 monolithic pipeline.
  runForAllPipelineWithPhases(db, dbEnabled, s, prop, settings,
                              explicit, defaultPhases[T]())

# The explicit-examples list is an `Examples[T]` — a `seq[ref T]`-backed,
# append-only box that never instantiates `seq[T]`'s grow/shrink (hence never
# `reset(T)` / `default(T)`). That keeps a `{.requiresInit.}` element type (or
# any no-valid-default type, e.g. a `range[1..n]` field, or an element reached
# via `oneOf` whose `reset` is strict-effects-tagged `RootEffect` under
# `--threads:on`) bindable through the engine. The boxing is hidden behind
# `Examples`' `seq`-like surface. (See `optbox`; REQUIRESINIT_VARIANT_BINDING.)
proc emptyExamples[T](): Examples[T] = Examples[T]()
  ## The no-examples case for `forAll` / `forAllUsing`.

proc forAll*[T](s: Strategy[T], prop: proc(x: T),
                settings = defaultSettings()): Report[T] =
  ## Check `prop` against values drawn from `s`. Deterministic in
  ## `settings.seed`. When `settings.testId` and `settings.dbPath` are
  ## both set, the reuse phase replays any DB-stored failure first; a
  ## fresh falsification is saved back to the directory-based DB.
  let db = directoryBasedDatabase(settings.dbPath)
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, emptyExamples[T]())

proc forAllUsing*[T](db: ExampleDatabase, s: Strategy[T], prop: proc(x: T),
                     settings = defaultSettings()): Report[T] =
  ## Variant of `forAll` that runs against an explicitly-supplied DB
  ## backend. DB is enabled whenever `settings.testId` is non-empty.
  let dbEnabled = settings.testId.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, emptyExamples[T]())

proc forAllWithExamples*[T](explicit: Examples[T], s: Strategy[T],
                            prop: proc(x: T),
                            settings = defaultSettings()): Report[T] =
  ## Run each value in `explicit` through `prop` before the random phase.
  ## Explicit examples are user-pinned regression seeds — the user said
  ## "this exact input matters," so we don't shrink them (no choice
  ## sequence to shrink) and report `choices: @[]` on failure.
  ##
  ## This `Examples[T]` overload is the core; the `given`/`property` DSL
  ## accumulates into an `Examples[T]` and calls it directly so no `seq[T]`
  ## is instantiated for a no-valid-default element type.
  let db = directoryBasedDatabase(settings.dbPath)
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, explicit)

proc forAllWithExamples*[T](explicit: openArray[T], s: Strategy[T],
                            prop: proc(x: T),
                            settings = defaultSettings()): Report[T] =
  ## Convenience overload that boxes a plain open array of examples. For a
  ## no-valid-default element type (`{.requiresInit.}` variant, etc.), pass
  ## an **array** literal `[a, b]` rather than a `seq` literal `@[a, b]` —
  ## the latter instantiates `seq[T]` at the call site, which the boxing
  ## here can't undo.
  forAllWithExamples(toExamples(explicit), s, prop, settings)


