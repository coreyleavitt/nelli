import std/[unittest, options, strutils]
import nelli
import nelli/engine/pipeline
import nelli/[choice, datasource, db]

# Pipeline driver smoke test: a minimal pipeline with a single
# `finalize`-style phase produces a valid Report through the
# `runPipeline` driver. This proves the type scaffolding +
# state propagation work end-to-end before we start migrating
# real phases (random, targeted, shrink, etc.) into the pipeline.

suite "engine pipeline: scaffolding":
  test "single-phase pipeline that sets finalReport returns it":
    # A trivial phase that produces an otPassed Report and terminates.
    proc passingPhase[T](state: var EngineState[T]): PhaseAction =
      state.output.finalReport = some(Report[T](
        outcome: otPassed,
        examples: 42,
        seed: state.spec.settings.seed,
        printEvents: state.spec.settings.printEvents))
      result = pcTerminate

    let s = integers(0, 100)
    var settings = defaultSettings()
    settings.seed = 0xdeadbeef'u64
    let spec = EngineSpec[int](
      s: s, prop: proc(x: int) = discard,
      settings: settings,
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    let report = runPipeline(state, @[Phase[int](
      name: "test-only", run: passingPhase[int])])
    check report.outcome == otPassed
    check report.examples == 42
    check report.seed == 0xdeadbeef'u64

  test "two-phase pipeline: first observes, second terminates":
    # Verify phases run in order and the driver continues on pcContinue.
    proc countingPhase[T](state: var EngineState[T]): PhaseAction =
      state.acc.examplesDone = 7
      result = pcContinue

    proc readingPhase[T](state: var EngineState[T]): PhaseAction =
      state.output.finalReport = some(Report[T](
        outcome: otPassed, examples: state.acc.examplesDone,
        seed: state.spec.settings.seed,
        printEvents: state.spec.settings.printEvents))
      result = pcTerminate

    let s = integers(0, 100)
    let spec = EngineSpec[int](
      s: s, prop: proc(x: int) = discard,
      settings: defaultSettings(),
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    let phases = @[
      Phase[int](name: "count", run: countingPhase[int]),
      Phase[int](name: "read",  run: readingPhase[int]),
    ]
    let report = runPipeline(state, phases)
    check report.outcome == otPassed
    check report.examples == 7   # second phase read what first wrote

suite "finalizePhase: terminal Report construction":
  test "produces otPassed from accumulated state when no falsification":
    # Real phase under test. finalizePhase consults the accumulators
    # (examplesDone, paretoFront, dbReplays, dbErrors) and snapshots
    # the current EngineFrame to populate Report.events.
    let spec = EngineSpec[int](
      s: integers(0, 100), prop: proc(x: int) = discard,
      settings: defaultSettings(),
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    state.acc.examplesDone = 42
    state.acc.dbReplays = 3
    state.acc.dbErrors = @["fake db error for test"]
    # We need a frame on the engineStack for snapshotEvents() to work.
    # (Real forAll pushes one via withEngineFrame; we mirror that.)
    proc runWithFrame(): Report[int] =
      # The pipeline's finalizePhase calls snapshotEvents() which
      # consults currentFrame(). We use forAll to push a frame for
      # us — its prop body runs runPipeline.
      var result: Report[int]
      discard forAll(integers(0, 0),
                    proc(x: int) =
                      result = runPipeline(state, @[
                        Phase[int](name: "finalize", run: finalizePhase[int])
                      ]),
                    Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                             maxShrinks: 1, maxRejections: 1))
      result
    let r = runWithFrame()
    check r.outcome == otPassed
    check r.examples == 42
    check r.dbReplays == 3
    check r.dbErrors == @["fake db error for test"]

  test "finalizePhase is a no-op when an upstream phase set finalReport":
    # finalizePhase yields control if upstream already finalized — the
    # otFalsified case (when shrinkPhase produces the report) flows
    # through finalize untouched.
    proc producer[T](state: var EngineState[T]): PhaseAction =
      state.output.finalReport = some(Report[T](
        outcome: otExhausted, examples: 99,
        seed: state.spec.settings.seed,
        printEvents: state.spec.settings.printEvents))
      pcContinue
    let spec = EngineSpec[int](
      s: integers(0, 100), prop: proc(x: int) = discard,
      settings: defaultSettings(),
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    proc runWithFrame(): Report[int] =
      var result: Report[int]
      discard forAll(integers(0, 0),
                    proc(x: int) =
                      result = runPipeline(state, @[
                        Phase[int](name: "producer", run: producer[int]),
                        Phase[int](name: "finalize", run: finalizePhase[int])
                      ]),
                    Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                             maxShrinks: 1, maxRejections: 1))
      result
    let r = runWithFrame()
    # Producer's report survived — finalize was a no-op.
    check r.outcome == otExhausted
    check r.examples == 99

suite "full pipeline: random + shrink + explain + finalize":
  test "falsifying property runs through the full pipeline":
    # End-to-end PBT through the new pipeline architecture. The
    # property `x < 50` over integers(0, 100) falsifies; the pipeline
    # should produce a Report equivalent to what legacy `forAll`
    # would produce.
    let spec = EngineSpec[int](
      s: integers(0, 100),
      prop: proc(x: int) = (ensure x < 50),
      settings: Settings(maxExamples: 200, seed: 1, flakyRetries: 0,
                         maxShrinks: 200, maxRejections: 200,
                         printEvents: true),
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    proc runWithFrame(): Report[int] =
      var result: Report[int]
      discard forAll(integers(0, 0),
                    proc(x: int) =
                      result = runPipeline(state, @[
                        Phase[int](name: "random", run: randomPhase[int]),
                        Phase[int](name: "shrink", run: shrinkPhase[int]),
                        Phase[int](name: "explain", run: explainPhase[int]),
                        Phase[int](name: "finalize", run: finalizePhase[int])
                      ]),
                    Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                             maxShrinks: 1, maxRejections: 1))
      result
    let r = runWithFrame()
    check r.outcome == otFalsified
    # Shrunk to the smallest x that still falsifies: x = 50.
    check r.counterexample.isSome
    check r.counterexample.get == 50
    # Explain populated necessity for at least the integer choice.
    check r.necessity.len == r.choices.len
    check r.necessity.len > 0

  test "passing property runs through the pipeline as otPassed":
    let spec = EngineSpec[int](
      s: integers(0, 100),
      prop: proc(x: int) = (ensure x >= 0),
      settings: Settings(maxExamples: 50, seed: 1, flakyRetries: 0,
                         maxShrinks: 50, maxRejections: 100,
                         printEvents: true),
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    proc runWithFrame(): Report[int] =
      var result: Report[int]
      discard forAll(integers(0, 0),
                    proc(x: int) =
                      result = runPipeline(state, @[
                        Phase[int](name: "random", run: randomPhase[int]),
                        Phase[int](name: "shrink", run: shrinkPhase[int]),
                        Phase[int](name: "explain", run: explainPhase[int]),
                        Phase[int](name: "finalize", run: finalizePhase[int])
                      ]),
                    Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                             maxShrinks: 1, maxRejections: 1))
      result
    let r = runWithFrame()
    check r.outcome == otPassed
    check r.examples == 50

suite "explicitExamplesPhase":
  test "failing explicit example short-circuits the pipeline":
    let spec = EngineSpec[int](
      s: integers(0, 100),
      prop: proc(x: int) = (ensure x >= 0),
      settings: Settings(maxExamples: 100, seed: 1, flakyRetries: 0,
                         maxShrinks: 50, maxRejections: 100,
                         printEvents: true),
      db: inMemoryDatabase(), dbEnabled: false,
      explicit: toExamples([-1, 5, 10]))    # -1 fails the ensure
    var state = initEngineState(spec)
    proc runWithFrame(): Report[int] =
      var result: Report[int]
      discard forAll(integers(0, 0),
                    proc(x: int) =
                      result = runPipeline(state, defaultPhases[int]()),
                    Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                             maxShrinks: 1, maxRejections: 1))
      result
    let r = runWithFrame()
    check r.outcome == otFalsified
    check r.counterexample.get == -1
    check r.choices.len == 0     # explicit doesn't shrink
    check "explicit example" in r.message

suite "dbReusePhase":
  test "replays a stored failing entry and feeds it to shrink":
    # Seed a DB with a known-failing entry; verify dbReusePhase
    # replays it and the rest of the pipeline shrinks it.
    let db = inMemoryDatabase()
    # Manually craft a falsifying choice sequence: int x = 73 in range [0, 100]
    let failingChoices = @[integerChoice(73, 0, 100, 0)]
    db.save("test-dbreuse", failingChoices)
    let spec = EngineSpec[int](
      s: integers(0, 100),
      prop: proc(x: int) = (ensure x < 50),  # 73 fails
      settings: Settings(maxExamples: 100, seed: 1, flakyRetries: 0,
                         maxShrinks: 100, maxRejections: 100,
                         testId: "test-dbreuse",
                         printEvents: true),
      db: db, dbEnabled: true,
      explicit: Examples[int]())
    var state = initEngineState(spec)
    proc runWithFrame(): Report[int] =
      var result: Report[int]
      discard forAll(integers(0, 0),
                    proc(x: int) =
                      result = runPipeline(state, defaultPhases[int]()),
                    Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                             maxShrinks: 1, maxRejections: 1))
      result
    let r = runWithFrame()
    check r.outcome == otFalsified
    # dbReusePhase counts the replay
    check r.dbReplays >= 1
    # And shrink minimized to 50 (the smallest failing value)
    check r.counterexample.get == 50
    check "from DB" in r.message
