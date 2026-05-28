import std/[unittest, options]
import proptest
import proptest/engine/pipeline
import proptest/[choice, datasource, db]

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
      explicit: @[])
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
      explicit: @[])
    var state = initEngineState(spec)
    let phases = @[
      Phase[int](name: "count", run: countingPhase[int]),
      Phase[int](name: "read",  run: readingPhase[int]),
    ]
    let report = runPipeline(state, phases)
    check report.outcome == otPassed
    check report.examples == 7   # second phase read what first wrote
