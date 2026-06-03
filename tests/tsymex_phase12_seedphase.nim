## Phase 12 cycle 14 — `symexSeedPhase[T]`.
##
## The phase replays a list of choice sequences (each a symex-
## derived witness) against the live strategy + property. Each seed
## is processed through `evalReplay`:
##
##   * ekFalsified → set `rawFalsification` with the replayed choice
##     seq; carries forward to `shrinkPhase` for minimisation.
##   * ekRejected  → `Overrun` (shape mismatch) or `Rejection`
##     internally caught by `evalReplay`; deposit one
##     `SymexFinding(status: sfNotApplicable, …)` and continue.
##   * ekPassed    → continue silently (the seed didn't falsify
##     under the current property — a normal outcome on a witness
##     that was constructed for a different invariant).
##
## Self-gates on `state.output.rawFalsification.isSome` so the
## phase runs only when no upstream source phase has already
## produced a falsification — matching the contract of every other
## source phase in `defaultPhases`.
import std/[unittest, options]
import proptest
import proptest/choice
import proptest/int128
import proptest/engine
import proptest/engine/phases
import proptest/engine/pipeline
import proptest/engine/types

# A custom three-phase pipeline that exercises symexSeedPhase
# end-to-end without any random or DB-reuse interference.
proc seedPipeline(seeds: seq[seq[ChoiceNode]]): seq[Phase[int]] =
  @[
    Phase[int](name: "symexSeed", run: symexSeedPhase[int](seeds).run),
    Phase[int](name: "shrink",    run: shrinkPhase[int]),
    Phase[int](name: "finalize",  run: finalizePhase[int]),
  ]

suite "symex Phase 12 cycle 14 — symexSeedPhase":
  test "falsifying seed produces otFalsified through shrink+finalize":
    discard consumeSymexFindings()
    # `integers(0, 1000)` draws one ckInteger(value, 0, 1000, 0).
    # A seed of `@[integerChoice(200, 0, 1000, 0)]` replays as 200.
    # The property fails on x ≥ 100, so 200 falsifies it.
    let s = integers(0, 1000)
    proc prop(x: int) =
      doAssert x < 100
    let seed = @[integerChoice(200'i64, 0'i64, 1000'i64, 0'i64)]
    let report = runForAllPipelineWithPhases(
      inMemoryDatabase(), dbEnabled = false,
      s, prop, defaultSettings(), toExamples[int](@[]),
      seedPipeline(@[seed]))
    check report.outcome == otFalsified

  test "shrinker runs on the symex-derived falsification":
    # The seed forces x = 200. The property fails for all x >= 100;
    # the shrinker must minimise the int down to 100 (the integer
    # boundary). Observable via `report.counterexample`.
    discard consumeSymexFindings()
    let s = integers(0, 1000)
    proc prop(x: int) =
      doAssert x < 100
    let seed = @[integerChoice(200'i64, 0'i64, 1000'i64, 0'i64)]
    let report = runForAllPipelineWithPhases(
      inMemoryDatabase(), dbEnabled = false,
      s, prop, defaultSettings(), toExamples[int](@[]),
      seedPipeline(@[seed]))
    check report.outcome == otFalsified
    # The shrinker drove the failing input down from 200 to the
    # boundary value 100. Observable proof that shrinkPhase ran on
    # the symex witness — `explicit` phase would not have shrunk.
    check report.counterexample.isSome
    check report.counterexample.get == 100

  test "shape-mismatched seed deposits sfNotApplicable, no falsification":
    # Strategy expects ONE ckInteger; seed has ZERO. evalReplay
    # raises Overrun → ekRejected → sfNotApplicable deposit. The
    # report passes (no falsification surfaced from a malformed
    # seed). The deposit is observable via consumeSymexFindings.
    discard consumeSymexFindings()
    let s = integers(0, 1000)
    proc prop(x: int) =
      doAssert x < 100
    let emptySeed: seq[ChoiceNode] = @[]
    let report = runForAllPipelineWithPhases(
      inMemoryDatabase(), dbEnabled = false,
      s, prop, defaultSettings(), toExamples[int](@[]),
      seedPipeline(@[emptySeed]))
    check report.outcome == otPassed
    let drained = consumeSymexFindings()
    check drained.len == 1
    check drained[0].status == sfNotApplicable
