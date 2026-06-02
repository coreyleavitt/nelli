## Engine pipeline architecture (Option C, #119).
##
## The engine runs as a *pipeline of phases*. Each phase reads / mutates
## a shared `EngineState[T]` and returns a `PhaseAction` telling the
## driver whether to continue. The driver is dumb — it iterates the
## phases in order; phases self-gate on state to decide whether they
## have work to do.
##
## **Why this shape**
##
## `Phase[T].run(state) → PhaseAction` is a uniform, deep interface
## (Ousterhout): each phase hides 80–300 LOC of orchestration behind
## one proc call. Phases are independently testable (synthesize state,
## run phase, assert output) and pluggable (users can splice, replace,
## or inject phases — coverage-guided targeting from #107 will become
## a phase replacing or augmenting `targetedPhase`).
##
## **Type-system-enforced invariants**
##
## `EngineState[T]` decomposes into three sub-objects whose names
## signal their mutability discipline:
##
## - `spec: EngineSpec[T]` — immutable after `initEngineState`. The
##   strategy, property (deadline-wrapped), settings, DB backend,
##   and any explicit examples. Phases read but never mutate.
## - `acc: EngineAccumulators` — running totals that grow monotonically
##   across phases (examples checked, rejections, Pareto front, DB
##   replay counter).
## - `output: EnginePhaseOutput[T]` — phase results that *downstream*
##   phases inspect to decide whether they have work to do. E.g.
##   `shrinkPhase` runs only when `output.rawFalsification.isSome`;
##   `explainPhase` runs only when `output.shrunkChoices.isSome`.
##
## **Termination**
##
## A phase that wants to short-circuit the pipeline sets
## `state.output.finalReport` and returns `pcTerminate`. The driver
## then reads the final report and returns it to the caller. If no
## phase sets `finalReport`, the implicit `finalizePhase` (at the end
## of `defaultPhases`) constructs one from accumulated state.

import std/[options]
import ../strategy, ../choice, ../rng, ../db, ../optbox
import ./types
export types

type
  RawFalsification*[T] = object
    ## A pre-shrink falsification produced by `dbReusePhase`,
    ## `explicitExamplesPhase`, `randomPhase`, or `targetedPhase`.
    ## Consumed by `shrinkPhase`, which produces the
    ## `shrunkChoices`/`shrunkExample`/`shrunkNotes` fields.
    value*: Opt[T]       ## `box(x)` when the strategy produced a value
                         ## before the property raised; empty when the
                         ## strategy itself raised mid-generation
    choices*: seq[ChoiceNode]
    message*: string
    notes*: seq[(string, string)]
    fromPhase*: string   ## "dbReuse" | "explicit" | "random" | "targeted"

  EngineSpec*[T] = object
    ## Immutable after `initEngineState`. Phases read freely.
    s*: Strategy[T]
    prop*: proc(x: T) {.closure.}
      ## Already deadline-wrapped if `settings.deadline > 0`.
    settings*: Settings
      ## Mutable copy at the runner level (e.g., `derandomize` rewrites
      ## `seed`) but immutable from a phase's perspective.
    db*: ExampleDatabase
    dbEnabled*: bool
    explicit*: seq[T]
      ## Populated by `forAllWithExamples`; empty for the plain
      ## `forAll` / `forAllUsing` entry points. `explicitExamplesPhase`
      ## skips itself when empty.

  EngineAccumulators* = object
    ## Mutated by phases. Grows monotonically through the run.
    master*: SplitMix64
    examplesDone*: int
    rejections*: int
    paretoFront*: seq[ParetoEntry]
    refPoint*: ScoreMap
    dbReplays*: int
    dbErrors*: seq[string]

  EnginePhaseOutput*[T] = object
    ## Phase results consumed by downstream phases.
    rawFalsification*: Option[RawFalsification[T]]
    shrunkChoices*: Option[seq[ChoiceNode]]
    shrunkExample*: Opt[T]
    shrunkNotes*: seq[(string, string)]
    isFlaky*: bool
      ## Set by `shrinkPhase` (pre-shrink flaky retry pass OR
      ## post-shrink replay non-reproduction). Downstream phases
      ## skip explain when flaky.
    necessity*: seq[Necessity]
    finalReport*: Option[Report[T]]
      ## When `some`, the driver returns it to the caller. Set by
      ## any phase that wants to short-circuit, or by `finalizePhase`
      ## at the implicit end of the default pipeline.

  EngineState*[T] = object
    spec*: EngineSpec[T]
    acc*: EngineAccumulators
    output*: EnginePhaseOutput[T]

  PhaseAction* = enum
    pcContinue,   ## advance to next phase
    pcTerminate   ## stop pipeline; driver reads `state.output.finalReport`

  Phase*[T] = object
    name*: string   ## for telemetry / debug; appears in any phaseTrace
                    ## diagnostic future work might add
    run*: proc(state: var EngineState[T]): PhaseAction {.nimcall.}
      ## `nimcall` matches plain top-level procs in engine.nim. The
      ## gcsafe-ness is enforced *at the phase definition site* (each
      ## phase proc carries `{.gcsafe.}` where applicable) rather than
      ## here, because some legitimate phases need to acquire the
      ## frame-stack threadvar in ways Nim's effect inference rejects.

proc initEngineState*[T](spec: EngineSpec[T]): EngineState[T] =
  ## Construct a fresh state from an immutable spec. Accumulators
  ## start zero; output is empty (no falsification, no shrink, no
  ## final report). Master RNG is seeded from `spec.settings.seed`.
  result.spec = spec
  result.acc.master = initSplitMix64(spec.settings.seed)

proc runPipeline*[T](state: var EngineState[T],
                     phases: openArray[Phase[T]]): Report[T] =
  ## The pipeline driver. Iterates phases in order; each phase decides
  ## whether to continue or terminate. The driver doesn't know which
  ## phase produces the final report — any phase can set
  ## `state.output.finalReport` and return `pcTerminate`, or the
  ## implicit `finalizePhase` at the end constructs one from state.
  ##
  ## If the pipeline ends without any phase setting `finalReport`,
  ## that's a programming error (an incomplete default pipeline);
  ## raise `Defect` with a diagnostic.
  for phase in phases:
    let action = phase.run(state)
    if action == pcTerminate: break
  if state.output.finalReport.isNone:
    raise newException(Defect,
      "engine pipeline ended without a final report — " &
      "missing a finalizePhase or a phase that sets state.output.finalReport")
  state.output.finalReport.get
