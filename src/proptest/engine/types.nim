## Shared type definitions for the engine and its pipeline phases.
##
## Extracted into its own module so `engine/pipeline.nim` and the
## phase modules can reference `Settings`, `Report[T]`, etc. without
## creating a circular dependency on `engine.nim` itself.
##
## Once the pipeline migration is complete (#119), `engine.nim`
## becomes a thin shim that re-exports these types alongside the
## pipeline driver and phase implementations.

import std/[options, tables, times]
import ../choice, ../datasource/distribution, ../optbox
export distribution, optbox

type
  SymexFindingStatus* = enum
    sfSat       ## a witness was found
    sfUnsat     ## target proved unreachable
    sfUnknown   ## solver gave up

  SymexFinding* = object
    ## Symex-derived evidence the engine carries through to the
    ## terminal report. `targetDesc` is a stringified rendering of
    ## the symex target (e.g. `label("magic")`,
    ## `assertion-violation`, `index-error`) — kept as a string at
    ## this layer so engine/types stays free of the smt/types
    ## dependency. `witnessChoices` is the witness linearised via
    ## `renderAsChoices` so the existing example-DB and regression-
    ## seed format can carry it. `z3Version` tags the entry for
    ## cross-version invalidation. Phase 7.
    targetDesc*:     string
    status*:         SymexFindingStatus
    covered*:        bool
    witnessChoices*: seq[ChoiceNode]
    z3Version*:      string

  FalsifiedError* = object of CatchableError
    ## Raised by `ensure` when a property is violated.

  DeadlineExceeded* = object of FalsifiedError
    ## A property invocation exceeded `Settings.deadline`. Subclass of
    ## `FalsifiedError` so it flows through the same falsification +
    ## shrinking machinery; the message carries the elapsed time.

  Settings* = object
    maxExamples*: int
    maxRejections*: int
    seed*: uint64
    testId*: string
    dbPath*: string
    flakyRetries*: int
    maxShrinks*: int
    useSA*: bool
    targetedSAIters*: int
    derandomize*: bool
    deadline*: Duration
    printEvents*: bool
    strictDb*: bool
    autoLabels*: bool
      ## When true (the default once the engine constructs Settings via
      ## `defaultSettings()`), the engine installs a sink for built-in
      ## strategy distribution labels (#108). Each combinator (`integers`,
      ## `lists`, `oneOf`, …) emits one categorical event per draw
      ## describing what it produced; the labels appear in
      ## `Report.events.categorical` under the reserved `auto.` prefix.
    coverageGuided*: bool
      ## When true, the engine sets `setCoverageMode(cmRecording)` for
      ## the run and wraps every property call so the per-example
      ## coverage delta is recorded under the reserved label
      ## `__coverage__`. The existing targeted phase then treats coverage
      ## as just-another-Pareto-objective alongside any user `target()`
      ## scores. #107.
    integerBias*: IntegerBiasConfig
      ## Distribution bias policy for `drawInteger` (#103). `randomPhase`
      ## copies this onto the per-example DataSource so tests for
      ## bias-sensitive code (heavy arithmetic, parser fuzzing) can dial
      ## boundary injection up or down. Defaults to `defaultIntegerBias`
      ## (30/30/40 with 50% shrinkTowards) via `defaultSettings()`.

  Outcome* = enum
    otPassed, otFalsified, otExhausted, otFlaky

  Necessity* = enum
    nUnknown, nNecessary, nFree

  ScoreMap* = Table[string, float]

  ParetoEntry* = object
    scores*: ScoreMap
    choices*: seq[ChoiceNode]

  NumericSummary* = object
    count*: int
    mn*, mx*, mean*, p50*, p90*, p99*: float

  EventStats* = object
    categorical*: Table[string, int]
    numeric*: Table[string, NumericSummary]

  Report*[T] = object
    outcome*: Outcome
    examples*: int
    counterexample*: Opt[T]
      ## `box(x)` for the falsifying value; empty when the property passed
      ## or the strategy raised before producing a value. `Opt` (not
      ## `std/options.Option`) so a `{.requiresInit.}` element type with no
      ## valid default can still be reported. See `optbox`.
    choices*: seq[ChoiceNode]
    message*: string
    seed*: uint64
    paretoFront*: seq[ParetoEntry]
    dbReplays*: int
    notes*: seq[(string, string)]
    events*: EventStats
    necessity*: seq[Necessity]
    dbErrors*: seq[string]
    printEvents*: bool
    displayed*: string
    coverageHits*: int
      ## Cumulative distinct coverage edges discovered across the whole
      ## run (union of per-example bitmaps). `0` when
      ## `Settings.coverageGuided` was off. #107.
    symexFindings*: seq[SymexFinding]
      ## Symex-derived evidence accumulated during the run. Populated
      ## by `assertCoveredBy` calls made inside the property (via the
      ## thread-local sink in `proptest/symex`) plus any
      ## `withSymexSeeds`-injected seeds. Empty when symex wasn't
      ## used. Phase 7.

func defaultSettings*(): Settings =
  Settings(maxExamples: 100, maxRejections: 1000,
           seed: 0x1234567890abcdef'u64, flakyRetries: 5,
           maxShrinks: 500, useSA: true, targetedSAIters: 200,
           printEvents: true, autoLabels: true,
           integerBias: defaultIntegerBias)
