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
import ../choice

type
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
    coverageGuided*: bool
      ## When true, the engine sets `setCoverageMode(cmRecording)` for
      ## the run and wraps every property call so the per-example
      ## coverage delta is recorded under the reserved label
      ## `__coverage__`. The existing targeted phase then treats coverage
      ## as just-another-Pareto-objective alongside any user `target()`
      ## scores. #107.

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
    counterexample*: Option[T]
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

func defaultSettings*(): Settings =
  Settings(maxExamples: 100, maxRejections: 1000,
           seed: 0x1234567890abcdef'u64, flakyRetries: 5,
           maxShrinks: 500, useSA: true, targetedSAIters: 200,
           printEvents: true)
