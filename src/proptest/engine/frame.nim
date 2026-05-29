## Per-example state for the engine.
##
## Each `forAll` run owns one `EngineFrame` pushed onto `engineStack`
## (thread-local). The frame accumulates:
##
## - **Per-example state** (cleared on each prop call): `notes`, `scores`.
## - **Cross-example state** (lives the run): `eventsCategorical`, `eventsNumeric`.
##
## Stacking via `engineStack` is what makes nested `forAll` calls compose
## (#91): the inner run gets a fresh frame, runs its own examples, pops;
## the outer's frame is restored intact. Without the stack, the inner
## run would clobber the outer's `note()` / `event()` / `target()` state.
##
## This module is the foundation of the engine — `eval.nim` and every
## phase imports it. No dependencies on engine internals (only `types.nim`
## for `ScoreMap` / `EventStats` / `NumericSummary`).

import std/[tables, algorithm]
import ./types

type EngineFrame* = object
  notes*: seq[(string, string)]                ## per-example
  scores*: ScoreMap                            ## per-example
  eventsCategorical*: Table[string, int]       ## cross-example
  eventsNumeric*: Table[string, seq[float]]    ## cross-example

var engineStack* {.threadvar.}: seq[EngineFrame]

template withEngineFrame*(body: untyped) =
  ## Push a fresh frame for `body`; guarantees pop on any exit path.
  engineStack.add EngineFrame()
  try: body
  finally: discard engineStack.pop()

proc currentFrame*: var EngineFrame {.inline.} =
  ## Top of the per-thread engine stack. Required to be non-empty.
  if engineStack.len == 0:
    raise newException(ValueError,
      "note/target/event called outside any forAll — there's no example to attach to")
  engineStack[^1]

# --- user-facing accumulator APIs --------------------------------------------

proc event*(label: string) =
  ## Tag the current example with a categorical event. Counts persist
  ## across examples and surface in `Report.events.categorical`.
  if currentFrame().eventsNumeric.hasKey(label):
    raise newException(ValueError,
      "event label '" & label & "' was already used for a numeric event")
  inc currentFrame().eventsCategorical.mgetOrPut(label, 0)

proc event*[T: SomeNumber](label: string, value: T) =
  ## Tag the current example with a numeric sample.
  if currentFrame().eventsCategorical.hasKey(label):
    raise newException(ValueError,
      "event label '" & label & "' was already used for a categorical event")
  currentFrame().eventsNumeric.mgetOrPut(label, @[]).add float(value)

proc note*[T](label: string, value: T) =
  ## Attach `(label, $value)` to the current example's debug context.
  currentFrame().notes.add (label, $value)

const
  targetPosSentinel* = 1e300
    ## Finite stand-in for `+Inf` in `target()`. Substituting a sentinel
    ## preserves user intent while keeping the augmented-Tchebycheff
    ## aggregator finite.
  targetNegSentinel* = -1e300

proc target*(score: float, label: string = "") =
  ## Declare a numeric `score` for an objective named `label` ("" is the
  ## default). Non-finite scores are clamped to finite sentinels so the
  ## SA aggregator stays well-defined.
  if score != score:
    stderr.writeLine "proptest: target(\"" & label &
                     "\") received NaN; treating as " & $targetNegSentinel
    currentFrame().scores[label] = targetNegSentinel
  elif score == Inf:
    stderr.writeLine "proptest: target(\"" & label &
                     "\") received +Inf; clamping to " & $targetPosSentinel
    currentFrame().scores[label] = targetPosSentinel
  elif score == NegInf:
    stderr.writeLine "proptest: target(\"" & label &
                     "\") received -Inf; clamping to " & $targetNegSentinel
    currentFrame().scores[label] = targetNegSentinel
  else:
    currentFrame().scores[label] = score

# --- snapshot helpers (used by report construction) --------------------------

proc quantile*(sorted: seq[float], q: float): float =
  ## Linear-interpolated quantile of a pre-sorted sample.
  if sorted.len == 0: return 0.0
  if sorted.len == 1: return sorted[0]
  let pos = q * float(sorted.len - 1)
  let lo = int(pos)
  let frac = pos - float(lo)
  if lo + 1 < sorted.len:
    sorted[lo] * (1.0 - frac) + sorted[lo + 1] * frac
  else:
    sorted[^1]

proc snapshotEvents*(): EventStats =
  ## Build `EventStats` from the cross-example accumulators in the
  ## current frame. Sorts each numeric sample once for quantile calc.
  let f = currentFrame()
  for k, v in f.eventsCategorical: result.categorical[k] = v
  for k, samples in f.eventsNumeric:
    var s = samples
    s.sort do (a, b: float) -> int: cmp(a, b)
    var sum = 0.0
    for x in s: sum += x
    result.numeric[k] = NumericSummary(
      count: s.len, mn: s[0], mx: s[^1], mean: sum / float(s.len),
      p50: quantile(s, 0.5), p90: quantile(s, 0.9), p99: quantile(s, 0.99))
