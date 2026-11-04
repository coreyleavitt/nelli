## Per-example state for the engine.
##
## Each `forAll` run owns one `EngineFrame` pushed onto `engineStack`
## (thread-local). The frame accumulates:
##
## - **Per-example state** (cleared on each prop call): `notes`, `scores`.
## - **Cross-example state** (lives the run): `eventsCategorical`, `eventsNumeric`,
##   `symexFindings`.
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
import ../choice
import ./types

type EngineFrame* = object
  notes*: seq[(string, string)]                ## per-example
  scores*: ScoreMap                            ## per-example
  eventsCategorical*: Table[string, int]       ## cross-example
  eventsNumeric*: Table[string, seq[float]]    ## cross-example
  symexFindings*: seq[SymexFinding]            ## cross-example
    ## Review R2 (DD3). The findings `assertCoveredBy` made inside this run's
    ## property (`recordSymexFinding`), on every example. The engine moves
    ## them onto the run's `Report.symexFindings` when the run ends, passed or
    ## failed. A fresh frame per run: nothing carries over. Review R3 (E2):
    ## one entry per call site and target, in the order each was first made.
  symexFindingAt: Table[string, int]
    ## Review R3 (E2). Each entry's key (`findingKey`) to its index in
    ## `symexFindings`.
  symexFindingKeys: seq[string]
    ## The key of each entry, by index, so a closing frame hands its parent
    ## the same keys (`popEngineFrame`).

var engineStack* {.threadvar.}: seq[EngineFrame]

proc record(fr: var EngineFrame; key: string; f: SymexFinding) =
  ## Review R3 (E2). The entry for `key` becomes `f`: the latest finding of
  ## that call site for that target replaces the one before, in place.
  let at = fr.symexFindingAt.getOrDefault(key, -1)
  if at >= 0:
    fr.symexFindings[at] = f
  else:
    fr.symexFindingAt[key] = fr.symexFindings.len
    fr.symexFindingKeys.add key
    fr.symexFindings.add f

proc popEngineFrame*() =
  ## Pops the top frame. Review R3 (E3): its symex findings also reach the
  ## frame it was opened in, under the same keys, so a nested `forAll`'s
  ## findings are on the enclosing run's report whatever its caller does with
  ## the inner one (`laws` keeps only the outcome).
  var fr = engineStack.pop()
  if engineStack.len > 0:
    for i, f in fr.symexFindings:
      record(engineStack[^1], fr.symexFindingKeys[i], f)

template withEngineFrame*(body: untyped) =
  ## Push a fresh frame for `body`; guarantees pop on any exit path.
  engineStack.add EngineFrame()
  try: body
  finally: popEngineFrame()

proc currentFrame*: var EngineFrame {.inline.} =
  ## Top of the per-thread engine stack. Required to be non-empty.
  if engineStack.len == 0:
    raise newException(ValueError,
      "note/target/event called outside any forAll — there's no example to attach to")
  engineStack[^1]

func findingKey(site: string; f: SymexFinding): string =
  ## Review R3 (E2). What makes two findings one entry: the call site that
  ## made them, and the target (one multi-target call makes one per target).
  $site.len & ':' & site & f.targetDesc

proc recordSymexFinding*(site: string; f: SymexFinding) =
  ## Review R2 (DD3), R3 (E2, E3). Records a finding `assertCoveredBy` made at
  ## `site` (its call site, `file(line, col)`) on the running property's
  ## frame. A call site keeps one entry per target, the latest: the next
  ## example, a shrink or a cache hit on the same call replaces it, and two
  ## call sites that find the same thing are two entries. Constant time.
  ##
  ## Outside any engine frame (no `forAll` is running on this thread: a test
  ## body, a `fuzz` or concolic harness, a thread the property started) it
  ## records nothing. There the finding's only channel is the call itself:
  ## `assertCoveredBy` returns it, and its `SymexCoverageDefect` carries it.
  if engineStack.len == 0: return
  record(engineStack[^1], findingKey(site, f), f)

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

const reservedLabelPrefix* = "__"
  ## Engine-internal label namespace. `target()` rejects user-supplied
  ## labels starting with `__` so engine-injected scores (e.g.
  ## `__coverage__` for #107 coverage-guided forAll) can't be silently
  ## overwritten from inside a property. The engine sets reserved-label
  ## scores by writing `currentFrame().scores[label]` directly, bypassing
  ## this validation.

proc target*(score: float, label: string = "") =
  ## Declare a numeric `score` for an objective named `label` ("" is the
  ## default). Non-finite scores are clamped to finite sentinels so the
  ## SA aggregator stays well-defined. Raises `ValueError` when `label`
  ## starts with `__` — that prefix is reserved for engine-injected
  ## objectives (see `reservedLabelPrefix`).
  if label.len >= 2 and label[0] == '_' and label[1] == '_':
    raise newException(ValueError,
      "target() label '" & label & "' uses reserved prefix '__'; " &
      "the '__' namespace is owned by the engine (e.g. __coverage__)")
  if score != score:
    stderr.writeLine "nelli: target(\"" & label &
                     "\") received NaN; treating as " & $targetNegSentinel
    currentFrame().scores[label] = targetNegSentinel
  elif score == Inf:
    stderr.writeLine "nelli: target(\"" & label &
                     "\") received +Inf; clamping to " & $targetPosSentinel
    currentFrame().scores[label] = targetPosSentinel
  elif score == NegInf:
    stderr.writeLine "nelli: target(\"" & label &
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
