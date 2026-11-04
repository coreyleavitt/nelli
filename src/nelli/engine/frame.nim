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
  symexFindings*: OrderedTable[string, SymexFinding]  ## cross-example
    ## Review R2 (DD3). The findings `assertCoveredBy` made inside this run's
    ## property (`recordSymexFinding`), on every example. The engine moves
    ## them onto the run's `Report.symexFindings` when the run ends, passed or
    ## failed. A fresh frame per run: nothing carries over. Review R3 (E2),
    ## R4 (U1): one entry per `findingKey` (the `fn`, its call site and the
    ## target), in the order each was first made, holding the most severe
    ## finding made under that key (`severity`).

var engineStack* {.threadvar.}: seq[EngineFrame]

type Severity = enum
  ## Review R4 (U1), R5 (D3a), R6 (N2). How much a report needs to show a
  ## finding, weakest first. Each meaning has its own rank, so a tie never
  ## lets a later, weaker finding replace an earlier, stronger one (equal
  ## ranks keep the latest):
  ##   skAudit             `sfNotApplicable` / `sfReplayMiss`: not verdicts,
  ##                       only a record that symex was skipped or missed;
  ##   skTrustedCovered    a trusted claim the test covered;
  ##   skUnconfirmed       a covered claim no trust backs;
  ##   skUnknown           decided nothing (`sfUnknown`, accepted or not);
  ##   skUnconfirmedMiss   an unconfirmed claim the run did not reach (kept
  ##                       when `acceptUnknown` downgrades it, so it carries
  ##                       no failure);
  ##   skCoverageFailure   a TRUSTED claim the test failed to cover: the one
  ##                       finding no other may displace.
  skAudit, skTrustedCovered, skUnconfirmed, skUnknown, skUnconfirmedMiss,
  skCoverageFailure

func severity(f: SymexFinding): Severity =
  case f.status
  of sfNotApplicable, sfReplayMiss: skAudit
  of sfUnknown: skUnknown
  of sfSat, sfUnsat, sfRaised:
    if not f.covered:
      if trusted(f): skCoverageFailure else: skUnconfirmedMiss
    elif not trusted(f): skUnconfirmed
    else: skTrustedCovered

proc record(fr: var EngineFrame; key: string; f: SymexFinding) =
  ## Review R3 (E2), R4 (U1). The entry for `key` becomes `f` unless the
  ## entry it holds is more severe: a later passing example, shrink candidate
  ## or cache hit must not hide an earlier failure. Equal severity keeps the
  ## latest. The entry keeps its place in the order.
  if key in fr.symexFindings and
     severity(fr.symexFindings[key]) > severity(f):
    return
  fr.symexFindings[key] = f

proc popEngineFrame*() =
  ## Pops the top frame. Review R3 (E3): its symex findings also reach the
  ## frame it was opened in, under the same keys, so a nested `forAll`'s
  ## findings are on the enclosing run's report whatever its caller does with
  ## the inner one (`laws` keeps only the outcome).
  var fr = engineStack.pop()
  if engineStack.len > 0:
    for k, f in fr.symexFindings:
      record(engineStack[^1], k, f)

proc pushEngineFrame*() =
  ## Opens a fresh frame. Review R4 (X3): the one way a frame is opened;
  ## pair it with `popEngineFrame` on every exit path (`withEngineFrame`).
  engineStack.add EngineFrame()

template withEngineFrame*(body: untyped) =
  ## Push a fresh frame for `body`; guarantees pop on any exit path.
  pushEngineFrame()
  try: body
  finally: popEngineFrame()

proc currentFrame*: var EngineFrame {.inline.} =
  ## Top of the per-thread engine stack. Required to be non-empty.
  if engineStack.len == 0:
    raise newException(ValueError,
      "note/target/event called outside any forAll — there's no example to attach to")
  engineStack[^1]

var droppedFindings {.threadvar.}: int

proc resetDroppedSymexFindings*() =
  ## Review R5 (3c). Zeroes this thread's drop count (`droppedSymexFindings`).
  ## The count is per thread and only ever grows, so a test that reads it
  ## resets it first, or compares against a reading taken before.
  droppedFindings = 0

proc droppedSymexFindings*(): int =
  ## Review R4 (X8). How many findings `recordSymexFinding` dropped on this
  ## thread because no engine frame was open. A nonzero count in a test that
  ## expected its finding on a `Report` means the call ran outside `forAll`.
  droppedFindings

type FindingOrigin* = object
  ## Review R5 (3b). Where a finding came from: the call site that made it
  ## (`file(line, col)`) and the identity of the `fn` it checked. Two strings
  ## that are easy to swap as arguments, so they travel as named fields.
  site*: string
  fnId*: string

func findingKey(o: FindingOrigin; f: SymexFinding): string =
  ## Review R3 (E2), R4 (U1). What makes two findings one entry: the `fn`
  ## under test, the call site that made them (a template or helper shares
  ## one among several `fn`s, a generic one among its instantiations) and the
  ## target (one multi-target call makes one per target).
  $o.fnId.len & ':' & o.fnId & $o.site.len & ':' & o.site & f.targetDesc

proc recordSymexFinding*(origin: FindingOrigin; f: SymexFinding) =
  ## Review R2 (DD3), R3 (E2, E3), R4 (U1, X8). Records a finding
  ## `assertCoveredBy` made at `origin.site` (its call site, `file(line, col)`) on
  ## `origin.fnId` (the identity of the `fn` it checked) on the running property's
  ## frame. One entry per fn, site and target; it holds the most severe
  ## finding made under that key, the latest among equals, so a failure on one
  ## example is not overwritten by a later pass. Constant time.
  ##
  ## Outside any engine frame (no `forAll` is running on this thread: a test
  ## body, a `fuzz` or concolic harness, a thread the property started) it
  ## records nothing, and counts the drop (`droppedSymexFindings`). There the
  ## finding's only channel is the call itself: `assertCoveredBy` returns it,
  ## and its `SymexCoverageDefect` carries it.
  if engineStack.len == 0:
    inc droppedFindings
    return
  record(engineStack[^1], findingKey(origin, f), f)

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
