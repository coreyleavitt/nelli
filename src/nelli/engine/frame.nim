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

import std/[tables, algorithm, atomics]
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
  claimOf: Table[string, string]
    ## RFC-0016 INT-36 (0005 review R4-09). Each `symexFindings` key's claim:
    ## its `fn` and target, without the call site (`claimKey`).
  firstOfClaim: Table[string, string]
    ## The first `symexFindings` key made for each claim, the entry a nested
    ## run's finding of that claim under another call site merges into.
  dbErrors*: seq[string]                       ## cross-example
    ## RFC-0016 INT-34 (0005 review R2-10). The errors the symex cache's reads
    ## and writes hit inside this run's property (`recordSymexDbError`), in
    ## order. The engine adds them to the run's `Report.dbErrors` when the run
    ## ends, whatever its outcome. They were a thread-local list the next run
    ## to fail drained, so a run could report another's errors and lose its own.

var engineStack* {.threadvar.}: seq[EngineFrame]

type Severity = enum
  ## Review R4 (U1), R5 (D3a), R6 (N2). How much a report needs to show a
  ## finding, weakest first. Each meaning has its own rank, so a tie never
  ## lets a later, weaker finding replace an earlier, stronger one (equal
  ## ranks keep the latest):
  ##   skAudit             `sfNotApplicable` / `sfReplayMiss`: not verdicts.
  ##                       Only `sfNotApplicable` is ever built (in
  ##                       `engine/phases.nim`, when symex was skipped, and
  ##                       in `symex.nim`'s zero-targets arm of
  ##                       `symexFindAllWitnesses`); `sfReplayMiss` is never
  ##                       constructed in `src`. Exists for `severity`'s
  ##                       exhaustiveness only: neither site goes through
  ##                       `recordSymexFinding`, so `record` never sees it;
  ##   skTrustedCovered    a trusted claim the test covered;
  ##   skUnconfirmed       a covered claim no trust backs;
  ##   skUnknown           decided nothing (`sfUnknown`, accepted or not);
  ##   skUnconfirmedMiss   an untrusted claim the run did not reach
  ##                       (`covered = false`). With `acceptUnknownAsCovered =
  ##                       true` it carries NO failure (`failure = ""`) and
  ##                       raises nothing; with `false` it raises a
  ##                       `SymexCoverageDefect`. It ranks below
  ##                       `skCoverageFailure` because that claim is trusted,
  ##                       and above `skUnknown` because it is a claim, not a
  ##                       non-answer;
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

proc recordKeyed(fr: var EngineFrame; key, claim: string; f: SymexFinding) =
  if key notin fr.symexFindings:
    fr.claimOf[key] = claim
    if claim notin fr.firstOfClaim: fr.firstOfClaim[claim] = key
  record(fr, key, f)

func stronger(f, g: SymexFinding): bool =
  ## RFC-0016 INT-36 (0005 review R4-09). Whether `f` should stand for a
  ## claim `g` already stands for: it is more severe, or as severe and the
  ## stronger claim (`claimRank`); a full tie keeps the later `f`, as
  ## `record` does.
  let sf = severity(f)
  let sg = severity(g)
  sf > sg or (sf == sg and claimRank(f.soundness) >= claimRank(g.soundness))

proc popEngineFrame*() =
  ## Pops the top frame. Review R3 (E3): its symex findings also reach the
  ## frame it was opened in, so a nested `forAll`'s findings are on the
  ## enclosing run's report whatever its caller does with the inner one
  ## (`laws` keeps only the outcome).
  ##
  ## RFC-0016 INT-36 (0005 review R4-09). They merge on the claim (the `fn`
  ## and the target), not the call site: a nested run that re-finds the
  ## enclosing run's claim at its own call site joins the entry the
  ## enclosing frame already holds for it (the one under the same key, else
  ## the first made for that claim) instead of adding a second. The entry
  ## kept is the more severe, then the stronger claim (`claimRank`). Two
  ## call sites in ONE run stay two entries (review R3 E2): only `record`
  ## sees those, and it keys on the site.
  var fr = engineStack.pop()
  if engineStack.len > 0:
    template parent: untyped = engineStack[^1]
    for k, f in fr.symexFindings:
      let claim = fr.claimOf.getOrDefault(k)
      let into =
        if k in parent.symexFindings: k
        else: parent.firstOfClaim.getOrDefault(claim)
      if into.len > 0 and into in parent.symexFindings:
        if stronger(f, parent.symexFindings[into]):
          parent.symexFindings[into] = f
      else:
        recordKeyed(parent, k, claim, f)
    # RFC-0016 INT-34: a nested run's DB errors are its enclosing run's too.
    parent.dbErrors.add fr.dbErrors

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

var droppedFindings: Atomic[int]
  ## RFC-0016 INT-36 (0005 review R5-07). One count for the process, not per
  ## thread: a drop on a thread the property started is a drop of the run
  ## that started it, and that run reads the count's change
  ## (`Report.droppedSymexFindings`).

proc resetDroppedSymexFindings*() =
  ## Review R5 (3c). Zeroes the process's drop count (`droppedSymexFindings`).
  ## A run reports how far the count moved while it ran, so a reset while a
  ## run is in progress makes that run's figure wrong: compare against a
  ## reading taken before instead, where you can.
  droppedFindings.store(0)

proc droppedSymexFindings*(): int =
  ## Review R4 (X8), RFC-0016 INT-36 (R5-07). How many findings
  ## `recordSymexFinding` dropped in this process, on any thread, because no
  ## engine frame was open on the thread that made them. A run's change in it
  ## is on its report (`Report.droppedSymexFindings`) and every renderer.
  droppedFindings.load()

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

func claimKey(o: FindingOrigin; f: SymexFinding): string =
  ## RFC-0016 INT-36 (0005 review R4-09). `findingKey` without the call site:
  ## what a nested run's finding merges into its enclosing run's on.
  $o.fnId.len & ':' & o.fnId & f.targetDesc

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
    droppedFindings.atomicInc()
    return
  recordKeyed(engineStack[^1], findingKey(origin, f), claimKey(origin, f), f)

var unownedDbErrors {.threadvar.}: seq[string]
  ## RFC-0016 INT-34. The symex DB errors made on this thread outside any run
  ## (a standalone `saveSymexWitness`, say). No report reads them: they are
  ## the caller's, through `consumeSymexDbErrors`.

let mainThreadId = getThreadId()
  ## The thread that initialised this module: the process's main thread. A
  ## standalone symex call there, outside any run, is the caller's to
  ## consume; on any other thread no one is expected to (see
  ## `recordSymexDbError`).

var droppedDbErrs: Atomic[int]
  ## RFC-0016 INT-36's design for DB errors (wiring audit C-3). One count for
  ## the process: the errors made with no engine frame open, on a thread that
  ## is not the main thread. A run reads the count's change
  ## (`Report.droppedSymexDbErrors`).

proc droppedSymexDbErrors*(): int =
  ## How many symex DB errors `recordSymexDbError` made off any run's
  ## thread (no engine frame open, and not the main thread), in this process.
  ## A run's change in it is on its report
  ## (`Report.droppedSymexDbErrors`) and every renderer.
  droppedDbErrs.load()

proc recordSymexDbError*(msg: string) =
  ## Phase 14 C2, RFC-0016 INT-34 (0005 review R2-10). Records an error a
  ## symex cache read or write hit. Inside a run (an engine frame is open on
  ## this thread) it is that run's, and its report shows it
  ## (`EngineFrame.dbErrors`); outside any run it is held for the caller
  ## (`consumeSymexDbErrors`).
  ##
  ## The thread's list dies with the thread, so an error no one will consume
  ## is also counted (`droppedSymexDbErrors`). "Unowned and not consumed" is
  ## decided as INT-36 decides it for findings, at the call, not later: no
  ## frame on this thread, and this is a thread other than the main one (a
  ## thread the property started; a worker has no caller reading its list).
  ## A standalone call on the main thread is the caller's and is not
  ## counted. A worker that does consume its own list still shows in the
  ## count: the count only over-reports, never loses an error.
  if engineStack.len > 0: engineStack[^1].dbErrors.add msg
  else:
    unownedDbErrors.add msg
    if getThreadId() != mainThreadId: droppedDbErrs.atomicInc()

proc popEngineFrameTakingDbErrors*(): seq[string] =
  ## Pops the top frame and returns the symex DB errors it holds (they also
  ## reach the enclosing frame, as `popEngineFrame` merges them). For a
  ## caller whose own report must show errors made before an inner run
  ## opens its frame (`symexForAll`'s layer 1).
  result = engineStack[^1].dbErrors
  popEngineFrame()

proc consumeSymexDbErrors*(): seq[string] =
  ## The symex DB errors made on this thread outside any run since the last
  ## call, oldest first, and forgets them. A run's own errors are on its
  ## report, never here.
  result = move unownedDbErrors
  unownedDbErrors = @[]

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

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(engineStack, unownedDbErrors)

registerThreadStateRelease(releaseThreadState)
