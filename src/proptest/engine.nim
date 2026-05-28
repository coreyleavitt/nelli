## The property runner.
##
## `forAll` generates up to `maxExamples` values from a strategy and checks the
## property against each, classifying every example as pass, falsified, or
## rejected (`assume`/filter). It returns a `Report` rather than raising, so it
## composes; the test-framework adapter (`dsl.nim`) turns a falsified report
## into a single unittest failure.
##
## **Targeted PBT.** A property can call `target(score, label = "")` zero or
## more times per example. The engine tracks a bounded Pareto front of
## non-dominated examples across all labels and, after the random phase,
## explores around the front with two phases:
## * **Pareto-aware greedy hill-climb** — try ±{1, 10, 100, 1000} perturbations
##   on each integer choice; a perturbation is accepted iff its score-tuple is
##   not dominated by any current front member.
## * **Simulated-annealing escape** — from each front member, do K Cauchy-
##   distributed proposals. Acceptance uses random-weight Tchebycheff
##   scalarization (reaches the full Pareto front, including non-convex
##   regions, unlike weighted-sum). Falsifications discovered during either
##   phase are shrunk and reported as falsifications.
##
## **Cross-run resumption** — the secondary corpus persists the full Pareto
## front (label-keyed score tables) so a follow-up run seeds its targeted
## phase from where the last one left off.

import std/[math, tables, sets, options, hashes, times, monotimes, algorithm,
            strutils]
export options
import ./strategy, ./datasource, ./rng, ./choice, ./shrinker, ./db, ./int128

type
  FalsifiedError* = object of CatchableError
    ## Raised by `ensure` when a property is violated.

  Settings* = object
    maxExamples*: int    ## how many valid examples to check before declaring success
    maxRejections*: int  ## rejection budget before giving up (otExhausted)
    seed*: uint64        ## master seed; the run is deterministic in it
    testId*: string      ## opaque ID for DB lookup; empty = DB disabled
    dbPath*: string      ## directory of the example DB; empty = DB disabled
    flakyRetries*: int   ## re-runs of a failing example to confirm reproducibility
                         ## (any retry that *passes* ⇒ otFlaky; 0 disables)
    maxShrinks*: int     ## hard cap on the shrinker's outer fixpoint iterations
                         ## (default 500); guards against pathological shrink loops
    useSA*: bool         ## if true, run the simulated-annealing escape phase
                         ## after greedy hill-climb (default true)
    targetedSAIters*: int  ## number of SA proposals per front member (default 200)
    derandomize*: bool
      ## When true, the master seed is derived from `hash(testId)` rather
      ## than `seed`. Gives each test an independent, bit-for-bit
      ## reproducible run across hosts without relying on a single global
      ## constant. Requires a non-empty `testId` (raises `ValueError`
      ## otherwise — silent fall-through would defeat the point).
    deadline*: Duration
      ## Per-example time budget. When `> 0`, a property invocation that
      ## takes longer than this is treated as a falsification with a
      ## `DeadlineExceeded` exception; the slow input is shrunk the same
      ## way as any other failure. `0` (default) = unlimited.
    printEvents*: bool
      ## Controls whether `repro()` (and DSL checkpoints) include the
      ## `[events]` section. `Report.events` is always populated; this
      ## flag only gates the *render*. Default true. Set false for
      ## tests that event() heavily and want clean failure output.

  DeadlineExceeded* = object of FalsifiedError
    ## A property invocation exceeded `Settings.deadline`. Subclass of
    ## `FalsifiedError` so it flows through the same falsification +
    ## shrinking machinery; the message carries the elapsed time.

  Outcome* = enum
    otPassed, otFalsified, otExhausted, otFlaky

  Necessity* = enum
    ## Per-choice annotation produced by the `explain` phase.
    nUnknown,    ## explain phase didn't run (passing / explicit example)
    nNecessary,  ## perturbing this choice makes the property pass — the
                 ## failure depends on this value
    nFree        ## perturbing this choice keeps the property failing —
                 ## the choice doesn't carry information about the bug

  ScoreMap* = Table[string, float]
    ## A targeted example's score, keyed by label. Empty when the property
    ## made no `target()` calls.

  ParetoEntry* = object
    scores*: ScoreMap
    choices*: seq[ChoiceNode]

  NumericSummary* = object
    ## Summary of a single numeric event label across all examples in
    ## a run. We keep min/max/mean and three quantiles; storing raw
    ## samples is left to the engine until report time.
    count*: int
    mn*, mx*, mean*, p50*, p90*, p99*: float

  EventStats* = object
    categorical*: Table[string, int]
    numeric*: Table[string, NumericSummary]

  Report*[T] = object
    outcome*: Outcome
    examples*: int               ## valid examples checked
    counterexample*: Option[T]
      ## `some(value)` for a normal `otFalsified`/`otFlaky` outcome. `none`
      ## when the outcome is `otPassed`/`otExhausted`, *or* when the
      ## strategy itself raised before assigning a value (rare; surfaces
      ## with stateful per-step `invariant:` violations and the like).
      ## In the latter case, `choices` is still the reproducible artifact.
    choices*: seq[ChoiceNode]    ## the failing choice sequence (for shrinking/DB)
    message*: string             ## failure detail
    seed*: uint64                ## the master seed `forAll` ran with
    paretoFront*: seq[ParetoEntry]
      ## non-dominated examples seen during targeted search; empty when no
      ## `target()` calls were made
    dbReplays*: int
      ## How many stored entries from the example database were replayed
      ## during the DB-reuse phase. `0` when the DB is disabled or empty;
      ## `>= 1` when a known failure was found and re-shrunk before the
      ## random phase ran. Surfaces the example-DB's contribution so
      ## "did the persistence work?" is answerable from the Report.
    notes*: seq[(string, string)]
      ## `(label, $value)` pairs accumulated by `note(...)` calls during
      ## the failing prop invocation, in order. After shrinking, these are
      ## the notes captured by replaying the *shrunk* choice sequence — so
      ## the displayed context matches the minimal counterexample. Empty
      ## when the property didn't call `note` (or the run passed).
    events*: EventStats
    necessity*: seq[Necessity]
      ## One entry per `choices[i]` flagging whether that choice's
      ## value is required for the failure (`nNecessary`) or not
      ## (`nFree`). Populated by the explain phase after shrinking;
      ## empty for passed / explicit-example reports.
    printEvents*: bool
      ## Carries `Settings.printEvents` so `repro()` knows whether to
      ## include the `[events]` section. The underlying `events` table
      ## is always populated; this flag gates only the render.
      ## Cross-example distribution observability accumulated by
      ## `event(label[, numericValue])`. Categorical counts answer
      ## "what fraction of my inputs were of kind X"; numeric
      ## summaries surface min/max/mean/quantiles. Both persist across
      ## passing examples — the user's protection against silently
      ## degenerate generators ("I tested 100 lists, 99 were empty").
    displayed*: string
      ## Custom counterexample rendering produced by the strategy's
      ## `displayWith` proc, applied to the *shrunk* value. Empty when
      ## the strategy carries no display proc, or when `counterexample`
      ## is `none` (no value to render). `repro()` and the DSL checkpoint
      ## prefer this over `$counterexample.get` when non-empty.

func defaultSettings*(): Settings =
  Settings(maxExamples: 100, maxRejections: 1000,
           seed: 0x1234567890abcdef'u64, flakyRetries: 5,
           maxShrinks: 500, useSA: true, targetedSAIters: 200,
           printEvents: true)

template assume*(cond: untyped) =
  ## Discard the current example unless `cond` holds (raises `Rejection`, which
  ## the runner counts against the rejection budget). Prefer constraining the
  ## strategy over heavy `assume`.
  if not cond:
    raise newException(Rejection, "assumption failed: " & astToStr(cond))

template ensure*(cond: untyped) =
  ## Assert a property holds for the current example; raises `FalsifiedError`
  ## (which `forAll` catches) with the failing expression's text.
  if not cond:
    raise newException(FalsifiedError, "ensure failed: " & astToStr(cond))

template assumeOk*(expr: untyped): auto =
  ## Evaluate `expr`, `assume` that its `.isOk` holds, and return its
  ## `.get` value. Duck-typed on `.isOk: bool` + `.get: T` — works with
  ## any `Result`-shaped type as well as types adapted via stand-in
  ## procs. Replaces the recurring two-liner
  ## `let r = expr; assume r.isOk; let v = r.get`.
  let r = expr
  assume r.isOk
  r.get

template assumeSome*(expr: untyped): auto =
  ## `Option[T]` form of `assumeOk`: rejects the example if the result
  ## is `none`, otherwise returns the contained value.
  let o = expr
  assume o.isSome
  o.get

# --- per-example debug notes ------------------------------------------------

type EngineFrame = object
  ## One per-`forAll` worth of per-example accumulators. Stacking these
  ## via `engineStack` is what makes nested `forAll` calls compose —
  ## the inner run gets a fresh frame, runs its own examples, and pops;
  ## the outer's frame is restored intact. Without the stack, the inner
  ## run would clobber the outer's `note()` / `event()` / `target()`
  ## state for the outer example currently being checked.
  notes: seq[(string, string)]            ## per-example, cleared each prop call
  scores: ScoreMap                         ## per-example, cleared each prop call
  eventsCategorical: Table[string, int]    ## cross-example, lives the frame
  eventsNumeric: Table[string, seq[float]] ## cross-example, lives the frame

var engineStack {.threadvar.}: seq[EngineFrame]

template withEngineFrame(body: untyped) =
  ## Push a fresh frame for the duration of `body`. Guarantees pop on
  ## any exit path (return, raise) so a nested `forAll`'s frame can't
  ## leak across into the caller's state.
  engineStack.add EngineFrame()
  try:
    body
  finally:
    discard engineStack.pop()

proc currentFrame: var EngineFrame {.inline.} =
  ## Top of the per-thread engine stack. Required to be non-empty —
  ## `note()` / `target()` / `event()` outside any `forAll` is a
  ## programming error.
  if engineStack.len == 0:
    raise newException(ValueError,
      "note/target/event called outside any forAll — there's no example to attach to")
  engineStack[^1]

proc event*(label: string) =
  ## Tag the current example with a categorical event named `label`.
  ## Counts persist across all examples and surface in `Report.events.categorical`,
  ## so the user can see "my generator produced this kind X% of the time."
  ## Raises `ValueError` if `label` was already used for a numeric event
  ## in this run — mixed kinds in one label hide the signal.
  if currentFrame().eventsNumeric.hasKey(label):
    raise newException(ValueError,
      "event label '" & label & "' was already used for a numeric event")
  inc currentFrame().eventsCategorical.mgetOrPut(label, 0)

proc event*[T: SomeNumber](label: string, value: T) =
  ## Tag the current example with a numeric sample. The Report carries
  ## min/max/mean and p50/p90/p99 of all samples seen.
  if currentFrame().eventsCategorical.hasKey(label):
    raise newException(ValueError,
      "event label '" & label & "' was already used for a categorical event")
  currentFrame().eventsNumeric.mgetOrPut(label, @[]).add float(value)

proc note*[T](label: string, value: T) =
  ## Attach `(label, $value)` to the current example. On falsification, the
  ## notes accumulated during the failing prop invocation are included in
  ## `Report.notes`; otherwise discarded. No effect on generation or
  ## shrinking. Generic on `T` — auto-`$`s the value at the call site so
  ## `note("after step 3", encode(d))` works alongside `note("count", n)`.
  currentFrame().notes.add (label, $value)

# --- targeted PBT: a label-keyed score the engine tries to maximize ---------


const
  targetPosSentinel* = 1e300
    ## Finite stand-in for `+Inf` in `target()`. Substituting a sentinel
    ## preserves the user's intent ("this score is as high as possible")
    ## while keeping the augmented-Tchebycheff aggregator finite.
  targetNegSentinel* = -1e300

proc target*(score: float, label: string = "") =
  ## Within a property, declare a numeric `score` for an objective named
  ## `label` ("" is the default-objective label). Multiple labels per example
  ## are allowed and tracked as a multi-objective Pareto front; the engine
  ## tries to maximize each label.
  ##
  ## Non-finite inputs are sanitized so SA's augmented-Tchebycheff aggregator
  ## stays well-defined — every coerced value is **finite**. With `NegInf`
  ## as the NaN target, a label whose every example produced NaN would leave
  ## `refPoint[label] = NegInf`, and `bumpedRef(NegInf, 1.0) = NegInf` made
  ## the aggregator return `NaN`, killing SA acceptance for the rest of the
  ## run. A finite sentinel keeps the math defined.
  ##
  ## * **NaN** → `targetNegSentinel` (-1e300). "Undefined" maps to "worst
  ##   possible" via a finite stand-in.
  ## * **+Inf** → `targetPosSentinel` (1e300).
  ## * **−Inf** → `targetNegSentinel` (-1e300).
  ##
  ## A stderr warning is emitted in each case so the user knows.
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

# --- Pareto helpers ---------------------------------------------------------

proc dominates*(a, b: ScoreMap): bool =
  ## True iff `a` Pareto-dominates `b`: a ≥ b on every label seen in either
  ## map, with strict > on at least one. A label missing from a side counts
  ## as `-Inf` there — so the union of labels is what dominance compares over.
  if a.len == 0 and b.len == 0: return false
  var labels: HashSet[string]
  for k in a.keys: labels.incl k
  for k in b.keys: labels.incl k
  var strict = false
  for k in labels:
    let av = a.getOrDefault(k, NegInf)
    let bv = b.getOrDefault(k, NegInf)
    if av < bv: return false
    if av > bv: strict = true
  strict

proc insertPareto(front: var seq[ParetoEntry],
                  entry: ParetoEntry, cap = 32) =
  ## Add `entry` to the front, dropping any current member it dominates.
  ## Returns silently if the new entry is dominated by an existing one or
  ## if it ties an existing entry's score tuple exactly (we keep the older
  ## example so cross-run behavior is deterministic). Caps the front at
  ## `cap` by evicting the lowest sum-of-scores entry when over capacity.
  for e in front:
    if dominates(e.scores, entry.scores):
      return
    if e.scores == entry.scores:
      return
  var kept: seq[ParetoEntry]
  for e in front:
    if not dominates(entry.scores, e.scores):
      kept.add e
  kept.add entry
  if kept.len > cap:
    var worstIdx = 0
    var worstSum = Inf
    for i in 0 ..< kept.len:
      var s = 0.0
      for v in kept[i].scores.values: s += v
      if s < worstSum:
        worstSum = s
        worstIdx = i
    kept.delete(worstIdx)
  front = kept

# --- Tchebycheff scalarization for SA acceptance ----------------------------

proc augmentedTchebycheff(scores, refPoint: ScoreMap,
                          weights: Table[string, float]): float =
  ## Tchebycheff aggregator for maximization: returns
  ## `max_l w[l] * (refPoint[l] - scores[l]) + ρ * Σ_l w[l] * (refPoint[l] - scores[l])`.
  ## Lower is better. The small ρ-term breaks ties between solutions equally
  ## bad in the max sense — required for Pareto-optimality of all front points
  ## (textbook augmented-Tchebycheff). Missing label on the scores side reads
  ## as `-Inf` (worst possible).
  const rho = 1e-4
  var maxTerm = NegInf
  var sumTerm = 0.0
  for k, w in weights:
    let r = refPoint.getOrDefault(k, 0.0)
    let s = scores.getOrDefault(k, NegInf)
    let term = w * (r - s)
    if term > maxTerm: maxTerm = term
    sumTerm += term
  maxTerm + rho * sumTerm

# --- proposal distributions for SA ------------------------------------------

proc cauchyDelta(rng: var SplitMix64, scale: float): float =
  ## Standard Cauchy(0, scale) sample via inverse CDF — heavy-tailed so SA
  ## takes both small polishing steps and occasional very large jumps in the
  ## same chain. The "Fast SA" recipe.
  let u = float(rng.next shr 11) * (1.0 / 9007199254740992.0)
  scale * tan(PI * (u - 0.5))

# --- shared replay/eval helpers ---------------------------------------------

type EvalKind = enum ekPassed, ekFalsified, ekRejected

type Eval[T] = object
  case kind: EvalKind
  of ekPassed:
    value: T
    scores: ScoreMap
    choices: seq[ChoiceNode]
  of ekFalsified:
    fValue: Option[T]
      ## `some(x)` when `prop(x)` raised after `x` was assigned; `none`
      ## when the strategy itself raised before assigning `x`. The
      ## difference matters for `Report.counterexample` honesty.
    fChoices: seq[ChoiceNode]
    fMsg: string
    fNotes: seq[(string, string)]
      ## Snapshot of `noteStack` at the moment of falsification — the
      ## `(label, $value)` pairs the property accumulated before raising.
  of ekRejected: discard

proc evalReplay[T](s: Strategy[T], prop: proc(x: T),
                   candidate: seq[ChoiceNode]): Eval[T] =
  ## Replay a candidate through the strategy and check the property. Returns
  ## the verdict + (for passes) any score map and the canonicalized choice
  ## sequence. Used by both hill-climb and SA.
  var ds = newReplaySource(candidate)
  var x: T
  currentFrame().scores.clear(); currentFrame().notes.setLen(0)
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return Eval[T](kind: ekRejected)
  # When the *strategy itself* raises (typically a per-step `invariant:` in
  # a stateful machine), `x` was never assigned — propagate `none(T)` so
  # the Report's `counterexample` is honest about there being no value.
  # The recorded choice sequence is still the reproducible artifact.
  except FalsifiedError as e:
    return Eval[T](kind: ekFalsified, fValue: none(T), fChoices: ds.recorded, fNotes: currentFrame().notes,
                   fMsg: "strategy raised: " & e.msg)
  except CatchableError as e:
    return Eval[T](kind: ekFalsified, fValue: none(T), fChoices: ds.recorded, fNotes: currentFrame().notes,
                   fMsg: "strategy raised: " & $e.name & ": " & e.msg)
  except Defect as e:
    return Eval[T](kind: ekFalsified, fValue: none(T), fChoices: ds.recorded, fNotes: currentFrame().notes,
                   fMsg: "strategy crashed: " & $e.name & ": " & e.msg)
  try:
    prop(x)
    Eval[T](kind: ekPassed, value: x, scores: currentFrame().scores, choices: ds.recorded)
  except Rejection:
    Eval[T](kind: ekRejected)
  except FalsifiedError as e:
    Eval[T](kind: ekFalsified, fValue: some(x), fChoices: ds.recorded, fNotes: currentFrame().notes, fMsg: e.msg)
  except CatchableError as e:
    Eval[T](kind: ekFalsified, fValue: some(x), fChoices: ds.recorded, fNotes: currentFrame().notes,
            fMsg: $e.name & ": " & e.msg)
  except Defect as e:
    Eval[T](kind: ekFalsified, fValue: some(x), fChoices: ds.recorded, fNotes: currentFrame().notes,
            fMsg: "crashed: " & $e.name & ": " & e.msg)


# --- helpers for hill-climb / SA -------------------------------------------

const
  maxSafeInt64Float* = 9223372036854774784.0
    ## `nextDown(2^63)` as an exact float64 — the largest float strictly
    ## below `2^63`. `int64(this)` is well-defined; `int64(2^63.0)` is UB.

proc clampToInt64*(candF: float, lo, hi: int64): int64 =
  ## Clamp a float candidate to `[lo, hi]` in int64 space, snapping the
  ## upper bound to a float strictly below `2^63.0` when `hi == high(int64)`.
  ## The obvious `int64(clamp(candF, lo.float, hi.float))` wraps to
  ## `low(int64)` when `candF >= 2^63.0`, because `float(high(int64))`
  ## rounds up one ULP past the int64 max and `int64()` of that is UB. We
  ## lose at most `2^11 = 2048` representable values at the very top —
  ## noise at the int64 scale. NaN inputs map to `lo`. **Singleton range
  ## `lo == hi` short-circuits** so the answer is exactly the bound even
  ## at the un-representable int64 edge.
  if lo == hi: return lo
  if candF != candF: return lo
  let safeHi = if hi == high(int64): maxSafeInt64Float else: hi.float
  let safeLo = lo.float  # low(int64) is exactly representable in float64
  int64(clamp(candF, safeLo, safeHi))

proc updateRefPoint(refPoint: var ScoreMap, scores: ScoreMap) =
  ## refPoint[label] = max(refPoint[label], scores[label]) + small epsilon
  ## (so Tchebycheff distances are well-defined and strictly positive at
  ## the ideal frontier).
  for k, v in scores:
    let cur = refPoint.getOrDefault(k, NegInf)
    if v > cur:
      refPoint[k] = v

proc bumpedRef(refPoint: ScoreMap, eps: float): ScoreMap =
  result = refPoint
  for k, v in result.mpairs:
    v += eps

proc randomWeights(rng: var SplitMix64, labels: HashSet[string]): Table[string, float] =
  ## Draw a positive weight per label (Dirichlet(1,...,1) via -log(U)) and
  ## L1-normalize. Re-drawn each SA outer iter so different facets of the
  ## front get explored.
  var sum = 0.0
  for k in labels:
    let u = max(1e-12, float(rng.next shr 11) * (1.0 / 9007199254740992.0))
    let w = -ln(u)
    result[k] = w
    sum += w
  if sum > 0.0:
    for k in result.keys:
      result[k] = result[k] / sum

# --- targeted-PBT phase ----------------------------------------------------

proc runTargetedPhase[T](
    s: Strategy[T],
    prop: proc(x: T),
    settings: Settings,
    db: ExampleDB,
    dbEnabled: bool,
    master: var SplitMix64,
    paretoFront: var seq[ParetoEntry],
    refPoint: var ScoreMap,
    examples: int,
    handleFalsification:
      proc(value: Option[T], choices: seq[ChoiceNode],
           msg, prefix: string, ex: int,
           originalNotes: seq[(string, string)]): Report[T]
): Option[Report[T]] =
  ## Pareto-aware greedy hill-climb → simulated-annealing escape →
  ## secondary-corpus save. Mutates `paretoFront` and `refPoint` in place.
  ## Returns `some(report)` for a falsification discovered during the
  ## climb or SA (which `forAll` then propagates as its own return); `none`
  ## when the phase completes without a falsification (`forAll` continues
  ## to its passing return). The helper is kept private — its parameter
  ## list is intimately coupled to `forAll`'s state and changing it for
  ## a future caller would be a no-op.

  # --- Pareto-aware greedy hill-climb -------------------------------------
  # Big steps first so we can cross falsifying boundaries before fine-tuning.
  const deltas = [int64(1000), -1000, 100, -100, 10, -10, 1, -1]
  block climb:
    var iter = 0
    while iter < 50:
      var improved = false
      var i = 0
      while i < paretoFront.len:
        let base = paretoFront[i]
        for cIdx in 0 ..< base.choices.len:
          if base.choices[cIdx].kind != ckInteger: continue
          # Skip forced nodes (singletons, p=0/1 booleans, etc.). Mirrors the
          # SA loop's gate; perturbing a forced value wastes an `evalReplay`
          # (the replay layer just clamps the value back) and would write a
          # constraint-violating intVal into the candidate sequence.
          if base.choices[cIdx].wasForced: continue
          let nv = base.choices[cIdx].intVal
          let lo = base.choices[cIdx].intC.min
          let hi = base.choices[cIdx].intC.max
          if not (fitsInt64(nv) and fitsInt64(lo) and fitsInt64(hi)):
            # Integer constraints spanning more than `int64` — hill-climb's
            # ±{1,10,100,1000} delta set isn't meaningful at that scale, and
            # the float clamp's safe-edge snap would lose all 128-bit bits.
            # The public `integers(int, int)` strategy never produces these
            # bounds; skipping is a no-op for today's surface. If 128-bit
            # int strategies land later, this branch needs an Int128-aware
            # delta set and `bounded128`-style proposals.
            continue
          let baseVal = toInt64(nv); let loI = toInt64(lo); let hiI = toInt64(hi)
          for d in deltas:
            # `baseVal + d` is unchecked int64 arithmetic — overflows when
            # baseVal is near int64 extremes. Do the add in float space, then
            # use the safe-edge clamp before the cast so a value at the
            # `2^63.0` float-rounding edge doesn't wrap to `low(int64)`.
            let candF = baseVal.float + d.float
            if candF < loI.float or candF > hiI.float: continue
            let candVal = clampToInt64(candF, loI, hiI)
            var cand = base.choices
            cand[cIdx].intVal = toInt128(candVal)
            let e = evalReplay(s, prop, cand)
            case e.kind
            of ekRejected: continue
            of ekFalsified:
              return some(handleFalsification(
                e.fValue, e.fChoices, e.fMsg, " via target", examples, e.fNotes))
            of ekPassed:
              if e.scores.len == 0: continue
              # Track membership of *this exact candidate* before and after
              # insertion. `insertPareto` adds the candidate iff it isn't
              # dominated by an existing entry, evicting any entries the
              # candidate strictly dominates. So a length increase OR an
              # equal-length swap that includes our candidate signals real
              # progress; equal scores against `base` (length unchanged,
              # candidate not in front) means no improvement.
              let before = paretoFront.len
              insertPareto(paretoFront, ParetoEntry(scores: e.scores,
                                                    choices: e.choices))
              updateRefPoint(refPoint, e.scores)
              var candidateAccepted = paretoFront.len > before
              if not candidateAccepted:
                for entry in paretoFront:
                  if entry.scores == e.scores: candidateAccepted = true; break
              if candidateAccepted: improved = true
        inc i
      if not improved: break
      inc iter

  # --- simulated-annealing escape ------------------------------------------
  # `targetedSAIters` is taken literally: a value of 0 disables the SA loop
  # in conjunction with `useSA`. Callers wanting the engine's default should
  # start from `defaultSettings()` and override the fields they care about.
  if settings.useSA and settings.targetedSAIters > 0:
    var saRng = initSplitMix64(master.next)
    var labels: HashSet[string]
    for e in paretoFront:
      for k in e.scores.keys: labels.incl k
    if labels.len > 0:
      let initialFrontLen = paretoFront.len
      var startIdx = 0
      # T₀ scales with the absolute score magnitude — Tchebycheff distances
      # are in the same units as scores, so acceptance probabilities need a
      # temperature of that order or downhill moves are *never* accepted.
      var t0: float = 1.0
      for v in refPoint.values:
        if abs(v) > t0: t0 = abs(v)
      while startIdx < min(initialFrontLen, 4):  # explore up to 4 seeds
        var current = paretoFront[startIdx].choices
        var currentScores = paretoFront[startIdx].scores
        var temperature = t0
        const alpha = 0.97
        # Re-draw weights / reference periodically so we explore different
        # facets of the front.
        var weights = randomWeights(saRng, labels)
        var bumpedR = bumpedRef(refPoint, 1.0)
        var currentAggr = augmentedTchebycheff(currentScores, bumpedR, weights)
        for k in 0 ..< settings.targetedSAIters:
          if (k mod 25) == 0 and k > 0:
            weights = randomWeights(saRng, labels)
            bumpedR = bumpedRef(refPoint, 1.0)
            currentAggr = augmentedTchebycheff(currentScores, bumpedR, weights)
          # Pick a random integer position and a Cauchy-distributed delta.
          var intPositions: seq[int]
          for ci in 0 ..< current.len:
            if current[ci].kind == ckInteger and not current[ci].wasForced and
               fitsInt64(current[ci].intC.min) and fitsInt64(current[ci].intC.max):
              intPositions.add ci
          if intPositions.len == 0: break
          let posIdx = int(saRng.bounded(uint64(intPositions.len)))
          let pos = intPositions[posIdx]
          let lo = toInt64(current[pos].intC.min)
          let hi = toInt64(current[pos].intC.max)
          # Do the candidate arithmetic in float space and clamp BEFORE the
          # cast. Cauchy is heavy-tailed: with a wide-range scale, samples
          # whose magnitude exceeds int64 are routine, and any of `hi - lo`,
          # `int64(cauchy)`, or `baseVal + d` can overflow int64 if expressed
          # in integer arithmetic. Float arithmetic on these magnitudes is
          # well-defined; the final cast is on a value already in `[lo, hi]`.
          let scale = max(1.0, (hi.float - lo.float) * 0.5)
          let baseVal = toInt64(current[pos].intVal)
          let target = baseVal.float + cauchyDelta(saRng, scale)
          let candVal = clampToInt64(target, lo, hi)
          if candVal == baseVal: continue
          var cand = current
          cand[pos].intVal = toInt128(candVal)
          let e = evalReplay(s, prop, cand)
          case e.kind
          of ekRejected: discard
          of ekFalsified:
            return some(handleFalsification(
              e.fValue, e.fChoices, e.fMsg, " via SA", examples, e.fNotes))
          of ekPassed:
            if e.scores.len == 0:
              temperature *= alpha
              continue
            updateRefPoint(refPoint, e.scores)
            bumpedR = bumpedRef(refPoint, 1.0)
            # Refresh `currentAggr` against the *new* reference point so the
            # acceptance Δ is measured between two aggregators on the same
            # yardstick. Computing the candidate against the new ref while
            # leaving `current` on the old one biased every comparison.
            currentAggr = augmentedTchebycheff(currentScores, bumpedR, weights)
            let candAggr = augmentedTchebycheff(e.scores, bumpedR, weights)
            let dE = currentAggr - candAggr  # positive = improvement
            var accept = dE >= 0.0
            if not accept and temperature > 1e-9:
              let r = float(saRng.next shr 11) * (1.0 / 9007199254740992.0)
              accept = r < exp(dE / temperature)
            if accept:
              current = e.choices
              currentScores = e.scores
              currentAggr = candAggr
            # Whether we moved or not, record non-dominated points.
            insertPareto(paretoFront,
                         ParetoEntry(scores: e.scores, choices: e.choices))
            # Cool.
            temperature *= alpha
        inc startIdx

  # --- save targeted state to secondary corpus ----------------------------
  # Single batched write — one read-modify-write for the whole Pareto front
  # instead of N (used to be O(N) DB cycles per `forAll`).
  if dbEnabled and paretoFront.len > 0:
    var batch: seq[ScoredEntry]
    for entry in paretoFront:
      var summary = NegInf
      for v in entry.scores.values:
        if v > summary: summary = v
      if summary == NegInf: summary = 0.0
      batch.add (choices: entry.choices, score: summary, scores: entry.scores)
    db.saveSecondary(settings.testId, batch)

  none(Report[T])

# --- the property runner ---------------------------------------------------

proc quantile(sorted: seq[float], q: float): float =
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

proc snapshotEvents(): EventStats =
  ## Build the final `EventStats` from the cross-example threadvars.
  ## Sorts each numeric sample once to compute quantiles.
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

proc renderDisplayed[T](s: Strategy[T], value: Option[T]): string =
  ## Apply the strategy's optional `display` proc to the (shrunk) value.
  ## Returns `""` when no display is attached or no value exists — the
  ## sentinel that tells `repro()`/DSL to fall back to default `$`.
  if s.display != nil and value.isSome: s.display(value.get) else: ""

proc perturbations(node: ChoiceNode): seq[ChoiceNode] =
  ## A small set of alternative values for one choice, all respecting
  ## the node's constraints. Used by `explain` to test whether the
  ## failure depends on this specific value. We try 4-6 alternatives —
  ## enough to detect "free" choices reliably without quadratic cost.
  if node.wasForced: return  # forced choices have no degrees of freedom
  case node.kind
  of ckInteger:
    let lo = node.intC.min
    let hi = node.intC.max
    let st = node.intC.shrinkTowards
    var cand: seq[ChoiceInt]
    cand.add st
    cand.add lo
    cand.add hi
    if lo + toInt128(1) <= hi: cand.add lo + toInt128(1)
    for c in cand:
      if c != node.intVal and c >= lo and c <= hi:
        result.add ChoiceNode(kind: ckInteger,
                              intC: node.intC, intVal: c)
  of ckBoolean:
    result.add ChoiceNode(kind: ckBoolean,
                          boolC: node.boolC, boolVal: not node.boolVal)
  of ckFloat:
    let cons = node.floatC
    for v in [0.0, 1.0, -1.0]:
      if v != node.floatVal and v >= cons.min and v <= cons.max:
        result.add ChoiceNode(kind: ckFloat,
                              floatC: cons, floatVal: v)
  of ckBytes:
    let cons = node.bytesC
    if node.bytesVal.len > 0 and cons.minSize == 0:
      result.add ChoiceNode(kind: ckBytes, bytesC: cons, bytesVal: @[])
    var allZero = newSeq[byte](node.bytesVal.len)
    if allZero != node.bytesVal:
      result.add ChoiceNode(kind: ckBytes, bytesC: cons, bytesVal: allZero)
  of ckString:
    let cons = node.strC
    if node.strVal.len > 0 and cons.minSize == 0:
      result.add ChoiceNode(kind: ckString, strC: cons, strVal: "")

proc explain[T](s: Strategy[T], prop: proc(x: T),
                choices: seq[ChoiceNode],
                originalMsg: string): seq[Necessity] =
  ## For each choice, try a small set of perturbations. If any
  ## perturbation makes the property pass (or rejects), the original
  ## value was *necessary* for the failure. If all perturbations still
  ## falsify, the choice is *free* — the bug doesn't care about it.
  result = newSeq[Necessity](choices.len)
  for i in 0 ..< choices.len:
    var madePass = false
    for perturbed in perturbations(choices[i]):
      var trial = choices
      trial[i] = perturbed
      let e = evalReplay(s, prop, trial)
      if e.kind == ekPassed or e.kind == ekRejected:
        madePass = true
        break
    result[i] = if madePass: nNecessary else: nFree

proc forAll*[T](s: Strategy[T], prop: proc(x: T),
                settings = defaultSettings()): Report[T] =
  ## Check `prop` against values drawn from `s`. Deterministic in `settings.seed`.
  ## When `settings.testId` and `settings.dbPath` are set, the reuse phase
  ## replays any DB-stored failure first; a fresh falsification is saved back.
  var settings = settings  # local mutable copy; `derandomize` rewrites `seed`
  if settings.derandomize:
    # Each test independently reproducible: seed is `hash(testId)`.
    # Empty `testId` is a user error — silent fall-through (using the
    # global default `seed`) would defeat the point of derandomize.
    if settings.testId.len == 0:
      raise newException(ValueError,
        "Settings.derandomize=true requires a non-empty Settings.testId")
    settings.seed = cast[uint64](hash(settings.testId))
  # Push a fresh per-`forAll` engine frame. Nested `forAll` calls
  # (the metamorphic / parametric-law pattern) compose because each
  # one runs against its own frame; the outer frame is restored on
  # `defer`'s pop, regardless of which return path we take.
  engineStack.add EngineFrame()
  defer: discard engineStack.pop()
  # Deadline enforcement: wrap `prop` once at entry. Every downstream
  # call site (random phase, shrinker, `evalReplay`, flaky retries) uses
  # the wrapped form, so the shrinker minimizes deadline-exceeding inputs
  # by the same machinery as logic failures — no separate timeout outcome
  # needed. Cost when no deadline is set: a single nil-closure shadow.
  let originalProp = prop
  let deadline = settings.deadline
  let hasDeadline = deadline.inNanoseconds > 0
  let prop =
    if hasDeadline:
      proc(x: T) =
        let start = getMonoTime()
        originalProp(x)
        let elapsed = getMonoTime() - start
        if elapsed.inNanoseconds > deadline.inNanoseconds:
          raise newException(DeadlineExceeded,
            "deadline exceeded: " & $elapsed & " > " & $deadline)
    else:
      originalProp
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  let db = newExampleDB(settings.dbPath)  # cheap value-wrapper; reused throughout
  var dbReplays = 0  # counted across DB reuse + targeted seeding; threaded into every Report below
  if dbEnabled:
    # Collect stale entries first; batch-prune in one write at the end so
    # we don't do N full file rewrites for an aging DB.
    var staleEntries: seq[seq[ChoiceNode]]
    var hitFalsifying = false
    for entry in db.loadPrimary(settings.testId):
      inc dbReplays
      let r = evalReplay(s, prop, entry)
      case r.kind
      of ekFalsified:
        hitFalsifying = true
        # Flush any pruning collected so far before we return.
        if staleEntries.len > 0:
          db.removeMany(settings.testId, staleEntries)
        let shrunk = shrink(s, prop, r.fChoices, settings.maxShrinks)
        let shrunkEval = evalReplay(s, prop, shrunk.choices)
        let shrunkNotes =
          if shrunkEval.kind == ekFalsified: shrunkEval.fNotes
          else: @[]
        if shrunk.flaky:
          return Report[T](outcome: otFlaky, examples: 0,
                           counterexample: shrunk.example, choices: shrunk.choices,
                           message: "flaky from DB: " & r.fMsg,
                           seed: settings.seed, dbReplays: dbReplays,
                           notes: shrunkNotes,
                           displayed: renderDisplayed(s, shrunk.example),
                           events: snapshotEvents(), printEvents: settings.printEvents)
        db.save(settings.testId, shrunk.choices)
        let necessityDB = explain(s, prop, shrunk.choices, r.fMsg)
        return Report[T](outcome: otFalsified, examples: 0,
                         counterexample: shrunk.example, choices: shrunk.choices,
                         message: "from DB: " & r.fMsg,
                         seed: settings.seed, dbReplays: dbReplays,
                         notes: shrunkNotes, necessity: necessityDB,
                         displayed: renderDisplayed(s, shrunk.example),
                         events: snapshotEvents(), printEvents: settings.printEvents)
      of ekPassed, ekRejected:
        staleEntries.add entry
    # No DB entry reproduced — flush the prune list in one write.
    if not hitFalsifying and staleEntries.len > 0:
      db.removeMany(settings.testId, staleEntries)

  var master = initSplitMix64(settings.seed)
  var examples = 0
  var rejections = 0
  var paretoFront: seq[ParetoEntry]
  var refPoint: ScoreMap

  proc handleFalsification(value: Option[T], choices: seq[ChoiceNode],
                           msg, prefix: string, ex: int,
                           originalNotes: seq[(string, string)] = @[]):
                            Report[T] =
    ## `value` is `some(x)` when the engine had a real value before the
    ## failure (the normal case), `none` when the strategy itself raised
    ## mid-generation. `originalNotes` is the `note()` context the failing
    ## prop run accumulated — used for the early-return paths (flaky-retry
    ## passed) where we don't shrink and so don't re-run for shrunk notes.
    var flakyRetryPassed = false
    for _ in 0 ..< settings.flakyRetries:
      let e = evalReplay(s, prop, choices)
      if e.kind == ekPassed:
        flakyRetryPassed = true
        break
    if flakyRetryPassed:
      return Report[T](outcome: otFlaky, examples: ex,
                       counterexample: value, choices: choices,
                       message: "flaky" & prefix & ": " & msg,
                       seed: settings.seed, paretoFront: paretoFront,
                       dbReplays: dbReplays, notes: originalNotes,
                       displayed: renderDisplayed(s, value),
                       events: snapshotEvents(), printEvents: settings.printEvents)
    let shrunk = shrink(s, prop, choices, settings.maxShrinks)
    # Re-run the property on the shrunk choice sequence to capture the
    # `note(...)` context that *the shrunk counterexample* produced. The
    # shrinker calls its own `tryFalsifies` hundreds of times; threading
    # notes through every replay is wasteful when only the final example's
    # notes matter. One extra `evalReplay` per falsification is negligible.
    let shrunkEval = evalReplay(s, prop, shrunk.choices)
    let shrunkNotes =
      if shrunkEval.kind == ekFalsified: shrunkEval.fNotes
      else: @[]
    if shrunk.flaky:
      return Report[T](outcome: otFlaky, examples: ex,
                       counterexample: shrunk.example, choices: shrunk.choices,
                       message: "flaky (post-shrink)" & prefix & ": " & msg,
                       seed: settings.seed, paretoFront: paretoFront,
                       dbReplays: dbReplays, notes: shrunkNotes,
                       displayed: renderDisplayed(s, shrunk.example),
                       events: snapshotEvents(), printEvents: settings.printEvents)
    if dbEnabled:
      db.save(settings.testId, shrunk.choices)
    let necessity = explain(s, prop, shrunk.choices, msg)
    Report[T](outcome: otFalsified, examples: ex,
              counterexample: shrunk.example, choices: shrunk.choices,
              message: prefix & ": " & msg, seed: settings.seed,
              paretoFront: paretoFront, dbReplays: dbReplays,
              notes: shrunkNotes, necessity: necessity,
              displayed: renderDisplayed(s, shrunk.example),
              events: snapshotEvents(), printEvents: settings.printEvents)

  # --- random-generation phase --------------------------------------------
  while examples < settings.maxExamples:
    var ds = newDataSource(initSplitMix64(master.next))
    var rejected = false
    var failMessage = ""
    var falsified = false
    var valueOpt: Option[T]   # `some(x)` iff `s.generate` returned a value
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    try:
      let x = s.generate(ds)
      valueOpt = some(x)
      prop(x)
    except Rejection:
      rejected = true
    except FalsifiedError as e:
      falsified = true; failMessage = e.msg
    except CatchableError as e:
      falsified = true; failMessage = "raised " & $e.name & ": " & e.msg
    except Defect as e:
      falsified = true; failMessage = "crashed: " & $e.name & ": " & e.msg
    if falsified:
      # Snapshot `noteStack` before re-runs; the property's failing
      # context belongs to *this* example.
      return handleFalsification(valueOpt, ds.recorded, failMessage, "",
                                 examples, currentFrame().notes)
    if rejected:
      inc rejections
      if rejections > settings.maxRejections:
        return Report[T](outcome: otExhausted, examples: examples,
                         seed: settings.seed, paretoFront: paretoFront,
                         dbReplays: dbReplays, events: snapshotEvents(), printEvents: settings.printEvents)
      continue
    if currentFrame().scores.len > 0:
      let entry = ParetoEntry(scores: currentFrame().scores, choices: ds.recorded)
      insertPareto(paretoFront, entry)
      updateRefPoint(refPoint, entry.scores)
    inc examples

  # --- cross-run resumption: seed the front from the secondary corpus ---
  if dbEnabled:
    for entry in db.loadSecondary(settings.testId):
      var scores: ScoreMap
      if entry.scores.len > 0:
        scores = entry.scores
      else:
        scores[""] = entry.score
      insertPareto(paretoFront, ParetoEntry(scores: scores, choices: entry.choices))
      updateRefPoint(refPoint, scores)

  if paretoFront.len == 0:
    return Report[T](outcome: otPassed, examples: examples,
                     seed: settings.seed, dbReplays: dbReplays,
                     events: snapshotEvents(), printEvents: settings.printEvents)

  # --- targeted phase: hill-climb + SA + secondary-corpus save ------------
  let targeted = runTargetedPhase(s, prop, settings, db, dbEnabled,
                                  master, paretoFront, refPoint, examples,
                                  handleFalsification)
  if targeted.isSome:
    return targeted.get

  Report[T](outcome: otPassed, examples: examples,
            seed: settings.seed, paretoFront: paretoFront,
            dbReplays: dbReplays, events: snapshotEvents(), printEvents: settings.printEvents)

proc forAllWithExamples*[T](explicit: openArray[T], s: Strategy[T],
                            prop: proc(x: T),
                            settings = defaultSettings()): Report[T] =
  ## Run each value in `explicit` through `prop` before the random phase.
  ## Explicit examples are user-pinned regression seeds — the user said
  ## "this exact input matters," so we don't shrink them (no choice
  ## sequence to shrink) and report `choices: @[]` on failure. If all
  ## explicit cases pass, fall through to the standard `forAll`.
  ##
  ## Deadline / event accumulators behave identically to `forAll`: the
  ## explicit phase counts toward the same `Report.events`, and the
  ## deadline (if set) applies to each explicit invocation.
  # Push the engine frame for this run; `defer` ensures we pop before
  # `forAll` (called below in the fall-through) is entered with the
  # frame stack already-stacked. Pop happens at proc exit regardless
  # of return path.
  engineStack.add EngineFrame()
  defer: discard engineStack.pop()
  # Apply deadline wrapper identical to `forAll`.
  let originalProp = prop
  let deadline = settings.deadline
  let hasDeadline = deadline.inNanoseconds > 0
  let prop =
    if hasDeadline:
      proc(x: T) =
        let start = getMonoTime()
        originalProp(x)
        let elapsed = getMonoTime() - start
        if elapsed.inNanoseconds > deadline.inNanoseconds:
          raise newException(DeadlineExceeded,
            "deadline exceeded: " & $elapsed & " > " & $deadline)
    else:
      originalProp
  for i, ex in explicit:
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    try:
      prop(ex)
    except FalsifiedError as e:
      return Report[T](outcome: otFalsified, examples: i,
                       counterexample: some(ex), choices: @[],
                       message: "from explicit example #" & $i & ": " & e.msg,
                       seed: settings.seed, dbReplays: 0,
                       events: snapshotEvents(),
                       printEvents: settings.printEvents)
    except CatchableError as e:
      return Report[T](outcome: otFalsified, examples: i,
                       counterexample: some(ex), choices: @[],
                       message: "from explicit example #" & $i & " raised " &
                                $e.name & ": " & e.msg,
                       seed: settings.seed, dbReplays: 0,
                       events: snapshotEvents(),
                       printEvents: settings.printEvents)
    except Defect as e:
      return Report[T](outcome: otFalsified, examples: i,
                       counterexample: some(ex), choices: @[],
                       message: "from explicit example #" & $i &
                                " crashed: " & $e.name & ": " & e.msg,
                       seed: settings.seed, dbReplays: 0,
                       events: snapshotEvents(),
                       printEvents: settings.printEvents)
  # All explicit examples passed — delegate to the standard random phase.
  # NOTE: forAll will re-reset the event accumulators, which is fine — its
  # contract is "deterministic in settings.seed across the whole call,"
  # and the explicit examples' event contributions are not visible in
  # the final Report. That's a deliberate tradeoff: explicit examples
  # are regression seeds, not part of the random distribution being
  # surveyed via `event()`. If a user disagrees, they call event()
  # inside the explicit body and inspect Report.events on a passing
  # explicit-only run (no `given` → no forAll fall-through).
  forAll(s, originalProp, settings)

proc displayCounterexample*[T](r: Report[T]): string =
  ## Render `r`'s counterexample for a failure log: prefer the custom
  ## `displayed` string (from `Strategy.displayWith`), fall back to
  ## `$counterexample.get`, or — when the strategy raised mid-generation
  ## with no value to show — return an explanatory marker. Used by the
  ## `property` DSL's checkpoint and by `repro()`.
  if r.displayed.len > 0: r.displayed
  elif r.counterexample.isSome: $r.counterexample.get
  else: "<none — strategy raised; see choices>"

proc repro*[T](r: Report[T]): string =
  ## Format a `Report` as a multi-line, copy-pasteable repro string suitable
  ## for failure logs or bug reports. Always includes outcome, examples, and
  ## seed; on falsifying/flaky outcomes it also includes the counterexample,
  ## any failure message, and the rendered choice sequence.
  result = "outcome=" & $r.outcome & "\n"
  result &= "examples=" & $r.examples & "\n"
  result &= "seed=" & $r.seed & "\n"
  if r.dbReplays > 0:
    result &= "db_replays=" & $r.dbReplays & "\n"
  if r.outcome in {otFalsified, otFlaky}:
    result &= "counterexample=" & displayCounterexample(r) & "\n"
    if r.message.len > 0:
      result &= "message=" & r.message & "\n"
    for (label, value) in r.notes:
      result &= "note[" & label & "]=" & value & "\n"
    if r.choices.len > 0:
      if r.necessity.len == r.choices.len:
        # Per-choice annotation produced by the `explain` phase: mark
        # each value as `[necessary]` (the failure depends on it) or
        # `[free]` (it doesn't carry information about the bug). The
        # one-line-per-choice form replaces the compact seq render
        # only when explain data is available, so the user sees the
        # debug aid without losing the choice values.
        result &= "choices:\n"
        for i in 0 ..< r.choices.len:
          let tag = case r.necessity[i]
                    of nNecessary: "[necessary]"
                    of nFree:      "[free]"
                    of nUnknown:   "[?]"
          result &= "  " & $r.choices[i] & " " & tag & "\n"
      else:
        result &= "choices=" & $r.choices & "\n"
  if r.printEvents and
     (r.events.categorical.len > 0 or r.events.numeric.len > 0):
    result &= "[events]\n"
    # Categorical first, sorted by label for stable output.
    var catLabels: seq[string]
    for k in r.events.categorical.keys: catLabels.add k
    catLabels.sort()
    var total = 0
    for k in catLabels: total += r.events.categorical[k]
    for k in catLabels:
      let n = r.events.categorical[k]
      let pct = 100.0 * float(n) / float(max(1, total))
      result &= "  " & k & " = " & $n & " (" & $pct.formatFloat(ffDecimal, 1) & "%)\n"
    # Numeric summaries
    var numLabels: seq[string]
    for k in r.events.numeric.keys: numLabels.add k
    numLabels.sort()
    for k in numLabels:
      let s = r.events.numeric[k]
      result &= "  " & k & ": n=" & $s.count &
                " min=" & s.mn.formatFloat(ffDecimal, 3) &
                " mean=" & s.mean.formatFloat(ffDecimal, 3) &
                " p50=" & s.p50.formatFloat(ffDecimal, 3) &
                " p90=" & s.p90.formatFloat(ffDecimal, 3) &
                " p99=" & s.p99.formatFloat(ffDecimal, 3) &
                " max=" & s.mx.formatFloat(ffDecimal, 3) & "\n"
