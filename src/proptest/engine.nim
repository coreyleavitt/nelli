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
# Settings, Report[T], Outcome, Necessity, ParetoEntry, EventStats,
# ScoreMap, NumericSummary, FalsifiedError, DeadlineExceeded,
# defaultSettings — all extracted to engine/types.nim so the new
# pipeline phases (#119) can reference them without a circular
# import on engine.nim itself.
import ./engine/types
export types
import ./engine/frame
export frame
import ./engine/eval
export eval
import ./engine/pipeline
export pipeline

# Forward declarations: `runForAllPipeline` (defined alongside `forAll`
# in the middle of this file) calls `defaultPhases[T]()`, which is defined
# at the bottom alongside the phase implementations. Forward-declare so
# the middle of the file compiles without reordering the layout.
proc defaultPhases*[T](): seq[Phase[T]]

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

const
  maxSafeInt64Float* = 9223372036854774784.0
    ## `nextDown(2^63)` as an exact float64 — the largest float strictly
    ## below the int64 ceiling, used by `clampToInt64` to dodge the
    ## `float(high(int64))` rounding-up-by-one-ULP trap.

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

proc logScaledIntDeltas*(width: int64): seq[int64] =
  ## Log-scaled `±2^k` perturbation set for the hill-climb. `width` is
  ## the constraint range's width (`max - min`), used to bound `k`.
  ## Emitted big-to-small so a single sweep can cross a wide falsifying
  ## boundary before fine-tuning. The fixed `±{1,10,100,1000}` set this
  ## replaces was useless for ranges wider than ~10^4.
  if width <= 0: return @[]
  var k = 0
  while k < 62 and (1'i64 shl (k+1)) <= width:
    inc k
  while k >= 0:
    let d = 1'i64 shl k
    result.add d
    result.add -d
    dec k

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
  # `deltas` is computed per-Pareto-entry below from each choice's actual
  # constraint width, so a million-wide range proposes ±2^19, not ±1000.
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
          # `hi - lo` can overflow int64 (e.g. `low(int)..high(int)` is
          # ~2^64-1 wide). Do the subtraction in Int128 and saturate so
          # the delta generator picks the largest meaningful 2^k.
          let widthI128 = toInt128(hiI) - toInt128(loI)
          let width = if widthI128 > toInt128(high(int64)): high(int64)
                      else: toInt64(widthI128)
          for d in logScaledIntDeltas(width):
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


proc runForAllPipeline[T](db: ExampleDatabase, dbEnabled: bool,
                          s: Strategy[T], prop: proc(x: T),
                          settings: Settings,
                          explicit: seq[T]): Report[T] =
  ## The new pipeline-based runner. Constructs an `EngineSpec[T]`,
  ## pushes a fresh `EngineFrame`, applies the deadline-wrapping to
  ## `prop`, then iterates `defaultPhases[T]()` via `runPipeline`.
  ##
  ## Replaces the legacy `runForAllImpl`. The behavior is identical
  ## from the caller's perspective — the same `Report[T]` shape comes
  ## out — but every previously-monolithic step (DB reuse, explicit,
  ## random, targeted, shrink, explain, finalize) is now an
  ## independently-testable phase.
  var settings = settings
  if settings.derandomize:
    if settings.testId.len == 0:
      raise newException(ValueError,
        "Settings.derandomize=true requires a non-empty Settings.testId")
    settings.seed = cast[uint64](hash(settings.testId))
  engineStack.add EngineFrame()
  defer: discard engineStack.pop()
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
  let spec = EngineSpec[T](
    s: s, prop: prop, settings: settings,
    db: db, dbEnabled: dbEnabled, explicit: explicit)
  var state = initEngineState(spec)
  runPipeline(state, defaultPhases[T]())

proc forAll*[T](s: Strategy[T], prop: proc(x: T),
                settings = defaultSettings()): Report[T] =
  ## Check `prop` against values drawn from `s`. Deterministic in
  ## `settings.seed`. When `settings.testId` and `settings.dbPath` are
  ## both set, the reuse phase replays any DB-stored failure first; a
  ## fresh falsification is saved back to the directory-based DB.
  let db = directoryBasedDatabase(settings.dbPath)
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, @[])

proc forAllUsing*[T](db: ExampleDatabase, s: Strategy[T], prop: proc(x: T),
                     settings = defaultSettings()): Report[T] =
  ## Variant of `forAll` that runs against an explicitly-supplied DB
  ## backend. DB is enabled whenever `settings.testId` is non-empty.
  let dbEnabled = settings.testId.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, @[])

proc forAllWithExamples*[T](explicit: openArray[T], s: Strategy[T],
                            prop: proc(x: T),
                            settings = defaultSettings()): Report[T] =
  ## Run each value in `explicit` through `prop` before the random phase.
  ## Explicit examples are user-pinned regression seeds — the user said
  ## "this exact input matters," so we don't shrink them (no choice
  ## sequence to shrink) and report `choices: @[]` on failure.
  let db = directoryBasedDatabase(settings.dbPath)
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  runForAllPipeline(db, dbEnabled, s, prop, settings, @explicit)

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

# --- Reporter: built-in output formats --------------------------------------

type OutputFormat* = enum
  ## Selects how `renderReport` serializes a `Report`. The four formats
  ## cover the CI / tooling matrix: human-readable text (the default
  ## that `repro()` emits), structured JSON for downstream tooling,
  ## JUnit XML for the test-runner ecosystem, and GitHub Actions'
  ## `::error::` annotation format for inline PR comments.
  ofText, ofJson, ofJunit, ofGithubAnnotation

proc xmlEscape(s: string): string =
  result = newStringOfCap(s.len)
  for c in s:
    case c
    of '<': result.add "&lt;"
    of '>': result.add "&gt;"
    of '&': result.add "&amp;"
    of '"': result.add "&quot;"
    of '\'': result.add "&apos;"
    else: result.add c

proc jsonEscape(s: string): string =
  result = newStringOfCap(s.len + 2)
  for c in s:
    case c
    of '\\': result.add "\\\\"
    of '"':  result.add "\\\""
    of '\n': result.add "\\n"
    of '\r': result.add "\\r"
    of '\t': result.add "\\t"
    else:
      if ord(c) < 0x20: result.add "\\u00" & toHex(ord(c), 2).toLowerAscii
      else: result.add c

proc renderJson[T](r: Report[T]): string =
  result = "{"
  result &= "\"outcome\":\"" & $r.outcome & "\""
  result &= ",\"examples\":" & $r.examples
  result &= ",\"seed\":" & $r.seed
  if r.dbReplays > 0:
    result &= ",\"dbReplays\":" & $r.dbReplays
  if r.message.len > 0:
    result &= ",\"message\":\"" & jsonEscape(r.message) & "\""
  if r.counterexample.isSome or r.displayed.len > 0:
    result &= ",\"counterexample\":\"" &
              jsonEscape(displayCounterexample(r)) & "\""
  else:
    result &= ",\"counterexample\":null"
  if r.notes.len > 0:
    result &= ",\"notes\":["
    for i, n in r.notes:
      if i > 0: result &= ","
      result &= "{\"label\":\"" & jsonEscape(n[0]) &
                "\",\"value\":\"" & jsonEscape(n[1]) & "\"}"
    result &= "]"
  if r.dbErrors.len > 0:
    result &= ",\"dbErrors\":["
    for i, e in r.dbErrors:
      if i > 0: result &= ","
      result &= "\"" & jsonEscape(e) & "\""
    result &= "]"
  result &= "}"

proc renderJunit[T](r: Report[T], testName: string,
                    suiteName: string = "proptest"): string =
  let failures = if r.outcome in {otFalsified, otFlaky, otExhausted}: 1 else: 0
  result = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
  result &= "<testsuite name=\"" & xmlEscape(suiteName) &
            "\" tests=\"1\" failures=\"" & $failures & "\">\n"
  result &= "  <testcase name=\"" & xmlEscape(testName) & "\">\n"
  if failures > 0:
    let body = displayCounterexample(r) & "\n" & r.message
    result &= "    <failure message=\"" & xmlEscape(r.message) & "\">"
    result &= xmlEscape(body)
    result &= "</failure>\n"
  result &= "  </testcase>\n"
  result &= "</testsuite>\n"

proc renderGithub[T](r: Report[T], testName: string): string =
  ## `::error::` for failures, `::notice::` otherwise. Single line
  ## (GitHub Actions parses one annotation per line).
  let level = if r.outcome in {otFalsified, otFlaky, otExhausted}: "error"
              else: "notice"
  let cx = displayCounterexample(r)
  result = "::" & level & "::" & testName & " — " & $r.outcome &
           " (counterexample: " & cx & "; seed=" & $r.seed & ")"

proc renderReport*[T](r: Report[T], format = ofText,
                      testName = "property"): string =
  ## Serialize `r` in the chosen `format`. `ofText` matches `repro(r)`
  ## (kept as a separate proc for back-compat). `testName` is used by
  ## `ofJunit` (as the `<testcase>` name) and `ofGithubAnnotation`
  ## (as the message prefix); the text/JSON forms ignore it.
  case format
  of ofText:             repro(r)
  of ofJson:             renderJson(r)
  of ofJunit:            renderJunit(r, testName)
  of ofGithubAnnotation: renderGithub(r, testName)

# ============================================================================
# Pipeline phases (toward #119 — engine redesign as pluggable phase pipeline)
# ============================================================================
# Phases consume / mutate `EngineState[T]` (defined in engine/pipeline.nim).
# For session 1 of #119, only `finalizePhase` is implemented as a working
# phase; subsequent sessions add `randomPhase`, `shrinkPhase`, etc., and
# eventually switch `forAll` / `forAllUsing` to use `runPipeline` instead of
# the legacy `runForAllImpl`.
#
# Phases live in engine.nim for now because they need access to engine
# internals (`snapshotEvents`, `renderDisplayed`, `evalReplay`, `perturbations`).
# Once those internals are also extracted into sub-modules, phases move into
# their own files (`engine/phase_finalize.nim`, `engine/phase_random.nim`, …).

proc dbReusePhase*[T](state: var EngineState[T]): PhaseAction =
  ## Replay primary DB entries for `state.spec.settings.testId`. On the
  ## first entry that reproduces a falsification, set
  ## `state.output.rawFalsification` (with `fromPhase = "dbReuse"`) and
  ## `pcContinue` so `shrinkPhase` minimizes it. Stale entries (those
  ## that no longer falsify) are batched + pruned in one
  ## removeMany call to avoid N writes.
  ##
  ## Self-gates on rawFalsification.isNone (skips when an upstream
  ## source phase already produced one — though dbReuse is the first
  ## source phase, so in practice this guard is defense in depth).
  if state.output.rawFalsification.isSome: return pcContinue
  if not state.spec.dbEnabled: return pcContinue
  var primaryEntries: seq[seq[ChoiceNode]]
  try:
    primaryEntries = state.spec.db.loadPrimary(state.spec.settings.testId)
  except DbError as e:
    state.acc.dbErrors.add("loadPrimary: " & e.msg)
    if state.spec.settings.strictDb:
      state.output.finalReport = some(Report[T](
        outcome: otFalsified, examples: 0,
        message: "DB: loadPrimary: " & e.msg,
        seed: state.spec.settings.seed,
        dbReplays: 0,
        events: snapshotEvents(),
        printEvents: state.spec.settings.printEvents,
        dbErrors: state.acc.dbErrors))
      return pcTerminate
    return pcContinue

  var staleEntries: seq[seq[ChoiceNode]]
  for entry in primaryEntries:
    inc state.acc.dbReplays
    let r = evalReplay(state.spec.s, state.spec.prop, entry)
    case r.kind
    of ekFalsified:
      if staleEntries.len > 0:
        try: state.spec.db.removeMany(state.spec.settings.testId, staleEntries)
        except DbError as e: state.acc.dbErrors.add("removeMany: " & e.msg)
      state.output.rawFalsification = some(RawFalsification[T](
        value: r.fValue, choices: r.fChoices,
        message: r.fMsg, notes: r.fNotes,
        fromPhase: "dbReuse"))
      return pcContinue
    of ekPassed, ekRejected:
      staleEntries.add entry
  if staleEntries.len > 0:
    try: state.spec.db.removeMany(state.spec.settings.testId, staleEntries)
    except DbError as e: state.acc.dbErrors.add("removeMany: " & e.msg)
  pcContinue

proc explicitExamplesPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Run user-pinned regression seeds from `state.spec.explicit` before
  ## the random phase. An explicit failure short-circuits with
  ## `choices: @[]` (no shrinking on user-pinned values — the user said
  ## "this exact input matters") and a "from explicit example" message.
  ## Skips if a prior source phase (e.g. dbReuse) already produced a
  ## falsification.
  if state.output.rawFalsification.isSome: return pcContinue
  if state.spec.explicit.len == 0: return pcContinue
  for i, ex in state.spec.explicit:
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    template fail(reason: string): untyped =
      state.output.finalReport = some(Report[T](
        outcome: otFalsified, examples: i,
        counterexample: some(ex), choices: @[],
        message: "from explicit example #" & $i & " " & reason,
        seed: state.spec.settings.seed,
        dbReplays: state.acc.dbReplays,
        events: snapshotEvents(),
        printEvents: state.spec.settings.printEvents,
        dbErrors: state.acc.dbErrors))
      return pcTerminate
    try:
      state.spec.prop(ex)
    except Rejection:
      continue
    except FalsifiedError as e:
      fail(": " & e.msg)
    except CatchableError as e:
      fail("raised " & $e.name & ": " & e.msg)
    except Defect as e:
      fail("crashed: " & $e.name & ": " & e.msg)
  pcContinue

proc randomPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Self-gates: skip if an upstream source phase (dbReuse, explicit)
  ## already produced a falsification.
  if state.output.rawFalsification.isSome: return pcContinue
  ## Generate random inputs from `state.spec.s`, run the property, and
  ## either accumulate (passing examples, with their scores feeding the
  ## Pareto front) or short-circuit:
  ## - On falsification: set `state.output.rawFalsification` and
  ##   `pcContinue` so `shrinkPhase` processes it.
  ## - On rejection-budget exhaustion: set the final `otExhausted`
  ##   Report and `pcTerminate`.
  while state.acc.examplesDone < state.spec.settings.maxExamples:
    var ds = newDataSource(initSplitMix64(state.acc.master.next))
    var rejected = false
    var failMessage = ""
    var falsified = false
    var valueOpt: Option[T]
    currentFrame().scores.clear(); currentFrame().notes.setLen(0)
    try:
      let x = state.spec.s.generate(ds)
      valueOpt = some(x)
      state.spec.prop(x)
    except Rejection:
      rejected = true
    except FalsifiedError as e:
      falsified = true; failMessage = e.msg
    except CatchableError as e:
      falsified = true; failMessage = "raised " & $e.name & ": " & e.msg
    except Defect as e:
      falsified = true; failMessage = "crashed: " & $e.name & ": " & e.msg
    if falsified:
      state.output.rawFalsification = some(RawFalsification[T](
        value: valueOpt, choices: ds.recorded,
        message: failMessage, notes: currentFrame().notes,
        fromPhase: "random"))
      return pcContinue
    if rejected:
      inc state.acc.rejections
      if state.acc.rejections > state.spec.settings.maxRejections:
        state.output.finalReport = some(Report[T](
          outcome: otExhausted, examples: state.acc.examplesDone,
          seed: state.spec.settings.seed,
          paretoFront: state.acc.paretoFront,
          dbReplays: state.acc.dbReplays,
          events: snapshotEvents(),
          printEvents: state.spec.settings.printEvents,
          dbErrors: state.acc.dbErrors))
        return pcTerminate
      continue
    if currentFrame().scores.len > 0:
      let entry = ParetoEntry(scores: currentFrame().scores, choices: ds.recorded)
      insertPareto(state.acc.paretoFront, entry)
      updateRefPoint(state.acc.refPoint, entry.scores)
    inc state.acc.examplesDone
  pcContinue

proc shrinkPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Process `state.output.rawFalsification` if set:
  ## 1. Pre-shrink flaky retry pass (settings.flakyRetries iterations).
  ## 2. Shrinker to minimize the failing choice sequence.
  ## 3. Re-evalReplay on shrunk choices to capture the shrunk-example
  ##    note context (matches `Report.notes` semantics).
  ## 4. Post-shrink flaky check from `shrink.flaky`.
  ## 5. Persist to DB (when enabled and not flaky).
  ## Mutates `state.output` with the shrink results.
  ##
  ## No-op (returns `pcContinue`) when there's no falsification to process.
  if state.output.rawFalsification.isNone: return pcContinue
  let raw = state.output.rawFalsification.get

  # Step 1: pre-shrink flaky detect.
  var flakyRetryPassed = false
  for _ in 0 ..< state.spec.settings.flakyRetries:
    let e = evalReplay(state.spec.s, state.spec.prop, raw.choices)
    if e.kind == ekPassed:
      flakyRetryPassed = true
      break
  if flakyRetryPassed:
    state.output.isFlaky = true
    state.output.shrunkChoices = some(raw.choices)
    state.output.shrunkExample = raw.value
    state.output.shrunkNotes = raw.notes
    return pcContinue

  # Step 2-3: shrink + capture shrunk notes.
  let shrunk = shrink(state.spec.s, state.spec.prop, raw.choices,
                       state.spec.settings.maxShrinks)
  let shrunkEval = evalReplay(state.spec.s, state.spec.prop, shrunk.choices)
  let shrunkNotes = if shrunkEval.kind == ekFalsified: shrunkEval.fNotes
                    else: @[]

  state.output.shrunkChoices = some(shrunk.choices)
  state.output.shrunkExample = shrunk.example
  state.output.shrunkNotes = shrunkNotes
  state.output.isFlaky = shrunk.flaky

  # Step 5: DB persistence on the successfully-shrunk failure.
  if state.spec.dbEnabled and not shrunk.flaky:
    try:
      state.spec.db.save(state.spec.settings.testId, shrunk.choices)
    except DbError as e:
      state.acc.dbErrors.add("save: " & e.msg)
      if state.spec.settings.strictDb:
        state.output.finalReport = some(Report[T](
          outcome: otFalsified, examples: state.acc.examplesDone,
          counterexample: none(T), choices: @[],
          message: "DB: save: " & e.msg,
          seed: state.spec.settings.seed,
          dbReplays: state.acc.dbReplays,
          events: snapshotEvents(),
          printEvents: state.spec.settings.printEvents,
          dbErrors: state.acc.dbErrors))
        return pcTerminate
  pcContinue

proc targetedPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Hill-climb + simulated-annealing over the Pareto front built by
  ## `randomPhase`. Cross-run resumption: loads secondary corpus first
  ## to seed the front from prior runs.
  ##
  ## Implementation: wraps the existing `runTargetedPhase` with a
  ## capture-only callback that stores any falsification into
  ## `state.output.rawFalsification` for downstream `shrinkPhase` to
  ## process. The callback returns a placeholder Report that
  ## `runTargetedPhase` discards as `some(...)`; we ignore that and
  ## use the captured raw falsification instead.
  ##
  ## Self-gates: skip if a prior phase already falsified.
  if state.output.rawFalsification.isSome: return pcContinue

  # Cross-run resumption: seed the front from the secondary corpus
  # *before* the empty-front check — a saved Pareto front from a
  # previous run is reason to run targeting even if this run's random
  # phase didn't produce any scored examples (e.g., maxExamples = 0).
  if state.spec.dbEnabled:
    var secondaryEntries: seq[ScoredEntry]
    try:
      secondaryEntries = state.spec.db.loadSecondary(state.spec.settings.testId)
    except DbError as e:
      state.acc.dbErrors.add("loadSecondary: " & e.msg)
    for entry in secondaryEntries:
      var scores: ScoreMap
      if entry.scores.len > 0: scores = entry.scores
      else: scores[""] = entry.score
      insertPareto(state.acc.paretoFront,
                   ParetoEntry(scores: scores, choices: entry.choices))
      updateRefPoint(state.acc.refPoint, scores)

  if state.acc.paretoFront.len == 0: return pcContinue

  var captured: Option[RawFalsification[T]]
  proc captureCb(value: Option[T], choices: seq[ChoiceNode],
                 msg, prefix: string, ex: int,
                 originalNotes: seq[(string, string)]): Report[T] =
    captured = some(RawFalsification[T](
      value: value, choices: choices,
      message: msg, notes: originalNotes,
      fromPhase: "targeted"))
    Report[T](outcome: otFalsified)  # placeholder; not consumed

  let _ = runTargetedPhase(
    state.spec.s, state.spec.prop, state.spec.settings,
    state.spec.db, state.spec.dbEnabled,
    state.acc.master, state.acc.paretoFront, state.acc.refPoint,
    state.acc.examplesDone, captureCb)

  if captured.isSome:
    state.output.rawFalsification = captured
  pcContinue

proc explainPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Run the explain pass (per-choice necessity) when we have a
  ## non-flaky shrunken falsification. Skips when flaky (the shrunk
  ## example doesn't reliably reproduce, so necessity wouldn't be
  ## meaningful).
  if state.output.shrunkChoices.isNone or state.output.isFlaky:
    return pcContinue
  let raw = state.output.rawFalsification.get
  state.output.necessity = explain(state.spec.s, state.spec.prop,
                                    state.output.shrunkChoices.get,
                                    raw.message)
  pcContinue

proc finalizePhase*[T](state: var EngineState[T]): PhaseAction =
  ## Terminal phase: build the final Report from accumulated state.
  ## When upstream phases already set `finalReport` (e.g.,
  ## `randomPhase` on exhaustion, `shrinkPhase` on strict-DB error),
  ## this phase is a no-op.
  ##
  ## When a shrunken falsification is present, builds an `otFalsified`
  ## (or `otFlaky`) Report. Otherwise builds `otPassed`.
  ## See also `defaultPhases[T]()` for the canonical pipeline.
  if state.output.finalReport.isSome: return pcContinue
  if state.output.shrunkChoices.isSome and
     state.output.rawFalsification.isSome:
    let raw = state.output.rawFalsification.get
    let outcome = if state.output.isFlaky: otFlaky else: otFalsified
    let prefix =
      case raw.fromPhase
      of "dbReuse": "from DB"
      of "explicit": "from explicit example"
      of "targeted": "via target"
      else: ""
    let msgPrefix =
      if state.output.isFlaky:
        (if prefix.len > 0: "flaky (post-shrink) " & prefix & ": "
         else: "flaky (post-shrink): ")
      else:
        (if prefix.len > 0: prefix & ": " else: ": ")
    state.output.finalReport = some(Report[T](
      outcome: outcome,
      examples: state.acc.examplesDone,
      counterexample: state.output.shrunkExample,
      choices: state.output.shrunkChoices.get,
      message: msgPrefix & raw.message,
      seed: state.spec.settings.seed,
      paretoFront: state.acc.paretoFront,
      dbReplays: state.acc.dbReplays,
      notes: state.output.shrunkNotes,
      necessity: state.output.necessity,
      displayed: renderDisplayed(state.spec.s, state.output.shrunkExample),
      events: snapshotEvents(),
      printEvents: state.spec.settings.printEvents,
      dbErrors: state.acc.dbErrors))
    return pcContinue
  # Default: otPassed
  state.output.finalReport = some(Report[T](
    outcome: otPassed,
    examples: state.acc.examplesDone,
    seed: state.spec.settings.seed,
    paretoFront: state.acc.paretoFront,
    dbReplays: state.acc.dbReplays,
    events: snapshotEvents(),
    printEvents: state.spec.settings.printEvents,
    dbErrors: state.acc.dbErrors))
  pcContinue

proc defaultPhases*[T](): seq[Phase[T]] =
  ## The canonical PBT pipeline. Each entry is one phase, run in
  ## order; phases self-gate on state so the same list works for
  ## every kind of run (passing, falsifying, flaky, exhausted,
  ## DB-replayed, explicit-pinned, targeted).
  @[
    Phase[T](name: "dbReuse",  run: dbReusePhase[T]),
    Phase[T](name: "explicit", run: explicitExamplesPhase[T]),
    Phase[T](name: "random",   run: randomPhase[T]),
    Phase[T](name: "targeted", run: targetedPhase[T]),
    Phase[T](name: "shrink",   run: shrinkPhase[T]),
    Phase[T](name: "explain",  run: explainPhase[T]),
    Phase[T](name: "finalize", run: finalizePhase[T]),
  ]
