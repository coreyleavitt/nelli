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

import std/[math, tables, sets]
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

  Outcome* = enum
    otPassed, otFalsified, otExhausted, otFlaky

  ScoreMap* = Table[string, float]
    ## A targeted example's score, keyed by label. Empty when the property
    ## made no `target()` calls.

  ParetoEntry* = object
    scores*: ScoreMap
    choices*: seq[ChoiceNode]

  Report*[T] = object
    outcome*: Outcome
    examples*: int               ## valid examples checked
    counterexample*: T           ## meaningful when otFalsified
    choices*: seq[ChoiceNode]    ## the failing choice sequence (for shrinking/DB)
    message*: string             ## failure detail
    seed*: uint64                ## the master seed `forAll` ran with
    paretoFront*: seq[ParetoEntry]
      ## non-dominated examples seen during targeted search; empty when no
      ## `target()` calls were made

func defaultSettings*(): Settings =
  Settings(maxExamples: 100, maxRejections: 1000,
           seed: 0x1234567890abcdef'u64, flakyRetries: 5,
           maxShrinks: 500, useSA: true, targetedSAIters: 200)

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

# --- targeted PBT: a label-keyed score the engine tries to maximize ---------

var targetedScores {.threadvar.}: ScoreMap
  ## Per-example score map — **thread-local** so concurrent test runners
  ## (e.g. `testament -j N`, `--threads:on`) don't race on a shared global.
  ## Reset by the engine before each `prop` invocation; the property writes
  ## into it via `target(score, label)`. Not exported: the only legitimate
  ## reader is `forAll`, the only writer `target`.

proc target*(score: float, label: string = "") =
  ## Within a property, declare a numeric `score` for an objective named
  ## `label` ("" is the default-objective label). Multiple labels per example
  ## are allowed and tracked as a multi-objective Pareto front; the engine
  ## tries to maximize each label.
  ##
  ## NaN is silently coerced to `NegInf` (and a stderr warning is emitted)
  ## because NaN evades Pareto-dominance comparisons (`NaN < x` is always
  ## false), which would let NaN-scored examples accumulate unboundedly and
  ## displace genuinely good ones. Treat "undefined" as "worst" — the engine
  ## then ignores or evicts the example just like any other low-score one.
  if score != score:
    stderr.writeLine "proptest: target(\"" & label &
                     "\") received NaN; treating as -Inf"
    targetedScores[label] = NegInf
  else:
    targetedScores[label] = score

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
    fValue: T
    fChoices: seq[ChoiceNode]
    fMsg: string
  of ekRejected: discard

proc evalReplay[T](s: Strategy[T], prop: proc(x: T),
                   candidate: seq[ChoiceNode]): Eval[T] =
  ## Replay a candidate through the strategy and check the property. Returns
  ## the verdict + (for passes) any score map and the canonicalized choice
  ## sequence. Used by both hill-climb and SA.
  var ds = newReplaySource(candidate)
  var x: T
  targetedScores.clear()
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return Eval[T](kind: ekRejected)
  except FalsifiedError as e:
    return Eval[T](kind: ekFalsified, fValue: x, fChoices: ds.recorded, fMsg: e.msg)
  except CatchableError as e:
    return Eval[T](kind: ekFalsified, fValue: x, fChoices: ds.recorded,
                   fMsg: $e.name & ": " & e.msg)
  except Defect as e:
    return Eval[T](kind: ekFalsified, fValue: x, fChoices: ds.recorded,
                   fMsg: "crashed: " & $e.name & ": " & e.msg)
  try:
    prop(x)
    Eval[T](kind: ekPassed, value: x, scores: targetedScores, choices: ds.recorded)
  except Rejection:
    Eval[T](kind: ekRejected)
  except FalsifiedError as e:
    Eval[T](kind: ekFalsified, fValue: x, fChoices: ds.recorded, fMsg: e.msg)
  except CatchableError as e:
    Eval[T](kind: ekFalsified, fValue: x, fChoices: ds.recorded,
            fMsg: $e.name & ": " & e.msg)
  except Defect as e:
    Eval[T](kind: ekFalsified, fValue: x, fChoices: ds.recorded,
            fMsg: "crashed: " & $e.name & ": " & e.msg)

proc tryReplayStored[T](s: Strategy[T], prop: proc(x: T),
                        stored: seq[ChoiceNode]
                       ): tuple[falsified: bool, x: T,
                                choices: seq[ChoiceNode], msg: string] =
  ## Compat wrapper used by the DB-reuse phase — same fail semantics as the
  ## original implementation.
  let e = evalReplay(s, prop, stored)
  case e.kind
  of ekFalsified: (true, e.fValue, e.fChoices, e.fMsg)
  of ekPassed: (false, e.value, e.choices, "")
  of ekRejected:
    var x: T
    (false, x, stored, "")

# --- helpers for hill-climb / SA -------------------------------------------

const
  maxSafeInt64Float* = 9223372036854774784.0
    ## `nextDown(2^63)` as an exact float64 — the largest float strictly
    ## below `2^63`. `int64(this)` is well-defined; `int64(2^63.0)` is UB.

proc clampToInt64*(candF: float, lo, hi: int64): int64 =
  ## Clamp a float candidate to `[lo, hi]` in int64 space, snapping the upper
  ## bound to a float strictly below `2^63.0` when `hi == high(int64)`. The
  ## obvious `int64(clamp(candF, lo.float, hi.float))` wraps to `low(int64)`
  ## when `candF >= 2^63.0`, because `float(high(int64))` rounds up one ULP
  ## past the int64 max and `int64()` of that is undefined. We lose at most
  ## `2^11 = 2048` representable values at the very top — noise compared to
  ## the int64 range. NaN inputs are treated as "out of range" and map to
  ## `lo` so the cast is total.
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

# --- the property runner ---------------------------------------------------

proc forAll*[T](s: Strategy[T], prop: proc(x: T),
                settings = defaultSettings()): Report[T] =
  ## Check `prop` against values drawn from `s`. Deterministic in `settings.seed`.
  ## When `settings.testId` and `settings.dbPath` are set, the reuse phase
  ## replays any DB-stored failure first; a fresh falsification is saved back.
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  let db = newExampleDB(settings.dbPath)  # cheap value-wrapper; reused throughout
  if dbEnabled:
    for entry in db.loadPrimary(settings.testId):
      let r = tryReplayStored(s, prop, entry)
      if r.falsified:
        let shrunk = shrink(s, prop, r.choices, settings.maxShrinks)
        if shrunk.flaky:
          return Report[T](outcome: otFlaky, examples: 0,
                           counterexample: shrunk.example, choices: shrunk.choices,
                           message: "flaky from DB: " & r.msg,
                           seed: settings.seed)
        db.save(settings.testId, shrunk.choices)
        return Report[T](outcome: otFalsified, examples: 0,
                         counterexample: shrunk.example, choices: shrunk.choices,
                         message: "from DB: " & r.msg,
                         seed: settings.seed)
      db.remove(settings.testId, entry)

  var master = initSplitMix64(settings.seed)
  var examples = 0
  var rejections = 0
  var paretoFront: seq[ParetoEntry]
  var refPoint: ScoreMap

  proc handleFalsification(value: T, choices: seq[ChoiceNode],
                           msg, prefix: string, ex: int): Report[T] =
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
                       seed: settings.seed, paretoFront: paretoFront)
    let shrunk = shrink(s, prop, choices, settings.maxShrinks)
    if shrunk.flaky:
      return Report[T](outcome: otFlaky, examples: ex,
                       counterexample: shrunk.example, choices: shrunk.choices,
                       message: "flaky (post-shrink)" & prefix & ": " & msg,
                       seed: settings.seed, paretoFront: paretoFront)
    if dbEnabled:
      db.save(settings.testId, shrunk.choices)
    Report[T](outcome: otFalsified, examples: ex,
              counterexample: shrunk.example, choices: shrunk.choices,
              message: prefix & ": " & msg, seed: settings.seed,
              paretoFront: paretoFront)

  # --- random-generation phase --------------------------------------------
  while examples < settings.maxExamples:
    var ds = newDataSource(initSplitMix64(master.next))
    var x: T
    var rejected = false
    var failMessage = ""
    var falsified = false
    targetedScores.clear()
    try:
      x = s.generate(ds)
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
      return handleFalsification(x, ds.recorded, failMessage, "", examples)
    if rejected:
      inc rejections
      if rejections > settings.maxRejections:
        return Report[T](outcome: otExhausted, examples: examples,
                         seed: settings.seed, paretoFront: paretoFront)
      continue
    if targetedScores.len > 0:
      let entry = ParetoEntry(scores: targetedScores, choices: ds.recorded)
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
                     seed: settings.seed)

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
          let nv = base.choices[cIdx].intVal
          let lo = base.choices[cIdx].intC.min
          let hi = base.choices[cIdx].intC.max
          if not (fitsInt64(nv) and fitsInt64(lo) and fitsInt64(hi)): continue
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
              return handleFalsification(e.fValue, e.fChoices, e.fMsg,
                                         " via target", examples)
            of ekPassed:
              if e.scores.len == 0: continue
              let before = paretoFront.len
              insertPareto(paretoFront, ParetoEntry(scores: e.scores,
                                                    choices: e.choices))
              updateRefPoint(refPoint, e.scores)
              if paretoFront.len != before or paretoFront[^1].scores != base.scores:
                improved = true
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
            return handleFalsification(e.fValue, e.fChoices, e.fMsg,
                                       " via SA", examples)
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

  Report[T](outcome: otPassed, examples: examples,
            seed: settings.seed, paretoFront: paretoFront)

proc repro*[T](r: Report[T]): string =
  ## Format a `Report` as a multi-line, copy-pasteable repro string suitable
  ## for failure logs or bug reports. Always includes outcome, examples, and
  ## seed; on falsifying/flaky outcomes it also includes the counterexample,
  ## any failure message, and the rendered choice sequence.
  result = "outcome=" & $r.outcome & "\n"
  result &= "examples=" & $r.examples & "\n"
  result &= "seed=" & $r.seed & "\n"
  if r.outcome in {otFalsified, otFlaky}:
    result &= "counterexample=" & $r.counterexample & "\n"
    if r.message.len > 0:
      result &= "message=" & r.message & "\n"
    if r.choices.len > 0:
      result &= "choices=" & $r.choices & "\n"
