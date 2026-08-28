## Targeted PBT: Pareto front + greedy hill-climb + simulated-annealing.
##
## A deep module: ~400 LOC of multi-objective search hidden behind one
## entry point (`targetedPhase`, the uniform `proc(state: var
## EngineState[T]): PhaseAction` every pipeline phase implements — see
## `engine/pipeline.nim`). Also exposes pure helpers (`dominates`,
## `insertPareto`, `logScaledIntDeltas`, `perturbations`, `explain`)
## that are independently useful and testable.
##
## `logScaledIntDeltas` (the hill-climb's ±2^k perturbation set) is
## re-exported from `nelli/intdeltas` (RFC-fuzzer-nextgen U1) — the fuzz
## adapter's `fuzzir.nim` draws mutants from the SAME kernel now, rather
## than an independently-maintained duplicate. It stayed here as a
## deliberately re-exported name rather than a bare import so no caller
## of `logScaledIntDeltas` via `import nelli` needed to change.
##
## The targeting algorithm itself: from each Pareto front member, run
## (a) Pareto-aware greedy hill-climb with log-scaled `±2^k` integer
## perturbations and (b) simulated-annealing escape with Cauchy-
## distributed proposals + augmented-Tchebycheff acceptance.
## Falsifications discovered during either pass become `RawFalsification`
## records for the shrink phase to process.

import std/[math, tables, sets, options, hashes]
import ../strategy, ../datasource, ../rng, ../choice, ../shrinker, ../db, ../int128, ../optbox
import ../intdeltas
export intdeltas
import ./types, ./frame, ./eval, ./render, ./pipeline

# Make `Eval` constructors / fields visible to expressions in this file.
# `evalReplay` returns `Eval[T]`; the targeting code reads `.kind` and
# the per-variant fields.

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

proc insertPareto*(front: var seq[ParetoEntry],
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

proc updateRefPoint*(refPoint: var ScoreMap, scores: ScoreMap) =
  ## refPoint[label] = max(refPoint[label], scores[label]) + small epsilon
  ## (so Tchebycheff distances are well-defined and strictly positive at
  ## the ideal frontier).
  for k, v in scores:
    let cur = refPoint.getOrDefault(k, NegInf)
    if v > cur:
      refPoint[k] = v

proc bumpedRef*(refPoint: ScoreMap, eps: float): ScoreMap =
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

proc targetedPhase*[T](state: var EngineState[T]): PhaseAction =
  ## Hill-climb + simulated-annealing over the Pareto front built by
  ## `randomPhase`, then a secondary-corpus save. Cross-run resumption:
  ## loads the secondary corpus first to seed the front from prior runs.
  ##
  ## Same uniform one-parameter signature as every other phase (see
  ## `engine/pipeline.nim`'s `Phase[T]`) — no adapter, no capture
  ## callback. A falsification found during the climb or SA is written
  ## straight to `state.output.rawFalsification` and the phase returns
  ## `pcContinue` so `shrinkPhase` processes it, exactly like
  ## `randomPhase` does. This phase never terminates the pipeline
  ## itself (`pcTerminate`).
  ##
  ## Self-gates: skip if a prior phase already falsified.
  if state.output.rawFalsification.isSome: return pcContinue

  template s: untyped = state.spec.s
  template prop: untyped = state.spec.prop
  template settings: untyped = state.spec.settings
  template paretoFront: untyped = state.acc.paretoFront
  template refPoint: untyped = state.acc.refPoint
  template master: untyped = state.acc.master

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
      insertPareto(paretoFront, ParetoEntry(scores: scores, choices: entry.choices))
      updateRefPoint(refPoint, scores)

  if paretoFront.len == 0: return pcContinue

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
              state.output.rawFalsification = some(RawFalsification[T](
                value: e.fValue, choices: e.fChoices,
                message: e.fMsg, notes: e.fNotes,
                fromPhase: "targeted", crash: e.fCrash))
              return pcContinue
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
            state.output.rawFalsification = some(RawFalsification[T](
              value: e.fValue, choices: e.fChoices,
              message: e.fMsg, notes: e.fNotes,
              fromPhase: "targeted", crash: e.fCrash))
            return pcContinue
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
  if state.spec.dbEnabled and paretoFront.len > 0:
    var batch: seq[ScoredEntry]
    for entry in paretoFront:
      var summary = NegInf
      for v in entry.scores.values:
        if v > summary: summary = v
      if summary == NegInf: summary = 0.0
      batch.add (choices: entry.choices, score: summary, scores: entry.scores)
    state.spec.db.saveSecondary(settings.testId, batch)

  pcContinue

# --- the property runner ---------------------------------------------------


proc perturbations*(node: ChoiceNode): seq[ChoiceNode] =
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

proc explain*[T](s: Strategy[T], prop: proc(x: T),
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
