## The property runner.
##
## `forAll` generates up to `maxExamples` values from a strategy and checks the
## property against each, classifying every example as pass, falsified, or
## rejected (`assume`/filter). It returns a `Report` rather than raising, so it
## composes; the test-framework adapter (later) turns a falsified report into a
## single unittest failure.
##
## Shrinking is *not* here — this runner reports the first failing example as-is.
## Minimizing it is the shrinker's job (M4), which will re-run the property over
## reduced versions of `Report.choices`.

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

  Outcome* = enum
    otPassed, otFalsified, otExhausted, otFlaky

  Report*[T] = object
    outcome*: Outcome
    examples*: int               ## valid examples checked
    counterexample*: T           ## meaningful when otFalsified
    choices*: seq[ChoiceNode]    ## the failing choice sequence (for shrinking/DB)
    message*: string             ## failure detail
    seed*: uint64                ## the master seed `forAll` ran with

func defaultSettings*(): Settings =
  Settings(maxExamples: 100, maxRejections: 1000,
           seed: 0x1234567890abcdef'u64, flakyRetries: 5,
           maxShrinks: 500)

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

# --- targeted PBT: a score the engine tries to maximize ---------------------

var targetedScore*: float = 0.0
var targetedSet*: bool = false

proc target*(score: float) =
  ## Within a property, declare a numeric score the engine should try to
  ## maximize. After the random-generation phase, a brief hill-climb on the
  ## choice sequence pushes the best-scored example higher; if a perturbation
  ## falsifies the property, that's the counterexample.
  targetedScore = score
  targetedSet = true

proc tryReplayStored[T](s: Strategy[T], prop: proc(x: T),
                        stored: seq[ChoiceNode]
                       ): tuple[falsified: bool, x: T,
                                choices: seq[ChoiceNode], msg: string] =
  ## Replay a stored choice sequence through `s` and check `prop`. Returns
  ## whether it still falsifies (so the engine can short-circuit on DB hits).
  var rep = newReplaySource(stored)
  var x: T
  try:
    x = s.generate(rep)
  except Rejection, Overrun:
    return (false, x, rep.recorded, "")
  except FalsifiedError as e:
    return (true, x, rep.recorded, e.msg)
  except CatchableError as e:
    return (true, x, rep.recorded, $e.name & ": " & e.msg)
  except Defect as e:
    return (true, x, rep.recorded, "crashed: " & $e.name & ": " & e.msg)
  try:
    prop(x); (false, x, rep.recorded, "")
  except Rejection:
    (false, x, rep.recorded, "")
  except FalsifiedError as e:
    (true, x, rep.recorded, e.msg)
  except CatchableError as e:
    (true, x, rep.recorded, $e.name & ": " & e.msg)
  except Defect as e:
    (true, x, rep.recorded, "crashed: " & $e.name & ": " & e.msg)

proc forAll*[T](s: Strategy[T], prop: proc(x: T),
                settings = defaultSettings()): Report[T] =
  ## Check `prop` against values drawn from `s`. Deterministic in `settings.seed`.
  ## When `settings.testId` and `settings.dbPath` are set, the reuse phase
  ## replays any DB-stored failure first; a fresh falsification is saved back.
  let dbEnabled = settings.testId.len > 0 and settings.dbPath.len > 0
  if dbEnabled:
    let db = newExampleDB(settings.dbPath)
    for entry in db.loadPrimary(settings.testId):
      let r = tryReplayStored(s, prop, entry)
      if r.falsified:
        # Re-shrink under the *current* property — the stored sequence may be
        # stale (the property may have tightened) or never have been minimal
        # (e.g. pre-staged). Persist the re-shrunk version.
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
      # Stored entry no longer reproduces — auto-prune so the DB stays useful.
      db.remove(settings.testId, entry)

  var master = initSplitMix64(settings.seed)
  var examples = 0
  var rejections = 0
  var bestScore = NegInf
  var bestChoices: seq[ChoiceNode]
  while examples < settings.maxExamples:
    var ds = newDataSource(initSplitMix64(master.next))
    var x: T
    var rejected = false
    var failMessage = ""
    var falsified = false
    targetedSet = false
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
      # A crash (IndexDefect, OverflowDefect, nil deref, …) is a real bug, so
      # it falsifies the property. Catching Defects relies on the default
      # `--panics:off`; under `--panics:on` such a crash aborts instead.
      falsified = true; failMessage = "crashed: " & $e.name & ": " & e.msg
    if falsified:
      # Confirm the failure is reproducible before shrinking — re-running a
      # flaky property would produce nonsense minimal examples. We **replay
      # the whole strategy+prop pipeline** through the recorded choice
      # sequence so non-determinism on either side (a strategy that raises
      # only sometimes, or a prop that does) is caught; any retry that
      # reaches a normal return means the failure isn't deterministic.
      var flakyRetryPassed = false
      for _ in 0 ..< settings.flakyRetries:
        var rep = newReplaySource(ds.recorded)
        try:
          let xRep = s.generate(rep)
          prop(xRep)
          flakyRetryPassed = true
          break
        except CatchableError, Defect:
          discard  # still raising — that's the consistent case
      if flakyRetryPassed:
        return Report[T](outcome: otFlaky, examples: examples,
                         counterexample: x, choices: ds.recorded,
                         message: "flaky: " & failMessage,
                         seed: settings.seed)
      # Hand the failing choice sequence to the shrinker for minimization.
      let shrunk = shrink(s, prop, ds.recorded, settings.maxShrinks)
      if shrunk.flaky:
        return Report[T](outcome: otFlaky, examples: examples,
                         counterexample: shrunk.example, choices: shrunk.choices,
                         message: "flaky (post-shrink): " & failMessage,
                         seed: settings.seed)
      if dbEnabled:
        # Persist the (shrunk) failure so the next run reproduces it instantly.
        newExampleDB(settings.dbPath).save(settings.testId, shrunk.choices)
      return Report[T](outcome: otFalsified, examples: examples,
                       counterexample: shrunk.example, choices: shrunk.choices,
                       message: failMessage,
                       seed: settings.seed)
    if rejected:
      inc rejections
      if rejections > settings.maxRejections:
        return Report[T](outcome: otExhausted, examples: examples,
                         seed: settings.seed)
      continue
    if targetedSet and targetedScore > bestScore:
      bestScore = targetedScore
      bestChoices = ds.recorded
    inc examples

  # --- cross-run resumption: seed from the secondary corpus ---
  # If a previous run saved a higher-scored non-failing example for this test,
  # let it serve as the hill-climb starting point so targeting resumes where it
  # left off across runs (otherwise target() is amnesiac).
  if dbEnabled:
    let db = newExampleDB(settings.dbPath)
    for entry in db.loadSecondary(settings.testId):
      if entry.score > bestScore:
        bestScore = entry.score
        bestChoices = entry.choices
        break  # secondary is sorted highest-first; first is the best seed
  # --- targeted hill-climb after the random phase ---
  if bestChoices.len > 0:
    # Big steps first: a +1 happens to "improve" any monotone score, and breaking
    # on the first improvement would stall on tiny gains and never try the wide
    # jumps that cross the falsifying boundary.
    const deltas = [int64(1000), -1000, 100, -100, 10, -10, 1, -1]
    var best = bestChoices
    var bestS = bestScore
    var iter = 0
    while iter < 50:
      var improved = false
      for i in 0 ..< best.len:
        if best[i].kind != ckInteger: continue
        let nv = best[i].intVal
        let lo = best[i].intC.min
        let hi = best[i].intC.max
        # Only handle int64-fitting values (the common case for native draws).
        proc fits(x: Int128): bool =
          (x.hi == 0 and x.lo <= uint64(high(int64))) or x.hi == -1
        if not (fits(nv) and fits(lo) and fits(hi)): continue
        let baseVal = toInt64(nv)
        let loI = toInt64(lo)
        let hiI = toInt64(hi)
        for d in deltas:
          let candVal = baseVal + d
          if candVal < loI or candVal > hiI: continue
          var cand = best
          cand[i].intVal = toInt128(candVal)
          # Replay and check.
          var rep = newReplaySource(cand)
          var xCand: T
          var hcFailMsg = ""
          var hcFailed = false
          targetedSet = false
          try:
            xCand = s.generate(rep)
            prop(xCand)
          except Rejection, Overrun:
            continue
          except FalsifiedError as e:
            hcFailed = true; hcFailMsg = e.msg
          except CatchableError as e:
            hcFailed = true; hcFailMsg = "raised " & $e.name & ": " & e.msg
          except Defect as e:
            hcFailed = true; hcFailMsg = "crashed: " & $e.name & ": " & e.msg
          if hcFailed:
            let shrunk = shrink(s, prop, rep.recorded, settings.maxShrinks)
            if shrunk.flaky:
              return Report[T](outcome: otFlaky, examples: examples,
                               counterexample: shrunk.example,
                               choices: shrunk.choices,
                               message: "flaky via target: " & hcFailMsg,
                               seed: settings.seed)
            if dbEnabled:
              newExampleDB(settings.dbPath).save(settings.testId, shrunk.choices)
            return Report[T](outcome: otFalsified, examples: examples,
                             counterexample: shrunk.example,
                             choices: shrunk.choices,
                             message: "via target: " & hcFailMsg,
                             seed: settings.seed)
          if targetedSet and targetedScore > bestS:
            best = cand
            bestS = targetedScore
            improved = true
            break
        if improved: break
      if not improved: break
      inc iter
    # Propagate hill-climb's gains back out so secondary-corpus save sees them.
    bestChoices = best
    bestScore = bestS

  # No falsification, but we may have a high-scoring example worth saving to
  # the secondary corpus so the next run's hill-climb resumes from there.
  if dbEnabled and bestChoices.len > 0 and bestScore != NegInf:
    newExampleDB(settings.dbPath).saveSecondary(
      settings.testId, bestChoices, bestScore)

  Report[T](outcome: otPassed, examples: examples, seed: settings.seed)

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
