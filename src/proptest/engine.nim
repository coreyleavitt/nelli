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

import ./strategy, ./datasource, ./rng, ./choice, ./shrinker, ./db

type
  FalsifiedError* = object of CatchableError
    ## Raised by `ensure` when a property is violated.

  Settings* = object
    maxExamples*: int    ## how many valid examples to check before declaring success
    maxRejections*: int  ## rejection budget before giving up (otExhausted)
    seed*: uint64        ## master seed; the run is deterministic in it
    testId*: string      ## opaque ID for DB lookup; empty = DB disabled
    dbPath*: string      ## directory of the example DB; empty = DB disabled

  Outcome* = enum
    otPassed, otFalsified, otExhausted

  Report*[T] = object
    outcome*: Outcome
    examples*: int               ## valid examples checked
    counterexample*: T           ## meaningful when otFalsified
    choices*: seq[ChoiceNode]    ## the failing choice sequence (for shrinking/DB)
    message*: string             ## failure detail

func defaultSettings*(): Settings =
  Settings(maxExamples: 100, maxRejections: 1000, seed: 0x1234567890abcdef'u64)

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
    let stored = db.load(settings.testId)
    if stored.len > 0:
      let r = tryReplayStored(s, prop, stored)
      if r.falsified:
        return Report[T](outcome: otFalsified, examples: 0,
                         counterexample: r.x, choices: r.choices,
                         message: "from DB: " & r.msg)

  var master = initSplitMix64(settings.seed)
  var examples = 0
  var rejections = 0
  while examples < settings.maxExamples:
    var ds = newDataSource(initSplitMix64(master.next))
    var x: T
    var rejected = false
    var failMessage = ""
    var falsified = false
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
      # Hand the failing choice sequence to the shrinker for minimization.
      let shrunk = shrink(s, prop, ds.recorded)
      if dbEnabled:
        # Persist the (shrunk) failure so the next run reproduces it instantly.
        newExampleDB(settings.dbPath).save(settings.testId, shrunk.choices)
      return Report[T](outcome: otFalsified, examples: examples,
                       counterexample: shrunk.example, choices: shrunk.choices,
                       message: failMessage)
    if rejected:
      inc rejections
      if rejections > settings.maxRejections:
        return Report[T](outcome: otExhausted, examples: examples)
      continue
    inc examples
  Report[T](outcome: otPassed, examples: examples)
