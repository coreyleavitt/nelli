## Stateful (rule-based) testing.
##
## A `StateMachine[S]` is an initial state plus a set of rules; each rule has
## an argument strategy, an execute proc, and an optional precondition. The
## `stateful` strategy generates a sequence of (rule, args) operations and
## returns the resulting final state — so `forAll(stateful(sm), invariant)`
## tests the invariant on whatever state any valid command sequence produces.
##
## Each step is wrapped in a span, so the shrinker drops a single command with
## one contiguous deletion (and can also lex-lower rule indices and arguments).
## The whole system is just a strategy on top of the existing engine — no
## special stateful runner.

import ./strategy, ./datasource, ./int128, ./choice

const labelStateStep* = 2
  ## Opaque span label for one state-machine step.

type
  Rule*[S] = object
    name*: string
    precondition*: proc(s: S): bool {.closure.}   ## nil = always enabled
    runStep*: proc(s: var S, src: var DataSource) {.closure.}

  StateMachine*[S] = object
    initial*: S
    rules*: seq[Rule[S]]
    invariant*: proc(s: S) {.closure.}
      ## Optional per-step check (e.g., `ensure s.count >= 0`). Called once on
      ## the initial state and after each rule fires. A raise (typically
      ## `FalsifiedError` from `ensure`) propagates and `forAll` reports the
      ## offending command sequence as a falsification — so an invariant
      ## violation is caught even when the final state recovers.

proc rule*[S, A](name: string, strat: Strategy[A],
                 execute: proc(s: var S, args: A),
                 precondition: proc(s: S): bool = nil): Rule[S] =
  ## Build a rule from an argument strategy, an executor, and an optional
  ## precondition (nil = always enabled).
  Rule[S](
    name: name,
    precondition: precondition,
    runStep: proc(s: var S, src: var DataSource) =
      let args = strat.run(src)
      execute(s, args))

proc stateful*[S](sm: StateMachine[S], maxSteps = 50): Strategy[S] =
  ## A strategy that generates a sequence of state-machine operations and
  ## returns the resulting state. At each step, only rules whose precondition
  ## holds are eligible; an index draws one uniformly.
  newStrategy(proc(src: var DataSource): S =
    result = sm.initial
    if not sm.invariant.isNil: sm.invariant(result)
    var steps = 0
    while steps < maxSteps:
      src.startSpan(labelStateStep)
      if not src.drawBoolean(0.9):
        src.endSpan()
        break
      # Collect enabled rules in *this* state.
      var enabled: seq[int]
      for i, r in sm.rules:
        if r.precondition.isNil or r.precondition(result):
          enabled.add i
      if enabled.len == 0:
        src.endSpan()
        break
      let pick = toInt64(src.drawInteger(
        toInt128(0), toInt128(enabled.high), toInt128(0))).int
      sm.rules[enabled[pick]].runStep(result, src)
      if not sm.invariant.isNil: sm.invariant(result)
      src.endSpan()
      inc steps)
