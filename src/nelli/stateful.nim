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

import ./strategy, ./datasource, ./int128, ./choice, ./promise_store
export promise_store

const labelStateStep* = 2
  ## Opaque span label for one state-machine step.

type
  Rule*[S] = object
    name*: string
    precondition*: proc(s: S): bool {.closure.}   ## nil = always enabled
    runStep*: proc(s: var S, src: var DataSource) {.closure.}

  StateMachine*[S] = object
    initial*: Strategy[S]
      ## Strategy that produces a fresh starting state at the beginning of
      ## each generated example. For a fixed initial state, use
      ## `just(stateValue)`; for a varying seed (a random corpus item, an
      ## `arbitrary(S)`-derived value, etc.), pass any `Strategy[S]`. The
      ## initial-state draw is part of the recorded choice sequence so the
      ## shrinker minimizes it alongside the rule selections.
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

type
  Bundle*[S, V] = object
    ## A named pool of typed values that lives inside `S` (user-owned
    ## storage — bundles are just labels on existing `seq` fields, not a
    ## parallel engine-managed concept). A consuming rule reads the pool
    ## via `accessor`, draws a recorded index, and feeds that pool entry
    ## as the rule's argument. The rule is auto-disabled when the pool
    ## is empty, so "openFile → readFile" patterns work without manual
    ## preconditions.
    ##
    ## Why user-owned: the choice sequence determines `S`, and bundles
    ## are part of `S`. The shrinker / replay machinery doesn't need to
    ## know bundles exist; they're emergent from state.
    name*: string
    accessor*: proc(s: S): seq[V] {.closure.}

proc bundle*[S, V](name: string,
                   accessor: proc(s: S): seq[V] {.closure.}): Bundle[S, V] =
  ## Declare a bundle: a name plus an accessor that extracts the pool
  ## seq from the current `S`. The user writes to the bundle by mutating
  ## the underlying field in the action body — no separate "produces"
  ## API in the MVP; that channel is just direct field assignment.
  Bundle[S, V](name: name, accessor: accessor)

proc rule*[S, V](name: string, consumes: Bundle[S, V],
                 execute: proc(s: var S, v: V),
                 precondition: proc(s: S): bool = nil): Rule[S] =
  ## Build a rule whose argument is drawn from a bundle. The combined
  ## precondition is `(pool non-empty) AND (user precondition)`, so the
  ## rule never fires with an empty pool. The index drawn from the
  ## pool is recorded as an integer choice — the shrinker can pull
  ## the consumed entry toward the start of the pool just like any
  ## other integer draw.
  Rule[S](
    name: name,
    precondition: proc(s: S): bool =
      if consumes.accessor(s).len == 0: return false
      if precondition.isNil: return true
      precondition(s),
    runStep: proc(s: var S, src: var DataSource) =
      let pool = consumes.accessor(s)
      let idx = toInt64(src.drawInteger(
        toInt128(0), toInt128(pool.high), toInt128(0))).int
      execute(s, pool[idx]))

proc stateful*[S](sm: StateMachine[S], maxSteps = 50): Strategy[S] =
  ## A strategy that generates a sequence of state-machine operations and
  ## returns the resulting state. At each step, only rules whose precondition
  ## holds are eligible; an index draws one uniformly.
  newStrategy(proc(src: var DataSource): S =
    # #109 — install a fresh promise store for this example. Simple rules
    # don't touch it; symbolic rules (producingRule / consumingRule)
    # read and write it via `storeNow()`. Restoring the prior store
    # composes nested stateful examples correctly.
    let priorStore = storeNow()
    installPromiseStore(newPromiseStore())
    defer: installPromiseStore(priorStore)
    result = sm.initial.run(src)
    if not sm.invariant.isNil: sm.invariant(result)
    var steps = 0
    while steps < maxSteps:
      src.startSpan(labelStateStep)
      try:
        if not src.drawBoolean(0.9): break
        # Collect enabled rules in *this* state.
        var enabled: seq[int]
        for i, r in sm.rules:
          if r.precondition.isNil or r.precondition(result):
            enabled.add i
        if enabled.len == 0: break
        let pick = toInt64(src.drawInteger(
          toInt128(0), toInt128(enabled.high), toInt128(0))).int
        sm.rules[enabled[pick]].runStep(result, src)
        if not sm.invariant.isNil: sm.invariant(result)
        inc steps
      finally:
        # `try/finally` ensures the span closes even if the rule's
        # `execute` or the invariant raises an arbitrary CatchableError
        # — keeps the generation-mode `DataSource`'s spanStack invariant
        # intact for any post-mortem inspection.
        src.endSpan())
