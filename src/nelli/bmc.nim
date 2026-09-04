## Bounded model checking for stateful machines (#113).
##
## **Verification, not bug-finding.** `stateful(sm)` samples one random
## plan per example; `bmcCheck` enumerates every enabled rule firing at
## each reachable state, breadth-first, up to a fixed depth. A
## successful run produces the verification claim "the invariant holds
## for every plan of length ≤ maxDepth from the given initial state."
##
## **v1 scope.** Arg strategies are *sampled* per branch with a
## deterministic seed derived from the plan path, not enumerated. For
## true exhaustive coverage, use rules whose arg strategy is `just(...)`
## or otherwise deterministic — the random fall-back stays correct
## (deterministic per-plan) but doesn't sweep the arg domain.
##
## **Symbolic refs.** Out of scope for v1: `bmcCheck` does *not* install
## a `PromiseStore`, so any `consumingRule` or `producingRule` will see
## `storeNow() == nil` and have its precondition refuse. Use the
## pre-#109 `rule[S, A]` / `rule[S, V](consumes = Bundle)` model with
## BMC; symbolic-ref BMC is a follow-up.

import std/[options, hashes, sets, tables]
import ./strategy, ./datasource, ./stateful, ./rng

type
  BmcOutcome* = enum
    bmcVerified,         ## frontier exhausted; no invariant violation
    bmcFalsified,        ## found a plan that violates the invariant
    bmcExhaustedBudget   ## hit maxStates before either above

  BmcStep* = object
    ## One step of an executed plan: the rule that fired (by name).
    ## Arg values aren't preserved in v1 — they're sampled per-branch
    ## with deterministic seeds; the (planPath, depth) tuple is
    ## sufficient to replay the exact sequence.
    ruleName*: string

  BmcResult*[S] = object
    outcome*: BmcOutcome
    depthReached*: int
      ## Maximum depth actually visited before termination.
    statesExplored*: int
      ## Frontier expansions performed. Equal to the BFS frontier size
      ## counted as states are popped; `< maxStates`.
    counterexample*: Option[seq[BmcStep]]
      ## The first invariant-violating plan found (BFS guarantees
      ## shortest-such by step count).
    finalState*: Option[S]
      ## State produced by the counterexample plan, when one was found.

  BmcSettings* = object
    ## Non-generic so users can write `BmcSettings(maxDepth: 5)` as an object
    ## literal without spelling the state type.
    ##
    ## RFC-0010: that advice used to be a trap. The literal above left
    ## `maxStates` at 0, and `explored >= settings.maxStates` returned
    ## `bmcExhaustedBudget` before expanding a single state -- so following
    ## this comment produced a verification run that verified nothing. The
    ## defaults are declared on the fields now, and 0 means *unlimited* on
    ## both caps (the convention `ResourceBudget` already uses), so an
    ## explicit zero says something a caller might deliberately want instead
    ## of the worst possible reading.
    ##
    ## These bound a verification CLAIM: `bmcVerified` means "the invariant
    ## holds for every plan up to `maxDepth`", so the depth is part of what a
    ## green run asserts. 5 is a starting point, not a guarantee -- raise it
    ## when the claim needs to be stronger.
    maxDepth*: int = 5
      ## Plan-length cap. Frontier states past this depth aren't
      ## expanded. 0 = unlimited (bounded then only by `maxStates`).
    maxStates*: int = 1000
      ## Hard cap on frontier expansions. Hitting this terminates with
      ## `bmcExhaustedBudget`. 0 = unlimited.

proc bmcCheck*[S](sm: StateMachine[S],
                  initial: S,
                  invariant: proc(s: S): bool,
                  settings: BmcSettings,
                  stateHash: proc(s: S): Hash = nil): BmcResult[S] =
  ## Breadth-first state-space search up to `settings.maxDepth` from
  ## `initial`. Returns the verification verdict + (on falsification)
  ## the shortest counterexample plan.
  type Frontier = object
    state: S
    plan: seq[BmcStep]
  var frontier: seq[Frontier] = @[Frontier(state: initial, plan: @[])]
  var visited = initHashSet[Hash]()
  var head = 0  # popping from a seq via incrementing head; cheaper than del
  var explored = 0
  var depthSeen = 0

  # Check the invariant on the initial state first. A 0-depth violation
  # is still a counterexample (the empty plan falsifies).
  if not invariant(initial):
    return BmcResult[S](
      outcome: bmcFalsified, depthReached: 0, statesExplored: 0,
      counterexample: some(newSeq[BmcStep]()),
      finalState: some(initial))

  while head < frontier.len:
    if settings.maxStates > 0 and explored >= settings.maxStates:
      return BmcResult[S](
        outcome: bmcExhaustedBudget,
        depthReached: depthSeen, statesExplored: explored,
        counterexample: none(seq[BmcStep]),
        finalState: none(S))
    let cur = frontier[head]
    inc head
    if cur.plan.len > depthSeen: depthSeen = cur.plan.len
    if settings.maxDepth > 0 and cur.plan.len >= settings.maxDepth: continue

    # Dedup, if a hash proc is supplied. Skips count as "popped but not
    # expanded" — `statesExplored` reflects unique expansions.
    if stateHash != nil:
      let h = stateHash(cur.state)
      if h in visited: continue
      visited.incl h
    inc explored

    # Enumerate enabled rules in this state.
    for i, r in sm.rules:
      if not r.precondition.isNil and not r.precondition(cur.state):
        continue
      # Deterministic seed per (path, rule index) so replays are stable
      # and identical plans always reach identical post-states.
      var seed: uint64 = 0xC0FFEE'u64
      for step in cur.plan:
        seed = seed * 1099511628211'u64 + uint64(hash(step.ruleName))
      seed = seed * 1099511628211'u64 + uint64(i)
      var ds = newDataSource(initSplitMix64(seed))
      var newS = cur.state
      try:
        r.runStep(newS, ds)
      except CatchableError:
        # A rule's execute proc raised — treat as a violation (the SM
        # invariant doesn't tolerate exceptions during operation).
        var plan = cur.plan
        plan.add BmcStep(ruleName: r.name)
        return BmcResult[S](
          outcome: bmcFalsified, depthReached: cur.plan.len + 1,
          statesExplored: explored,
          counterexample: some(plan), finalState: some(newS))
      var newPlan = cur.plan
      newPlan.add BmcStep(ruleName: r.name)
      if not invariant(newS):
        return BmcResult[S](
          outcome: bmcFalsified, depthReached: newPlan.len,
          statesExplored: explored,
          counterexample: some(newPlan), finalState: some(newS))
      frontier.add Frontier(state: newS, plan: newPlan)

  BmcResult[S](
    outcome: bmcVerified,
    depthReached: depthSeen, statesExplored: explored,
    counterexample: none(seq[BmcStep]), finalState: none(S))
