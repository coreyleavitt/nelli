## Bisimulation / observational equivalence checking (#115).
##
## **The strongest equivalence in concurrency theory.** Given two state
## machines and an observation function on each, decide whether they
## produce identical observation traces under every reachable plan up
## to depth N. The use case: a reference implementation `refImpl` and
## an optimized implementation `optImpl` — bisimulation proves they
## behave identically (subject to the depth bound).
##
## **Algorithm.** Lock-step BFS over `(state1, state2)` product pairs.
## For each pair:
##
## 1. Observations must agree: `observe1(s1) == observe2(s2)`. If not,
##    we've found a distinguishing plan — the plan that reached this
##    pair.
## 2. Both SMs must have the same set of enabled rule names. If not,
##    the next-step behavior diverges; distinguishing plan extends the
##    current with the asymmetric rule.
## 3. Both must advance by every common rule; the resulting pair is
##    enqueued.
##
## **v1 scope.** Same arg-sampling discipline as BMC: per-branch
## deterministic seed derivation. For TRUE bisimulation on
## non-deterministic systems (multiple legal next states per rule)
## use `just(...)` arg strategies. The Paige-Tarjan partition-refinement
## algorithm (the "gold standard" for finite LTS bisimulation) is a
## structural alternative; this lock-step BFS implementation is
## equivalent for deterministic systems and simpler to reason about.
##
## **Symbolic refs.** Same caveat as `bmcCheck`: no PromiseStore
## installation, so symbolic-ref rules are disabled.

import std/[hashes, sets, options, sequtils]
import ./strategy, ./datasource, ./stateful, ./rng, ./bmc

type
  BisimOutcome* = enum
    bisimEquivalent,         ## fixed point reached; no distinguishing plan
    bisimDistinguishable,    ## found a plan that distinguishes the two
    bisimExhaustedBudget     ## hit maxStates before deciding

  BisimReport*[S1, S2] = object
    outcome*: BisimOutcome
    distinguishingPlan*: Option[seq[BmcStep]]
      ## When `bisimDistinguishable`: the shortest plan that reveals
      ## the difference, BFS-guaranteed minimal.
    initialObs1*: string
    initialObs2*: string
      ## Observations at the distinguishing pair (or initial pair).
    statesExplored*: int

proc bisimulationCheck*[S1, S2](
    sm1: StateMachine[S1], initial1: S1,
    observe1: proc(s: S1): string,
    sm2: StateMachine[S2], initial2: S2,
    observe2: proc(s: S2): string,
    settings: BmcSettings,
    stateHash1: proc(s: S1): Hash = nil,
    stateHash2: proc(s: S2): Hash = nil): BisimReport[S1, S2] =
  ## Lock-step BFS over `(s1, s2)` product pairs. Returns
  ## `bisimEquivalent` iff every reachable pair shares observations
  ## and rule-enablement; otherwise the shortest distinguishing plan.
  type Frontier = object
    state1: S1
    state2: S2
    plan: seq[BmcStep]

  # First check: initial observations must agree.
  let initObs1 = observe1(initial1)
  let initObs2 = observe2(initial2)
  if initObs1 != initObs2:
    return BisimReport[S1, S2](
      outcome: bisimDistinguishable,
      distinguishingPlan: some(newSeq[BmcStep]()),
      initialObs1: initObs1, initialObs2: initObs2,
      statesExplored: 0)

  var frontier: seq[Frontier] = @[Frontier(
    state1: initial1, state2: initial2, plan: @[])]
  var visited = initHashSet[(Hash, Hash)]()
  var head = 0
  var explored = 0

  while head < frontier.len:
    let cur = frontier[head]
    inc head
    if cur.plan.len >= settings.maxDepth: continue
    if stateHash1 != nil and stateHash2 != nil:
      let h = (stateHash1(cur.state1), stateHash2(cur.state2))
      if h in visited: continue
      visited.incl h
    inc explored
    if explored >= settings.maxStates:
      return BisimReport[S1, S2](
        outcome: bisimExhaustedBudget,
        distinguishingPlan: none(seq[BmcStep]),
        initialObs1: initObs1, initialObs2: initObs2,
        statesExplored: explored)

    # Collect enabled rule-name sets on both sides.
    var enabled1: seq[string]
    for r in sm1.rules:
      if r.precondition.isNil or r.precondition(cur.state1):
        enabled1.add r.name
    var enabled2: seq[string]
    for r in sm2.rules:
      if r.precondition.isNil or r.precondition(cur.state2):
        enabled2.add r.name

    # Rule-set mismatch: the next-step behaviour diverges. Build the
    # distinguishing plan by extending the current with the
    # asymmetric rule. Either an enabled1 rule that 2 doesn't have,
    # or vice versa, witnesses divergence.
    for name in enabled1:
      if name notin enabled2:
        var plan = cur.plan
        plan.add BmcStep(ruleName: name)
        return BisimReport[S1, S2](
          outcome: bisimDistinguishable,
          distinguishingPlan: some(plan),
          initialObs1: initObs1, initialObs2: initObs2,
          statesExplored: explored)
    for name in enabled2:
      if name notin enabled1:
        var plan = cur.plan
        plan.add BmcStep(ruleName: name)
        return BisimReport[S1, S2](
          outcome: bisimDistinguishable,
          distinguishingPlan: some(plan),
          initialObs1: initObs1, initialObs2: initObs2,
          statesExplored: explored)

    # For each shared rule name, advance both sides; observe; enqueue.
    for name in enabled1:
      if name notin enabled2: continue
      # Find rules by name on each side.
      var ruleIdx1 = -1
      for i, r in sm1.rules:
        if r.name == name: ruleIdx1 = i; break
      var ruleIdx2 = -1
      for i, r in sm2.rules:
        if r.name == name: ruleIdx2 = i; break
      if ruleIdx1 < 0 or ruleIdx2 < 0: continue  # defensive

      # Deterministic per-branch seed (same derivation on both sides
      # so identical rules see identical arg streams).
      var seed: uint64 = 0xC0FFEE'u64
      for step in cur.plan:
        seed = seed * 1099511628211'u64 + uint64(hash(step.ruleName))
      seed = seed * 1099511628211'u64 + uint64(hash(name))
      var ds1 = newDataSource(initSplitMix64(seed))
      var ds2 = newDataSource(initSplitMix64(seed))
      var s1Next = cur.state1
      var s2Next = cur.state2
      try:
        sm1.rules[ruleIdx1].runStep(s1Next, ds1)
      except CatchableError:
        # Rule raised on side 1; if side 2 doesn't raise on the same
        # rule, the systems differ observationally. Treat as a
        # distinguisher with the plan that triggered the raise.
        var plan = cur.plan
        plan.add BmcStep(ruleName: name)
        return BisimReport[S1, S2](
          outcome: bisimDistinguishable,
          distinguishingPlan: some(plan),
          initialObs1: initObs1, initialObs2: initObs2,
          statesExplored: explored)
      try:
        sm2.rules[ruleIdx2].runStep(s2Next, ds2)
      except CatchableError:
        var plan = cur.plan
        plan.add BmcStep(ruleName: name)
        return BisimReport[S1, S2](
          outcome: bisimDistinguishable,
          distinguishingPlan: some(plan),
          initialObs1: initObs1, initialObs2: initObs2,
          statesExplored: explored)
      let o1 = observe1(s1Next)
      let o2 = observe2(s2Next)
      var newPlan = cur.plan
      newPlan.add BmcStep(ruleName: name)
      if o1 != o2:
        return BisimReport[S1, S2](
          outcome: bisimDistinguishable,
          distinguishingPlan: some(newPlan),
          initialObs1: o1, initialObs2: o2,
          statesExplored: explored)
      frontier.add Frontier(state1: s1Next, state2: s2Next, plan: newPlan)

  BisimReport[S1, S2](
    outcome: bisimEquivalent,
    distinguishingPlan: none(seq[BmcStep]),
    initialObs1: initObs1, initialObs2: initObs2,
    statesExplored: explored)
