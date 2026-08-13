import std/[unittest, hashes, options]
import nelli

# #115 — bisimulation / observational equivalence checking.
#
# Build on the BMC enumerator: lock-step BFS over (state1, state2)
# pairs. For each pair, both SMs must (a) have the same set of
# rule-name enablements, (b) advance to a pair whose observations
# agree. If any reachable pair fails either, return a counterexample
# plan. v1 restricts to deterministic-per-plan execution (same seed
# derivation as BMC), so this is bisimulation ≡ trace equivalence on
# deterministic SMs. Non-determinism with random args degrades
# gracefully (you might miss arg-specific differences).

type CS = object
  count: int

suite "bisimulationCheck — identical SMs":
  test "two identical counter SMs are reported bisimEquivalent":
    proc mkSM(): StateMachine[CS] =
      StateMachine[CS](
        initial: just(CS(count: 0)),
        rules: @[
          rule[CS, int]("inc", just(0),
            proc(s: var CS, _: int) = inc s.count)])
    let sm1 = mkSM()
    let sm2 = mkSM()
    proc obs(s: CS): string = $s.count
    proc h(s: CS): Hash = hash(s.count)
    let r = bisimulationCheck(
      sm1, initial1 = CS(count: 0), observe1 = obs,
      sm2, initial2 = CS(count: 0), observe2 = obs,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000),
      stateHash1 = h, stateHash2 = h)
    check r.outcome == bisimEquivalent
    check r.distinguishingPlan.isNone

suite "bisimulationCheck — distinguishability":
  test "different initial observations → empty distinguishing plan":
    proc mkSM(): StateMachine[CS] =
      StateMachine[CS](
        initial: just(CS(count: 0)),
        rules: @[
          rule[CS, int]("inc", just(0),
            proc(s: var CS, _: int) = inc s.count)])
    let sm1 = mkSM()
    let sm2 = mkSM()
    proc obs(s: CS): string = $s.count
    let r = bisimulationCheck(
      sm1, initial1 = CS(count: 0), observe1 = obs,
      sm2, initial2 = CS(count: 99), observe2 = obs,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000))
    check r.outcome == bisimDistinguishable
    check r.distinguishingPlan.get.len == 0
    check r.initialObs1 != r.initialObs2

  test "observations diverge after a multi-step plan":
    # sm1 increments by 1; sm2 increments by 2. After 2 ops:
    # sm1.count = 2, sm2.count = 4. The shortest distinguishing plan
    # has length 1 — sm1 reaches 1, sm2 reaches 2.
    let sm1 = StateMachine[CS](
      initial: just(CS(count: 0)),
      rules: @[
        rule[CS, int]("step", just(0),
          proc(s: var CS, _: int) = s.count += 1)])
    let sm2 = StateMachine[CS](
      initial: just(CS(count: 0)),
      rules: @[
        rule[CS, int]("step", just(0),
          proc(s: var CS, _: int) = s.count += 2)])
    proc obs(s: CS): string = $s.count
    let r = bisimulationCheck(
      sm1, initial1 = CS(count: 0), observe1 = obs,
      sm2, initial2 = CS(count: 0), observe2 = obs,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000))
    check r.outcome == bisimDistinguishable
    let plan = r.distinguishingPlan.get
    check plan.len == 1
    check plan[0].ruleName == "step"

  test "rule-set mismatch: sm1 has extra rule not enabled on sm2":
    # Initial observations agree, but sm1 fires "reset" while sm2
    # doesn't have it. After "step" + "reset" on sm1 vs "step" on
    # sm2, the rule sets disagree → distinguishing plan extends with
    # the asymmetric rule.
    let sm1 = StateMachine[CS](
      initial: just(CS(count: 0)),
      rules: @[
        rule[CS, int]("step", just(0),
          proc(s: var CS, _: int) = inc s.count),
        rule[CS, int]("reset", just(0),
          proc(s: var CS, _: int) = s.count = 0)])
    let sm2 = StateMachine[CS](
      initial: just(CS(count: 0)),
      rules: @[
        rule[CS, int]("step", just(0),
          proc(s: var CS, _: int) = inc s.count)])
    proc obs(s: CS): string = $s.count
    let r = bisimulationCheck(
      sm1, initial1 = CS(count: 0), observe1 = obs,
      sm2, initial2 = CS(count: 0), observe2 = obs,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000))
    check r.outcome == bisimDistinguishable
    let plan = r.distinguishingPlan.get
    # First step from the initial pair: sm1 has {step, reset},
    # sm2 has {step}. The asymmetric rule is "reset"; plan length 1.
    check plan.len == 1
    check plan[0].ruleName == "reset"

suite "bisimulationCheck — refactor-equivalence demo":
  type StackA = object
    elems: seq[int]
  type StackB = object
    elems: seq[int]
    topCache: int   # optimization: cached top; B updates eagerly

  test "naive stack and optimized stack (with top cache) are bisimilar":
    # Both support push/pop with observation = current top (or -1 if empty).
    # StackB's cache is observationally equivalent to recomputing on demand.
    let smA = StateMachine[StackA](
      initial: just(StackA(elems: @[])),
      rules: @[
        rule[StackA, int]("pushOne", just(0),
          proc(s: var StackA, _: int) = s.elems.add 7),
        rule[StackA, int]("pop", just(0),
          proc(s: var StackA, _: int) =
            if s.elems.len > 0: discard s.elems.pop)])
    let smB = StateMachine[StackB](
      initial: just(StackB(elems: @[], topCache: -1)),
      rules: @[
        rule[StackB, int]("pushOne", just(0),
          proc(s: var StackB, _: int) =
            s.elems.add 7
            s.topCache = 7),
        rule[StackB, int]("pop", just(0),
          proc(s: var StackB, _: int) =
            if s.elems.len > 0:
              discard s.elems.pop
              s.topCache = if s.elems.len > 0: s.elems[^1] else: -1)])
    proc obsA(s: StackA): string =
      if s.elems.len == 0: "-1" else: $s.elems[^1]
    proc obsB(s: StackB): string = $s.topCache
    proc hA(s: StackA): Hash = hash(s.elems.len)
    proc hB(s: StackB): Hash = hash(s.elems.len)
    let r = bisimulationCheck(
      smA, initial1 = StackA(elems: @[]), observe1 = obsA,
      smB, initial2 = StackB(elems: @[], topCache: -1), observe2 = obsB,
      settings = BmcSettings(maxDepth: 8, maxStates: 1000),
      stateHash1 = hA, stateHash2 = hB)
    check r.outcome == bisimEquivalent
