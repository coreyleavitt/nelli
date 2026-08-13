import std/[unittest, options, hashes]
import nelli

# #113 — bounded model checking for stateful machines.
#
# `bmcCheck` does breadth-first search over rule sequences up to a
# given depth. Where `stateful(sm)` samples one random plan per
# example, BMC enumerates all enabled rule firings at each state.
# A passing BMC run *verifies* the invariant for all plans up to
# depth N (modulo the v1 caveat that args are sampled, not
# enumerated — for true completeness, use rules with `just(...)` args).

type CounterS = object
  count: int

suite "bmcCheck — verification path":
  test "trivial noop SM verifies the invariant at depth 5":
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("noop", just(0),
          proc(s: var CounterS, _: int) = discard)])
    let r = bmcCheck(
      sm, initial = CounterS(count: 0),
      invariant = proc(s: CounterS): bool = true,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000))
    check r.outcome == bmcVerified
    check r.counterexample.isNone

suite "bmcCheck — falsification path":
  test "incrementing-only SM exceeds threshold; BMC returns shortest plan":
    # `inc` adds 1 to count. Invariant: count <= 2. BMC at depth 5
    # should find: noop is enabled but adds nothing; inc reaches 3 in 3
    # steps. The shortest falsifying plan has exactly 3 ops (all `inc`).
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("inc", just(0),
          proc(s: var CounterS, _: int) = inc s.count)])
    let r = bmcCheck(
      sm, initial = CounterS(count: 0),
      invariant = proc(s: CounterS): bool = s.count <= 2,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000))
    check r.outcome == bmcFalsified
    check r.counterexample.isSome
    let plan = r.counterexample.get
    check plan.len == 3
    for step in plan:
      check step.ruleName == "inc"
    check r.finalState.isSome
    check r.finalState.get.count == 3

  test "invariant violated by the initial state yields empty plan":
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("noop", just(0),
          proc(s: var CounterS, _: int) = discard)])
    let r = bmcCheck(
      sm, initial = CounterS(count: -1),
      invariant = proc(s: CounterS): bool = s.count >= 0,
      settings = BmcSettings(maxDepth: 5, maxStates: 1000))
    check r.outcome == bmcFalsified
    check r.counterexample.get.len == 0

suite "bmcCheck — stateHash dedup":
  test "without dedup, branching factor 2 grows to 2^depth states":
    # Two inc rules. Without dedup the BFS visits each plan; with
    # branching = 2 and depth = 8, frontier is 1 + 2 + 4 + ... + 256 = 511.
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("incA", just(0),
          proc(s: var CounterS, _: int) = inc s.count),
        rule[CounterS, int]("incB", just(0),
          proc(s: var CounterS, _: int) = inc s.count)])
    let r = bmcCheck(
      sm, initial = CounterS(count: 0),
      invariant = proc(s: CounterS): bool = true,
      settings = BmcSettings(maxDepth: 8, maxStates: 10_000))
    check r.outcome == bmcVerified
    # Without dedup we expand all 2^k paths up through depth 8.
    check r.statesExplored >= 200   # at least ~2^7 are expanded

  test "with stateHash dedup, the same SM collapses to depth+1 states":
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("incA", just(0),
          proc(s: var CounterS, _: int) = inc s.count),
        rule[CounterS, int]("incB", just(0),
          proc(s: var CounterS, _: int) = inc s.count)])
    proc h(s: CounterS): Hash = hash(s.count)
    let r = bmcCheck(
      sm, initial = CounterS(count: 0),
      invariant = proc(s: CounterS): bool = true,
      settings = BmcSettings(maxDepth: 8, maxStates: 10_000),
      stateHash = h)
    check r.outcome == bmcVerified
    # With dedup, every (count) reached by incA is the same as by incB;
    # we expand at most one branch per unique count → ≤ 10 expansions.
    check r.statesExplored <= 12

suite "bmcCheck — budget enforcement":
  test "maxStates cap terminates with bmcExhaustedBudget":
    # Three-rule SM with no dedup, depth 12 = 3^12 ≈ 530k frontier
    # entries. maxStates: 50 cuts it off long before.
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("a", just(0),
          proc(s: var CounterS, _: int) = inc s.count),
        rule[CounterS, int]("b", just(0),
          proc(s: var CounterS, _: int) = inc s.count),
        rule[CounterS, int]("c", just(0),
          proc(s: var CounterS, _: int) = inc s.count)])
    let r = bmcCheck(
      sm, initial = CounterS(count: 0),
      invariant = proc(s: CounterS): bool = true,
      settings = BmcSettings(maxDepth: 12, maxStates: 50))
    check r.outcome == bmcExhaustedBudget
    check r.statesExplored == 50

  test "maxDepth cap stops expansion but reports verification":
    # SM that never violates; depth 3 enumerates only 3 expansions then
    # frontier exhausts (no more children at depth 3).
    let sm = StateMachine[CounterS](
      initial: just(CounterS(count: 0)),
      rules: @[
        rule[CounterS, int]("inc", just(0),
          proc(s: var CounterS, _: int) = inc s.count)])
    let r = bmcCheck(
      sm, initial = CounterS(count: 0),
      invariant = proc(s: CounterS): bool = true,
      settings = BmcSettings(maxDepth: 3, maxStates: 1000))
    check r.outcome == bmcVerified
    check r.depthReached == 3
    # `statesExplored` counts expansions (nodes whose children get
    # pushed). Depths 0, 1, 2 each expand exactly one child; depth-3
    # nodes are popped past the maxDepth check without expansion.
    check r.statesExplored == 3
