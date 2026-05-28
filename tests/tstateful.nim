import std/unittest
import proptest

type CounterState = object
  count: int

suite "stateful testing":
  test "counter is non-negative when dec is gated on count > 0":
    let sm = StateMachine[CounterState](
      initial: CounterState(count: 0),
      rules: @[
        rule[CounterState, int]("inc", just(0),
          proc(s: var CounterState, _: int) = s.count += 1),
        rule[CounterState, int]("dec", just(0),
          proc(s: var CounterState, _: int) = s.count -= 1,
          proc(s: CounterState): bool = s.count > 0),
      ])
    let r = forAll(stateful(sm, maxSteps = 30),
                   proc(s: CounterState) = ensure s.count >= 0)
    check r.outcome == otPassed

  test "a buggy decrement (allowed at 0) is caught and shrinks":
    let buggy = StateMachine[CounterState](
      initial: CounterState(count: 0),
      rules: @[
        rule[CounterState, int]("inc", just(0),
          proc(s: var CounterState, _: int) = s.count += 1),
        rule[CounterState, int]("dec", just(0),
          proc(s: var CounterState, _: int) = s.count -= 1,
          # bug: allows dec even when count == 0
          proc(s: CounterState): bool = s.count >= 0),
      ])
    let r = forAll(stateful(buggy, maxSteps = 20),
                   proc(s: CounterState) = ensure s.count >= 0)
    check r.outcome == otFalsified
    check r.counterexample.count == -1  # shrinks to a single dec from 0
