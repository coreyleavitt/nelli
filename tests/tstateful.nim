import std/unittest
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

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

  test "a per-step invariant that always holds passes":
    let sm = StateMachine[CounterState](
      initial: CounterState(count: 0),
      rules: @[
        rule[CounterState, int]("inc", just(0),
          proc(s: var CounterState, _: int) = s.count += 1),
      ],
      invariant: proc(s: CounterState) = ensure s.count >= 0)
    let r = forAll(stateful(sm, maxSteps = 10),
                   proc(s: CounterState) = ensure true)
    check r.outcome == otPassed

  test "per-step invariant catches a transient violation final-state would miss":
    # FlagState can recover to flag=false via clearFlag, so a sequence like
    # [setFlag, clearFlag] ends clean. Only a *per-step* check catches the
    # bad intermediate state — this is the case #64 exists for.
    type FlagState = object
      flag: bool

    let machine = StateMachine[FlagState](
      initial: FlagState(flag: false),
      rules: @[
        rule[FlagState, int]("setFlag", just(0),
          proc(s: var FlagState, _: int) = s.flag = true),
        rule[FlagState, int]("clearFlag", just(0),
          proc(s: var FlagState, _: int) = s.flag = false),
      ],
      invariant: proc(s: FlagState) = ensure not s.flag)

    # The property body does NOT check final state.
    let r = forAll(stateful(machine, maxSteps = 30),
                   proc(s: FlagState) = ensure true)
    check r.outcome == otFalsified

  test "invariant on initial state is caught before any rule fires":
    type BadInit = object
      ok: bool
    let sm = StateMachine[BadInit](
      initial: BadInit(ok: false),                       # already violating
      rules: @[
        rule[BadInit, int]("noop", just(0),
          proc(s: var BadInit, _: int) = discard),
      ],
      invariant: proc(s: BadInit) = ensure s.ok)
    let r = forAll(stateful(sm, maxSteps = 5),
                   proc(s: BadInit) = ensure true)
    check r.outcome == otFalsified
