import std/[unittest, sets]
import nelli
import nelli/[int128, choice, serialize, rng, datasource, shrinker]

type CounterState = object
  count: int

suite "stateful: initial is a Strategy[S]":
  test "drawing initial from sampledFrom yields multiple distinct start states":
    # `initial` is now a `Strategy[S]` — passing a varying strategy makes
    # each example start from a different seed state without callers
    # rolling their own ops-list strategy.
    let starts = @[CounterState(count: 0),
                   CounterState(count: 10),
                   CounterState(count: 100)]
    let sm = StateMachine[CounterState](
      initial: sampledFrom(starts),
      rules: @[
        rule[CounterState, int]("noop", just(0),
          proc(s: var CounterState, _: int) = discard)],
      invariant: nil)
    var seen: HashSet[int]
    for i in 0 ..< 30:
      var ds = newDataSource(initSplitMix64(uint64(i + 1)))
      let finalState = stateful(sm, maxSteps = 1).generate(ds)
      seen.incl finalState.count
    # All three initial counts should appear across 30 fresh examples.
    check 0 in seen
    check 10 in seen
    check 100 in seen

  test "shrinker minimizes the initial state alongside the rule sequence":
    # Property: `final count != 0`. A no-op rule machine keeps `count`
    # unchanged, so the property fails iff `initial.count != 0`. The
    # initial is drawn from `integers(-50, 50).map(toState)`, and the
    # shrinker should minimize `count` toward 0 (shrinkTowards), landing
    # on `count = 1` (the smallest nonzero value).
    let initial = map(integers(-50, 50),
                      proc(n: int): CounterState = CounterState(count: n))
    let sm = StateMachine[CounterState](
      initial: initial,
      rules: @[
        rule[CounterState, int]("noop", just(0),
          proc(s: var CounterState, _: int) = discard)])
    let r = forAll(stateful(sm, maxSteps = 5),
                   proc(s: CounterState) = ensure s.count == 0)
    check r.outcome == otFalsified
    # The shrunk counterexample has the smallest-magnitude nonzero count
    # (either +1 or -1 — both are minimal under the shrinker's "closest
    # to shrinkTowards = 0 that still falsifies" rule).
    check abs(r.counterexample.get.count) == 1

suite "stateful testing":
    # The strategy can produce already-violating initial states; the
    # invariant must catch them before any rule has a chance to fix
    # the state up. Uses `sampledFrom` with a single bad value to
    # guarantee the bad initial.
    let sm = StateMachine[CounterState](
      initial: sampledFrom(@[CounterState(count: -1)]),  # always bad
      rules: @[
        rule[CounterState, int]("inc", just(0),
          proc(s: var CounterState, _: int) = s.count += 1)],
      invariant: proc(s: CounterState) = ensure s.count >= 0)
    let r = forAll(stateful(sm, maxSteps = 5),
                   proc(_: CounterState) = ensure true)
    check r.outcome == otFalsified  # invariant fires on initial

suite "stateful testing":
  test "counter is non-negative when dec is gated on count > 0":
    let sm = StateMachine[CounterState](
      initial: just(CounterState(count: 0)),
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
      initial: just(CounterState(count: 0)),
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
    check r.counterexample.get.count == -1  # shrinks to a single dec from 0

  test "a per-step invariant that always holds passes":
    let sm = StateMachine[CounterState](
      initial: just(CounterState(count: 0)),
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
      initial: just(FlagState(flag: false)),
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

  test "per-step invariant raise leaves counterexample = none (strategy raised)":
    # A per-step `invariant:` that raises `FalsifiedError` *during*
    # `runStep` aborts the strategy mid-generation — no FlagState value
    # ever flows out. The Report's `counterexample` should reflect that
    # honestly: `none`, not a misleading `default(FlagState)`. The choice
    # sequence is the reproducible artifact.
    type FlagState = object
      flag: bool
    let machine = StateMachine[FlagState](
      initial: just(FlagState(flag: false)),
      rules: @[
        rule[FlagState, int]("setFlag", just(0),
          proc(s: var FlagState, _: int) = s.flag = true),
      ],
      invariant: proc(s: FlagState) = ensure not s.flag)
    let r = forAll(stateful(machine, maxSteps = 5),
                   proc(s: FlagState) = ensure true)
    check r.outcome == otFalsified
    check r.counterexample.isNone
    check r.choices.len > 0     # the reproducible artifact remains

  test "invariant on initial state is caught before any rule fires":
    type BadInit = object
      ok: bool
    let sm = StateMachine[BadInit](
      initial: just(BadInit(ok: false)),                       # already violating
      rules: @[
        rule[BadInit, int]("noop", just(0),
          proc(s: var BadInit, _: int) = discard),
      ],
      invariant: proc(s: BadInit) = ensure s.ok)
    let r = forAll(stateful(sm, maxSteps = 5),
                   proc(s: BadInit) = ensure true)
    check r.outcome == otFalsified
