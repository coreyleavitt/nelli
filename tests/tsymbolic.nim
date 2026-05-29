import std/unittest
import proptest
import proptest/[datasource, rng]

# #109 — symbolic-reference stateful testing.
#
# The model: rules may *produce* values (under a symbolic name) and
# *consume* values produced by earlier rules. A typed promise store
# carries the produced values across rule firings within one example.
# Consumers can only fire when their referenced promises are fulfilled,
# so the runtime enablement check enforces dependency order — and
# shrinking, which deletes spans from the choice IR and re-replays,
# preserves dep order automatically (orphan consumers get filtered out
# by the same predicate).

suite "PromiseStore — typed round-trip":
  test "fulfill then read returns the value":
    let store = newPromiseStore()
    let id = (ruleName: "open", occurrence: 0)
    store.fulfill[:int](id, 42)
    check store.has(id)
    check store.read[:int](id) == 42

  test "read raises on missing key":
    let store = newPromiseStore()
    let id = (ruleName: "open", occurrence: 0)
    check not store.has(id)
    expect ValueError:
      discard store.read[:int](id)

  test "read raises on type mismatch":
    let store = newPromiseStore()
    let id = (ruleName: "open", occurrence: 0)
    store.fulfill[:int](id, 7)
    expect ValueError:
      discard store.read[:string](id)

suite "producingRule + consumingRule integration":
  type State = object
    fires: int    ## bookkeeping: how many rules fired total

  test "producingRule's action result is fulfilled in the store":
    # An open rule that returns a unique int handle each fire. After
    # firing, the store should hold a Promise[int] at ("open", 0).
    var handleCounter = 0
    let openRule = producingRule[State, int, int](
      name = "open",
      args = just(0),
      action = proc(s: var State, _: int): int =
        inc handleCounter
        inc s.fires
        handleCounter)
    let sm = StateMachine[State](
      initial: just(State()),
      rules: @[openRule])
    let r = forAll(stateful(sm, maxSteps = 3),
                   proc(s: State) = ensure s.fires < 100)
    check r.outcome == otPassed
    # Direct unit-style test: build a store, fire the rule's runStep,
    # confirm the promise is set.
    let store = newPromiseStore()
    installPromiseStore(store)
    defer: installPromiseStore(nil)
    var s = State()
    var ds = newDataSource(initSplitMix64(1))
    openRule.runStep(s, ds)
    check store.has((ruleName: "open", occurrence: 0))
    let h = store.read[:int]((ruleName: "open", occurrence: 0))
    check h >= 1

  test "consumingRule[1] receives the previously-produced value":
    # open produces handle = 99; read consumes it.
    var sawHandle = 0
    let openRule = producingRule[State, int, int](
      name = "open",
      args = just(0),
      action = proc(s: var State, _: int): int =
        inc s.fires
        99)
    let readRule = consumingRule[State, int, int](
      name = "read",
      args = just(0),
      consumes = symRef[int]("open", 0),
      action = proc(s: var State, _: int, h: int) =
        sawHandle = h
        inc s.fires)
    let store = newPromiseStore()
    installPromiseStore(store)
    defer: installPromiseStore(nil)
    var s = State()
    var ds = newDataSource(initSplitMix64(2))
    openRule.runStep(s, ds)
    readRule.runStep(s, ds)
    check sawHandle == 99

  test "consumingRule is filtered out when its ref is unfulfilled":
    # Empty store: read shouldn't be enabled.
    let openRule = producingRule[State, int, int](
      name = "open",
      args = just(0),
      action = proc(s: var State, _: int): int = 1)
    let readRule = consumingRule[State, int, int](
      name = "read",
      args = just(0),
      consumes = symRef[int]("open", 0),
      action = proc(s: var State, _: int, h: int) = discard)
    let store = newPromiseStore()
    installPromiseStore(store)
    defer: installPromiseStore(nil)
    let s0 = State()
    # readRule.precondition reports false until open has fired.
    check not readRule.precondition(s0)
    # Fire open; now read is enabled.
    var s = State()
    var ds = newDataSource(initSplitMix64(3))
    openRule.runStep(s, ds)
    check readRule.precondition(s)

  test "consumingRule[2] receives both refs":
    var sawA, sawB: int
    let alphaRule = producingRule[State, int, int](
      name = "alpha",
      args = just(0),
      action = proc(s: var State, _: int): int = 7)
    let betaRule = producingRule[State, int, int](
      name = "beta",
      args = just(0),
      action = proc(s: var State, _: int): int = 13)
    let bothRule = consumingRule[State, int, int, int](
      name = "both",
      args = just(0),
      consumes = (symRef[int]("alpha", 0), symRef[int]("beta", 0)),
      action = proc(s: var State, _: int, a: int, b: int) =
        sawA = a; sawB = b)
    let store = newPromiseStore()
    installPromiseStore(store)
    defer: installPromiseStore(nil)
    var s = State()
    var ds = newDataSource(initSplitMix64(9))
    # both is disabled until both alpha and beta have fired.
    check not bothRule.precondition(s)
    alphaRule.runStep(s, ds)
    check not bothRule.precondition(s)   # still missing beta
    betaRule.runStep(s, ds)
    check bothRule.precondition(s)
    bothRule.runStep(s, ds)
    check sawA == 7
    check sawB == 13

suite "end-to-end: open/read SM with falsifying invariant":
  type FsState = object
    openCalls: int   # how many opens happened in this example
    reads: int       # how many reads happened

  test "a sequence that includes read necessarily includes a prior open":
    # Build an SM with two rules: open (producing) and read (consuming).
    # The invariant catches any state where reads > 0. The shrunk
    # falsifying plan must have at least one open before the read —
    # otherwise read would have been disabled by its consume predicate.
    let openR = producingRule[FsState, int, int](
      name = "open",
      args = just(0),
      action = proc(s: var FsState, _: int): int =
        inc s.openCalls
        s.openCalls)  # handle = current openCalls counter
    let readR = consumingRule[FsState, int, int](
      name = "read",
      args = just(0),
      consumes = symRef[int]("open", 0),
      action = proc(s: var FsState, _: int, h: int) =
        inc s.reads)
    let sm = StateMachine[FsState](
      initial: just(FsState()),
      rules: @[openR, readR])
    # Check the falsifying condition as a property on the *final* state
    # so the strategy completes generation (rather than raising mid-run)
    # — only then does `r.counterexample` carry the shrunk state.
    let r = forAll(stateful(sm, maxSteps = 8),
                   proc(s: FsState) = ensure s.reads == 0)
    check r.outcome == otFalsified
    # Counterexample: any state with reads > 0 must have openCalls > 0.
    check r.counterexample.isSome
    let cx = r.counterexample.get
    check cx.reads >= 1
    check cx.openCalls >= 1
