import std/[unittest, options, locks, atomics, os]
import nelli
import nelli/[datasource, rng]

# parallelCheck: the convenience layer over isLinearisable. Generates
# a parallel plan (sequential prefix + N parallel suffixes), runs each
# suffix on its own thread with barrier synchronization + jitter
# injection, builds a history, and checks linearisability. Repetitions
# re-run the same plan to surface scheduler-dependent races.

# A trivial counter SUT for the round-trip tests.
type
  Counter = object
    count: int
    lock: Lock

  CounterState = object
    count: int

proc newSafeCounter(): ptr Counter =
  result = cast[ptr Counter](allocShared0(sizeof(Counter)))
  initLock(result[].lock)

proc safeInc(c: ptr Counter): int {.gcsafe.} =
  withLock c[].lock:
    inc c[].count
    result = c[].count

proc safeGet(c: ptr Counter): int {.gcsafe.} =
  withLock c[].lock:
    result = c[].count

proc applyIncModel(s: var CounterState): int =
  inc s.count
  s.count

proc applyGetModel(s: var CounterState): int = s.count

proc intEq(a, b: int): bool = a == b

suite "parallelCheck: trivial round-trip":
  test "spec with no ops produces a trivially-linearisable result":
    # Edge case: spec with empty ops list. Generates an empty plan,
    # builds an empty history, isLinearisable trivially accepts.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[])
    var ds = newDataSource(initSplitMix64(1))
    let s = parallelCheck(spec, intEq,
                         prefixSteps = 0,
                         parallelSteps = 0,
                         threads = 0,
                         repetitions = 1,
                         maxJitter = 0)
    let r = s.generate(ds)
    check r.linearisable

  test "prefix-only plan produces a sequential history of the right length":
    # 5 incs on the main thread, no parallel suffixes. The witness
    # length matches the number of prefix steps (history is purely
    # sequential, trivially linearisable).
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = safeInc(c),
          applyModel: applyIncModel),
      ])
    var ds = newDataSource(initSplitMix64(2))
    let s = parallelCheck(spec, intEq,
                         prefixSteps = 5,
                         parallelSteps = 0,
                         threads = 0,
                         repetitions = 1,
                         maxJitter = 0)
    let r = s.generate(ds)
    check r.linearisable
    check r.witness.len == 5

suite "parallelCheck: thread-safe SUT (no race)":
  test "locked counter passes parallelCheck under forAll":
    # The properly-locked counter is linearisable for any schedule.
    # forAll across many examples should always see linearisable=true.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = safeInc(c),
          applyModel: applyIncModel),
        LinOpDef[CounterState, ptr Counter, int](
          opId: 1,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = safeGet(c),
          applyModel: applyGetModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 1,
                    parallelSteps = 2,
                    threads = 2,
                    repetitions = 3,
                    maxJitter = 50),
      prop,
      Settings(maxExamples: 20, seed: 1,
               flakyRetries: 0, maxShrinks: 20,
               maxRejections: 50))
    check r.outcome == otPassed

# A racy (lock-free WRONG) counter: read, +1, write — no atomicity.
# Two concurrent incs from `count = N` both read N, both write N+1,
# both return N+1. The model says one should return N+1 and the
# other N+2.
proc racyInc(c: ptr Counter): int {.gcsafe.} =
  let v = c[].count
  # Deliberately widen the race window between the read and the
  # write. Without this, the two are back-to-back instructions: on
  # an oversubscribed host (e.g. six concurrent sweep containers)
  # the OS time-slices the two threads instead of truly running them
  # concurrently, so the nanosecond-wide gap almost never straddles
  # a context switch and the race is never observed -- every history
  # comes out linearisable and the test flakes red for the wrong
  # reason. Sleeping here forces the scheduler to actually run the
  # other thread inside the window, so it reads the same pre-write
  # value we did. This does not change what's wrong with the
  # counter -- it is still an unsynchronized read-modify-write --
  # it just makes the wrongness observable regardless of machine
  # load. Do not remove this "for performance"; it is load-bearing
  # for the test's ability to catch the race at all.
  sleep(1)
  c[].count = v + 1
  v + 1

proc racyGet(c: ptr Counter): int {.gcsafe.} = c[].count

suite "parallelCheck: racy SUT is caught":
  test "lock-free wrong counter is detected as non-linearisable":
    # This test is inherently nondeterministic in nature — racy bugs
    # depend on scheduling. `racyInc` widens its own read/write
    # window with an explicit sleep (see comment there) so the race
    # is caught deterministically in practice, independent of host
    # load. On top of that we use many repetitions per plan + many
    # examples + jitter (staggering thread start times) to maximize
    # the chance of catching it within the budget even if the sleep
    # trick alone weren't enough on some platform.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyInc(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 50),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    # `otFalsified` is a clean catch; `otFlaky` is also a catch — the
    # property is non-deterministic, which is exactly what a race
    # causes (sometimes linearisable, sometimes not, depending on
    # the schedule).
    check r.outcome in {otFalsified, otFlaky}
    # For otFalsified, the diverging op surfaces. For otFlaky, the
    # counterexample captured may be from a *replay* that happened
    # to schedule benignly — we don't assert divergingOp in that
    # case, since the post-shrink replay can land on a linearisable
    # schedule even though the original was racy.
    if r.outcome == otFalsified and r.counterexample.isSome:
      check r.counterexample.get.divergingOp.isSome
      check r.counterexample.get.divergingOp.get == 0
