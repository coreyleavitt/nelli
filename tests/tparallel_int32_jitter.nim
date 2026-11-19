## RFC-0016 INT-32 (0005 review R1-34). `ScheduledOp.jitter` spends at most
## one scheduler-yield system call per op, whatever its size: the rest of the
## delay is CPU pauses (`spinJitter`). It spent one `sched_yield` /
## `SwitchToThread` per unit, up to `maxJitter` (100 by default) per op.
import std/[unittest, locks, monotimes, times]
import nelli
import nelli/[datasource, rng]

type
  Counter = object
    count: int
    lock: Lock
  CounterState = object
    count: int

proc newCounter(): ptr Counter =
  result = cast[ptr Counter](allocShared0(sizeof(Counter)))
  initLock(result[].lock)

proc inc1(c: ptr Counter): int {.gcsafe.} =
  withLock c[].lock:
    inc c[].count
    result = c[].count

proc incModel(s: var CounterState): int =
  inc s.count
  s.count

proc intEq(a, b: int): bool = a == b

proc spec(): LinSpec[CounterState, ptr Counter, int] =
  LinSpec[CounterState, ptr Counter, int](
    modelInitial: CounterState(),
    newSUT: proc(): ptr Counter {.gcsafe.} = newCounter(),
    ops: @[LinOpDef[CounterState, ptr Counter, int](
      opId: 0,
      applySUT: proc(c: ptr Counter): int {.gcsafe, closure.} = inc1(c),
      applyModel: proc(s: var CounterState): int {.gcsafe, closure.} =
        incModel(s))])

proc runOnce(maxJitter, steps, threads: int): tuple[yields: int, ms: float] =
  var ds = newDataSource(initSplitMix64(7))
  let s = parallelCheck(spec(), intEq, prefixSteps = steps,
                        parallelSteps = steps, threads = threads,
                        repetitions = 1, maxJitter = maxJitter)
  let y0 = schedulerYields()
  let t0 = getMonoTime()
  let r = s.generate(ds)
  doAssert r.linearisable
  (yields: schedulerYields() - y0,
   ms: (getMonoTime() - t0).inNanoseconds.float / 1e6)

suite "INT-32 (6): jitter costs at most one system call per op":
  test "a plan at maxJitter = 100 yields at most once per op":
    const steps = 50
    const threads = 2
    let ops = steps + steps * threads
    let r = runOnce(100, steps, threads)
    checkpoint "maxJitter=100: " & $r.yields & " yields over " & $ops &
               " ops, " & $r.ms & " ms"
    echo "INT-32 jitter: maxJitter=100: ", r.yields, " yields over ", ops,
         " ops, ", r.ms, " ms"
    check r.yields <= ops
    check r.yields > 0

  test "maxJitter = 0 spends nothing":
    let r = runOnce(0, 20, 2)
    check r.yields == 0
