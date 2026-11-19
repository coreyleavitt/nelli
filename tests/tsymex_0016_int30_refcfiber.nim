## RFC-0016 INT-30 (0005 review R2-28). A replay under a tracing collector
## (`--mm:refc`, this file's `.nim.cfg`) keeps what the SUT holds on its stack
## while the collector runs. On Windows the re-executed child would run the SUT
## on a fiber sized as the host's stack; refc's stack scan, from the fiber to
## the bottom the thread recorded, would span unrelated memory and miss the
## fiber's references. Only ARC and ORC run on the fiber now (`fiberSafe`).
##
## The payload carries the host's stack size, as the entry macro's does, so
## the child takes the fiber path where it has one.
import std/unittest
import nelli/smt/replayproc

type Cell = ref object
  v: int
  next: Cell

proc churn(): ReplayReport =
  ## Cells held only by this frame while the collector runs many times.
  var keep: Cell
  for i in 0 ..< 2000:
    keep = Cell(v: i, next: keep)
  for round in 0 ..< 100:
    var junk: seq[string]
    for k in 0 ..< 1000: junk.add newString(64)
    GC_fullCollect()
  var p = keep
  var i = 1999
  var ok = true
  while p != nil:
    if p.v != i: ok = false
    dec i
    p = p.next
  ReplayReport(reached: ok and i == -1, bound: true)

when replayReexecs:
  proc childRun(payload: string): ReplayReport {.nimcall.} = churn()
  let registered {.used.} = replayChildEntry("int30-refc-site", childRun)

proc replay(): ReplayChild =
  when replayForks:
    runReplayForked(proc (): ReplayReport {.closure, gcsafe.} =
      {.cast(gcsafe).}:
        result = churn(), 60_000)
  else:
    var payload = newString(8)
    var stack = int64(callerStackSize())
    copyMem(addr payload[0], addr stack, 8)
    runReplayReexec("int30-refc-site", payload, 60_000)

suite "INT-30: a replay under a tracing collector":
  test "the SUT's stack references survive the collector":
    let c = replay()
    checkpoint describe(c)
    check c.ending == reFinished
    check c.reached
