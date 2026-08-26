## RFC-fuzzer-nextgen E1 stage 1, C2: the `Worker[T]` seam. Appendix C pins a
## completion-oriented `submitAsync[T](w, input: ChoiceSeq): WorkerHandle[T]`
## plus a blocking `submit[T](w, input: ChoiceSeq): Observation` convenience
## wrapper — the shape E1's single-worker reference impl uses. This file pins
## the in-process `Worker`: replaying a choice sequence through it must be
## OBSERVATIONALLY EQUIVALENT to today's `Target.run` on the value that same
## sequence generates — same verdict, same coverage, same typed crash.
##
## Stage-1 correction: the Worker wraps `(Strategy[T], Target[T])`, not a raw
## `prop` — this is what lets the hot `fuzz` loop route through it (via the
## `Orchestrator`) without losing the ability to hand `fuzz()` a stub/custom
## `Target[T]`. `submit` does exactly what the pre-refactor fuzz loop did
## inline: replay `input` through `s`, then run the resulting value through
## `target`.

import std/[unittest, options]
import nelli
import nelli/[datasource, rng]

proc branchyProp(n: int) {.cover.} =
  # mirrors tfuzzloop.nim's branchyProp: four branches so coverage varies.
  if n mod 2 == 0:
    if n > 100: discard else: discard
  else:
    if n < -50: discard else: discard

proc crashyProp(n: int) {.cover.} =
  doAssert n != 13, "unlucky"

suite "fuzz: Worker[T] seam (RFC-fuzzer-nextgen E1 C2)":
  test "in-process Worker.submit matches Target.run for the value the same choices generate":
    let s = integers(-200, 200)
    var ds = newDataSource(initSplitMix64(0xC0FFEE'u64))
    let val = s.generate(ds)
    let choices = ds.recorded

    let target = inProcessTarget(branchyProp)
    let worker = newInProcessWorker(s, target)
    let workerObs = worker.submit(choices)
    let targetObs = target.run(val)

    check workerObs.verdict == targetObs.verdict
    check workerObs.coverage.counters == targetObs.coverage.counters

  test "in-process Worker.submit surfaces a typed crash the same way Target.run does":
    let s = just(13)
    var ds = newDataSource(initSplitMix64(1'u64))
    let val = s.generate(ds)
    let choices = ds.recorded

    let target = inProcessTarget(crashyProp)
    let worker = newInProcessWorker(s, target)
    let workerObs = worker.submit(choices)
    let targetObs = target.run(val)

    check workerObs.verdict == vInteresting
    check workerObs.verdict == targetObs.verdict
    check workerObs.crash.isSome
    check targetObs.crash.isSome
    check workerObs.crash.get.kind == targetObs.crash.get.kind
    check workerObs.crash.get.defect == targetObs.crash.get.defect

  test "a choice sequence too short for the strategy is vRejected, not a crash":
    let s = integers(-200, 200)
    let worker = newInProcessWorker(s, inProcessTarget(branchyProp))
    let obs = worker.submit(@[])   # integers() draws — an empty sequence overruns
    check obs.verdict == vRejected

  test "generation-time Overrun/Rejection never escapes submit (E1 stage-1 fix)":
    # Same scenario as above, phrased as the specific behavior-preservation
    # invariant the fuzz loop depends on: submit must return, not raise, so
    # the loop's `if obs.verdict == vRejected: continue` is the only skip
    # path needed (no separate try/except around generation in the loop).
    let s = integers(-200, 200)
    let worker = newInProcessWorker(s, inProcessTarget(branchyProp))
    var obs: Observation[int]
    var raised = false
    try:
      obs = worker.submit(@[])
    except CatchableError, Defect:
      raised = true
    check not raised
    check obs.verdict == vRejected

  test "submitAsync returns a handle carrying the submitted input (E1: minimal)":
    let s = just(0)
    let worker = newInProcessWorker(s, inProcessTarget(branchyProp))
    var ds = newDataSource(initSplitMix64(2'u64))
    discard s.generate(ds)
    let choices = ds.recorded
    let handle = worker.submitAsync(choices)
    check handle.input == choices
