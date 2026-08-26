## RFC-fuzzer-nextgen E1 stage 1, C2: the `Worker[T]` seam. Appendix C pins a
## completion-oriented `submitAsync[T](w, input: ChoiceSeq): WorkerHandle[T]`
## plus a blocking `submit[T](w, input: ChoiceSeq): Observation` convenience
## wrapper — the shape E1's single-worker reference impl uses. This file pins
## the in-process `Worker`: replaying a choice sequence through it must be
## OBSERVATIONALLY EQUIVALENT to today's `Target.run` on the value that same
## sequence generates — same verdict, same coverage, same typed crash. Not
## yet routed into the hot `fuzz` loop (that's C3's job) — this pins the seam
## standing alone.

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

    let worker = newInProcessWorker(s, branchyProp)
    let workerObs = worker.submit(choices)
    let targetObs = inProcessTarget(branchyProp).run(val)

    check workerObs.verdict == targetObs.verdict
    check workerObs.coverage.counters == targetObs.coverage.counters

  test "in-process Worker.submit surfaces a typed crash the same way Target.run does":
    let s = just(13)
    var ds = newDataSource(initSplitMix64(1'u64))
    let val = s.generate(ds)
    let choices = ds.recorded

    let worker = newInProcessWorker(s, crashyProp)
    let workerObs = worker.submit(choices)
    let targetObs = inProcessTarget(crashyProp).run(val)

    check workerObs.verdict == vInteresting
    check workerObs.verdict == targetObs.verdict
    check workerObs.crash.isSome
    check targetObs.crash.isSome
    check workerObs.crash.get.kind == targetObs.crash.get.kind
    check workerObs.crash.get.defect == targetObs.crash.get.defect

  test "a choice sequence too short for the strategy is vRejected, not a crash":
    let s = integers(-200, 200)
    let worker = newInProcessWorker(s, branchyProp)
    let obs = worker.submit(@[])   # integers() draws — an empty sequence overruns
    check obs.verdict == vRejected

  test "submitAsync returns a handle carrying the submitted input (E1: minimal)":
    let s = just(0)
    let worker = newInProcessWorker(s, branchyProp)
    var ds = newDataSource(initSplitMix64(2'u64))
    discard s.generate(ds)
    let choices = ds.recorded
    let handle = worker.submitAsync(choices)
    check handle.input == choices
