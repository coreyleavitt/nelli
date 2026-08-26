## RFC-fuzzer-nextgen E1 stage 1, C3: the `Orchestrator[T]` seam
## (Appendix C — NOT `Pool`; "pool" is the `seq[Worker[T]]` it owns). At E1
## this is a SINGLE-worker reference implementation that owns the
## `CoverageFrontier` and the admission decision: `admit[T](o, input,
## candidate): AdmitResult` is a direct in-memory frontier fold (no
## fresh-spawn re-verify yet — that's E3a), but the signature is shaped so a
## later re-verify doesn't need to change it.
##
## Stage-1 correction: `Orchestrator.run` takes a `ChoiceSeq` (the Worker's
## currency, Appendix C), not a materialized value — `newOrchestrator` builds
## one in-process `Worker` from `(s, target)` and `run` is exactly
## `worker.submit`. This is what makes the Worker seam load-bearing rather
## than a dead parallel path: the hot `fuzz` loop drives execution through
## this exact seam (mirrors `CoverageFrontier.admit` for admission, target-
## agnostic like the existing stub-`Target` tests in `tfuzzloop.nim`). The
## full `fuzz()` loop is rerouted through this same seam internally (no
## change to `fuzz`'s own signature or to
## `tfuzzloop`/`tfuzzdedup`/`tfuzzstopcrash`, which stay byte-for-byte green
## and are the regression pin for "same fuzz outcome as today").

import std/[unittest, options]
import nelli

suite "fuzz: Orchestrator[T] seam (RFC-fuzzer-nextgen E1 C3)":
  test "Orchestrator.run replays the ChoiceSeq through the strategy and drives the wrapped Target":
    var calls = 0
    var lastVal = -1
    let target = Target[int](run: proc(x: int): Observation[int] =
      inc calls
      lastVal = x
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var frontier = newCoverageFrontier()
    let o = newOrchestrator(just(5), target, frontier)
    let obs = o.run(@[])   # just(5) consumes no choices
    check calls == 1
    check lastVal == 5
    check obs.verdict == vOk
    check obs.coverage.counters == @[1'u8]

  test "Orchestrator.run folds a generation-time Overrun into vRejected, same as the Worker does":
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var frontier = newCoverageFrontier()
    let o = newOrchestrator(integers(-200, 200), target, frontier)
    let obs = o.run(@[])   # integers() draws — an empty sequence overruns
    check obs.verdict == vRejected

  test "Orchestrator.admit mirrors CoverageFrontier.admit: first new-edge observation is admitted":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0, 0])))
    let o = newOrchestrator(just(0), target, frontier)
    let obs = o.run(@[])
    let ar = admit(o, @[], obs)
    check ar.admitted
    check ar.provenance == pvMutation           # E1: the only source the loop drives
    check frontier.coveredEdges == 1             # the SAME frontier the caller passed in

  test "Orchestrator.admit: re-observing the same coverage is not admitted again":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)
    let obsA = o.run(@[])
    discard admit(o, @[], obsA)
    let obsB = o.run(@[])                        # same coverage, second run
    let ar2 = admit(o, @[], obsB)
    check not ar2.admitted
    check frontier.coveredEdges == 1

  test "Orchestrator.admit: a higher bucket on a known edge is new again (order-independence carries)":
    var frontier = newCoverageFrontier()
    var n = 0
    let target = Target[int](run: proc(x: int): Observation[int] =
      inc n
      # 1 hit then 3 hits on the same slot -> bucket rises 1 -> 3
      let count = if n == 1: 1'u8 else: 3'u8
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[count])))
    let o = newOrchestrator(just(0), target, frontier)
    let ar1 = admit(o, @[], o.run(@[]))
    check ar1.admitted
    let ar2 = admit(o, @[], o.run(@[]))
    check ar2.admitted                            # bucket rose 1 -> 3: new again

  test "fuzz() routed through the Orchestrator still matches the pinned tfuzzloop trajectory":
    # Cross-check against tfuzzloop.nim's own "deterministic in the seed" pin —
    # the real regression guard for C3 is that suite staying green unmodified;
    # this test additionally exercises the SAME scenario through this file so
    # a future edit to fuzz()'s internals that only breaks Orchestrator-routed
    # runs (but not a hand-built Orchestrator) still gets caught here.
    proc branchyProp(n: int) {.cover.} =
      if n mod 2 == 0:
        (if n > 100: discard else: discard)
      else:
        (if n < -50: discard else: discard)
    proc run(): FuzzReport =
      var f = newCoverageFrontier()
      fuzz(integers(-200, 200), inProcessTarget(branchyProp), f,
           FuzzSettings(maxIterations: 200, seed: 7))
    let a = run()
    let b = run()
    check a.iterations == b.iterations
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len
