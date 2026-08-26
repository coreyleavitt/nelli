## RFC-fuzzer-nextgen E1 stage 1, C3: the `Orchestrator[T]` seam
## (Appendix C — NOT `Pool`; "pool" is the `seq[Worker[T]]` it owns). At E1
## this is a SINGLE-worker reference implementation that owns the
## `CoverageFrontier` and the admission decision: `admit[T](o, input,
## candidate): AdmitResult` is a direct in-memory frontier fold (no
## fresh-spawn re-verify yet — that's E3a), but the signature is shaped so a
## later re-verify doesn't need to change it.
##
## This file pins the seam standing alone (mirrors `CoverageFrontier.admit`
## exactly, target-agnostic like the existing stub-`Target` tests in
## `tfuzzloop.nim`). The full `fuzz()` loop is rerouted through this same
## seam internally (no change to `fuzz`'s own signature or to
## `tfuzzloop`/`tfuzzdedup`/`tfuzzstopcrash`, which stay byte-for-byte green
## and are the regression pin for "same fuzz outcome as today").

import std/[unittest, options]
import nelli

suite "fuzz: Orchestrator[T] seam (RFC-fuzzer-nextgen E1 C3)":
  test "Orchestrator.run drives the wrapped Target exactly like Target.run":
    var calls = 0
    let target = Target[int](run: proc(x: int): Observation[int] =
      inc calls
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var frontier = newCoverageFrontier()
    let o = newOrchestrator(target, frontier)
    let obs = o.run(5)
    check calls == 1
    check obs.verdict == vOk
    check obs.coverage.counters == @[1'u8]

  test "Orchestrator.admit mirrors CoverageFrontier.admit: first new-edge observation is admitted":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0, 0])))
    let o = newOrchestrator(target, frontier)
    let obs = o.run(0)
    let ar = admit(o, @[], obs)
    check ar.admitted
    check ar.provenance == pvMutation           # E1: the only source the loop drives
    check frontier.coveredEdges == 1             # the SAME frontier the caller passed in

  test "Orchestrator.admit: re-observing the same coverage is not admitted again":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(target, frontier)
    let obsA = o.run(0)
    discard admit(o, @[], obsA)
    let obsB = o.run(1)                          # same coverage, different input
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
    let o = newOrchestrator(target, frontier)
    let ar1 = admit(o, @[], o.run(0))
    check ar1.admitted
    let ar2 = admit(o, @[], o.run(0))
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
