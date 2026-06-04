## Phase 4a/4b (docs/fuzz/FUZZ_PLAN.md): the generalized `fuzz(s, target, frontier,
## settings)` loop and the `Target` seam, tested directly (the shipped fuzz/coverage
## suites already pin that `fuzzWithIR` == `fuzz(inProcessTarget)`). Covers: in-process
## coverage + corpus growth, seed determinism, an arbitrary stub Target, crash retention.

import std/unittest
import proptest

proc branchyProp(n: int) {.cover.} =
  # four branches so coverage varies with the input — no crash (kept deterministic)
  if n mod 2 == 0:
    if n > 100: discard else: discard
  else:
    if n < -50: discard else: discard

suite "fuzz: generalized loop + Target (Phase 4a/4b)":
  test "fuzz over inProcessTarget finds coverage and grows the corpus":
    var frontier = newCoverageFrontier()
    let rep = fuzz(integers(-200, 200), inProcessTarget(branchyProp), frontier,
                   FuzzSettings(maxIterations: 500, seed: 1))
    check rep.iterations == 500
    check rep.coverageHits >= 1
    check rep.coverageHits == frontier.coveredEdges      # report mirrors the frontier
    check rep.corpus.kind == fckIR
    check rep.corpus.irEntries.len >= 1

  test "fuzz is deterministic in the seed":
    proc run(): FuzzReport =
      var f = newCoverageFrontier()
      fuzz(integers(-200, 200), inProcessTarget(branchyProp), f,
           FuzzSettings(maxIterations: 200, seed: 7))
    let a = run()
    let b = run()
    check a.iterations == b.iterations
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len

  test "fuzz drives an arbitrary Target (stub) and admits on its coverage":
    # No child process: a stub Target returns scripted coverage that grows over
    # calls, so admission is exercised target-agnostically.
    var calls = 0
    let stub = Target[int](run: proc(x: int): Observation[int] =
      inc calls
      var c = newSeq[uint8](4)
      for i in 0 ..< min(calls, 4): c[i] = 1'u8         # progressively more edges
      Observation[int](verdict: vOk, coverage: Coverage(counters: c)))
    var frontier = newCoverageFrontier()
    discard fuzz(integers(-10, 10), stub, frontier, FuzzSettings(maxIterations: 8, seed: 3))
    check calls > 0
    check frontier.coveredEdges >= 1                     # the stub's coverage was admitted

  test "fuzz retains vInteresting findings":
    let crashy = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vInteresting, message: "boom",
                       coverage: Coverage(counters: @[1'u8])))
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), crashy, frontier, FuzzSettings(maxIterations: 5, seed: 1))
    check rep.irCrashes.len >= 1
    check rep.irCrashes[0].message == "boom"
