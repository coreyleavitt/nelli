## RFC-fuzzer-nextgen E1 stage 2, C4: the call-site `fuzz(...)` macro.
## Behavior-preserving front: `fuzz(<strategyExpr>, <propExpr>, <settings?>)`
## must be identical (same iterations/corpus/crashes for a fixed seed) to
## the explicit `fuzz(s, inProcessTarget(prop), frontier, settings)` wiring
## `tfuzzloop.nim`/`tfuzzcovcorpus.nim` already write by hand.

import std/unittest
import nelli

proc branchyProp(n: int) {.cover.} =
  # mirrors tfuzzloop.nim's branchyProp: four branches so coverage varies.
  if n mod 2 == 0:
    if n > 100: discard else: discard
  else:
    if n < -50: discard else: discard

proc crashyProp(n: int) {.cover.} =
  doAssert n != 13, "unlucky"

suite "fuzz: call-site macro (RFC-fuzzer-nextgen E1 C4)":
  test "fuzz(s, namedProp, settings) matches the explicit fuzz(s, inProcessTarget(prop), frontier, settings) path":
    var explicitFrontier = newCoverageFrontier()
    let explicitReport = fuzz(integers(-200, 200), inProcessTarget(branchyProp), explicitFrontier,
                               FuzzSettings(maxIterations: 500, seed: 1))
    let macroReport = fuzz(integers(-200, 200), branchyProp,
                            FuzzSettings(maxIterations: 500, seed: 1))
    check macroReport.iterations == explicitReport.iterations
    check macroReport.coverageHits == explicitReport.coverageHits
    check macroReport.corpus.kind == explicitReport.corpus.kind
    check macroReport.corpus.irEntries.len == explicitReport.corpus.irEntries.len
    check macroReport.corpus.irEntries == explicitReport.corpus.irEntries
    check macroReport.irCrashes.len == explicitReport.irCrashes.len

  test "fuzz(s, namedProp) with no settings arg compiles (defaults to FuzzSettings())":
    # NOT executed: FuzzSettings() has maxIterations==0 and timeBudget==0, so
    # the loop's own (pre-existing, unrelated to this macro) "uncapped fuzzer"
    # semantics would run forever — exactly what an explicit
    # `fuzz(s, prop, FuzzSettings())` call would also do. `compiles` proves
    # the 2-arg overload type-checks and expands without running it.
    check compiles(fuzz(integers(-10, 10), branchyProp))

  test "fuzz(...) retains vInteresting findings the same way the explicit path does":
    var explicitFrontier = newCoverageFrontier()
    let explicitReport = fuzz(just(13), inProcessTarget(crashyProp), explicitFrontier,
                               FuzzSettings(maxIterations: 5, seed: 1))
    let macroReport = fuzz(just(13), crashyProp, FuzzSettings(maxIterations: 5, seed: 1))
    check macroReport.irCrashes.len == explicitReport.irCrashes.len
    check macroReport.irCrashes.len >= 1

  test "fuzz(...) accepts an inline lambda property, lifted to a module-scope proc":
    let r = fuzz(integers(-20, 20), proc(x: int) = discard x,
                 FuzzSettings(maxIterations: 30, seed: 4))
    check r.iterations == 30

  test "fuzz(...) is deterministic in the seed (mirrors tfuzzloop's own pin)":
    proc run(): FuzzReport =
      fuzz(integers(-200, 200), branchyProp, FuzzSettings(maxIterations: 200, seed: 7))
    let a = run()
    let b = run()
    check a.iterations == b.iterations
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len
