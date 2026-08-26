## RFC-fuzzer-nextgen E1 stage 2, C4: the call-site `fuzz(...)` macro.
## Behavior-preserving front: `fuzz(<strategyExpr>, <propExpr>, <settings?>)`
## must be identical (same iterations/corpus/crashes for a fixed seed) to
## the explicit `fuzz(s, inProcessTarget(prop), frontier, settings)` wiring
## `tfuzzloop.nim`/`tfuzzcovcorpus.nim` already write by hand.

import std/unittest
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

## --- C5: call-site-id worker-mode entry + in-process reconstruction --------

var rebuildCounter = 0
proc countedIntegers(lo, hi: int): Strategy[int] =
  ## Stamps identity: a genuine re-construction increments this on every
  ## call. Used to distinguish "worker re-entry re-ran the construction
  ## expression" from "worker re-entry reused the parent's captured closure".
  inc rebuildCounter
  integers(lo, hi)

suite "fuzz: worker-mode reentry (RFC-fuzzer-nextgen E1 C5)":
  test "runWorkerReentry(id, input) matches a fresh Worker built the same way, for the same input":
    rebuildCounter = 0
    discard fuzz(countedIntegers(-50, 50), branchyProp, FuzzSettings(maxIterations: 5, seed: 9))
    let id = nelliLastFuzzCallSiteId
    check id.len > 0
    check rebuildCounter == 1   # the macro's own immediate call constructed once

    var ds = newDataSource(initSplitMix64(0xABCD'u64))
    let val = integers(-50, 50).generate(ds)
    discard val
    let choices = ds.recorded

    let referenceWorker = newInProcessWorker(integers(-50, 50), inProcessTarget(branchyProp))
    let referenceObs = referenceWorker.submit(choices)
    let reentryObs = runWorkerReentry(id, choices)

    check reentryObs.verdict == referenceObs.verdict
    check reentryObs.coverage.counters == referenceObs.coverage.counters

  test "runWorkerReentry reconstructs a FRESH strategy instance, not the parent's captured one":
    rebuildCounter = 0
    discard fuzz(countedIntegers(-50, 50), branchyProp, FuzzSettings(maxIterations: 5, seed: 9))
    check rebuildCounter == 1
    let id = nelliLastFuzzCallSiteId

    var ds = newDataSource(initSplitMix64(0x1234'u64))
    discard integers(-50, 50).generate(ds)
    let choices = ds.recorded

    discard runWorkerReentry(id, choices)
    check rebuildCounter == 2   # the reentry re-ran countedIntegers(...): a genuine rebuild

    discard runWorkerReentry(id, choices)
    check rebuildCounter == 3   # each call reconstructs again — not memoized after the first

  test "runWorkerReentry surfaces a typed crash the same way the parent's Worker does":
    discard fuzz(just(13), crashyProp, FuzzSettings(maxIterations: 3, seed: 1))
    let id = nelliLastFuzzCallSiteId

    let choices: ChoiceSeq = @[]   # just(13) draws nothing
    let reentryObs = runWorkerReentry(id, choices)
    check reentryObs.verdict == vInteresting
    check reentryObs.crash.isSome
    check reentryObs.crash.get.kind == ckException
