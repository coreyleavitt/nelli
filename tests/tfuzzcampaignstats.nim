## RFC-fuzzer-nextgen S5 (a+b) — campaign observability surface.
##
## `CampaignStats` (fuzz.nim) is an AFL-`fuzzer_stats`-equivalent, READ-ONLY
## surface populated once, at the end of the `fuzz[T]` loop, from state the
## loop/`Orchestrator` already track. This suite proves each field reflects
## reality against deterministic FAKE targets/bridges (no real Z3 needed —
## G3's own real-bridge headline, `tfuzzconcolicbridge_real.nim`, separately
## proves the production translation compiles/runs and now also asserts the
## S5b surface directly).
import std/unittest
import nelli
import nelli/choice

proc plainTarget(): Target[int] =
  ## Constant coverage regardless of input — a "plateau" fixture: the very
  ## first admit improves the frontier once, nothing after it ever does.
  Target[int](run: proc(x: int): Observation[int] =
    Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))

proc everNovelTarget(): Target[int] =
  ## Each call reveals exactly one brand-new bucket (never seen by any
  ## earlier call, regardless of `x`) — so EVERY admit improves the
  ## frontier, deterministically, independent of mutation/RNG behavior.
  var callCount = 0
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](2000)
    for i in 0 .. callCount: c[i] = 1'u8
    inc callCount
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc crashEveryCallTarget(): Target[int] =
  Target[int](run: proc(x: int): Observation[int] =
    Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                     message: "boom"))

proc crashOnceEarlyTarget(): Target[int] =
  var callCount = 0
  Target[int](run: proc(x: int): Observation[int] =
    inc callCount
    if callCount == 1:
      Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                       message: "boom")
    else:
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))

suite "CampaignStats (RFC-fuzzer-nextgen S5a)":

  test "execs matches iterations, corpusSize matches the corpus, coverageEdges matches the frontier":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 1'u64, maxIterations: 15)
    let report = fuzz(integers(0, 100), plainTarget(), frontier, settings)
    check report.stats.execs == report.iterations
    check report.stats.corpusSize == report.corpus.irEntries.len
    check report.stats.coverageEdges == frontier.coveredEdges
    check report.stats.coverageEdges == report.coverageHits
    check report.stats.execsPerSec >= 0.0

  test "sinceLastCoverageAdmits advances once coverage plateaus and matches coverage.nim's own staleness":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 1'u64, maxIterations: 25)
    let report = fuzz(integers(0, 100), plainTarget(), frontier, settings)
    check report.stats.sinceLastCoverageAdmits > 0
    check report.stats.sinceLastCoverageAdmits == staleness(frontier.stats)

  test "sinceLastCoverageAdmits resets to 0 when the very last admit itself raises new coverage":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 1'u64, maxIterations: 20)
    let report = fuzz(integers(0, 100), everNovelTarget(), frontier, settings)
    check report.stats.sinceLastCoverageAdmits == 0

  test "sinceLastCrashIters is 0 when the very last observation itself crashes":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 1'u64, maxIterations: 10, keepAllCrashes: true)
    let report = fuzz(integers(0, 100), crashEveryCallTarget(), frontier, settings)
    check report.stats.sinceLastCrashIters == 0
    check report.stats.crashCount == report.irCrashes.len
    check report.stats.crashCount > 0

  test "sinceLastCrashIters advances once later observations stop crashing":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 1'u64, maxIterations: 20)
    let report = fuzz(integers(0, 100), crashOnceEarlyTarget(), frontier, settings)
    check report.stats.crashCount == 1
    check report.stats.sinceLastCrashIters > 0

  test "respawnCount counts Orchestrator worker recycles; fuzz()'s own entry never wires one (stays 0)":
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = makeWorker(),
                                  recycleAfterInputs = 2)
    for i in 0 ..< 6: discard o.run(@[])
    check respawnCount(o) == 3   # every 2nd input recycles: 6 / 2 = 3

    var frontier2 = newCoverageFrontier()
    let report = fuzz(integers(0, 100), plainTarget(), frontier2,
                      FuzzSettings(seed: 1'u64, maxIterations: 10))
    check report.stats.respawnCount == 0
    check report.stats.stormTripped == false
    check report.stats.stormBackoffLevel == 0

  test "cullCount counts periodic culling ticks; 0 under uniformCorpus (the opt-out)":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 1'u64, maxIterations: 120, cullCadence: 10)
    let report = fuzz(integers(0, 100), everNovelTarget(), frontier, settings)
    check report.stats.cullCount > 0

    var frontier2 = newCoverageFrontier()
    let settings2 = FuzzSettings(seed: 1'u64, maxIterations: 120, cullCadence: 10,
                                 uniformCorpus: true)
    let report2 = fuzz(integers(0, 100), everNovelTarget(), frontier2, settings2)
    check report2.stats.cullCount == 0

  test "totalMutationOps mirrors FuzzReport.totalMutationOps; operatorPulls has one entry per active arm":
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 100), plainTarget(), frontier,
                      FuzzSettings(seed: 3'u64, maxIterations: 12))
    check report.stats.totalMutationOps == report.totalMutationOps
    # Default settings: 5 base IR mutators + S3's always-on interesting-value
    # arm (enableI2S/uniformHavoc both left at their defaults) = 6 arms.
    check report.stats.operatorPulls.len == 6

proc deadbeefGateS5(x: int) {.cover, covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

proc gateTargetS5(): Target[int] =
  Target[int](run: proc(x: int): Observation[int] =
    if x == 0xCAFEBABE:
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 1'u8]))
    else:
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0'u8])))

suite "CampaignStats — provenance + concolic-yield surfacing (RFC-fuzzer-nextgen S5b)":

  test "a pure-mutation campaign attributes all corpus growth to pvMutation":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 7'u64, maxIterations: 30)
    let report = fuzz(integers(0, 100), plainTarget(), frontier, settings)
    check report.stats.provenanceCounts[pvMutation] > 0
    check report.stats.provenanceCounts[pvI2S] == 0
    check report.stats.provenanceCounts[pvConcolic] == 0

  test "an I2S campaign attributes its winning admissions to pvI2S":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGateS5,
                          FuzzSettings(seed: 42'u64, maxIterations: 200, enableI2S: true))
    check report.coverageHits == 2   # both "hit" and "miss" — I2S alone breaks the gate
    check report.stats.provenanceCounts[pvI2S] > 0

  test "the identical campaign with enableI2S left at false never attributes anything to pvI2S":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGateS5,
                          FuzzSettings(seed: 42'u64, maxIterations: 200))
    check report.stats.provenanceCounts[pvI2S] == 0

  test "a stalled campaign with a fake concolic bridge attributes admission to pvConcolic and surfaces its yield tally":
    var bridgeCalls = 0
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      inc bridgeCalls
      if targetBranchIndex == 0:
        ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                             materialized: @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)],
                             yieldTotals: ConcolicYieldTotals(solvedExact: 1, intendedCovered: 1))
      else:
        ConcolicBridgeResult(outcome: coUnmodelable, coverage: ccNotApplicable,
                             yieldTotals: ConcolicYieldTotals(unmodelable: 1))
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5, stallRounds: 1)
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTargetS5(), frontier, settings,
                      concolicBridge = bridge)
    check bridgeCalls > 0
    check frontier.coveredEdges == 2       # the gate edge, admitted via the bridge
    check report.stats.provenanceCounts[pvConcolic] > 0
    check report.stats.concolicYield.solvedExact >= 1
    check report.stats.concolicYield.intendedCovered >= 1
    check report.stats.concolicYield.unmodelable >= 1   # tallied even from a non-winning attempt

  test "no bridge wired: concolicYield stays all-zero and provenanceCounts[pvConcolic] is 0":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTargetS5(), frontier, settings)
    check report.stats.provenanceCounts[pvConcolic] == 0
    check report.stats.concolicYield.solvedExact == 0
    check report.stats.concolicYield.unmodelable == 0
