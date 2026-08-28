## RFC-z3-optional S1b2 — missing-libz3 degradation.
##
## Today's baseline is campaign ABORT, not graceful anything:
## `tryConcolicBridge` has no `try`/`except`, and neither does
## `runConcolicFlipImpl`. `SoftlinkError` is not a `Z3Error`, so the
## Phase-14 C4 policy neither covers it nor sits on this entry point. A
## consumer who opted into the assist on a machine where `libz3` cannot be
## loaded gets their whole fuzzing campaign killed by an OPTIONAL feature.
##
## The catch cannot live in `fuzz.nim` — naming `SoftlinkError` there means
## importing softlink, which breaks the property this RFC exists to
## restore; and catching bare `CatchableError` would contradict the tree's
## standing "walker `ValueError`/`AssertionDefect` are real bugs and must
## propagate" policy, masking exactly the R1 class
## `tfuzzconcolicbridge_real.nim` exists to prove aborts loudly.
##
## So the guard lives in `nelli/concolic`, which legitimately reaches Z3
## and can name the type — and it is a NAMED, EXPORTED wrapper rather than
## something buried inside the macro's codegen, precisely so this file can
## exercise the real production guard around a fake raising bridge.
## `concolicAssist` wraps its own generated closure in the same
## `guardSolverUnavailable`; there is no parallel test-only path.
##
## That is what makes this DoD falsifiable at all: both CI containers ship
## libz3, so a test that needed a genuinely libz3-less environment could
## never run. Here the failure is injected, and the assertions are positive
## — the degrade arm is OBSERVED TO FIRE, not merely defined.
import std/[unittest, tables]
import nelli
import nelli/concolic
import nelli/choice
import softlink

proc degradeGate(drawnInt: int) {.cover.} =
  if drawnInt == 0xCAFEBABE:
    discard "gate"
  else:
    discard "miss"

proc raisingBridge(calls: ref int): ConcolicBridgeEntry =
  ## A bridge that fails exactly the way a missing `libz3` fails: the lazy
  ## symbol load raises `SoftlinkError` on first use. Z3-free by
  ## construction — nothing here touches the real solver.
  let c = calls
  result = proc(trace: seq[ChoiceNode]; targetBranchIndex: int): ConcolicBridgeResult =
    inc c[]
    raise SoftlinkError(msg: "libz3.so(.4|): cannot open shared object file",
                        symbol: "Z3_mk_config",
                        library: "libz3.so(.4|)")

suite "RFC-z3-optional S1b2 — a campaign whose solver cannot load degrades, not aborts":

  test "the campaign runs to completion instead of dying on the optional feature":
    let calls = new(int)
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(degradeGate), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = ConcolicAssist(bridge: guardSolverUnavailable(raisingBridge(calls)),
                                              stallRounds: 1, maxBranchAttempts: 8))
    check report.iterations == 60

  test "the degrade is REPORTED, not swallowed: cfoSolverUnavailable is observed to fire":
    # An arm that is defined but never observed firing is the
    # defined-but-dark class this RFC deletes elsewhere; asserting it
    # positively is what keeps this one honest.
    let calls = new(int)
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(degradeGate), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = ConcolicAssist(bridge: guardSolverUnavailable(raisingBridge(calls)),
                                              stallRounds: 1, maxBranchAttempts: 8))
    check report.stats.concolicYield.solverUnavailable > 0
    check report.stats.concolicYield.flip.byOutcome[cfoSolverUnavailable] > 0
    # And nothing is falsely claimed: no solve, no concolic admission.
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic == 0
    check report.stats.provenanceCounts[pvConcolic] == 0

  test "the latch stops re-attempting the load: the failing bridge is invoked exactly once":
    # Without a latch the bridge is re-entered up to `maxBranchAttempts`
    # times per stall round, EVERY stall round — so a broken load is
    # re-attempted (and re-raised, and re-caught) hundreds of times across
    # a campaign. `maxBranchAttempts = 8` and a 60-iteration campaign that
    # stalls repeatedly make that difference unmissable: 1 versus many.
    let calls = new(int)
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(degradeGate), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = ConcolicAssist(bridge: guardSolverUnavailable(raisingBridge(calls)),
                                              stallRounds: 1, maxBranchAttempts: 8))
    check calls[] == 1
    # The latch suppresses the RE-ATTEMPT, not the REPORTING: every
    # subsequent guarded call still answers `cfoSolverUnavailable`, so the
    # yield tally reflects how often the assist was actually wanted.
    check report.stats.concolicYield.solverUnavailable > 1

  test "a guarded bridge that does NOT raise is passed through untouched":
    # The guard must be transparent on the happy path — a wrapper that
    # perturbed a working bridge would be worse than the abort it fixes.
    var calls = 0
    let working = proc(trace: seq[ChoiceNode]; targetBranchIndex: int): ConcolicBridgeResult =
      inc calls
      ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                           materialized = @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]))
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(degradeGate), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = ConcolicAssist(bridge: guardSolverUnavailable(working),
                                              stallRounds: 1, maxBranchAttempts: 8))
    check calls > 0
    check report.coverageHits == 2
    check report.stats.concolicYield.solvedExact > 0
    check report.stats.concolicYield.solverUnavailable == 0

  test "a real assist is guarded by construction, and its happy path is unaffected":
    # `concolicAssist` wraps its own generated closure in the same guard —
    # so the production path gets the degrade for free, and this pins that
    # adding the guard did not break real solving.
    let report = fuzzConcolic(integers(0, 0xFFFFFFFF), degradeGate,
                              FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.coverageHits == 2
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.concolicYield.solverUnavailable == 0
