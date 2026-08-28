## RFC-z3-optional — `concolicAssist`, the opt-in bridge builder.
##
## Design D's whole claim is that the Z3-free seam ALREADY exists (`fuzz`'s
## zero-defaulted assist parameter / `newOrchestrator`'s nil-defaulted
## bridge) and that v0.6.0's defect was auto-*wiring* it from core. That claim
## is only true if a real, Z3-backed bridge can be built OUTSIDE
## `fuzzmacro`'s codegen and handed to those seams by an ordinary caller.
## Nothing in the tree tested that: every real bridge came from the macro,
## and every raw-seam test passed a hand-written fake.
##
## Both suites here are that missing proof, and they are the two seams the
## RFC documents:
##
## 1. `fuzz`'s runtime `assist` proc parameter;
## 2. the raw `newOrchestrator(..., concolicBridge = ...)` seam — the
##    documented `concolicBridge = concolicAssist(s, p).bridge` form. This
##    one keeps its shape by design: it IS the low-level seam, and it
##    deliberately keeps bridge and policy as independent knobs.
##
## The assertions are the discriminating pair (`solvedExact +
## solvedOptimistic > 0`, plus a `pvConcolic` admission), not "the suite is
## green": a bridge that never fires passes every non-discriminating check
## in the Track-G suites.
##
## `import nelli` + `import nelli/concolic` is the target consumer shape:
## core alone never reaches Z3, and the assist arrives with the extra
## import.
import std/[unittest, tables]
import nelli
import nelli/concolic
import nelli/choice

proc magicGate(drawnInt: int) {.cover.} =
  ## The RFC's headline example (same body as
  ## `tfuzzconcolicbridge_real.nim`): mutation over `integers(0, 0xFFFFFFFF)`
  ## would need up to 2^32 tries to land exactly on 0xCAFEBABE, so a
  ## second covered edge here can only have come from a real solve.
  if drawnInt == 0xCAFEBABE:
    discard "gate"
  else:
    discard "miss"

suite "RFC-z3-optional — concolicAssist through fuzz's runtime assist parameter":

  test "the assist, passed to `fuzz`'s assist parameter, breaks the 0xCAFEBABE gate":
    let assist = concolicAssist(integers(0, 0xFFFFFFFF), magicGate)
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(magicGate), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = assist)
    check report.coverageHits == 2   # BOTH edges — including the magic-byte gate
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.provenanceCounts[pvConcolic] > 0

  test "the identical campaign with no assist wired never reaches the gate":
    # The paired negative control: same seed, same iteration budget — the
    # ONLY difference is the assist. Without it the campaign covers one
    # edge, which is what makes the check above a signal rather than a
    # tautology. Note there is no second key to also omit: under the
    # reified assist, this IS the off switch.
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(magicGate), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.coverageHits == 1
    check report.stats.provenanceCounts[pvConcolic] == 0

  test "the assist carries its own activation policy":
    # `stallRounds`/`maxBranchAttempts` travel WITH the assist (round-2
    # refinement) rather than living in a second, separately-omittable
    # `GuidanceConfig` key. An assist that defaulted `stallRounds` to 0
    # would be inert by construction — the exact no-op the reification
    # exists to close.
    let assist = concolicAssist(integers(0, 0xFFFFFFFF), magicGate)
    check assist.bridge != nil
    check assist.stallRounds == 1
    check assist.maxBranchAttempts == 8
    let tuned = concolicAssist(integers(0, 0xFFFFFFFF), magicGate,
                               stallRounds = 3, maxBranchAttempts = 2)
    check tuned.stallRounds == 3
    check tuned.maxBranchAttempts == 2

suite "RFC-z3-optional — concolicAssist through the raw newOrchestrator seam":

  test "a stalled orchestrator wired with the real assist bridge admits a pvConcolic seed":
    # `concolicBridge = concolicAssist(s, p).bridge` is the documented
    # advanced form for the low-level seam. Round 3 found it exercised
    # nowhere — all seven orchestrator-level sites in
    # `tfuzzconcolicbridge.nim` hand-write a fake — so it would have
    # shipped dark.
    let assist = concolicAssist(integers(0, 0xFFFFFFFF), magicGate)
    var frontier = newCoverageFrontier()
    let o = newOrchestrator(integers(0, 0xFFFFFFFF), inProcessTarget(magicGate), frontier,
                            policy = orchestratorPolicy(stallRounds = 1),
                            concolicBridge = assist.bridge)
    # A concrete miss trace, admitted repeatedly so the shared frontier
    # goes stale — the precondition `tryConcolicBridge` gates on.
    let missTrace = @[integerChoice(1, 0, 0xFFFFFFFF, 0)]
    for i in 0 ..< 5:
      discard admit(o, missTrace, o.run(missTrace))
    check frontier.coveredEdges == 1

    let r = tryConcolicBridge(o, missTrace)
    check r.ar.admitted
    check r.ar.provenance == pvConcolic
    check o.concolicYield.solvedExact + o.concolicYield.solvedOptimistic > 0
    check frontier.coveredEdges == 2   # the solve reached the gate edge
