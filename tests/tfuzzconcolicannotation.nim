## RFC-0016 K8-0 -- `annotationViolations` gets its reader.
##
## A false `{.symexTransparent.}` claim is a PARSE-time fact about the
## property (the annotated callee's result is used, or an argument is not
## inert), found when the concolic assist walks the property. Before K8-0 it
## reached `ConcolicCollectResult.annotationViolations` and stopped there:
## `runConcolicFlipImpl` read the collect for its counters and dropped the
## violations, so the fuzzer, the only production caller, never saw them.
##
## The reader: `ConcolicFlipResult.annotationViolations` carries them out of
## the walker, the `Orchestrator` accumulates them (one per distinct site and
## kind, however many flips ran), and `FuzzReport.annotationViolations` hands
## them to the caller beside `irCrashes`. Verdict-neutral: a violation is a
## defect in the annotated code, not a crash, so it never adds a crash or
## changes the campaign's trajectory.
import std/unittest
import nelli
import nelli/concolic
import nelli/choice

var probeState = 11   ## module-level: unmodellable, and deliberately so

proc probe(): int {.symexTransparent.} = probeState

proc gateWithFalseClaim(drawnInt: int) {.cover.} =
  let p = probe()          ## result USED: the transparent promise is false
  discard p
  if drawnInt == 0xCAFEBABE:
    discard "gate"
  else:
    discard "miss"

proc gateClean(drawnInt: int) {.cover.} =
  if drawnInt == 0xCAFEBABE:
    discard "gate"
  else:
    discard "miss"

suite "K8-0 -- annotation violations reach the fuzzer's caller":

  test "fuzz with a concolic assist reports a false transparent claim":
    let assist = concolicAssist(integers(0, 0xFFFFFFFF), gateWithFalseClaim)
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF),
                      inProcessTarget(gateWithFalseClaim), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = assist)
    check report.stats.concolicYield.collect.parseDeclines == 0
    check report.annotationViolations.len == 1      # deduped across flips
    check report.annotationViolations[0].callee == "probe"
    check report.annotationViolations[0].kind == avResultUsed
    check report.irCrashes.len == 0                 # not a crash

  test "fuzzConcolic surfaces it through the default form":
    let report = fuzzConcolic(integers(0, 0xFFFFFFFF), gateWithFalseClaim,
                              FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.annotationViolations.len == 1
    check report.annotationViolations[0].callee == "probe"

  test "a clean property reports none (the field is not always-on)":
    let assist = concolicAssist(integers(0, 0xFFFFFFFF), gateClean)
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(gateClean),
                      frontier, FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = assist)
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0   # the bridge ran
    check report.annotationViolations.len == 0

  test "no assist, no walk: nothing to report":
    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 0xFFFFFFFF),
                      inProcessTarget(gateWithFalseClaim), frontier,
                      FuzzSettings(seed: 42'u64, maxIterations: 20))
    check report.annotationViolations.len == 0

  test "the flip result itself carries the violations (K8a's raw seam)":
    let trace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let flip = concolicFlip(gateWithFalseClaim, trace, bindings, 0)
    check flip.annotationViolations.len == 1
    check flip.annotationViolations[0].callee == "probe"
    let clean = concolicFlip(gateClean, trace, bindings, 0)
    check clean.annotationViolations.len == 0
