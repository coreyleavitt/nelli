## RFC-fuzzer-nextgen G3 C4 — the REAL concolic bridge, end to end.
## `tfuzzconcolicbridge.nim` already proved the orchestration (staleness
## detection, re-verify-gated admission, S1 Entropic energy) is correct
## against a FAKE `ConcolicBridgeEntry`; this file is the headline that was
## blocked on that work — a real Z3 solve breaking through a gate mutation
## cannot reach.
##
## **RFC-z3-optional inverted this file's premise.** It used to be
## deliberately just `import nelli`, on the grounds that a caller who never
## mentions symex "still gets it for free". That freebie is precisely what
## made `import nelli` reach Z3, breaking the contract `README.md:91-95`
## documents and `tests/tsmoke.nim` asserts. The assist is now opt-in: the
## extra `import nelli/concolic` below IS the seam, and `fuzzConcolic` is
## the documented default form.
import std/[unittest, tables]
import nelli
import nelli/concolic

proc magicGate(drawnInt: int) {.cover.} =
  ## The RFC's own headline example (mirrors G2's `magicByteGate`, now under
  ## REAL `{.cover.}` instrumentation so it produces two distinct, real
  ## bitmap edges): mutation over `integers(0, 0xFFFFFFFF)` would need up to
  ## 2^32 tries to land exactly on 0xCAFEBABE.
  if drawnInt == 0xCAFEBABE:
    discard "gate"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen G3 C4 — real concolic bridge through fuzz()":

  test "stalled campaign through fuzzConcolic breaks the 0xCAFEBABE gate":
    let report = fuzzConcolic(integers(0, 0xFFFFFFFF), magicGate,
                              FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.coverageHits == 2   # BOTH edges — including the magic-byte gate
    # RFC-fuzzer-nextgen S5b: the real bridge's yield taxonomy reaches
    # CampaignStats — this campaign's stall-triggered bridge call(s) solved
    # at least once (exact or optimistic; the gate breaks either way).
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.provenanceCounts[pvConcolic] > 0

  test "the identical campaign with no assist (plain fuzz) never reaches the gate":
    # The negative control now differs by the ENTRY POINT, not by a nested
    # config key: `fuzz` is the Z3-free door, `fuzzConcolic` the assisted
    # one. There is no third state where you called the assisted door and
    # got nothing.
    let report = fuzz(integers(0, 0xFFFFFFFF), magicGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.coverageHits == 1   # only the ordinary (miss) edge
    check report.stats.provenanceCounts[pvConcolic] == 0

proc uint64Gate(x: uint64) {.cover.} =
  if x == 0xCAFEBABE'u64:
    discard "gate"
  else:
    discard "miss"

suite "R1 — concolic bridge never aborts a campaign on an int64-unrepresentable draw":

  test "a plain uint64 param (ordinary derived strategy) through the real bridge completes the campaign":
    # `arbitrary(uint64)` is `derive.nim`'s stock strategy: it draws over the
    # FULL uint64 range, whose upper half does not fit `int64` (the
    # concolic bridge's Z3 domain). Before the fix, the bridge narrowed
    # that range unguarded, built an inverted/unsatisfiable Z3 domain, and
    # `materializeConcolicModel` raised `ValueError` — uncaught anywhere
    # between the bridge and the fuzz loop, aborting the entire campaign.
    # `fuzzConcolic` is what reaches the concolic assist at all; plain
    # `fuzz` never builds a bridge.
    let report = fuzzConcolic(arbitrary(uint64), uint64Gate,
                              FuzzSettings(seed: 42'u64, maxIterations: 60))
    # The campaign must run to completion (no exception escaping mid-loop) —
    # `iterations` reaching `maxIterations` is the proof, independent of
    # whether the concolic bridge itself happened to solve anything this run.
    check report.iterations == 60
    check report.coverageHits >= 1
