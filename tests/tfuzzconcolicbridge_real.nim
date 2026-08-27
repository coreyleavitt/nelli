## RFC-fuzzer-nextgen G3 C4 — the REAL concolic bridge, wired through the
## `fuzz(...)` macro (`fuzzmacro.nim`), end to end. `tfuzzconcolicbridge.nim`
## already proved the orchestration (staleness detection, re-verify-gated
## admission, S1 Entropic energy) is correct against a FAKE
## `ConcolicBridgeEntry`; this file is the headline that was blocked on that
## work — a real Z3 solve, invoked automatically by the macro, breaking
## through a gate mutation cannot reach.
##
## Deliberately just `import nelli` (not `import nelli/symex`): the whole
## point of wiring the bridge INTO the macro is that an ordinary caller who
## never mentions symex/Z3 still gets it for free.
import std/unittest
import nelli

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

  test "stalled campaign with the real bridge wired (stallRounds > 0) breaks the 0xCAFEBABE gate":
    let report = fuzz(integers(0, 0xFFFFFFFF), magicGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60, guidance: GuidanceConfig(stallRounds: 1)))
    check report.coverageHits == 2   # BOTH edges — including the magic-byte gate
    # RFC-fuzzer-nextgen S5b: the real bridge's yield taxonomy reaches
    # CampaignStats — this campaign's stall-triggered bridge call(s) solved
    # at least once (exact or optimistic; the gate breaks either way).
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.provenanceCounts[pvConcolic] > 0

  test "the identical campaign with stallRounds left at 0 (the default) never reaches the gate":
    let report = fuzz(integers(0, 0xFFFFFFFF), magicGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.coverageHits == 1   # only the ordinary (miss) edge

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
    # `stallRounds: 1` is required to reach the concolic bridge at all (the
    # default `0` disables it).
    let report = fuzz(arbitrary(uint64), uint64Gate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60, guidance: GuidanceConfig(stallRounds: 1)))
    # The campaign must run to completion (no exception escaping mid-loop) —
    # `iterations` reaching `maxIterations` is the proof, independent of
    # whether the concolic bridge itself happened to solve anything this run.
    check report.iterations == 60
    check report.coverageHits >= 1
