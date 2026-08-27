## RFC-fuzzer-nextgen S2 — the operator bandit WIRED into the fuzz loop.
## `nelli/bandit.nim`'s `OperatorBandit`/`chooseOperator`/`credit` (proven in
## isolation in `tfuzzbandit.nim`) replaces the old uniform `mod pickMax`
## mutator pick as the loop's DEFAULT. `FuzzSettings.uniformOperators` is the
## S1-style opt-out (mirrors `uniformSchedule`'s polarity): the adaptive
## strategy is unconditionally the default, and `uniformOperators: true`
## reproduces the pre-S2 uniform trajectory.
##
## Determinism gating (like S1): every `tfuzz*`/`tdb` test that pins an exact
## seed-dependent trajectory (`tfuzzi2s.nim`'s `coverageHits == 1`/`== 2`
## headline gates in particular) was re-verified GREEN under the bandit-as-
## default before this default was chosen — none pinned the old uniform
## pick specifically, so the flip needed no separate determinism gate on
## THEIR side; this file adds S2's OWN loop-level coverage.
import std/unittest
import nelli

proc monotoneCoverageTarget(): Target[int] =
  ## Bigger inputs light strictly more edges — mirrors `tfuzzschedule.nim`'s
  ## own fixture (kept local so this file has no cross-file test coupling).
  Target[int](run: proc(x: int): Observation[int] =
    let k = max(0, min(x, 64))
    var c = newSeq[byte](64)
    for i in 0 ..< k: c[i] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc banditDeadbeefGate(x: int) {.cover, covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

suite "operator bandit — loop wiring (RFC-fuzzer-nextgen S2)":
  test "the bandit (the default) is deterministic in the seed":
    var f1 = newCoverageFrontier()
    var f2 = newCoverageFrontier()
    let a = fuzz(integers(0, 100000), monotoneCoverageTarget(), f1,
                 FuzzSettings(maxIterations: 400, seed: 7))
    let b = fuzz(integers(0, 100000), monotoneCoverageTarget(), f2,
                 FuzzSettings(maxIterations: 400, seed: 7))
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len

  test "uniformOperators fallback is deterministic in the seed":
    var f1 = newCoverageFrontier()
    var f2 = newCoverageFrontier()
    let a = fuzz(integers(0, 100000), monotoneCoverageTarget(), f1,
                 FuzzSettings(maxIterations: 400, seed: 7, scheduling: SchedulingConfig(uniformOperators: true)))
    let b = fuzz(integers(0, 100000), monotoneCoverageTarget(), f2,
                 FuzzSettings(maxIterations: 400, seed: 7, scheduling: SchedulingConfig(uniformOperators: true)))
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len

  test "the bandit default finds at least as much coverage as the uniform fallback":
    var fb = newCoverageFrontier()
    var fu = newCoverageFrontier()
    let bandit = fuzz(integers(0, 100000), monotoneCoverageTarget(), fb,
                      FuzzSettings(maxIterations: 400, seed: 3))
    let uniform = fuzz(integers(0, 100000), monotoneCoverageTarget(), fu,
                       FuzzSettings(maxIterations: 400, seed: 3, scheduling: SchedulingConfig(uniformOperators: true)))
    check bandit.coverageHits > 0
    check bandit.coverageHits >= uniform.coverageHits

  test "enableI2S: true — the I2S arm participates in the bandit (default operator selection)":
    # Same shape as tfuzzi2s.nim's own headline, but exercised under the
    # BANDIT default (uniformOperators left unset) rather than G5's
    # standalone fixture — proves the 6th (I2S) arm is genuinely reachable
    # through chooseOperator's arm-index space, not just present when
    # forced via the old uniform mod-6 pick.
    let withI2S = fuzzWith(integers(0, 0xFFFFFFFF), banditDeadbeefGate,
                           FuzzSettings(seed: 11'u64, maxIterations: 300, guidance: GuidanceConfig(enableI2S: true)))
    check withI2S.coverageHits == 2   # both the "hit" and "miss" edges
    let withoutI2S = fuzzWith(integers(0, 0xFFFFFFFF), banditDeadbeefGate,
                              FuzzSettings(seed: 11'u64, maxIterations: 300))
    check withoutI2S.coverageHits == 1  # only "miss" — the bandit alone can't guess 1-in-4B
