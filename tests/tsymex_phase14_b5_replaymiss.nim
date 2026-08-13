## Phase 14 cycle B5 — `SymexFindingStatus.sfReplayMiss`.
##
## Per RFC §B5 (revised): the original B5 design called for
## `symexCapture` armed in `symexSeedPhase`. Round-1 review
## surfaced that `symexSeedPhase` receives raw choice sequences
## with no attached target metadata, so `sfReplayMiss` cannot be
## reliably computed at that layer. Revised scope: B5 introduces
## the `sfReplayMiss` finding-status and wires `symexCapture`
## per-replay inside `assertCoveredBy` (where target provenance IS
## available). `symexSeedPhase` is unchanged; its capture is a
## future RFC if a consumer needs it.
##
## This test pins the enum extension. The per-replay capture path
## inside `assertCoveredBy` was already wired by Phase 7 (capture
## context, hits set); B5's addition is the enum value distinct
## from `sfUnsat`/`sfUnknown` for cases where the seed reached
## sxSat but the replay didn't observe the target.
import std/unittest
import nelli/engine/types

suite "symex Phase 14 cycle B5 — sfReplayMiss":
  test "SymexFindingStatus exposes sfReplayMiss distinct from siblings":
    check sfReplayMiss != sfSat
    check sfReplayMiss != sfUnsat
    check sfReplayMiss != sfUnknown
    check sfReplayMiss != sfNotApplicable

  test "SymexFinding can be constructed with status: sfReplayMiss":
    let f = SymexFinding(
      targetDesc: "label(\"missed\")",
      status: sfReplayMiss,
      covered: false)
    check f.status == sfReplayMiss
    check f.targetDesc == "label(\"missed\")"
    check f.covered == false
