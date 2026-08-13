## Phase 12 cycle 19 — `derandomize=true` × symex-seed integration.
##
## Contract pin: when the user enables deterministic-replay mode
## via `Settings.derandomize = true` + a non-empty `Settings.testId`,
## two consecutive `symexForAll` calls must produce identical
## Reports AND the symex-seed path must still run (i.e., derandomize
## does NOT short-circuit Layer 1 + symexSeedPhase). No code change
## from the prior cycle — this cycle pins the contract observably.
import std/[unittest, options]
import nelli
import nelli/symex
import nelli/engine/types

proc handleFalsifying(req: int) =
  # `symexFindAllWitnesses` surfaces the marker target; the random
  # loop afterwards falsifies on `req == 0` (the SAT witness), so
  # the Report carries a shrunk counterexample for the equality
  # comparison below.
  if req == 0:
    symexTarget("zero")
  doAssert req != 0

suite "symex Phase 12 cycle 19 — derandomize × symex seeds":
  test "derandomize=true: two runs produce identical Reports and the symex path ran":
    var settings = defaultSettings()
    settings.derandomize = true
    settings.testId = "phase12-cycle19-pin"

    discard consumeSymexFindings()
    let r1 = symexForAll(integers(0, 1000), handleFalsifying,
                         inMemoryDatabase(), forAllSettings = settings)
    discard consumeSymexFindings()
    let r2 = symexForAll(integers(0, 1000), handleFalsifying,
                         inMemoryDatabase(), forAllSettings = settings)

    # Determinism: identical verdicts and counterexamples.
    check r1.outcome == r2.outcome
    check r1.outcome == otFalsified
    check r1.counterexample == r2.counterexample
    check r1.counterexample.isSome
    check r1.counterexample.get == 0

    # Symex path actually ran on both calls — neither Report can
    # have an empty symexFindings list, and the "zero" label
    # finding is present in each.
    proc hasZeroFinding(r: Report[int]): bool =
      for f in r.symexFindings:
        if f.targetDesc == "label(\"zero\")" and f.status == sfSat:
          return true
      false
    check hasZeroFinding(r1)
    check hasZeroFinding(r2)
