## Phase 12 cycle 16 — `symexForAll` single-arg sugar macro.
##
## One-line entry that combines Layer 1 (`symexFindAllWitnesses` →
## discovered targets + witnesses) with Layer 2
## (`forAllWithSymexSeeds` → engine pipeline with `symexSeedPhase`).
## The SUT proc doubles as the property under the random + symex-
## seeded loop.
##
## The Report carries `symexFindings` so callers can audit which
## targets symex reached without needing a separate Layer-1 call.
import std/[unittest, options]
import nelli
import nelli/symex
import nelli/engine/types

# Module-scope SUT so `getImpl` can resolve it during macro
# expansion.
proc handle(req: int) =
  if req == 0:
    symexTarget("zero")

proc handlePair(a: int, b: bool) =
  # Two-arg SUT for the multi-arg destructuring path. `symexTarget`
  # only fires when both arms pin (Z3 picks `a=0, b=true`).
  if a == 0 and b:
    symexTarget("pair-hit")

suite "symex Phase 12 cycle 16 — symexForAll (single-arg)":
  test "Report.symexFindings carries the auto-discovered label finding":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let report = symexForAll(integers(0, 1000), handle, db)
    # The SUT never raises — symex's witness merely *reaches* the
    # marker. The terminal Report is otPassed.
    check report.outcome == otPassed
    # The label target's finding is present in the Report.
    var found = false
    for f in report.symexFindings:
      if f.targetDesc == "label(\"zero\")" and f.status == sfSat:
        found = true
    check found

  test "multi-arg fn destructures the strategy's tuple element type":
    # `map(integers(), booleans())` yields `Strategy[(int, bool)]`.
    # The macro emits a wrapper that splats the tuple positionally
    # into `handlePair(a, b)` while passing `handlePair` itself to
    # Layer 1 for IR scanning.
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let report = symexForAll(
      map(integers(0, 1000), booleans()),
      handlePair, db)
    check report.outcome == otPassed
    var found = false
    for f in report.symexFindings:
      if f.targetDesc == "label(\"pair-hit\")" and f.status == sfSat:
        found = true
    check found
