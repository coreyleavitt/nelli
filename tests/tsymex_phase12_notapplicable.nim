## Phase 12 cycle 5 — `sfNotApplicable` enum case on
## `SymexFindingStatus`. Semantically distinct from `sfUnsat`:
## `sfUnsat` is "we searched, the target is unreachable"; the new
## case is "symex was not the appropriate tool here" — e.g. the
## zero-targets fallback (cycle 18) and the shape-mismatch seed
## path in `symexSeedPhase` (cycle 14).
##
## The audit step of this cycle confirmed that no existing site
## pattern-matches `SymexFindingStatus` exhaustively (`grep -n
## "case.*status"` returns equality probes only), so no follow-on
## case-arm updates are required.
import std/unittest
import nelli/engine/types

suite "symex Phase 12 cycle 5 — sfNotApplicable":
  test "sfNotApplicable is a distinct, constructible status":
    let f = SymexFinding(targetDesc: "no-targets-discovered",
                         status: sfNotApplicable)
    check f.status == sfNotApplicable
    check $f.status == "sfNotApplicable"
    # Distinct from the three pre-existing cases — same string
    # surface as sfUnsat would falsely conflate "tool inapplicable"
    # with "searched and proved unreachable".
    check $f.status != $sfSat
    check $f.status != $sfUnsat
    check $f.status != $sfUnknown
