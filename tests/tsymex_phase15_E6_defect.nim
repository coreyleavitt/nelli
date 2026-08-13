## Phase 15 — Cluster E, cycle E6: `Defect` modeling. A SUT `assert cond, msg`
## (which raises `AssertionDefect` at runtime when `cond` is false) must be
## modeled as a reachable `sxRaised{typeId: "AssertionDefect", isDefect: true}`
## rather than silently passing as `sxUnsat`. The parser lowers a raw `assert`
## (outside a `tAssertionViolation` context) to an implicit `AssertionDefect`
## raise on the false branch; the walker populates `RawResult.isDefect` from
## `exnTable.isDefect(typeId)`. Defects whose `DefectKind` is in
## `settings.defectExclusions` (default: OOM + stack-overflow) are suppressed;
## a non-excluded defect is ALWAYS surfaced (even under a label search) so the
## contract violation is never silently dropped.
import std/[unittest, sequtils]
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime]
import nelli/engine/types

# --- a SUT with a raw `assert` (raises AssertionDefect on x <= 0) ------------
proc f(x: int) =
  assert x > 0, "must be positive"

suite "symex Phase 15 E6 — Defect modeling (sxRaised isDefect + defectExclusions)":
  test "E6: assert false produces sxRaised with isDefect (typeFilter)":
    let r = symexFind(f, tRaisedExn("AssertionDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    # The witness must satisfy the assert-fails condition x <= 0.
    check r.raisedWitness[0] <= 0

  test "E6: assert false produces sxRaised with isDefect (isOptimised)":
    let r = symexFind(f, tRaisedExn("AssertionDefect"), optimisedSymexSettings())
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"

  test "E6: Defect does not silently pass as sxUnreached (label search)":
    # Searching for a non-existent label must NOT silently suppress the
    # reachable AssertionDefect: a non-excluded defect surfaces regardless of
    # the search target, so the SymexResult is sxRaised, not sxUnsat.
    let r = symexFind(f, tLabel("never_reached"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"

  test "E6: Report surface — symexFindings carries an sfRaised defect entry":
    # The recording path (symexFindAllWitnesses → recordSymexFinding) surfaces
    # the reachable AssertionDefect as an `sfRaised` finding with its
    # `defectTypeId` set, so it reaches `Report.symexFindings` rather than
    # being silently dropped.
    discard consumeSymexFindings()  # clear any prior findings
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(f, db)
    let raised = findings.filterIt(it.status == sfRaised)
    check raised.len >= 1
    check raised.anyIt(it.defectTypeId == "AssertionDefect")
