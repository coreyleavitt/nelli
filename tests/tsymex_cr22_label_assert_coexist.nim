## CR-22 regression: label + doAssert coexistence in a single proc body.
##
## Bug: `parseStmtInner` applied `findAssertFailsCond` greedily to the entire
## enclosing `nnkStmtList`.  When a doAssert expansion was found ANYWHERE in
## the subtree, the whole StmtList was replaced by the assert-raise IR,
## silently dropping sibling statements (e.g. `symexTarget` calls).
##
## Fix (CR-22): scope the detection to the `nnkPragmaBlock` node that IS the
## assert expansion.  The StmtList arm now parses each child individually;
## the `symexTarget` label and the `doAssert` both surface as separate IR
## nodes in the correct order.
##
## This file is the dedicated regression guard for CR-22.  It pins that:
##   1. A symexTarget label that PRECEDES a doAssert in the same proc body
##      produces an sfSat finding with the correct label.
##   2. The doAssert still produces an sfRaised(AssertionDefect) finding
##      alongside the label — neither suppresses the other.
##   3. A standalone doAssert (no label sibling) still works identically.
import std/[unittest, sequtils]
import proptest/symex
import proptest/db
import proptest/smt/[types, dsl, runtime]
import proptest/engine/types

# --- CR-22: proc with BOTH a label and a doAssert ----------------------------
proc withLabelAndAssert(x: int) =
  if x == 0:
    symexTarget("zero")   # label precedes the assert
  doAssert x != 0         # assert must NOT swallow the label

# --- Control: standalone doAssert (no label) — E6 baseline must still work --
proc standaloneAssert(x: int) =
  doAssert x > 0

suite "CR-22 regression — symexTarget label + doAssert coexistence":

  test "label preceding doAssert: sfSat for the label IS found":
    ## Before the fix, `parseStmtInner` replaced the entire StmtList with the
    ## assert-raise IR, causing irCollectLabels to find zero labels and
    ## symexFindAllWitnesses to return no sfSat finding.
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(withLabelAndAssert, db)
    let satFindings = findings.filterIt(
      it.status == sfSat and it.targetDesc == "label(\"zero\")")
    check satFindings.len >= 1

  test "doAssert still raises sfRaised(AssertionDefect) alongside the label":
    ## The assert-raise IR for the doAssert must be preserved as a sibling,
    ## not lost.  The walker must still surface sxRaised{AssertionDefect}.
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(withLabelAndAssert, db)
    let raisedFindings = findings.filterIt(
      it.status == sfRaised and it.defectTypeId == "AssertionDefect")
    check raisedFindings.len >= 1

  test "symexFind tLabel still locates the label with a co-present doAssert":
    let r = symexFind(withLabelAndAssert, tLabel("zero"))
    check r.status == sxSat
    check r.witness[0] == 0

  test "standalone doAssert (no label): sfRaised still produced — E6 baseline":
    ## Guard: the scoped fix must not break the simple E6 case where the
    ## entire proc body IS the doAssert expansion and nothing else.
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(standaloneAssert, db)
    let raised = findings.filterIt(
      it.status == sfRaised and it.defectTypeId == "AssertionDefect")
    check raised.len >= 1

  test "symexFind tRaisedExn on standalone doAssert: sxRaised — E6 baseline":
    let r = symexFind(standaloneAssert, tRaisedExn("AssertionDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] <= 0
