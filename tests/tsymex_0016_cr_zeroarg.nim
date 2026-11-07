## RFC-0016 code-review fix -- every public symex entry point accepts a
## zero-parameter SUT. `symexFindAllWitnesses` built its witness type from
## the parameter list and failed to compile ("type expected") when empty.
import std/unittest
import nelli
import nelli/symex
import nelli/engine/types

proc sutHit() =
  symexTarget("hit")

proc sutDead() =
  let x = 3
  if x > 5: symexTarget("dead")

suite "zero-argument SUT":
  test "symexFindAllWitnesses: reachable label is sfSat":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(sutHit, db)
    check fs.len == 1
    check fs[0].targetDesc == "label(\"hit\")"
    check fs[0].status == sfSat

  test "symexFindAllWitnesses: unreachable label is sfUnsat":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(sutDead, db)
    check fs.len == 1
    check fs[0].status == sfUnsat

  test "symexFind: reachable is sxSat, unreachable is sxUnsat":
    check symexFind(sutHit, tLabel("hit")).status == sxSat
    check symexFind(sutDead, tLabel("dead")).status == sxUnsat

  test "assertCoveredBy accepts a zero-argument SUT":
    assertCoveredBy(sutHit, tLabel("hit"))

  test "symexForAll accepts a zero-argument SUT":
    let db = inMemoryDatabase()
    let report = symexForAll(just(()), sutHit, db)
    check report.outcome == otPassed
    var found = false
    for f in report.symexFindings:
      if f.targetDesc == "label(\"hit\")" and f.status == sfSat: found = true
    check found
