## Phase 14 cycle A7b — `var T` propagation downstream.
##
## A7b removes Phase-12's `var T` guard in
## `symexFindAllWitnesses` and changes `assertCoveredBy`'s
## test-runtime emission to wrap each witness component in a
## fresh `var` local so `var T` SUTs receive an addressable
## lvalue (pre-A7b emission `testFn(wit[0], …)` rejected `var T`
## SUTs at compile time).
##
## RED test 1 — `symexFindAllWitnesses` accepts a `var T` SUT and
## reports the label finding.
##
## RED test 2 — `assertCoveredBy` accepts a `var T` SUT and
## verifies coverage on the witness.
import std/[unittest, options]
import nelli
import nelli/symex
import nelli/engine/types

proc varParamSUT(x: var int) =
  x = x * 2
  if x == 10:
    symexTarget("doubled-to-10")

suite "symex Phase 14 cycle A7b — var T downstream":
  test "symexFindAllWitnesses accepts var T SUT":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(varParamSUT, db)
    var sawHit = false
    for f in findings:
      if f.targetDesc == "label(\"doubled-to-10\")" and f.status == sfSat:
        sawHit = true
    check sawHit

  test "assertCoveredBy with var T SUT covers the witness":
    # The SUT itself doubles `x` in-place then targets when x==10,
    # so the witness x=5 (initial value) drives the test runtime
    # to the target. Pre-A7b the emitted `testFn(wit[0])` failed
    # to compile because `wit[0]` is an rvalue.
    assertCoveredBy(varParamSUT, tLabel("doubled-to-10"))
