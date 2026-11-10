## RFC-0016 W3-z R4 (findings U4, U5).
##
## U4: the concolic float -> int conversion decides its undefined side through
## `decideUndefined`, so the flip solve keeps it defined (`definedFacts`) and an
## out-of-range input is reported on `undefinedReached`, never used as a seed
## the fuzzer would run natively.
## U5: `ConcolicFlipResult.soundness` carries the reached undefined kinds and
## the collect pass's declines, and `fromFlip` claims it, so an unsat flip over
## either is not a trusted `sxUnsat`.
import std/[unittest, strutils]
import nelli/symex
import nelli/int128
import nelli/smt/errorkind
import ./s8cu_helpers

const i32max = 2147483647'i64

proc cvtGate(a: int32) =
  if int32(float32(a)) == 2147483647'i32:   # only an out-of-range conversion
    symexTarget("big")

proc divGate(a, b: uint32) =
  if a > 0'u32:
    if a div b > a:
      symexTarget("wrapped")

let bs1 = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
let bs2 = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
            ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]

suite "W3-z R4: concolic undefined behaviour is wired":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 316


  test "U4: an out-of-range float -> int conversion is never the seed":
    let r = concolicFlip(cvtGate, @[integerChoice(1, -i32max - 1, i32max, 0)],
                         bs1, 0, pinSettingsConst, z3TimeoutMs = 60000'u)
    check r.outcome == cfoUnsat
    check r.materialized.len == 0
    check r.undefinedReached.len == 1
    if r.undefinedReached.len == 1:
      check r.undefinedReached[0].kind == UbKind(ubFloatToIntRange)

  test "U5: an unsat flip over a reached undefined operation is not trusted":
    let r = concolicFlip(divGate, @[integerChoice(5, 0, 4294967295'i64, 0),
                                    integerChoice(2, 0, 4294967295'i64, 0)],
                         bs2, 1, pinSettingsConst)
    check r.outcome == cfoUnsat
    check r.undefinedReached.len == 1
    check r.soundness.witnessUndefined == {UbOrdinal(ord(ubUnsignedDivZero) -
                                                    ord(low(UbKind)))}
    check not fromFlip[(int32,)](r, "concolicFlip").res.trusted

  test "U5: an unsat flip over a decline is not trusted":
    var r = oneShotFlip(cfoUnsat, ccoNotApplicable)
    r.soundness.replay = rsNotNeeded
    check fromFlip[(int32,)](r, "concolicFlip").res.trusted   # clean: unchanged
    r.soundness.runTaint = {scIncomplete}
    check not fromFlip[(int32,)](r, "concolicFlip").res.trusted
