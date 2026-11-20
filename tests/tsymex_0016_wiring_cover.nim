## Wiring audit (wave 4), C-8: `assertCoveredBy`'s raised finding names the
## defect it reaches (`defectTypeId`), as `symexFindAllWitnesses`' does.
import std/[unittest, strutils]
import nelli/symex

proc boom(x: int) =
  doAssert x != 7

suite "C-8: assertCoveredBy sets defectTypeId on a raised finding":
  test "an assertion violation":
    let f = assertCoveredBy(boom, tAssertionViolation())
    check f.status == sfRaised
    check f.defectTypeId.len > 0
    check "AssertionDefect" in f.defectTypeId

