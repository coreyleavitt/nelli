## RFC-0005 S8cd item 4 -- where Nim reads a set expression: an array set.
## The "nim" tests run each SUT natively; a set of at most 64 values is a C
## integer, a larger one an array (see `isEagerIR`).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

include s8cd_setorder_fixture

type Mx = range[0'u8 .. 64'u8]  # the smallest array

orderSuts(Mx, Mx(1), Mx(2), Mx(3), Mx(4), mx)
orderSuts(uint8, 1'u8, 2'u8, 3'u8, 4'u8, by)

suite "S8cd item 4: an array set":
  orderPins("mx", true, unionNestedmx, compareTempmx, eqLazymx, inLazymx, inLitmx,
            cardInnermx, cardBaremx, ctorEagermx, elemEagerSetLazymx)
  orderPins("by", true, unionNestedby, compareTempby, eqLazyby, inLazyby, inLitby,
            cardInnerby, cardBareby, ctorEagerby, elemEagerSetLazyby)

suite "S8cd":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 249
