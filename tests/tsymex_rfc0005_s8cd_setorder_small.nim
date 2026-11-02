## RFC-0005 S8cd item 4 -- where Nim reads a set expression: a C integer set.
## The "nim" tests run each SUT natively; a set of at most 64 values is a C
## integer, a larger one an array (see `isEagerIR`).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

include s8cd_setorder_fixture

type
  Sm = range[0'u8 .. 7'u8]
  Md = range[0'u8 .. 63'u8]  # the largest C integer

orderSuts(Sm, Sm(1), Sm(2), Sm(3), Sm(4), sm)
orderSuts(Md, Md(1), Md(2), Md(3), Md(4), md)

suite "S8cd item 4: a C integer set":
  orderPins("sm", false, unionNestedsm, compareTempsm, eqLazysm, inLazysm, inLitsm,
            cardInnersm, cardBaresm, ctorEagersm, elemEagerSetLazysm)
  orderPins("md", false, unionNestedmd, compareTempmd, eqLazymd, inLazymd, inLitmd,
            cardInnermd, cardBaremd, ctorEagermd, elemEagerSetLazymd)

suite "S8cd":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 249
