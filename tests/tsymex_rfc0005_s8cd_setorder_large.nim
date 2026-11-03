## RFC-0005 S8cd item 4 -- where Nim reads a set expression: an array set.
## The "nim" tests run each SUT natively; a set of at most 64 values is a C
## integer, a larger one an array (see `isEagerIR`).
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8cd_setorder_by`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 103 s). One set type
## a file.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

include s8cd_setorder_fixture

type Mx = range[0'u8 .. 64'u8]  # the smallest array

orderSuts(Mx, Mx(1), Mx(2), Mx(3), Mx(4), mx)

suite "S8cd item 4: an array set":
  orderPins("mx", true, unionNestedmx, compareTempmx, eqLazymx, inLazymx, inLitmx,
            cardInnermx, cardBaremx, ctorEagermx, elemEagerSetLazymx)

suite "S8cd":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 249
