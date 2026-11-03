## RFC-0005 S8cd item 4 -- where Nim reads a set expression: an array set.
## The "nim" tests run each SUT natively; a set of at most 64 values is a C
## integer, a larger one an array (see `isEagerIR`).
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8cd_setorder_large`. Split so that each part compiles and
## runs in under 60 s on the Windows legs (the whole file took 103 s): one set
## type a file.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

include s8cd_setorder_fixture

type Mx = range[0'u8 .. 64'u8]  # the smallest array

orderSuts(uint8, 1'u8, 2'u8, 3'u8, 4'u8, by)

suite "S8cd item 4: an array set":
  orderPins("by", true, unionNestedby, compareTempby, eqLazyby, inLazyby, inLitby,
            cardInnerby, cardBareby, ctorEagerby, elemEagerSetLazyby)
