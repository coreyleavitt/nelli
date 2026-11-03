## RFC-0005 S8cd item 4 -- where Nim reads a set expression: a C integer set.
## The "nim" tests run each SUT natively; a set of at most 64 values is a C
## integer, a larger one an array (see `isEagerIR`).
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8cd_setorder_md`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 100 s): one set type
## a file.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

include s8cd_setorder_fixture

type
  Sm = range[0'u8 .. 7'u8]
  Md = range[0'u8 .. 63'u8]  # the largest C integer

orderSuts(Sm, Sm(1), Sm(2), Sm(3), Sm(4), sm)

suite "S8cd item 4: a C integer set":
  orderPins("sm", false, unionNestedsm, compareTempsm, eqLazysm, inLazysm, inLitsm,
            cardInnersm, cardBaresm, ctorEagersm, elemEagerSetLazysm)

suite "S8cd":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 249
