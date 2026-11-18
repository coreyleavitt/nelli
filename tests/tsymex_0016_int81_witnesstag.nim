## RFC-0016 INT-81 (witness fidelity, red until fixed): the walker's witness
## builds a ref cell as the static type of the position it fills
## (`resolveRef`, `new(result)` in runtime.nim), not the run-type tag the
## model chose. A verdict that needs a descendant behind a base-typed
## parameter (a method override, a down-conversion, `of`) is correct, but its
## witness replays as the base type and misses the target natively. Found
## converting the ref family (K9d-10): `tsymex_rfc0005_s8bn_remainder_d`'s
## `sutTagAlias` (`ta`) and `sutMethodParam` (`mp6`) stay `symexFind`.
##
## The bar: a witness cell is allocated as the type its tag names, so every
## sat verdict below replays to its target.
import std/unittest
import nelli/symex
from ./s8cu_helpers import pinFind

type
  Shape = ref object of RootObj
  Square = ref object of Shape
  Base = ref object of RootObj
    x: int
  Mid = ref object of Base
    y: int

method m(o: Shape): int {.base.} = 5
method m(o: Square): int = 6

proc dispatch(o: Shape) =
  if o != nil and o.m == 6: symexTarget("hit")

proc isMid(b: Base) =
  if b != nil and b of Mid: symexTarget("hit")

proc downConv(b: Base; d: Mid) =
  if b != nil and d != nil and Base(d) == b:
    try:
      if Mid(b).y == d.y: symexTarget("hit")
    except ObjectConversionDefect:
      discard

suite "INT-81: a witness cell has its run-type tag's type":
  test "a method call on a base-typed parameter reaches the override":
    check pinFind(dispatch, tLabel("hit")).status == sxSat

  test "a base-typed parameter that is a descendant":
    check pinFind(isMid, tLabel("hit")).status == sxSat

  test "a down-conversion of a parameter aliasing a descendant one":
    check pinFind(downConv, tLabel("hit")).status == sxSat
