## RFC-0016 INT-80 (precision, red until fixed): the walker declines a
## `pointer` parameter and a `pointer` field of a by-value parameter
## (`feUnsupportedParamType`), where a `ref` or `ptr` one is modelled. Found
## converting the ref family (K9d-10): `pinFind` now generates a `pointer`
## domain (nil and the addresses of `ref int` cells), so every verdict below
## would be pinned natively the moment the walker decides it.
##
## The bar: a `pointer` parameter or field is nil or an address, compared
## with nil and with another `pointer` exactly as Nim does; a verdict over it
## is definite and reproduced natively over the generated domain.
import std/unittest
import nelli/symex
from ./s8cu_helpers import pinFind

type PHolder = object
  tag: bool
  p: pointer

proc pNonNil(x: pointer) =
  if x != nil: symexTarget("hit")

proc pBothNil(x, y: pointer) =
  if x == nil and y == nil: symexTarget("hit")

proc pNeverBoth(x: pointer) =
  if x == nil and x != nil: symexTarget("hit")

proc pField(h: PHolder) =
  if h.tag and h.p == nil: symexTarget("hit")

suite "INT-80: a pointer parameter is modelled, not declined":
  test "a pointer parameter compared with nil is sat, pinned on its witness":
    let r = pinFind(pNonNil, tLabel("hit"))
    checkpoint $r.errors
    check r.status == sxSat

  test "two pointer parameters":
    check pinFind(pBothNil, tLabel("hit")).status == sxSat

  test "an impossible pointer test is unsat, pinned over the domain":
    check pinFind(pNeverBoth, tLabel("hit")).status == sxUnsat

  test "a pointer field of a by-value parameter":
    check pinFind(pField, tLabel("hit")).status == sxSat
