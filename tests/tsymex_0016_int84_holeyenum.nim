## RFC-0016 INT-84 (soundness, red until fixed): a holey enum parameter's
## hole is a trusted sxSat witness. The walker bounds an enum parameter by
## `[0, maxOrd]` (#163 W7), which for a holey enum keeps the holes: an
## ordinal between two declared values is a model value, and a target only
## a hole reaches is a trusted sxSat. Natively no caller can pass a hole
## (it is no value of the type), so no input reaches the target. Found
## converting the impure family (K9d-11a): `tsymex_163audit_range_domain`
## asserted the false sxSat as a documented imprecision ("sparse enum --
## the hole"), and pinFind replayed the hole witness until it learned to
## refuse one.
##
## The bar: an enum parameter, field or element ranges over its declared
## values only, so each target below that only a hole reaches is sxUnsat,
## pinned natively over every declared value; a target a declared value
## reaches stays sxSat, its witness replayed.
import std/[unittest]
import nelli/symex
import ./s8cu_helpers

type
  Sparse = enum
    sA = 0
    sB = 3
  Wide = enum
    wA = 1
    wB = 5
    wC = 9
  Holder = object
    s: Sparse
    n: int

proc holeParam(e: Sparse) =
  if e != sA and e != sB: symexTarget("hit")

proc holeOrd(w: Wide) =
  if ord(w) == 4: symexTarget("hit")

proc holeField(h: Holder) =
  if ord(h.s) == 2: symexTarget("hit")

proc holeElem(xs: seq[Sparse]) =
  if xs.len > 0 and ord(xs[0]) == 1: symexTarget("hit")

proc declaredOrd(w: Wide) =
  if ord(w) == 5: symexTarget("hit")

suite "INT-84: a holey enum's hole is no input":
  test "a parameter only a hole reaches is sxUnsat":
    check pinFind(holeParam, tLabel("hit")).status == sxUnsat

  test "an ordinal between two declared values is sxUnsat":
    check pinFind(holeOrd, tLabel("hit")).status == sxUnsat

  test "a field only a hole reaches is sxUnsat":
    check pinFind(holeField, tLabel("hit")).status == sxUnsat

  test "an element only a hole reaches is sxUnsat":
    check pinFind(holeElem, tLabel("hit")).status == sxUnsat

  test "control: a declared value is reached":
    check pinFind(declaredOrd, tLabel("hit")).status == sxSat
