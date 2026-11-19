## RFC-0016 INT-84 (soundness): a holey enum parameter's
## hole was a trusted sxSat witness. The walker bounded an enum parameter by
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
## reaches stays sxSat, its witness replayed. A hole the program makes is
## a value natively (probed): `E(k)` checks `low .. high` only (Nim warns
## `HoleEnumConv`), `cast[E]` checks nothing, and a zero-initialised slot of
## an enum without ordinal 0 holds 0; `for e in E` needs std/enumutils for a
## holey enum and yields its declared values; `succ`, `pred`, `inc` and
## `a .. b` over one do not compile.
import std/[unittest, tables, enumutils, strutils]
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
  Neg = enum
    nA = -2
    nB = 2
  HolderRef = ref Holder

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

proc holeNeg(e: Neg) =
  if ord(e) == 0: symexTarget("hit")

proc holeArray(a: array[2, Sparse]) =
  if ord(a[1]) == 2: symexTarget("hit")

proc holeRefField(r: HolderRef) =
  if r != nil and ord(r.s) == 1: symexTarget("hit")

proc holeTableVal(t: Table[int, Sparse]) =
  if t.hasKey(0) and ord(t[0]) == 2: symexTarget("hit")

proc holeSetCard(s: set[Sparse]) =
  if card(s) > 2: symexTarget("hit")

# A hole the program makes is a value natively: a conversion to a holey
# enum checks `low .. high` only (Nim warns `HoleEnumConv`), and a cast
# checks nothing. Each stays reachable.
proc convHole(k: int) =
  let e = Sparse(k)
  if ord(e) == 1: symexTarget("hit")

proc castHole(k: uint8) =
  let e = cast[Sparse](k)
  if ord(e) == 2: symexTarget("hit")

proc convHoleSeq(k: int) =
  var xs = @[sA]
  xs[0] = Sparse(k)
  if ord(xs[0]) == 2: symexTarget("hit")

proc convHoleField(k: int) =
  var h = Holder(s: sA)
  h.s = Sparse(k)
  if ord(h.s) == 1: symexTarget("hit")

proc convHoleRef(r: HolderRef; k: int) =
  if r != nil:
    r.s = Sparse(k)
    if ord(r.s) == 2: symexTarget("hit")

# A zero-initialised local of an enum without ordinal 0 holds the hole 0
# natively, and the walk keeps it.
proc zeroLocal(k: int) =
  var w: Wide
  if k == 1 and ord(w) == 0: symexTarget("hit")

# `items` over a holey enum (std/enumutils) yields its declared values.
proc itemsHole(k: int) =
  for e in items(Sparse):
    if k == 1 and ord(e) == 1: symexTarget("hit")

proc itemsDeclared(k: int) =
  for e in items(Sparse):
    if k == 1 and ord(e) == 3: symexTarget("hit")

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

  test "a negative-ordinal enum's hole at zero is sxUnsat":
    check pinFind(holeNeg, tLabel("hit")).status == sxUnsat

  test "an array element only a hole reaches is sxUnsat":
    check pinFind(holeArray, tLabel("hit")).status == sxUnsat

  test "a ref cell's field only a hole reaches is sxUnsat":
    check pinFind(holeRefField, tLabel("hit")).status == sxUnsat

  test "a table value only a hole reaches is sxUnsat":
    check pinFind(holeTableVal, tLabel("hit")).status == sxUnsat

  test "a set of a holey enum holds its declared values only":
    check pinFind(holeSetCard, tLabel("hit")).status == sxUnsat

suite "INT-84: a hole the program makes stays a value":
  test "a conversion to a holey enum reaches a hole":
    check pinFind(convHole, tLabel("hit")).status == sxSat

  test "a cast to a holey enum is not refuted":
    # A cast to an enum is declined (sxUnknown); the bar is no sxUnsat.
    check pinFind(castHole, tLabel("hit")).status != sxUnsat

  test "a zero-initialised local holds the hole 0":
    check pinFind(zeroLocal, tLabel("hit")).status == sxSat

suite "INT-84: items over a holey enum":
  # `items` (std/enumutils) is declined (sxUnknown); the bar is that no
  # hole is a verdict, and no declared step is refuted.
  test "no step yields a hole":
    check pinFind(itemsHole, tLabel("hit")).status != sxSat

  test "a declared step is not refuted":
    check pinFind(itemsDeclared, tLabel("hit")).status != sxUnsat

  test "a converted hole stored in a seq is read back":
    check pinFind(convHoleSeq, tLabel("hit")).status == sxSat

  test "a converted hole stored in a field is read back":
    check pinFind(convHoleField, tLabel("hit")).status == sxSat

  test "a converted hole stored in a ref cell is read back":
    check pinFind(convHoleRef, tLabel("hit")).status == sxSat

suite "INT-84: version floor":
  test "the walker version is at least INT-84's":
    check parseInt(symexWalkerVersion) >= 444
