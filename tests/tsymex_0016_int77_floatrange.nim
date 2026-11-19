## RFC-0016 INT-77: a float `range` parameter is modelled exactly.
##
## `range[0.0 .. 1.0]` and `range[-1.5'f32 .. 2.5'f32]` did not compile in the
## walker: `parseRangeBracket` read the bounds with `intVal`. Nim admits a
## value into a float range when `lo <= x and x <= hi` (an IEEE comparison in
## the base width), so the range is the closed interval with -0.0 admitted
## beside 0.0. The walker now constrains a float-range value to that interval
## wherever the type lands (a parameter, an object field, a seq element).
## Every verdict is pinned natively (`pinExact` over the float-range domain,
## `pinFind`, `s8cu_helpers`).
##
## RFC-0016 int6: Nim's check is `x < lo or x > hi` (`raiseRangeErrorF`), so
## NaN passes it and is a value of the range (probed: `v = NaN` stores into a
## `range[0.0 .. 1.0]`, and `unitNaN(NaN)` reaches its label). INT-77 read the
## check as `lo <= x and x <= hi` and pinned `x != x` unreachable.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  Unit = range[0.0 .. 1.0]
  Span32 = range[-1.5'f32 .. 2.5'f32]
  Box = object
    u: Unit
    k: int

proc unitHigh(x: range[0.0 .. 1.0]) =
  if x > 0.75: symexTarget("hit")

proc unitAbove(x: range[0.0 .. 1.0]) =
  if x > 1.0: symexTarget("hit")

proc unitBelow(x: range[0.0 .. 1.0]) =
  if x < 0.0: symexTarget("hit")

proc unitNaN(x: range[0.0 .. 1.0]) =
  if x != x: symexTarget("hit")

proc unitNegZero(x: range[0.0 .. 1.0]) =
  if x == 0.0 and 1.0 / x < 0.0: symexTarget("hit")

proc unitTop(x: range[0.0 .. 1.0]) =
  if x == 1.0: symexTarget("hit")

proc spanHigh(x: range[-1.5'f32 .. 2.5'f32]) =
  if x > 2.4999998'f32: symexTarget("hit")

proc spanAbove(x: range[-1.5'f32 .. 2.5'f32]) =
  if x > 2.5'f32: symexTarget("hit")

proc spanBelow(x: range[-1.5'f32 .. 2.5'f32]) =
  if x < -1.5'f32: symexTarget("hit")

proc spanLow(x: range[-1.5'f32 .. 2.5'f32]) =
  if x == -1.5'f32: symexTarget("hit")

proc spanNaN(x: range[-1.5'f32 .. 2.5'f32]) =
  if x != x: symexTarget("hit")

proc spanWide(x: range[-1.5'f32 .. 2.5'f32]) =
  ## the bound is in float32: no float32 lies strictly between 2.5 and its
  ## float32 successor, so a float64 reading of the interval would be wrong
  if float(x) > 2.5 and float(x) < 2.5000002: symexTarget("hit")

proc namedUnit(x: Unit) =
  if x > 1.0 or x < 0.0: symexTarget("hit")

proc namedSpan(x: Span32) =
  if x > 2.0'f32: symexTarget("hit")

proc boxField(b: Box) =
  if b.u > 1.0: symexTarget("hit")

proc boxFieldSat(b: Box) =
  if b.u > 0.5 and b.k == 3: symexTarget("hit")

proc seqElem(xs: seq[Unit]) =
  if xs.len == 1 and xs[0] < 0.0: symexTarget("hit")

proc seqLoop(xs: seq[Unit]) =
  if xs.len == 2:
    for x in xs:
      if x > 1.0: symexTarget("hit")

proc arrElem(a: array[2, Span32]) =
  if a[1] < -1.5'f32 or a[0] != a[0]: symexTarget("hit")

proc seqElemSat(xs: seq[Unit]) =
  if xs.len == 2 and xs[1] > 0.5: symexTarget("hit")

template k(n: untyped): CellKey = cellKey(faGeneric, "int77/" & n)

suite "INT-77: float range parameters":
  test "range[0.0 .. 1.0]: the closed interval and NaN":
    let d = boundaryOf(range[0.0 .. 1.0])
    check pinExact(unitHigh, k("unitHigh"), domain = d).status == sxSat
    check pinExact(unitAbove, k("unitAbove"), domain = d).status == sxUnsat
    check pinExact(unitBelow, k("unitBelow"), domain = d).status == sxUnsat
    let nan = pinExact(unitNaN, k("unitNaN"), domain = d)
    check nan.status == sxSat and nan.witness[0] != nan.witness[0]
    check pinExact(unitTop, k("unitTop"), domain = d).status == sxSat

  test "range[0.0 .. 1.0] admits -0.0, as Nim's range check does":
    let r = pinExact(unitNegZero, k("unitNegZero"),
                     domain = boundaryOf(range[0.0 .. 1.0]))
    check r.status == sxSat
    check r.witness[0] == 0.0 and (1.0 / r.witness[0]) < 0.0

  test "range[-1.5'f32 .. 2.5'f32]: the interval in float32":
    let d = boundaryOf(range[-1.5'f32 .. 2.5'f32])
    let h = pinExact(spanHigh, k("spanHigh"), domain = d)
    check h.status == sxSat and h.witness[0] == 2.5'f32
    check pinExact(spanAbove, k("spanAbove"), domain = d).status == sxUnsat
    check pinExact(spanBelow, k("spanBelow"), domain = d).status == sxUnsat
    check pinExact(spanLow, k("spanLow"), domain = d).status == sxSat
    let nan = pinExact(spanNaN, k("spanNaN"), domain = d)
    check nan.status == sxSat and nan.witness[0] != nan.witness[0]
    check pinExact(spanWide, k("spanWide"), domain = d).status == sxUnsat

  test "a named float range":
    check pinExact(namedUnit, k("namedUnit"),
                   domain = boundaryOf(Unit)).status == sxUnsat
    check pinExact(namedSpan, k("namedSpan"),
                   domain = boundaryOf(Span32)).status == sxSat

  test "a float range inside an object and a seq":
    check pinFind(boxField, tLabel("hit")).status == sxUnsat
    check pinFind(boxFieldSat, tLabel("hit")).status == sxSat
    check pinFind(seqElem, tLabel("hit")).status == sxUnsat
    let lp = pinFind(seqLoop, tLabel("hit"))
    checkpoint $lp.errors
    check lp.status == sxUnsat
    # int6: `a[0] != a[0]` holds for a NaN element, a value of the range
    check pinFind(arrElem, tLabel("hit")).status == sxSat
    check pinFind(seqElemSat, tLabel("hit")).status == sxSat

suite "INT-77: walker version":
  test "walker version floor >= 436":
    check parseInt(symexWalkerVersion) >= 436
