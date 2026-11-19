## RFC-0016 int6: a store into a float `range` local is range-checked as Nim
## checks it.
##
## Probed on the pinned toolchain (`range[0.0 .. 1.0]` and its float32 twin,
## from `v = 0.5`):
##   * `v = a`, `v += a`, `v -= a` and `v *= a` raise `RangeDefect` when the
##     result leaves the range ("value out of range: 2.0 notin 0.0 .. 1.0"),
##     `+Inf` and `-Inf` included;
##   * the check is `x < lo or x > hi`, so NaN passes it: `v = NaN`, and every
##     operator with a NaN operand, stores NaN without a raise. A float range
##     holds NaN; -0.0 passes too;
##   * `v /= a` on a float64 range never checks: system's `/=` for `float64` is
##     a plain `(x: var float64, y: float64)` routine, so the range local is
##     passed as a `float64` and `0.5 / 0.25` is stored as `2.0`. The float32
##     `/=` is the generic `[T: float | float32]` one, instantiated at the range
##     type, and checks (`0.5'f32 / 0.25'f32` raises);
##   * a value of a float range inside the target is checked too (`w = v`
##     with `v` holding 2.0 into `range[0.0 .. 1.5]` raises), unlike an
##     integer subrange's.
## The generic routines take `y: T`, so the operand is converted into the range
## at the call as well (probed: `v *= 2.0'f32` at `v == 0.5` raises "2.0 notin
## 0.0 .. 1.0" although the product is 1.0). Before this, none of the stores
## was checked: the walker carried the range only as a fact on an input.
## Every verdict here is judged against the
## native binary (`pinFind`: a witness is run natively, an `sxUnsat` is
## checked over the parameter's domain, a raise is compared by type).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  U64 = range[0.0 .. 1.0]
  U32 = range[0.0'f32 .. 1.0'f32]

# --- float64 -----------------------------------------------------------------

proc asg64(a: float) =
  var v: U64 = 0.5
  v = a
  symexTarget("t")
  discard v

proc asg64In(a: float) =
  var v: U64 = 0.5
  if a >= 0.0 and a <= 1.0:
    v = a
    symexTarget("t")
  discard v

proc asg64NaN(a: float) =
  var v: U64 = 0.5
  v = a
  if v != v: symexTarget("hit")

proc add64(a: float) =
  var v: U64 = 0.5
  v += a
  symexTarget("t")
  discard v

proc add64Top(a: float) =
  var v: U64 = 0.5
  v += a
  if v == 1.0: symexTarget("hit")

proc sub64(a: float) =
  var v: U64 = 0.5
  v -= a
  symexTarget("t")
  discard v

proc sub64Low(a: float) =
  var v: U64 = 0.5
  v -= a
  if v == 0.0: symexTarget("hit")

proc mul64(a: float) =
  var v: U64 = 0.5
  v *= a
  symexTarget("t")
  discard v

proc mul64Operand(a: float) =
  ## `0.0 * a` is in the range for every finite `a`: only the operand's own
  ## conversion into the range (`y: T`) raises, for `a` outside it
  var v: U64 = 0.0
  v *= a
  symexTarget("t")
  discard v

proc mul64NaN(a: float) =
  var v: U64 = 0.5
  v *= a
  if v != v: symexTarget("hit")

proc div64(a: float) =
  var v: U64 = 0.5
  v /= a
  symexTarget("t")
  discard v

proc div64Above(a: float) =
  var v: U64 = 0.5
  v /= a
  if v > 1.0: symexTarget("hit")

proc wider64(a: float) =
  ## a value of a narrower float range is checked into a wider one: `/=`
  ## stores 2.0 into `v`, and `w = v` raises (probed)
  var v: U64 = 0.5
  v /= a
  var w: range[0.0 .. 1.5] = 0.0
  w = v
  symexTarget("t")
  discard w

proc conv64(a: float) =
  let v = U64(a)
  symexTarget("t")
  discard v

proc conv64Int(a: int) =
  ## int6-r2: an integer converted into a float range is converted to the
  ## range's base, then checked (it faulted the walk: "operand is not a
  ## float")
  let v = U64(a)
  symexTarget("t")
  discard v

proc conv64IntTop(a: int) =
  let v = U64(a)
  if v == 1.0: symexTarget("hit")

# --- float32 -----------------------------------------------------------------

proc asg32(a: float32) =
  var v: U32 = 0.5'f32
  v = a
  symexTarget("t")
  discard v

proc asg32NaN(a: float32) =
  var v: U32 = 0.5'f32
  v = a
  if v != v: symexTarget("hit")

proc add32(a: float32) =
  var v: U32 = 0.5'f32
  v += a
  symexTarget("t")
  discard v

proc sub32(a: float32) =
  var v: U32 = 0.5'f32
  v -= a
  symexTarget("t")
  discard v

proc mul32(a: float32) =
  var v: U32 = 0.5'f32
  v *= a
  symexTarget("t")
  discard v

proc div32(a: float32) =
  var v: U32 = 0.5'f32
  v /= a
  symexTarget("t")
  discard v

proc conv32Int(a: int32) =
  ## int6-r2: the same into a float32 range
  let v = U32(a)
  symexTarget("t")
  discard v

proc div32In(a: float32) =
  var v: U32 = 0.5'f32
  if a >= 0.5'f32 and a <= 1.0'f32:
    v /= a
    symexTarget("t")
  discard v

# --- a float range parameter holds NaN ---------------------------------------

proc paramNaN(x: U64) =
  if x != x: symexTarget("hit")

proc paramNaN32(x: U32) =
  if x != x: symexTarget("hit")

template raises(fn: untyped) =
  let r = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(r.errors)
  check r.status == sxRaised
  check r.raisedTypeId == "RangeDefect"

template reaches(fn: untyped; tgt: SymexTarget) =
  let r = pinFind(fn, tgt)
  checkpoint show(r.errors)
  check r.status == sxSat

template neverRaises(fn: untyped) =
  let r = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(r.errors)
  check r.status == sxUnsat

suite "int6 float range store: float64":
  test "v = a raises outside the range, and stores inside it":
    raises(asg64)
    reaches(asg64, tLabel("t"))
    neverRaises(asg64In)
  test "v = NaN stores NaN without a raise":
    reaches(asg64NaN, tLabel("hit"))
  test "v += a":
    raises(add64)
    reaches(add64Top, tLabel("hit"))
  test "v -= a":
    raises(sub64)
    reaches(sub64Low, tLabel("hit"))
  test "v *= a, NaN included":
    raises(mul64)
    raises(mul64Operand)
    reaches(mul64NaN, tLabel("hit"))
  test "v /= a on a float64 range never checks":
    neverRaises(div64)
    reaches(div64Above, tLabel("hit"))
  test "a narrower float range stored into a wider one is checked":
    raises(wider64)
  test "U64(a)":
    raises(conv64)
    reaches(conv64, tLabel("t"))
  test "U64(i) for an integer i (int6-r2)":
    raises(conv64Int)
    reaches(conv64Int, tLabel("t"))
    reaches(conv64IntTop, tLabel("hit"))

suite "int6 float range store: float32":
  test "v = a":
    raises(asg32)
    reaches(asg32NaN, tLabel("hit"))
  test "v += a, v -= a, v *= a":
    raises(add32)
    raises(sub32)
    raises(mul32)
  test "U32(i) for an integer i (int6-r2)":
    raises(conv32Int)
    reaches(conv32Int, tLabel("t"))
  test "v /= a on a float32 range checks":
    raises(div32)
    neverRaises(div32In)

suite "int6 float range: NaN is a value of the type":
  test "a float range parameter may be NaN":
    reaches(paramNaN, tLabel("hit"))
    reaches(paramNaN32, tLabel("hit"))

suite "int6 float range store: walker version":
  test "walker version floor >= 463":
    check parseInt(symexWalkerVersion) >= 463
  test "walker version floor >= 480 (int6-r2: an integer into a float range)":
    check parseInt(symexWalkerVersion) >= 480
