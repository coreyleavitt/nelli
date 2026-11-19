## RFC-0016 int6: the `--rangeChecks:off` half of
## `tsymex_0016_int6p_floatrange_store` (this file's `.nim.cfg`). With the
## check compiled out, system's routines included, a store into a float range
## keeps the value whatever it is, so no `RangeDefect` is raised and the stored
## value is read back as it is. Judged against the native binary (`pinFind`:
## each label is reached by a witness run natively, each `sxUnsat` raise is
## checked over the parameter's domain).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  U64 = range[0.0 .. 1.0]
  U32 = range[0.0'f32 .. 1.0'f32]

proc asg64(a: float) =
  var v: U64 = 0.5
  v = a
  if v > 1.0: symexTarget("hit")

proc add64(a: float) =
  var v: U64 = 0.5
  v += a
  if v > 1.0: symexTarget("hit")

proc mul64(a: float) =
  var v: U64 = 0.5
  v *= a
  if v < 0.0: symexTarget("hit")

proc conv64(a: float) =
  let v = U64(a)
  if v > 1.0: symexTarget("hit")

proc sub32(a: float32) =
  var v: U32 = 0.5'f32
  v -= a
  if v < 0.0'f32: symexTarget("hit")

proc div32(a: float32) =
  var v: U32 = 0.5'f32
  v /= a
  if v > 1.0'f32: symexTarget("hit")

template unchecked(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxUnsat

suite "int6 float range store, range checks off":
  test "v = a and U(a) keep an out-of-range value":
    unchecked(asg64)
    unchecked(conv64)
  test "v += a, v *= a, v -= a keep it":
    unchecked(add64)
    unchecked(mul64)
    unchecked(sub32)
  test "float32's v /= a keeps it":
    unchecked(div32)

suite "int6 float range store, range checks off: walker version":
  test "walker version floor >= 463":
    check parseInt(symexWalkerVersion) >= 463
