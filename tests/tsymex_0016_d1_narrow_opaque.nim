## RFC-0016 review D1 S3 (precision). A `--overflowChecks:off` build (its
## `.nim.cfg`, no -fwrapv). The opaque-call scan asked the definedness table
## for the `signedWide` and `lowByMinusOneWide` rows whatever the operand's
## width, so an opaque `int8` or `int16` `+ - * div mod` reported
## `ubSignedOverflow` / `ubIntMinModMinusOne` where C computes in the promoted
## `int` and the narrowing wraps (rows `signedNarrow`,
## `lowByMinusOneNarrow`: defined). The class now follows the operand width, as
## `wrapDefined` does. A signed zero divisor stays undefined at every width.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

proc add8(a, b: int8) {.symexOpaque.} = discard a + b
proc mul16(a, b: int16) {.symexOpaque.} = discard a * b
proc add32(a, b: int32) {.symexOpaque.} = discard a + b
proc add64(a, b: int64) {.symexOpaque.} = discard a + b
proc div8(a, b: int8) {.symexOpaque.} = discard a div b
proc mod16(a, b: int16) {.symexOpaque.} = discard a mod b
proc div32(a, b: int32) {.symexOpaque.} = discard a div b
proc mod32(a, b: int32) {.symexOpaque.} = discard a mod b

proc sAdd8(x, y: int8) =
  if x == 5: symexTarget("hit")
  add8(x, y)
proc sMul16(x, y: int16) =
  if x == 5: symexTarget("hit")
  mul16(x, y)
proc sAdd32(x, y: int32) =
  if x == 5: symexTarget("hit")
  add32(x, y)
proc sAdd64(x, y: int64) =
  if x == 5: symexTarget("hit")
  add64(x, y)
proc sDiv8(x, y: int8) =
  if x == 5: symexTarget("hit")
  div8(x, y)
proc sMod16(x, y: int16) =
  if x == 5: symexTarget("hit")
  mod16(x, y)
proc sDiv32(x, y: int32) =
  if x == 5: symexTarget("hit")
  div32(x, y)
proc sMod32(x, y: int32) =
  if x == 5: symexTarget("hit")
  mod32(x, y)

template kinds(sut: untyped): untyped =
  let r = symexFind(sut, tLabel("hit"), pinSettingsConst)
  checkpoint show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  r.soundness.undefinedKinds

suite "D1 S3: opaque scan, operand width (checks off)":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 361

  test "int8 and int16 add/mul are defined: no ubSignedOverflow":
    check UbKind(ubSignedOverflow) notin kinds(sAdd8)
    check UbKind(ubSignedOverflow) notin kinds(sMul16)

  test "int32 and int64 add stay undefined: ubSignedOverflow":
    check UbKind(ubSignedOverflow) in kinds(sAdd32)
    check UbKind(ubSignedOverflow) in kinds(sAdd64)

  test "narrow low(T) div/mod -1 is defined; a zero divisor is not":
    let d8 = kinds(sDiv8)
    check UbKind(ubSignedOverflow) notin d8
    check UbKind(ubSignedDivZero) in d8
    let m16 = kinds(sMod16)
    check UbKind(ubIntMinModMinusOne) notin m16
    check UbKind(ubSignedDivZero) in m16

  test "wide low(T) div/mod -1 stays undefined":
    check UbKind(ubSignedOverflow) in kinds(sDiv32)
    check UbKind(ubIntMinModMinusOne) in kinds(sMod32)
