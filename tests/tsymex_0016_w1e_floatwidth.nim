## RFC-0016 W1-e / K2b -- float32 <-> float64 conversions. W1-e declined them
## (`feFloatWidth`, W-04); K2b models them exactly (`fp.to_fp` at the target
## width, round-nearest-even) and pins each against the native run.
## int <-> float verdicts are unchanged.
##
## Natively `float64(float32(x)) == x` is false for x = 0.1 (float32 rounds it)
## and true for x = 0.5 (exact in float32), so the old pass-through verdict was
## wrong on one side.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutRoundTrip(x: float64) =
  let y = float32(x)
  if float64(y) == x: symexTarget("same")

proc takes64(v: float64): bool = v == 0.1
proc takes64half(v: float64): bool = v == 0.5

proc sutHiddenWiden(x: float64) =
  let y = float32(x)
  if takes64(y): symexTarget("same")

proc sutHiddenVar(x: float64) =
  let y: float32 = 0.5'f32
  var z: float64 = y
  if z == x: symexTarget("same")

proc takes32(v: float32): bool = v == 0.5'f32

proc sutHiddenNarrow(x: float32) =
  if takes32(x): symexTarget("same")

proc sutNoConv32(x: float32) =
  let y = x + 1.0'f32
  if y == 2.5'f32: symexTarget("same")

proc sutIntToFloat(x: int8) =
  if float64(x) == 3.0: symexTarget("same")

proc sutFloatToInt(x: float64) =
  if x >= 0.0 and x < 100.0 and int(x) == 7: symexTarget("same")

proc sutRound01(x: float64) =
  if x == 0.1 and float64(float32(x)) == x: symexTarget("same")

# 1 + 2^-24 and 1 + 3 * 2^-24 are exact ties between adjacent float32 values.
proc sutTieDown(x: float64) =
  if x == 1.0000000596046448 and float32(x) == 1.0'f32: symexTarget("same")

proc sutTieUp(x: float64) =
  if x == 1.0000001788139343 and float32(x) == 1.0000002384185791'f32:
    symexTarget("same")

proc sutTieUpOdd(x: float64) =
  if x == 1.0000001788139343 and float32(x) == 1.0000001192092896'f32:
    symexTarget("same")

proc sutOverflow(x: float64) =
  if float32(x) > 3.4028234663852886e38'f32: symexTarget("same")

proc sutHiddenWiden5(x: float64) =
  let y = float32(x)
  if takes64half(y): symexTarget("same")

proc sutWidenSum(x: float64) =
  let y = float32(x)
  let z: float64 = y
  if float(y) == z and z == 1.5: symexTarget("same")

const dom = sampled([0.1, 0.5, 1.5, 3.0, 7.25, 1e300])
const tieDom = sampled([1.0, 1.0000000596046448, 1.0000001788139343,
                        1.0000001192092896, 1.0000002384185791])

suite "W1-e float widths":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 292  # K2b

  test "native outcome of the round trip: false for 0.1, true for 0.5":
    check nativeRun(sutRoundTrip(0.1)).hits.len == 0
    check "same" in nativeRun(sutRoundTrip(0.5)).hits

  test "explicit float32(x) / float64(y) is exact":
    let r = pinExact(sutRoundTrip, cellKey(axConstruct, "conv/float32<-float64"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxSat
    check not r.errors.named(feFloatWidth)

  test "0.1 is not representable in float32: the round trip never matches":
    let r = pinExact(sutRound01, cellKey(axConstruct, "conv/float32<-float64"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxUnsat

  test "a float32 tie rounds to even (down)":
    let r = pinExact(sutTieDown, cellKey(axConstruct, "conv/float32<-float64"),
                     target = tLabel("same"), domain = tieDom)
    check r.status == sxSat

  test "a float32 tie rounds to even (up), never to the odd neighbour":
    let r = pinExact(sutTieUp, cellKey(axConstruct, "conv/float32<-float64"),
                     target = tLabel("same"), domain = tieDom)
    check r.status == sxSat
    let r2 = pinExact(sutTieUpOdd, cellKey(axConstruct, "conv/float32<-float64"),
                      target = tLabel("same"), domain = tieDom)
    check r2.status == sxUnsat

  test "float32 overflow narrows to infinity":
    let r = pinExact(sutOverflow, cellKey(axConstruct, "conv/float32<-float64"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxSat

  test "hidden float32 -> float64 argument is exact":
    let r = pinExact(sutHiddenWiden, cellKey(axConstruct, "conv/float64<-float32/arg"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxUnsat
    let r2 = pinExact(sutHiddenWiden5, cellKey(axConstruct, "conv/float64<-float32/arg"),
                      target = tLabel("same"), domain = dom)
    check r2.status == sxSat

  test "hidden float32 -> float64 initialiser is exact":
    let r = pinExact(sutHiddenVar, cellKey(axConstruct, "conv/float64<-float32/var"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxSat

  test "float(y) of a float32 and a float32 sum widen exactly":
    let r = pinExact(sutWidenSum, cellKey(axConstruct, "conv/float64<-float32/arg"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxSat

  test "float32 arithmetic without a width change is not declined":
    let r = symexFind(sutNoConv32, tLabel("same"))
    check not r.errors.named(feFloatWidth)

  test "int -> float64 is unchanged":
    let r = pinExact(sutIntToFloat, cellKey(axConstruct, "conv/float64<-int"),
                     target = tLabel("same"), domain = sampled([-128'i8, 0, 3, 4, 127]))
    check r.status == sxSat

  test "float64 -> int is unchanged":
    let r = pinExact(sutFloatToInt, cellKey(axConstruct, "conv/int<-float64"),
                     target = tLabel("same"), domain = dom)
    check r.status == sxSat

proc sutMixedCmp(a: float32, b: float64) =
  if a == b: symexTarget("same")

proc sutMixedAdd(a: float32, b: float64) =
  if a + b == 2.0: symexTarget("same")

suite "W1-e operand widening":
  test "float32 widened as a binary operand is exact and not declined":
    let r = symexFind(sutMixedCmp, tLabel("same"))
    check r.status == sxSat
    check not r.errors.named(feFloatWidth)

  test "mixed float32 + float64 arithmetic is not declined":
    let r = symexFind(sutMixedAdd, tLabel("same"))
    check not r.errors.named(feFloatWidth)
