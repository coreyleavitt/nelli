## RFC-0016 W1-e -- float32 <-> float64 conversions decline `feFloatWidth`
## (W-04); int <-> float verdicts are unchanged.
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

const dom = sampled([0.1, 0.5, 1.5, 3.0, 7.25, 1e300])

suite "W1-e float widths":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 277

  test "native outcome of the round trip: false for 0.1, true for 0.5":
    check nativeRun(sutRoundTrip(0.1)).hits.len == 0
    check "same" in nativeRun(sutRoundTrip(0.5)).hits

  test "explicit float32(x) / float64(y) declines":
    pinDecline(sutRoundTrip, cellKey(axConstruct, "conv/float32<-float64"),
               feFloatWidth, target = tLabel("same"))

  test "hidden float32 -> float64 argument declines":
    pinDecline(sutHiddenWiden, cellKey(axConstruct, "conv/float64<-float32/arg"),
               feFloatWidth, target = tLabel("same"))

  test "hidden float32 -> float64 initialiser declines":
    pinDecline(sutHiddenVar, cellKey(axConstruct, "conv/float64<-float32/var"),
               feFloatWidth, target = tLabel("same"))

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
