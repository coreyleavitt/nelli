## RFC-0016 W3-z P10 (soundness). A float-first call is lowered by NAME
## (`mathInterception`), so a user routine spelled like a modelled std/math
## predicate must still be walked as its own body. `isInf`, `isFinite` and
## `isNormal` are not in std/math on this toolchain at all, so a call to one is
## always a user routine; `sqrt`/`signbit`/`classify` do exist, and a user
## overload (here on float32, which the SUT owns) must not take their model.
## Each case is decided against a native run.
import std/[unittest, math, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/stdlib_rows
import nelli/smt/stdlib_models
import ./s8cu_helpers

proc isFinite(x: float): bool = x < 10.0
proc isInf(x: float): bool = x > 5.0
proc isNormal(x: float): bool = x == 3.0
proc signbit(x: float32): bool = x > 0.0'f32
proc sqrt(x: float32): float32 = x + 1.0'f32

# E2b's SUT-defined predicates (IEEE meanings), moved here: walked as bodies.
proc ieeeInf(x: float): bool = x == Inf or x == -Inf
proc ieeeFinite(x: float): bool = x == x and not ieeeInf(x)
proc ieeeNormal(x: float): bool = classify(x) == fcNormal
proc fIsInf(a: float) =
  if ieeeInf(a) and a < 0.0: symexTarget("hit")
proc fIsFinite(a: float) =
  if ieeeFinite(a) and a < -1.0: symexTarget("hit")
proc fIsNormal(a: float) =
  if ieeeNormal(a) and a > 1.0: symexTarget("hit")

proc falseSat(x: float) =
  if isFinite(x) and x > 20.0: symexTarget("hit")
proc falseUnsat(x: float) =
  if isInf(x) and x == 6.0: symexTarget("hit")
proc normalUnsat(x: float) =
  if isNormal(x) and x == 3.0: symexTarget("hit")
proc normalSat(x: float) =
  if isNormal(x) and x == 4.0: symexTarget("hit")
proc signbitUnsat(x: float32) =
  if signbit(x) and x == 2.0'f32: symexTarget("hit")
proc sqrtHit(x: float32) =
  if sqrt(x) == 5.0'f32 and x == 4.0'f32: symexTarget("hit")

suite "P10: a user routine named like a float predicate is walked as its body":
  test "isFinite(x) = x < 10: `isFinite and x > 20` is unreachable (no false sat)":
    decides(falseSat, sxUnsat)
    check native(falseSat(25.0)) == "ran"
  test "isInf(x) = x > 5: `isInf and x == 6` is reachable (no false unsat)":
    decides(falseUnsat, sxSat)
    check native(falseUnsat(6.0)) == "hit"
  test "isNormal(x) = x == 3: `and x == 3` hits, `and x == 4` does not":
    decides(normalUnsat, sxSat)
    check native(normalUnsat(3.0)) == "hit"
    decides(normalSat, sxUnsat)
    check native(normalSat(4.0)) == "ran"
  test "a user float32 signbit/sqrt overload is not the std/math model":
    decides(signbitUnsat, sxSat)
    check native(signbitUnsat(2.0'f32)) == "hit"
    decides(sqrtHit, sxSat)   # the std/math model would be sqrt(4) = 2
    check native(sqrtHit(4.0'f32)) == "hit"

suite "P10: E2b's IEEE-bodied user predicates are exact":
  test "walked as bodies, each witness hits natively":
    decides(fIsInf, sxSat)
    decides(fIsFinite, sxSat)
    decides(fIsNormal, sxSat)
    check native(fIsInf(-Inf)) == "hit"
    check native(fIsFinite(-2.5)) == "hit"
    check native(fIsNormal(2.5)) == "hit"
    check native(fIsInf(2.5)) == "ran"
    check native(fIsFinite(NaN)) == "ran"

suite "P10: the walker version carries the change":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 312

suite "P10: std/math here does not export isInf, isFinite or isNormal":
  test "no row admits them, and the lowering no longer carries the names":
    var x = 1.5
    check not compiles(math.isInf(x))
    check not compiles(math.isFinite(x))
    check not compiles(math.isNormal(x))
    for n in ["isInf", "isFinite", "isNormal"]:
      check not admitFloatCall(n, 1).admitted
      check n notin mathFpModeledOps
