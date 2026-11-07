## RFC-0016 W1-d1a -- `low(T) mod -1` (and `low(T) div -1` with the overflow
## checks off) at 32 and 64 bits halt through `haltUndefined` (section 9.1
## item 2) instead of being a confined survivor.
##
## Native, probed on the pinned toolchain (c and cpp identical, operands
## through a `noinline` identity so nothing folds), x86-64 Linux:
##   default build (checks on)   low(int) mod -1 -> SIGFPE, rc 136, no handler
##                               runs; Nim has no check on `mod`.
##                               low(int) div -1 -> OverflowDefect (Nim's check)
##   overflowChecks off          low(int) mod -1 -> SIGFPE
##                               low(int) div -1 -> SIGFPE
## So this hardware never reaches the label, and the old trusted `sxUnsat`
## agreed with it. It is not an answer the language gives: the C division is
## undefined, and on a target where the quotient wraps (or the remainder is 0)
## the label is reached. The verdict is therefore no longer a trusted
## `sxUnsat`: the path halts and the run records `ubIntMinModMinusOne`
## (`dcOmitted`, run coordinate `{scIncomplete}`). Where Nim's own check forks
## a Defect (`div`, checks on) the op is Defect, not undefined, and there is
## one fork.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutModIntMin(x: int) =
  if x == low(int):
    let q = x mod -1
    if q == 0: symexTarget("hit")

proc sutModIntMin32(x: int32) =
  if x == low(int32):
    let q = x mod -1
    if q == 0: symexTarget("hit")

proc sutModIntMin16(x: int16) =
  if x == low(int16):
    let q = x mod -1
    if q == 0: symexTarget("hit")

proc sutModExcept(x: int) =
  if x == low(int):
    try:
      let q = x mod -1
      if q == 0: symexTarget("hit")
    except:
      symexTarget("c")

proc sutModDefined(x: int) =
  if x != low(int):
    let q = x mod -1
    if q == 0: symexTarget("hit")

proc sutModPositive(x: int) =
  ## `low(int)` is excluded by the path: the undefined side is UNSAT, so it
  ## is pruned and nothing is recorded.
  if x > 0 and x mod -1 == 0: symexTarget("hit")

proc modCallee(x: int): int = x mod -1

proc sutModViaCall(x: int) =
  if x == low(int):
    if modCallee(x) == 0: symexTarget("hit")

proc sutDivChecked(x: int) =
  ## Checks on: `low(int) div -1` is Nim's `OverflowDefect`.
  let q = x div -1
  if q == 7: symexTarget("hit")

{.push overflowChecks: off.}
proc sutDivUnchecked(x: int) =
  if x == low(int):
    let q = x div -1
    if q == 0: symexTarget("hit")
{.pop.}

const noOverflowChecks = SymexSettings(integerSemantics: isOptimised,
                                       arithChecks: {acDivByZero, acRange})

const probeMod = """
proc id(x: int): int {.noinline.} = x
echo id(low(int)) mod id(-1)
"""

const probeDiv = """
proc id(x: int): int {.noinline.} = x
echo id(low(int)) div id(-1)
"""

const probeDivChecked = """
proc id(x: int): int {.noinline.} = x
try:
  echo id(low(int)) div id(-1)
except OverflowDefect:
  echo "OverflowDefect"
  quit(0)
"""

suite "W1-d1a low(T) mod -1":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 279

  test "native: low(int) mod -1 is a SIGFPE in the default build":
    pinCrash(cellKey(axDefinedness, "mod/intMin/minusOne"), probeMod, [],
             ceDivTrap)

  test "native: low(int) mod -1 is a SIGFPE with the overflow checks off":
    pinCrash(cellKey(axDefinedness, "mod/intMin/minusOne"), probeMod,
             ["--overflowChecks:off"], ceDivTrap)

  test "native: low(int) div -1 is an OverflowDefect checked, a SIGFPE unchecked":
    let ok = nativeRun(sutDivChecked(low(int)))
    check ok.raised == "OverflowDefect"
    pinCrash(cellKey(axDefinedness, "div/intMin/minusOne"), probeDiv,
             ["--overflowChecks:off"], ceDivTrap)

  test "mod: the path halts, the verdict is not a trusted sxUnsat":
    pinDecline(sutModIntMin, cellKey(axDefinedness, "mod/intMin/minusOne"),
               ubIntMinModMinusOne)

  test "mod: the same at 32 bits":
    pinDecline(sutModIntMin32, cellKey(axDefinedness, "mod/int32Min/minusOne"),
               ubIntMinModMinusOne)

  test "mod: at 16 bits C promotes to int and the remainder is 0: defined":
    let r = pinExact(sutModIntMin16, cellKey(axDefinedness, "mod/int16Min/minusOne"),
                     domain = sampled([low(int16), -1'i16, 0, 7]))
    check r.status == sxSat
    check not r.errors.named(ubIntMinModMinusOne)

  test "an enclosing `except:` does not see the halt":
    let r = symexFind(sutModExcept, tLabel("c"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.status != sxSat
    check r.errors.named(ubIntMinModMinusOne)
    let r2 = symexFind(sutModExcept, tLabel("hit"))
    check not r2.trusted
    check r2.errors.named(ubIntMinModMinusOne)

  test "the defined side continues exactly":
    let r = pinExact(sutModDefined, cellKey(axDefinedness, "mod/minusOne/defined"))
    check r.status == sxSat
    check not r.errors.named(ubIntMinModMinusOne)

  test "an undefined side the path rules out is pruned, nothing recorded":
    let r = pinExact(sutModPositive, cellKey(axDefinedness, "mod/minusOne/pruned"))
    check r.status == sxSat
    check not r.errors.named(ubIntMinModMinusOne)

  test "through a call":
    let r = symexFind(sutModViaCall, tLabel("hit"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.errors.named(ubIntMinModMinusOne)

suite "W1-d1a low(T) div -1":
  test "checks on: one OverflowDefect fork, no halt":
    let r = pinExact(sutDivChecked, cellKey(axDefinedness, "div/intMin/minusOne/checked"),
                     target = tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check not r.errors.named(ubIntMinModMinusOne)

  test "checks off: the path halts":
    let r = symexFind(sutDivUnchecked, tLabel("hit"), noOverflowChecks)
    checkpoint show(r.errors)
    check not r.trusted
    check r.errors.named(ubIntMinModMinusOne)
