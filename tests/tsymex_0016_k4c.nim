## RFC-0016 K4c (section 8.1): the stdlib-body axis and its check-option delta.
##
## `math.nim` pushes `checks: off` over nearly all of std/math (PRC-09). A
## routine there runs unchecked in a build that checks, so the walker may
## neither raise its `OverflowDefect` / `DivByZeroDefect` (native does not) nor
## decline the whole routine when the body trips nothing (native decides).
## `stdlibAxis` rows carry the delta (`exercises`); the walker reads them in
## `applyStdlibDelta`. This build checks (the default); `tsymex_0016_k4c_off`
## is the same SUTs under `--overflowChecks:off`.
import std/[unittest, math, options, strutils]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/stdlib_rows
import nelli/smt/buildprofile
import ./s8cu_helpers

proc sIsPow2(a: int) =
  if isPowerOfTwo(a) and a == 8: symexTarget("hit")
proc sFloorDiv(a: int) =
  if floorDiv(a, 2) == 3 and a == 7: symexTarget("hit")
proc sFloorMod(a: int) =
  if floorMod(a, 3) == 2 and a == -1: symexTarget("hit")
proc sEuclDiv(a: int) =
  if euclDiv(a, -3) == 3 and a == -7: symexTarget("hit")
# The zero divisor: user code raises (a check), the stdlib body does not (the
# push turned it off) and the C division traps.
proc sUserDiv(a, b: int) =
  if a div b == 3 and b == 0: symexTarget("hit")
proc sFloorDivZero(a, b: int) =
  if floorDiv(a, b) == 3 and b == 0: symexTarget("hit")
# A routine in the same pushed region whose row declines keeps declining.
proc sCeilDiv(a: int) =
  if ceilDiv(a, 3) == 3 and a == 7: symexTarget("hit")

const smallInts = sampled([-7, -5, -3, -1, 0, 1, 2, 3, 5, 7, 8, 9])

suite "K4c: the rows":
  test "a walked row carries its check-option delta":
    let a = admitStdlibBody("math.floorDiv", ssBodyWalk)
    check a.admitted
    check a.payload.exercises == {coOverflow}
    check a.cell == cellKey(axStdlibBody, "math.floorDiv")

  test "a walked row declines at another site, naming its cell":
    let a = admitStdlibBody("math.floorDiv", ssType)
    check not a.admitted
    check "stdlib:math.floorDiv" in a.decline[1]

  test "a routine with no row is absent, a decline":
    let a = admitStdlibBody("math.noSuchRoutine", ssBodyWalk)
    check not a.admitted
    check a.decline[0] == some(feUnadmitted)

suite "K4c: a body under math.nim's push, checks on":
  test "math.isPowerOfTwo":
    let r = pinExact(sIsPow2, cellKey(axStdlibBody, "math.isPowerOfTwo"),
                     domain = smallInts)
    check r.status == sxSat
  test "math.floorDiv":
    let r = pinExact(sFloorDiv, cellKey(axStdlibBody, "math.floorDiv"),
                     domain = smallInts)
    check r.status == sxSat
  test "math.floorMod":
    let r = pinExact(sFloorMod, cellKey(axStdlibBody, "math.floorMod"),
                     domain = smallInts)
    check r.status == sxSat
  test "math.euclDiv":
    let r = pinExact(sEuclDiv, cellKey(axStdlibBody, "math.euclDiv"),
                     domain = smallInts)
    check r.status == sxSat

const probeFloorDivZero = """
import std/math
proc id(x: int): int {.noinline.} = x
echo floorDiv(id(5), id(0))
"""

suite "K4c: the delta pinned both ways (user routine checked, stdlib body not)":
  test "native: user `a div 0` raises, math.floorDiv(a, 0) traps":
    check native(sUserDiv(5, 0)) == "DivByZeroDefect"
    pinCrash(cellKey(axDefinedness, "div/zero/mathPushedOff"),
             probeFloorDivZero, [], ceDivTrap)

  test "walker: the user routine raises (checked)":
    let r = symexFind(sUserDiv, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    check not r.errors.named(ubSignedDivZero)

  test "walker: the stdlib body halts on the undefined division (unchecked)":
    pinDecline(sFloorDivZero, cellKey(axStdlibBody, "math.floorDiv"),
               ubSignedDivZero)
    let r = symexFind(sFloorDivZero, tLabel("hit"))
    check r.status != sxRaised

suite "K4c: a declined row keeps declining":
  test "math.ceilDiv is in the pushed region and its row declines":
    check native(sCeilDiv(7)) == "hit"
    let c = cellKey(axStdlibBody, "math.ceilDiv")
    pinDecline(sCeilDiv, c, feCheckOption, needle = render(c))
