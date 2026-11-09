## RFC-0016 K4c: the check-option delta under `--overflowChecks:off` (the
## cfg beside this file). The stdlib body is as unchecked as the build, so
## the user routine and `math.floorDiv` now agree: both halt on `x div 0`.
## `tsymex_0016_k4c` is the checks-on half of the pair.
import std/[unittest, math]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import ./s8cu_helpers

proc sUserDiv(a, b: int) =
  if a div b == 3 and b == 0: symexTarget("hit")
proc sFloorDivZero(a, b: int) =
  if floorDiv(a, b) == 3 and b == 0: symexTarget("hit")
proc sFloorDiv(a: int) =
  if floorDiv(a, 2) == 3 and a == 7: symexTarget("hit")

const probeUserDivZero = """
proc id(x: int): int {.noinline.} = x
echo id(5) div id(0)
"""
const probeFloorDivZero = """
import std/math
proc id(x: int): int {.noinline.} = x
echo floorDiv(id(5), id(0))
"""

suite "K4c (overflowChecks off): the user routine is as unchecked as the stdlib":
  test "native: both trap":
    pinCrash(cellKey(axDefinedness, "div/zero/userUnchecked"),
             probeUserDivZero, ["--overflowChecks:off"], ceDivTrap)
    pinCrash(cellKey(axDefinedness, "div/zero/mathPushedOff"),
             probeFloorDivZero, ["--overflowChecks:off"], ceDivTrap)

  test "walker: both halt on the undefined division":
    pinDecline(sUserDiv, cellKey(axDefinedness, "div/zero/userUnchecked"),
               ubSignedDivZero)
    pinDecline(sFloorDivZero, cellKey(axStdlibBody, "math.floorDiv"),
               ubSignedDivZero)

  test "math.floorDiv decides where the body trips nothing":
    check native(sFloorDiv(7)) == "hit"
    let r = pinExact(sFloorDiv, cellKey(axStdlibBody, "math.floorDiv"),
                     domain = sampled([-7, -1, 0, 1, 2, 7, 8]))
    check r.status == sxSat
