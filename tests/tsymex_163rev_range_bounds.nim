## Issue #163 review finding R14a (Low) -- the range LOWER boundary.
##
## Every ranged test in the existing corpus starts its declared range at 0
## (`range[0..100]`, `range[0..10]`, etc.), so nothing distinguishes "the
## solver correctly excludes `lo - 1`" from "the solver merely never lets a
## value go negative" -- the two read identically when `lo == 0`. A bug that
## swapped the LOWER-bound comparison direction (e.g. `bvsge`/`bvuge` for
## `bvsle`/`bvule`) would silently degrade to "no lower bound at all" and
## still pass every existing test, because none of them separately probes
## "one below the true floor" for a floor that is not already the type's own
## natural minimum.
##
## Pinned here: a `range[50..60]` (non-zero, positive floor) and a
## `range[-20..-5]` (negative floor, forcing a genuinely signed underlying
## representation). For each: the floor itself is reachable, one below the
## floor is NOT, the ceiling itself is reachable, and one above the ceiling
## is not (the already-well-covered complement, included as a sanity
## companion so an accidentally-inverted assertion cannot pass by disabling
## both bounds at once).
##
## Method note (inherited from #162/#163): every symbolic expectation is
## paired with the same computation run for real in this file -- here, by
## replaying each returned witness through the SUT's own declared range
## constructor, which raises `RangeDefect` for a value the true domain
## cannot hold.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

# =============================================================================
# A positive, non-zero lower bound.
# =============================================================================

type
  Range5060 = range[50..60]

proc mkRange5060(x: int): Range5060 = Range5060(x)

proc paramAtLo(x: Range5060) =
  if ord(x) == 50:
    symexTarget("lo")

proc paramBelowLo(x: Range5060) =
  ## The bug this test exists to catch: if the lower-bound assertion were
  ## dropped or its comparison direction swapped, the free variable backing
  ## `x` could take any value the underlying bit width admits below 50 --
  ## this target would then be falsely `sxSat`.
  if ord(x) < 50:
    symexTarget("below")

proc paramAtHiPos(x: Range5060) =
  if ord(x) == 60:
    symexTarget("hi")

proc paramAboveHi(x: Range5060) =
  if ord(x) > 60:
    symexTarget("above")

suite "#163 review R14a -- non-zero positive lower bound (range[50..60])":

  test "the oracle -- Nim itself refuses 49 and 61, accepts 50 and 60":
    expect RangeDefect:
      discard mkRange5060(49)
    expect RangeDefect:
      discard mkRange5060(61)
    check mkRange5060(50) == 50
    check mkRange5060(60) == 60

  test "the floor itself is reachable, and the witness genuinely constructs":
    let r = symexFind(paramAtLo, tLabel("lo"))
    check r.status == sxSat
    check mkRange5060(r.witness[0]) == 50

  test "one below the floor is NOT reachable":
    let r = symexFind(paramBelowLo, tLabel("below"))
    check r.status == sxUnsat

  test "the ceiling itself is reachable, and the witness genuinely constructs":
    let r = symexFind(paramAtHiPos, tLabel("hi"))
    check r.status == sxSat
    check mkRange5060(r.witness[0]) == 60

  test "one above the ceiling is NOT reachable (sanity companion)":
    let r = symexFind(paramAboveHi, tLabel("above"))
    check r.status == sxUnsat

# =============================================================================
# A negative lower bound -- forces a genuinely signed underlying width.
# =============================================================================

type
  RangeNeg = range[-20 .. -5]

proc mkRangeNeg(x: int): RangeNeg = RangeNeg(x)

proc paramAtLoNeg(x: RangeNeg) =
  if ord(x) == -20:
    symexTarget("lo")

proc paramBelowLoNeg(x: RangeNeg) =
  if ord(x) < -20:
    symexTarget("below")

proc paramAtHiNeg(x: RangeNeg) =
  if ord(x) == -5:
    symexTarget("hi")

proc paramAboveHiNeg(x: RangeNeg) =
  if ord(x) > -5:
    symexTarget("above")

suite "#163 review R14a -- negative lower bound (range[-20..-5])":

  test "the oracle -- Nim itself refuses -21 and -4, accepts -20 and -5":
    expect RangeDefect:
      discard mkRangeNeg(-21)
    expect RangeDefect:
      discard mkRangeNeg(-4)
    check mkRangeNeg(-20) == -20
    check mkRangeNeg(-5) == -5

  test "the negative floor itself is reachable, and the witness genuinely constructs":
    let r = symexFind(paramAtLoNeg, tLabel("lo"))
    check r.status == sxSat
    check mkRangeNeg(r.witness[0]) == -20

  test "one below the negative floor is NOT reachable":
    let r = symexFind(paramBelowLoNeg, tLabel("below"))
    check r.status == sxUnsat

  test "the negative ceiling itself is reachable, and the witness genuinely constructs":
    let r = symexFind(paramAtHiNeg, tLabel("hi"))
    check r.status == sxSat
    check mkRangeNeg(r.witness[0]) == -5

  test "one above the negative ceiling is NOT reachable (sanity companion)":
    let r = symexFind(paramAboveHiNeg, tLabel("above"))
    check r.status == sxUnsat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 135
