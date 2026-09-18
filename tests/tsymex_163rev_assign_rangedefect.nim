## Issue #163 review finding R22 (Medium, confirmed twice this round) -- a
## real Nim `RangeDefect` at an ASSIGNMENT into a `range[lo..hi]`-typed
## local is invisible to `symexFind`. `drainConvFloatToIntRaises`
## (`runtime.nim`) was the ONLY place `RangeDefect` was ever forked in the
## whole engine -- for float->int conversion -- so an assignment like
##
##     var v: range[1..100]
##     v = x + y          # raises RangeDefect if x + y falls outside 1..100
##
## simply never forked: the walker narrowed nothing and raised nothing, so
## a raise-target search targeting "RangeDefect" at this site could never
## find it.
##
## R17 (this round, `tsymex_163rev_armfield_write.nim`) deliberately did
## NOT fix this by asserting a range CONSTRAINT at the assignment site --
## that would tell the solver an out-of-range assignment cannot happen,
## silently making a genuine `RangeDefect` UNREACHABLE. The correct model,
## implemented here: the assignment FORKS. One branch has the value in
## `[lo,hi]` and continues; the other is outside and raises `RangeDefect`.
##
## Scope: this fixes ONLY the plain-local-variable assignment site
## (`isAssign`, a bare `v = expr` reassigning a `var v: range[lo..hi]`
## local). Object-field writes through a ref (plain field and variant-arm
## field) and seq/array element writes are NOT covered -- see the
## handoff for the enumerated remainder.
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation executed for real in Nim, in this file.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

# ---- Part 1: the headline -- a genuinely out-of-range assignment raises ----

proc assignOutOfRange(x, y: range[0..100]) =
  var v: range[1..100] = 1
  v = x + y                 # x+y can reach 200 -- outside [1,100]
  symexTarget("t")
  discard v

# ---- Part 2: the precision case -- provably in range, must NOT fork -------
# x, y are each bounded so x+y can reach at most 100 -- fits [1,100]'s
# upper bound; x+y's minimum is 0, which is BELOW 1 -- so this is only
# "provably in range" if the lower bound also holds. Use bounds that make
# the sum provably inside [1,100] on both ends.

proc assignProvablyInRange(x, y: range[1..50]) =
  var v: range[1..100] = 1
  v = x + y                 # x+y in [2,100] -- always inside [1,100]
  symexTarget("t")
  discard v

# ---- Part 3: non-regression -- an ordinary unranged local is unaffected ---

proc assignPlainInt(x, y: range[0..100]) =
  ## `x, y` are bounded (not merely `int`) so their sum cannot itself
  ## overflow int64 -- Phase 15 E6 surfaces ANY reachable `Defect` raise
  ## regardless of the search's `typeFilter` (`runtime.nim`'s `routeRaise`:
  ## a non-excluded defect "always surfaces"), so an unbounded `x + y`
  ## would confound this pin with a genuine, unrelated `OverflowDefect`
  ## rather than isolating the thing under test: `v`'s OWN declared type
  ## (plain `int`, no range) must never gain a `RangeDefect` fork.
  var v: int = 0
  v = x + y
  symexTarget("t")
  discard v

suite "#163 review R22 -- the oracle":

  test "Nim itself raises RangeDefect assigning an out-of-range sum into a ranged local":
    proc rt(x, y: range[0..100]): range[1..100] =
      var v: range[1..100] = 1
      v = x + y
      v
    expect RangeDefect:
      discard rt(100, 100)   # 200, outside [1,100]
    check rt(1, 0) == 1      # in range -- does not raise

  test "the oracle -- the precision-case sum never leaves the declared range":
    proc rt(x, y: range[1..50]): range[1..100] =
      var v: range[1..100] = 1
      v = x + y
      v
    check rt(1, 1) == 2
    check rt(50, 50) == 100

suite "#163 review R22 -- an out-of-range assignment raises instead of vanishing":

  test "a genuinely out-of-range assignment is found as sxRaised(RangeDefect)":
    ## Before the fix: sxUnsat (the walker modeled no RangeDefect fork at
    ## all -- there is genuinely nothing in the path space matching the
    ## search, since the raise itself was never built).
    let r = symexFind(assignOutOfRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the same program still reports sxSat reaching the label (the survivor path)":
    ## The in-range branch survives -- `x=0,y=0..100` (or any in-range
    ## sum) still reaches "t" normally.
    let r = symexFind(assignOutOfRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 -- a provably-in-range assignment does not fork":

  test "no RangeDefect is found when the sum cannot leave the declared range":
    let r = symexFind(assignProvablyInRange, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached normally":
    let r = symexFind(assignProvablyInRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 non-regression -- an ordinary unranged local is unaffected":

  test "no RangeDefect fork on a plain int local":
    let r = symexFind(assignPlainInt, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached":
    let r = symexFind(assignPlainInt, tLabel("t"))
    check r.status == sxSat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 136 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 136
