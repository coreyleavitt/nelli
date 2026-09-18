## Issue #163 review finding R27 (High, introduced THIS ROUND by R22's own
## fix, confirmed twice plus an adversarial verifier). R22 added
## `WalkCtx.localRangeTypes: Table[string, IRType]` to give `isAssign`
## (which carries no declared type of its own) a way to find its target's
## `range[lo..hi]` type. That table is keyed by the BARE SOURCE-TEXT NAME
## and lives on `WalkCtx` -- ONE instance for the whole walk -- while `Env`
## is correctly scoped PER-`Path`. Two failure directions follow:
##
## Direction 1 (silent skip -> false sxSat): a sibling branch's unrelated
## local sharing the ranged local's name DELETES the table entry (the
## `isLet` bookkeeping has no scope check), so a LATER assignment to the
## real ranged local no longer finds its type and the RangeDefect fork is
## silently skipped.
##
## Direction 2 (phantom raise -> false sxRaised): an inlined callee's
## `range[lo..hi]` local leaves its entry in the table after `popFrame`
## (only `w.frame` is saved/restored, not this table). A caller with an
## unrelated free `int` variable of the SAME NAME, assigned to after the
## call, gets checked against a range that has nothing to do with it.
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation executed for real in Nim, in this file.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

# ---- Direction 1: sibling-branch shadow silently deletes the tracked type --
#
##     proc f(cond: bool, y: range[0..500]) =
##       var v: range[1..10] = 1
##       if cond:
##         var v: int = 0      # unrelated shadow in the OTHER arm
##         v = 999
##       v = y                 # must still be checked: y can be > 10
##       symexTarget("t")
##       discard v
#
## Real Nim raises RangeDefect at the final `v = y` whenever `y` is outside
## [1,10], regardless of which branch of the `if` executed (the shadow
## local is a wholly separate variable, gone once its own block ends).

proc siblingShadowSkip(cond: bool, y: range[0..500]) =
  var v: range[1..10] = 1
  if cond:
    var v: int = 0
    v = 999
    discard v
  v = y
  symexTarget("t")
  discard v

suite "#163 review R27 -- the oracle (direction 1: sibling-branch shadow)":

  test "Nim itself raises RangeDefect on the post-if assignment regardless of branch":
    proc rt(cond: bool, y: range[0..500]): range[1..10] =
      var v: range[1..10] = 1
      if cond:
        var v: int = 0
        v = 999
        discard v
      v = y
      v
    expect RangeDefect:
      discard rt(true, 200)
    expect RangeDefect:
      discard rt(false, 200)
    check rt(true, 5) == 5
    check rt(false, 5) == 5

suite "#163 review R27 -- direction 1: a sibling shadow must not hide the check":

  test "the RangeDefect fork survives an unrelated same-named shadow in the other arm":
    ## Before the fix: the `if`'s branches walk against the SAME WalkCtx.
    ## The shadow arm's `var v: int = 0` runs `w.localRangeTypes.del("v")`
    ## unconditionally (no scope check), so by the time the post-if
    ## `v = y` statement walks, "v"'s entry is GONE -- the fork silently
    ## does not happen -- sxUnsat (nothing in the path space raises,
    ## because the raise was never modeled) instead of sxRaised.
    let r = symexFind(siblingShadowSkip, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(siblingShadowSkip, tLabel("t"))
    check r.status == sxSat

# ---- Direction 2: stale cross-call-frame entry produces a phantom raise ----
#
##     proc callee(z: range[1..10]) =
##       var v: range[1..10] = z    # isLet records "v" -> range[1..10]
##       discard v
##
##     proc caller(v: var int, y: int) =
##       callee(5)                  # inlines; popFrame does NOT clear the
##                                   # table -- "v"'s entry survives
##       v = y                      # `v` is a FORMAL, never isLet-declared
##                                   # in the caller -- nothing ever clears
##                                   # the stale entry -- phantom check
##                                   # against range[1..10]
##       symexTarget("t")
##       discard v
#
## Real Nim never raises here: `v` in `caller` is a plain (unranged) `var
## int` parameter, and `y` is an unconstrained `int` parameter -- there is
## no RangeDefect anywhere in `caller`'s body.

proc calleeWithRangedLocal(z: range[1..10]) =
  var v: range[1..10] = z
  discard v

proc staleCrossFramePhantom(v: var int, y: int) =
  calleeWithRangedLocal(5)
  v = y
  symexTarget("t")
  discard v

suite "#163 review R27 -- the oracle (direction 2: stale cross-call-frame entry)":

  test "Nim itself never raises -- caller's `v` is a plain unranged var int":
    proc rt(y: int): int =
      var v: int = -1
      calleeWithRangedLocal(5)
      v = y
      v
    check rt(999) == 999
    check rt(-999) == -999
    check rt(0) == 0

suite "#163 review R27 -- direction 2: a stale callee entry must not phantom-raise":

  test "no RangeDefect is found for a program that cannot raise one":
    ## Before the fix: `calleeWithRangedLocal`'s inlined body records
    ## "v" -> range[1..10] in the SHARED table; `popFrame` restores only
    ## `w.frame`, leaving the entry in place. The caller's own unrelated
    ## `var v: int = 0; v = y` then gets checked against range[1..10] even
    ## though `y` is a free, unconstrained int -- Z3 satisfies `y` outside
    ## [1,10] and the walker reports a phantom sxRaised(RangeDefect) for a
    ## program that cannot raise.
    let r = symexFind(staleCrossFramePhantom, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached (the program runs to completion)":
    let r = symexFind(staleCrossFramePhantom, tLabel("t"))
    check r.status == sxSat

# ---- Non-regression: R22's original local-assignment fork still works -----

proc plainAssignStillChecked(x, y: range[0..100]) =
  var v: range[1..100] = 1
  v = x + y
  symexTarget("t")
  discard v

suite "#163 review R27 non-regression -- R22's own local-assignment fork survives":

  test "Nim itself still raises for the un-shadowed, non-inlined case":
    proc rt(x, y: range[0..100]): range[1..100] =
      var v: range[1..100] = 1
      v = x + y
      v
    expect RangeDefect:
      discard rt(100, 100)
    check rt(1, 0) == 1

  test "the plain #163 R22 case is still found as sxRaised(RangeDefect)":
    let r = symexFind(plainAssignStillChecked, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the survivor path still reaches the label":
    let r = symexFind(plainAssignStillChecked, tLabel("t"))
    check r.status == sxSat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 136":
    check parseInt(symexWalkerVersion) >= 136
