## Issue #163 item 3 (rev) -- `maxFrontierSize` and why its default is `0`.
##
## HISTORY, and a reversal worth reading before changing this again.
##
## Round 8 (`991b0ff`) changed the omitted-field default from `0` (unbounded)
## to `256`, on two premises: that finding R22's new `RangeDefect` forks could
## multiply the frontier on a ranged loop counter, and that `256` was 16x the
## largest frontier measured (16) across ~20 heavy suites.
##
## BOTH premises turned out to be wrong, and round 9's full sweep proved it:
##
##  1. R22's forks do NOT multiply the frontier. `forkAssignRangeCheck` takes
##     one input `Path` and returns exactly ONE survivor; the out-of-range
##     sub-path is terminal via `discard routeRaise(...)` and never joins the
##     returned set. A ranged assignment in a loop NARROWS the same path's `pc`
##     each iteration. So the cap was bounding a growth mode that does not
##     exist. (Established by the round-9 correctness lens, then confirmed
##     against the code.)
##  2. The measurement was not broad enough. `tsymex_r6_a4_construct_
##     interactions`'s A4-3b -- a wide 10-tag variant constructed and then
##     reassigned symbolically -- carries 66 live paths past the cap, and the
##     prune turned a genuine UNSAT into `sxUnknown` (`beBudgetExhausted`).
##     That is a real completeness regression against the recorded baseline,
##     caught by the sweep and NOT by the ~20-suite sample.
##
## So the default is back to `0`. The cap mechanism itself is fine and is kept
## -- it degrades honestly (sets `sawUnknown`, records `beBudgetExhausted`, can
## never yield a truncated `sxUnsat`) and remains available per-run. What is
## reverted is only the DEFAULT, i.e. imposing it on every existing user to
## solve a problem that was never there.
##
## If you want a non-zero default again, the bar is: measure across the WHOLE
## corpus (`scripts/sweep.sh`), not a sample, and have a growth mode that
## actually needs bounding.
##
import std/[unittest, strutils, sequtils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/types

suite "#163 item 3 -- maxFrontierSize default":

  test "the omitted-field default is 0 (unbounded) -- see this file's header":
    ## Reverted from round 8's 256: the growth mode it bounded does not exist,
    ## and 256 regressed a genuine UNSAT to sxUnknown on a 10-tag variant
    ## reassign (66 live paths). The cap stays available per-run.
    check defaultResourceBudget().maxFrontierSize == 0
    check ResourceBudget().maxFrontierSize == 0

  test "an explicit 0 still means unlimited (the opt-out survives the new default)":
    let unlimited = ResourceBudget(maxFrontierSize: 0)
    check unlimited.maxFrontierSize == 0
    ## And an explicitly-set cap is still honoured, which is the point of
    ## keeping the mechanism while dropping the default.
    let capped = ResourceBudget(maxFrontierSize: 256)
    check capped.maxFrontierSize == 256

  test "an explicit non-zero literal is unaffected by the new default":
    let tight = ResourceBudget(maxFrontierSize: 1)
    check tight.maxFrontierSize == 1

# ---------------------------------------------------------------------------
# The default cap must not truncate an ordinary, currently-passing analysis:
# a SUT whose frontier grows well past #163 item 3's own MEASURED ceiling
# (16) but stays comfortably under the new default (256) must still resolve
# normally under DEFAULT settings -- no explicit budget override.
# ---------------------------------------------------------------------------

proc manyBranchesReachable(x: int) =
  # 6 nested ifs -> up to 64 paths, well past the measured 16-path ceiling
  # but well under the 256 default.
  if x mod 2 == 0:
    if x mod 3 == 0:
      if x mod 5 == 0:
        if x mod 7 == 0:
          if x mod 11 == 0:
            if x mod 13 == 0:
              symexTarget("deep-hit")

suite "#163 item 3 -- the default cap does not truncate an ordinary analysis":

  test "oracle -- x = 2*3*5*7*11*13 satisfies every mod-0 condition":
    let x = 2 * 3 * 5 * 7 * 11 * 13
    check x mod 2 == 0
    check x mod 3 == 0
    check x mod 5 == 0
    check x mod 7 == 0
    check x mod 11 == 0
    check x mod 13 == 0

  test "under DEFAULT settings (no explicit budget), the deep target is still sxSat":
    let r = symexFind(manyBranchesReachable, tLabel("deep-hit"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# The cap must degrade HONESTLY when it does fire: a classified `sxUnknown`
# (via `beBudgetExhausted`), never a silent truncation that could fake an
# `sxSat`/`sxUnsat`. Reuses `tsymex_phase14_frontier_pruning.nim`'s own
# UNSAT-shaped SUT (that file already pins the mechanism for an explicit
# tight cap; this pins that the DEGRADE PATH itself is unchanged by giving
# the field a non-zero default).
# ---------------------------------------------------------------------------

proc multiBranchUnreachable(x: int) =
  if x mod 2 == 0:
    if x mod 3 == 0:
      if x mod 5 == 0:
        if x == 1 and x == 2:
          symexTarget("never")

suite "#163 item 3 -- an exceeded cap degrades honestly (never a silent wrong verdict)":

  test "oracle -- x == 1 and x == 2 is unsatisfiable for any x":
    for x in [0, 1, 2, 6, 30, -30]:
      check not (x == 1 and x == 2)

  test "a tight explicit cap on an UNSAT target yields sxUnknown, not a fabricated sxUnsat/sxSat":
    const tightSettings = block:
      var s = defaultSymexSettings()
      s.budget.maxFrontierSize = 1
      s
    let r = symexFind(multiBranchUnreachable, tLabel("never"), tightSettings)
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == beBudgetExhausted)

  test "control: the same target under an unlimited (explicit 0) budget is genuinely sxUnsat":
    const unlimitedSettings = block:
      var s = defaultSymexSettings()
      s.budget.maxFrontierSize = 0
      s
    check symexFind(multiBranchUnreachable, tLabel("never"), unlimitedSettings).status == sxUnsat


suite "#163 item 3 -- walker version pin":

  test "walker version floor >= 138 (the round this fix lands in)":
    check parseInt(symexWalkerVersion) >= 139
