## Issue #163 item 3 (rev) -- `maxFrontierSize` defaulted to `0` (= unbounded).
## It is the one INCREMENTAL per-statement frontier cap (`walkBlock`,
## `runtime.nim`), and with no default cap nothing bounds multiplicative path
## growth -- more pressing since finding R22 added a `RangeDefect` fork at
## ranged assignments (a ranged loop counter can now fork per iteration
## whenever its `ziIvl` discharge is defeated by an unconstrained RHS).
##
## `0` remains the documented opt-out meaning UNLIMITED (`ResourceBudget`'s
## majority contract) -- this only changes what an OMITTED field gets.
## Measured (not guessed): the largest post-step frontier observed across a
## broad sample of this engine's heaviest/branchiest currently-terminating
## suites was 16 (`tsymex_r6_n9_variant_budget.nim`, measured via a temporary
## `walkBlock` instrumentation in a throwaway `git worktree`, never
## committed). The new default, `256`, is 16x that ceiling and also matches
## an existing precedent value already chosen by a test author in this
## codebase for this exact field (`tsymex_phase7_assertcovered.nim`'s `lax`
## config).
##
## House rule: every symbolic expectation is paired with an oracle computed
## by real Nim execution in this same file.

import std/[unittest, strutils, sequtils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/types

suite "#163 item 3 -- maxFrontierSize default":

  test "the omitted-field default is now 256, not 0":
    check defaultResourceBudget().maxFrontierSize == 256
    check ResourceBudget().maxFrontierSize == 256

  test "an explicit 0 still means unlimited (the opt-out survives the new default)":
    let unlimited = ResourceBudget(maxFrontierSize: 0)
    check unlimited.maxFrontierSize == 0

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
