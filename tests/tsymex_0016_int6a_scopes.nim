## RFC-0016 int6-a: the check-scope positions that still declined after
## int6-p2 and int6-o, one class per suite. This file builds with Nim's
## default checks and `-d:int6aPushed` (its `.cfg`).
##
## Native, on the pinned toolchain (each judged against the native binary by
## `pinFind`; a decline is `pinDecline` beside a `native` run of its input):
##   * stdlib: `system.delete` (system.nim:2123) and `strutils.cmpIgnoreStyle`
##     (strutils.nim:350) are compiled under their module's `push checks:
##     off`. `delete` still raises `IndexDefect` by its own explicit test, and
##     the caller's `Natural(i)` raises `RangeDefect`;
##   * ambiguous: a routine under `when defined(int6aPushed): {.push
##     rangeChecks: off.}` keeps `R(300)`; the scan cannot evaluate
##     `defined`, so the position reads both pushed and not;
##   * leaked: in `tsymex_0016_int6a_leak` (its own file: a user import
##     under a push is read as reaching every stdlib module, which would
##     taint the stdlib rows here);
##   * float: a routine under `when defined(int6aPushed): {.push nanChecks:
##     on.}` raises `FloatInvalidOpDefect` on `inf - inf`.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers

type R = range[0 .. 10]

const gk = cellKey(faGeneric, "int6a_scopes")

# ---- class 3: stdlib positions ---------------------------------------------

proc delAt(i: int) =
  var s = @[10, 20, 30]
  s.delete(i)
  if s.len == 2 and s[1] == 30: symexTarget("hit")

proc cmpStyle(a: string) =
  if a.len == 1 and cmpIgnoreStyle(a, "_F") == 0: symexTarget("hit")

# ---- class 1: an ambiguous position ----------------------------------------

when defined(int6aPushed):
  {.push rangeChecks: off.}
proc ambOff(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")
when defined(int6aPushed):
  {.pop.}

# ---- class 4: float checks maybe on and off --------------------------------

when defined(int6aPushed):
  {.push nanChecks: on.}
proc ambNan(a: float) =
  let d = a - a
  if d != d: symexTarget("hit")
when defined(int6aPushed):
  {.pop.}

suite "int6-a stdlib positions: a stdlib body under its module's push":
  test "system.delete under checks: off is walked, its own raise kept":
    check native(delAt(1)) == "hit"
    check native(delAt(3)) == "IndexDefect"
    check native(delAt(-1)) == "RangeDefect"
    let r = pinFind(delAt, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.named(feCheckOption)
    let x = pinFind(delAt, tRaisedExn("IndexDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
  test "strutils.cmpIgnoreStyle under checks: off is walked":
    check native(cmpStyle("f")) == "hit"
    let r = pinFind(cmpStyle, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.named(feCheckOption)

suite "int6-a ambiguous and float positions":
  test "a when-guarded push the scan cannot decide still declines":
    check native(ambOff(300)) == "hit"
    pinDecline(ambOff, gk, feCheckOption, needle = "ambOff")
  test "nanChecks maybe on and off still declines":
    check native(ambNan(Inf)) == "FloatInvalidOpDefect"
    pinDecline(ambNan, gk, feCheckOption, needle = "ambNan")

suite "int6-a: walker version":
  test "walker version floor >= 473":
    check parseInt(symexWalkerVersion) >= 473
