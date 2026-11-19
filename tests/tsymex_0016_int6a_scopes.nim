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
##     rangeChecks: off.}` keeps `R(300)`, and one under `when
##     defined(int6aNotDefined)` raises `RangeDefect`. int6-a2: the entry
##     macro has its call site evaluate each `defined(x)` and expands again,
##     so both are walked exactly; a `when` on a `const` still declines
##     (`ambConst` keeps 300);
##   * leaked: in `tsymex_0016_int6a_leak` (its own file: a user import
##     under a push is read as reaching every stdlib module, which would
##     taint the stdlib rows here);
##   * float: a routine under `when defined(int6aPushed): {.push nanChecks:
##     on.}` raises `FloatInvalidOpDefect` on `inf - inf`; decided as class 1
##     is (int6-a2), it is walked checked.

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

when defined(int6aNotDefined):
  {.push rangeChecks: off.}
proc ambNotOff(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")
when defined(int6aNotDefined):
  {.pop.}

when not defined(int6aNotDefined) and (defined(int6aPushed) or false):
  {.push rangeChecks: off.}
proc ambCompound(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")
when not defined(int6aNotDefined) and (defined(int6aPushed) or false):
  {.pop.}

const int6aConst = true
when int6aConst:
  {.push rangeChecks: off.}
proc ambConst(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")
when int6aConst:
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

template keeps(fn: untyped) =
  ## Natively `fn(300)` reaches the label and never raises `RangeDefect`.
  check native(fn(300)) == "hit"
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  check not r.errors.named(feCheckOption)
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxUnsat

suite "int6-a2 ambiguous positions: defined() decided at the call site":
  test "a push under a defined name is walked pushed":
    keeps(ambOff)
    keeps(ambCompound)
  test "a push under an undefined name is walked checked":
    check native(ambNotOff(300)) == "RangeDefect"
    check native(ambNotOff(5)) == "ran"
    let x = pinFind(ambNotOff, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
    check not x.errors.named(feCheckOption)
    let r = pinFind(ambNotOff, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "a when on a const is not decided and still declines":
    check native(ambConst(300)) == "hit"
    pinDecline(ambConst, gk, feCheckOption, needle = "ambConst")

suite "int6-a float positions":
  test "nanChecks pushed on under a defined name is walked checked":
    check native(ambNan(Inf)) == "FloatInvalidOpDefect"
    let x = pinFind(ambNan, tRaisedExn("FloatInvalidOpDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
    check not x.errors.named(feCheckOption)

suite "int6-a: walker version":
  test "walker version floor >= 474":
    check parseInt(symexWalkerVersion) >= 474
