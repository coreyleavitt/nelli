## RFC-0005 S8cu -- bodies, forward declarations, the routine kinds, callees, templates and
## the float checks.
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_helpers

type K = enum kA, kB, kC, kD
type P = object
  case k: K
  of kA, kB: x: int
  of kC: y: int
  else: discard

template writeWrongBranch(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")

template wrap(v: int) =
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("hit")

# ---- a body ----------------------------------------------------------------------
proc bodyPush(v: int) =
  var o = P(k: kA, x: v)
  {.push fieldChecks: off.}
  o.y = v
  {.pop.}
  symexTarget("hit")

proc bodyPushNested(v: int) =
  {.push checks: off.}
  proc inner(v: int) = writeWrongBranch(v)
  {.pop.}
  inner(v)

# ---- a forward declaration -----------------------------------------------------
{.push fieldChecks: off.}
proc fwdUnder(v: int)
{.pop.}
proc fwdUnder(v: int) = writeWrongBranch(v)

proc fwdClean(v: int)
{.push fieldChecks: off.}
proc fwdClean(v: int) = writeWrongBranch(v)
{.pop.}

# ---- routines of other kinds ------------------------------------------------------
type Base = ref object of RootObj
{.push overflowChecks: off.}
func funcOff(v: int): int = v + 1
proc inlineOff(v: int): int {.inline.} = v + 1
method methOff(b: Base; v: int): int {.base.} = v + 1
converter convOff(v: uint8): int = int(v) + high(int)
iterator closureOff(v: int): int {.closure.} = yield v + 1
let lambdaOff = proc (v: int): int = v + 1
iterator inlineIterDefUnder(v: int): int = yield v + 1
{.pop.}
proc viaFunc(v: int) =
  if v == high(int) and funcOff(v) < 0: symexTarget("hit")
proc viaInline(v: int) =
  if v == high(int) and inlineOff(v) < 0: symexTarget("hit")
proc viaMethod(v: int) =
  if v == high(int) and methOff(Base(), v) < 0: symexTarget("hit")
proc viaConverter(v: uint8) =
  let w: int = v
  if w < 0: symexTarget("hit")
proc viaClosureIter(v: int) =
  if v == high(int):
    for x in closureOff(v):
      if x < 0: symexTarget("hit")
proc viaLambda(v: int) =
  if v == high(int) and lambdaOff(v) < 0: symexTarget("hit")
proc viaInlineIter(v: int) =
  if v == high(int):
    for x in inlineIterDefUnder(v):
      if x < 0: symexTarget("hit")
iterator inlineIterClean(v: int): int = yield v + 1
{.push overflowChecks: off.}
proc inlineIterInPush(v: int) =
  if v == high(int):
    for x in inlineIterClean(v):
      if x < 0: symexTarget("hit")
{.pop.}

# ---- a callee --------------------------------------------------------------------
{.push fieldChecks: off.}
proc calleeOff(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
{.pop.}
proc viaCallee(v: int) =
  calleeOff(v)
  symexTarget("hit")
proc calleeNotReached(v: int) =
  ## A path no input takes does not decline (S8bc's drop).
  if v > 0 and v < 0: calleeOff(v)
  if v == 7: symexTarget("hit")

# ---- a template ------------------------------------------------------------------
{.push overflowChecks: off.}
template tplDefUnder(v: int): int = v + 1
{.pop.}
template tplClean(v: int): int = v + 1
proc tplOutOfPush(v: int) =
  if v == high(int):
    let w = tplDefUnder(v)
    if w < 0: symexTarget("hit")
{.push overflowChecks: off.}
proc tplInPush(v: int) =
  if v == high(int):
    let w = tplClean(v)
    if w < 0: symexTarget("hit")
{.pop.}

# ---- the float checks, off by default ----------------------------------------------
proc floatDefault(a: float) =
  if a == 1e308 and a * 10.0 > a: symexTarget("hit")
{.push floatChecks: on.}
proc floatOn(a: float) =
  if a == 1e308 and a * 10.0 > a: symexTarget("hit")
{.pop.}
{.push infChecks: on.}
proc infOn(a: float) =
  if a == 1e308 and a * 10.0 > a: symexTarget("hit")
{.pop.}
{.push nanChecks: on.}
proc nanOn(a: float) =
  if a == Inf and (a - a) != (a - a): symexTarget("hit")
{.pop.}
{.push checks: on.}
proc checksOnFloat(a: float) =
  if a == 1e308 and a * 10.0 > a: symexTarget("hit")
proc checksOnNoFloat(v: int) = writeWrongBranch(v)
{.pop.}

suite "S8cu: a body":

  test "a push in a body declines by its statement":
    check native(bodyPush(4)) == "hit"
    declines(bodyPush, feUnsupportedStmtKind)

  test "a routine nested under a body's push":
    check native(bodyPushNested(4)) == "hit"
    declines(bodyPushNested, feUnsupportedStmtKind)

suite "S8cu: a forward declaration":

  test "the options are the body's":
    check native(fwdUnder(4)) == "FieldDefect"
    decides(fwdUnder, sxRaised)
    check native(fwdClean(4)) == "hit"
    declines(fwdClean, feCheckOption)

suite "S8cu: routines of other kinds":

  test "a func and an inline proc":
    check native(viaFunc(high(int))) == "hit"
    declines(viaFunc, feOverflowCheckOption)
    check native(viaInline(high(int))) == "hit"
    declines(viaInline, feOverflowCheckOption)

  test "a method":
    check native(viaMethod(high(int))) == "hit"
    let r = symexFind(viaMethod, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown

  test "a converter":
    check native(viaConverter(1'u8)) == "hit"
    let r = symexFind(viaConverter, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown

  test "a closure iterator is compiled at its definition":
    check native(viaClosureIter(high(int))) == "hit"
    let r = symexFind(viaClosureIter, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown

  test "a lambda":
    check native(viaLambda(high(int))) == "hit"
    let r = symexFind(viaLambda, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown

  test "an inline iterator takes the routine it lands in":
    check native(viaInlineIter(high(int))) == "OverflowDefect"
    decides(viaInlineIter, sxRaised)
    check native(inlineIterInPush(high(int))) == "hit"
    declines(inlineIterInPush, feOverflowCheckOption)

suite "S8cu: a callee":

  test "a callee under a push":
    check native(viaCallee(4)) == "hit"
    declines(viaCallee, feCheckOption)

  test "one no input reaches does not decline the rest":
    check native(calleeNotReached(7)) == "hit"
    decides(calleeNotReached, sxSat)

suite "S8cu: templates":

  test "a template takes the routine it expands into":
    check native(tplOutOfPush(high(int))) == "OverflowDefect"
    decides(tplOutOfPush, sxRaised)
    check native(tplInPush(high(int))) == "hit"
    declines(tplInPush, feOverflowCheckOption)

suite "S8cu: the float checks":

  test "off by default: the model holds (control)":
    check native(floatDefault(1e308)) == "hit"
    decides(floatDefault, sxSat)

  test "on, the walker has no such raise":
    check native(floatOn(1e308)) == "FloatOverflowDefect"
    declines(floatOn, feCheckOption)
    check native(infOn(1e308)) == "FloatOverflowDefect"
    declines(infOn, feCheckOption)
    check native(nanOn(Inf)) == "FloatInvalidOpDefect"
    declines(nanOn, feCheckOption)

  test "`checks: on` turns them on, and matters only to float code":
    check native(checksOnFloat(1e308)) == "FloatOverflowDefect"
    declines(checksOnFloat, feCheckOption)
    check native(checksOnNoFloat(4)) == "FieldDefect"
    decides(checksOnNoFloat, sxRaised)
