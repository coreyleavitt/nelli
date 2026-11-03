## RFC-0005 S8cu -- the forms a check pragma comes in, in the routine's own file.
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

const fieldsStayOff = false
const fieldsStayOn = true

# ---- a bare statement holds until a pop restores what was pushed --------------
{.push.}
{.fieldChecks: off.}
proc bareOff(v: int) = writeWrongBranch(v)
{.pop.}
proc barePopped(v: int) = writeWrongBranch(v)

{.fieldChecks: off.}
proc bareNoPush(v: int) = writeWrongBranch(v)
{.fieldChecks: on.}
proc bareBackOn(v: int) = writeWrongBranch(v)

# ---- a user pragma, as a statement, is its contents -----------------------------
{.pragma: usr, fieldChecks: off.}
{.pragma: usrPush, push, fieldChecks: off.}
{.push.}
{.usr.}
proc userStmt(v: int) = writeWrongBranch(v)
{.pop.}
{.usrPush.}
proc userPush(v: int) = writeWrongBranch(v)
{.pop.}
proc afterUser(v: int) = writeWrongBranch(v)

# ---- nesting -------------------------------------------------------------------
{.push fieldChecks: off.}
{.push fieldChecks: on.}
proc innerOn(v: int) = writeWrongBranch(v)
{.pop.}
proc innerPopped(v: int) = writeWrongBranch(v)
{.pop.}
{.push checks: off.}
{.push fieldChecks: on.}
proc umbrellaInnerOn(v: int) = writeWrongBranch(v)
{.pop.}
{.pop.}

# ---- how the value and the name are spelled --------------------------------------
{.push fieldChecks: false.}
proc litFalse(v: int) = writeWrongBranch(v)
{.pop.}
{.push field_checks: off.}
proc underscored(v: int) = writeWrongBranch(v)
{.pop.}
{.push fieldChecks: fieldsStayOff.}
proc constOff(v: int) = writeWrongBranch(v)
{.pop.}
{.push fieldChecks: fieldsStayOn.}
proc constOn(v: int) = writeWrongBranch(v)
{.pop.}

# ---- `when` ---------------------------------------------------------------------
when true:
  {.push fieldChecks: off.}
proc whenTrue(v: int) = writeWrongBranch(v)
when true:
  {.pop.}
when false:
  {.push fieldChecks: off.}
proc whenFalse(v: int) = writeWrongBranch(v)
when false:
  {.pop.}
when not defined(s8cuNoSuchSymbol):
  {.push fieldChecks: off.}
proc whenTaken(v: int) = writeWrongBranch(v)
when not defined(s8cuNoSuchSymbol):
  {.pop.}
when defined(s8cuNoSuchSymbol):
  {.push fieldChecks: off.}
proc whenNotTaken(v: int) = writeWrongBranch(v)
when defined(s8cuNoSuchSymbol):
  {.pop.}

# ---- not a check -----------------------------------------------------------------
{.push nilChecks: off.}
proc nilOption(v: int) = writeWrongBranch(v)
{.pop.}
{.push assertions: off.}
proc assertionsOption(v: int) = writeWrongBranch(v)
{.pop.}

# ---- a template that pushes: LAST, every later position reads as under it -------
proc beforePushingTemplate(v: int) = writeWrongBranch(v)
template pushFields() =
  {.push fieldChecks: off.}
pushFields()
proc viaPushingTemplate(v: int) = writeWrongBranch(v)
{.pop.}

suite "S8cu: statements":

  test "a bare statement under a push, and the pop":
    check native(bareOff(4)) == "hit"
    declines(bareOff, feCheckOption)
    check native(barePopped(4)) == "FieldDefect"
    decides(barePopped, sxRaised)

  test "a bare statement with no push, and turned back on":
    check native(bareNoPush(4)) == "hit"
    declines(bareNoPush, feCheckOption)
    check native(bareBackOn(4)) == "FieldDefect"
    decides(bareBackOn, sxRaised)

suite "S8cu: user pragmas":

  test "a user pragma as a statement, with and without its own push":
    check native(userStmt(4)) == "hit"
    declines(userStmt, feCheckOption)
    check native(userPush(4)) == "hit"
    declines(userPush, feCheckOption)
    check native(afterUser(4)) == "FieldDefect"
    decides(afterUser, sxRaised)

  test "a check pragma does not compile on a routine, or through a pushed user pragma":
    check not compiles((proc () {.checks: off.} = discard))
    check not compiles((proc () {.fieldChecks: off.} = discard))
    check not compiles((proc () {.usr.} = discard))

suite "S8cu: nesting":

  test "an inner push turning the check back on":
    check native(innerOn(4)) == "FieldDefect"
    decides(innerOn, sxRaised)
    check native(innerPopped(4)) == "hit"
    declines(innerPopped, feCheckOption)

  test "under `checks: off` the others stay off":
    check native(umbrellaInnerOn(4)) == "FieldDefect"
    declines(umbrellaInnerOn, feCheckOption)

suite "S8cu: spelling":

  test "`false` and an underscore":
    check native(litFalse(4)) == "hit"
    declines(litFalse, feCheckOption)
    check native(underscored(4)) == "hit"
    declines(underscored, feCheckOption)

  test "a value that is no literal is not read, either way":
    check native(constOff(4)) == "hit"
    declines(constOff, feCheckOption)
    check native(constOn(4)) == "FieldDefect"
    declines(constOn, feCheckOption)

suite "S8cu: when":

  test "decided branches":
    check native(whenTrue(4)) == "hit"
    declines(whenTrue, feCheckOption)
    check native(whenFalse(4)) == "FieldDefect"
    decides(whenFalse, sxRaised)

  test "an undecided condition declines, whichever way it went":
    check native(whenTaken(4)) == "hit"
    declines(whenTaken, feCheckOption)
    check native(whenNotTaken(4)) == "FieldDefect"
    declines(whenNotTaken, feCheckOption)

suite "S8cu: not checks":

  test "`nilChecks` is no option, and `assertions` guards nothing here":
    check native(nilOption(4)) == "FieldDefect"
    decides(nilOption, sxRaised)
    check native(assertionsOption(4)) == "FieldDefect"
    decides(assertionsOption, sxRaised)

suite "S8cu: a template that pushes":

  test "a template that pushes, seen in its own file":
    check native(beforePushingTemplate(4)) == "FieldDefect"
    decides(beforePushingTemplate, sxRaised)
    check native(viaPushingTemplate(4)) == "hit"
    declines(viaPushingTemplate, feCheckOption)
