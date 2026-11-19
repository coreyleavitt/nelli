## RFC-0016 PRC-07 (float half, and the nil-checks line).
##
## Float checks. Read from the generated C of the pinned toolchain (c and cpp,
## a routine under `{.push nanChecks: on.}` / `infChecks` / `floatChecks`):
## only the binary float `+`, `-`, `*` and `/` are checked, after the
## operation, the NaN check first:
##   if (result != result) raiseFloatInvalidOp();                 nanChecks
##   if (result != 0.0 && result*0.5 == result) raiseFloatOverflow(result);
##                                                                 infChecks
## so an operand that is already infinite trips the second (`inf + 1`). Unary
## minus and the float conversions are not checked. Both raises are ordinary
## catchable defects. Before this slice a routine with either option on
## declined `feCheckOption`; it is now walked as compiled.
##
## Nil checks. Nim 2.2.10 has no `nilChecks` option: `--nilChecks:on` and
## `off` generate identical C, both builds SIGSEGV on a nil dereference, and
## `{.push nilChecks: off.}` changes nothing (`check_options.nim`). The walker
## already treats a nil dereference as an uncatchable crash in every build
## (`crashRaise`); the pin below holds the pushed routine to the plain one.
##
## Split (RFC-0016 INT-51) into three files so each runs inside the CI ceiling:
## `tsymex_0016_floatchecks_nan` (`nanChecks`, and both checks on a NaN),
## `tsymex_0016_floatchecks_inf` (`infChecks`) and
## `tsymex_0016_floatchecks_caught` (a catching caller, the compound
## assignments, the unpushed build and the nil-checks line). Every pin of the
## one file is in exactly one of them.
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import ./s8cu_helpers

const
  nanK = cellKey(axPragma, "routine/nanChecks")
  infK = cellKey(axPragma, "routine/infChecks")
  floatK = cellKey(axPragma, "routine/floatChecks")
  floats = sampled([0.0, 1.0, -1.0, 2.0, Inf, NegInf, NaN])

{.push floatChecks: on.}
proc bothCaught(a: float) =
  try:
    let r = 1.0 / a
    if r == 4.0: symexTarget("quarter")
  except FloatOverflowDefect:
    symexTarget("hit")
{.pop.}

{.push nanChecks: on, infChecks: on.}
proc pushedCompound(a: float) =
  ## `x /= 0.0` runs system's generic `/=`, which takes the options of its
  ## definition (the build's: off here), not this routine's push. Native,
  ## c and cpp (Nim 2.2.10): no raise, the NaN and the inf run on.
  var x = a
  x /= 0.0
  if x != x: symexTarget("hit")

proc pushedCompoundInf(a: float) =
  var x = a
  x *= 10.0
  if x == Inf: symexTarget("hit")
{.pop.}

proc plainDiv(a: float) =
  ## No push: the default build checks no float operation.
  let r = a / 0.0
  if r != r: symexTarget("hit")

type R = ref object
  a: int

proc nilPlain(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  except NilAccessDefect:
    symexTarget("hit")

{.push nilChecks: off.}
proc nilPushed(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  except NilAccessDefect:
    symexTarget("hit")
{.pop.}

template decided(body: untyped) =
  ## A verdict is decided only on a verified build row; cpp under Z3 4.13.4
  ## has none by design (`feHostUnadmitted`).
  if hostAdmission().isSome:
    skipUnadmitted()
  else:
    body

suite "PRC-07: float checks are walked as compiled":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 311

  test "a catching caller sees FloatOverflowDefect":
    decided:
      check native(bothCaught(0.0)) == "hit"
      let r = pinExact(bothCaught, floatK, domain = floats)
      check r.status == sxSat
      let q = pinExact(bothCaught, floatK, target = tLabel("quarter"),
                       domain = floats)
      check q.status == sxSat

  test "a compound assignment takes the build's checks, not the push":
    decided:
      check native(pushedCompound(0.0)) == "hit"
      let r = pinExact(pushedCompound, floatK, domain = floats)
      check r.status == sxSat
      let x = pinExact(pushedCompound, floatK, target = tRaisedExn(),
                       domain = floats)
      check x.status == sxUnsat
      check native(pushedCompoundInf(1e308)) == "hit"
      let i = pinExact(pushedCompoundInf, floatK, domain = floats)
      check i.status == sxSat
      let j = pinExact(pushedCompoundInf, floatK, target = tRaisedExn(),
                       domain = floats)
      check j.status == sxUnsat

  test "no push: the default build checks no float operation":
    decided:
      check native(plainDiv(0.0)) == "hit"
      let r = symexFind(plainDiv, tRaisedExn(), settings = pinSettingsConst)
      check r.status == sxUnsat

suite "PRC-07: nilChecks is no option":
  test "a nil dereference under `push nilChecks: off` is the same crash":
    decided:
      let p = symexFind(nilPlain, tNilAccess(), settings = pinSettingsConst)
      let q = symexFind(nilPushed, tNilAccess(), settings = pinSettingsConst)
      checkpoint show(q.errors)
      check p.status == sxRaised
      check q.status == p.status
      check q.raisedTypeId == p.raisedTypeId
      let h = symexFind(nilPushed, tLabel("hit"), settings = pinSettingsConst)
      check h.status == symexFind(nilPlain, tLabel("hit"),
                                  settings = pinSettingsConst).status
