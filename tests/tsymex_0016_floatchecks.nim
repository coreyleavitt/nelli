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

{.push nanChecks: on.}
proc nanDiv(a: float) =
  ## `a / 0.0`: NaN at `a == 0` (raises), `±inf` otherwise (no inf check).
  let r = a / 0.0
  if r > 0.0: symexTarget("hit")

proc nanDivPos(a: float) =
  ## Only positive `a`: `a / 0.0` is `+inf`, never NaN, and nothing raises.
  if a > 0.0:
    let r = a / 0.0
    if r > 0.0: symexTarget("hit")
{.pop.}

{.push infChecks: on.}
proc infDiv(a: float) =
  let r = 1.0 / a
  if r == 0.5: symexTarget("hit")

proc infAdd(a: float) =
  let r = a + 1.0
  if r == 3.0: symexTarget("hit")

proc infNeg(a: float) =
  ## `-2 * 1e308` is `-inf`: `raiseFloatOverflow` raises FloatUnderflowDefect.
  if a < 0.0:
    let r = a * 1e308
    if r == -1e308: symexTarget("hit")
{.pop.}

{.push floatChecks: on.}
proc bothSelf(a: float) =
  ## `a / a` is NaN at 0 and at ±inf, 1 elsewhere: never infinite.
  let r = a / a
  if r == 1.0: symexTarget("hit")

proc bothZero(a: float) =
  ## `0 / 0` with both checks on: the NaN check runs first.
  if a == 0.0:
    discard a / a

proc bothNeg(a: float) =
  ## Unary minus is unchecked: `-NaN` and `-inf` run on.
  let r = -a
  if r != r or r == NegInf: symexTarget("hit")

proc bothCaught(a: float) =
  try:
    let r = 1.0 / a
    if r == 4.0: symexTarget("quarter")
  except FloatOverflowDefect:
    symexTarget("hit")
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
    skip()
  else:
    body

suite "PRC-07: float checks are walked as compiled":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 311

  test "nanChecks: 0/0 raises FloatInvalidOpDefect":
    decided:
      check native(nanDiv(0.0)) == "FloatInvalidOpDefect"
      let r = pinExact(nanDiv, nanK, target = tRaisedExn("FloatInvalidOpDefect"),
                       domain = floats)
      check r.status == sxRaised

  test "nanChecks only: 1/0 returns inf, no raise":
    decided:
      check native(nanDiv(1.0)) == "hit"
      let r = pinExact(nanDiv, nanK, domain = floats)
      check r.status == sxSat
      check native(nanDivPos(1.0)) == "hit"
      let o = pinExact(nanDivPos, nanK, target = tRaisedExn(), domain = floats)
      check o.status == sxUnsat

  test "infChecks: 1/0 raises FloatOverflowDefect":
    decided:
      check native(infDiv(0.0)) == "FloatOverflowDefect"
      let r = pinExact(infDiv, infK, target = tRaisedExn("FloatOverflowDefect"),
                       domain = floats)
      check r.status == sxRaised
      let h = pinExact(infDiv, infK, domain = floats)
      check h.status == sxSat

  test "infChecks: inf + 1 raises FloatOverflowDefect":
    decided:
      check native(infAdd(Inf)) == "FloatOverflowDefect"
      let r = pinExact(infAdd, infK, target = tRaisedExn("FloatOverflowDefect"),
                       domain = floats)
      check r.status == sxRaised

  test "infChecks: a -inf result raises FloatUnderflowDefect":
    decided:
      check native(infNeg(-2.0)) == "FloatUnderflowDefect"
      check native(infNeg(-1.0)) == "hit"
      let r = pinExact(infNeg, infK, target = tRaisedExn(), domain = floats)
      check r.status == sxRaised
      check r.raisedTypeId == "FloatUnderflowDefect"

  test "both on: NaN wins for 0/0, a/a never overflows":
    decided:
      check native(bothSelf(0.0)) == "FloatInvalidOpDefect"
      let n = pinExact(bothSelf, floatK,
                       target = tRaisedExn("FloatInvalidOpDefect"), domain = floats)
      check n.status == sxRaised
      check native(bothZero(0.0)) == "FloatInvalidOpDefect"
      let z = pinExact(bothZero, floatK, target = tRaisedExn(), domain = floats)
      check z.status == sxRaised
      check z.raisedTypeId == "FloatInvalidOpDefect"

  test "unary minus is unchecked":
    decided:
      check native(bothNeg(NaN)) == "hit"
      let r = pinExact(bothNeg, floatK, domain = floats)
      check r.status == sxSat
      let x = pinExact(bothNeg, floatK, target = tRaisedExn(), domain = floats)
      check x.status == sxUnsat

  test "a catching caller sees FloatOverflowDefect":
    decided:
      check native(bothCaught(0.0)) == "hit"
      let r = pinExact(bothCaught, floatK, domain = floats)
      check r.status == sxSat
      let q = pinExact(bothCaught, floatK, target = tLabel("quarter"),
                       domain = floats)
      check q.status == sxSat

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
