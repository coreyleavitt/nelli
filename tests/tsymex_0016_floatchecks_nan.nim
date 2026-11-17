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
