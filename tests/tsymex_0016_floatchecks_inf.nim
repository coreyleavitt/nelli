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
