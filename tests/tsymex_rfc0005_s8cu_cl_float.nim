## RFC-0005 S8cu -- on the command line: float checks on (`--floatChecks:on`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets, options]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers
import nelli/smt/admission

const declKey = cellKey(faGeneric, "s8cu_cl_float")

# RFC-0016 PRC-07: a compound assignment runs system's generic `+=` family,
# which takes the build's float checks, whatever the routine pushes. Native
# (c and cpp, Nim 2.2.10, `--nanChecks:on --infChecks:on`): `x /= 0.0` at 0
# raises in a routine pushed `nanChecks: off`; its infix `x / 0.0` does not.
{.push nanChecks: off, infChecks: off.}
proc offCompound(a: float) =
  var x = a
  x /= 0.0
  if x != x: symexTarget("hit")

proc offInfix(a: float) =
  var x = a
  x = x / 0.0
  if x != x: symexTarget("hit")
{.pop.}

proc plainCompound(a: float) =
  var x = a
  x *= 10.0
  if x == 4.0: symexTarget("hit")

const floats = sampled([0.0, 1.0, -1.0, 0.4, 1e308, -1e308, Inf, NaN])

suite "S8cu: --floatChecks:on":

  test "float arithmetic is walked with the checks (RFC-0016 PRC-07)":
    check native(clFloat(1e308)) == "FloatOverflowDefect"
    if hostAdmission().isSome:
      skip()
    else:
      let r = pinExact(clFloat, declKey, target = tRaisedExn(),
                       domain = sampled([1e308, 0.0, 1.0, Inf, NaN]))
      check r.status == sxRaised
      check r.raisedTypeId == "FloatOverflowDefect"

  test "a compound assignment takes the build's checks (RFC-0016 PRC-07)":
    check native(offCompound(0.0)) == "FloatInvalidOpDefect"
    check native(offInfix(0.0)) == "hit"
    check native(plainCompound(1e308)) == "FloatOverflowDefect"
    check native(plainCompound(-1e308)) == "FloatUnderflowDefect"
    if hostAdmission().isSome:
      skip()
    else:
      let c = pinExact(offCompound, declKey, target = tRaisedExn(),
                       domain = floats)
      check c.status == sxRaised
      check c.raisedTypeId == "FloatInvalidOpDefect"
      let i = pinExact(offInfix, declKey, domain = floats)
      check i.status == sxSat
      let n = pinExact(offInfix, declKey, target = tRaisedExn(),
                       domain = floats)
      check n.status == sxUnsat
      let p = pinExact(plainCompound, declKey, target = tRaisedExn(),
                       domain = floats)
      check p.status == sxRaised
      let h = pinExact(plainCompound, declKey, domain = floats)
      check h.status == sxSat

  test "a routine with no float keeps its verdict (control)":
    check native(clField(4)) == "FieldDefect"
    decides(clField, sxRaised)
    check native(clPure(7)) == "hit"
    decides(clPure, sxSat)
