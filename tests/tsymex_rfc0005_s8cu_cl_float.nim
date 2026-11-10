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

  test "a routine with no float keeps its verdict (control)":
    check native(clField(4)) == "FieldDefect"
    decides(clField, sxRaised)
    check native(clPure(7)) == "hit"
    decides(clPure, sxSat)
