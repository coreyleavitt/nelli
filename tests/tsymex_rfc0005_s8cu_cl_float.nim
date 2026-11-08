## RFC-0005 S8cu -- on the command line: float checks on (`--floatChecks:on`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_cl_float")

suite "S8cu: --floatChecks:on":

  test "float arithmetic declines":
    check native(clFloat(1e308)) == "FloatOverflowDefect"
    pinDecline(clFloat, declKey, feCheckOption)

  test "a routine with no float keeps its verdict (control)":
    check native(clField(4)) == "FieldDefect"
    decides(clField, sxRaised)
    check native(clPure(7)) == "hit"
    decides(clPure, sxSat)
