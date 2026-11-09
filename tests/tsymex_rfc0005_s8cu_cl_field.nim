## RFC-0005 S8cu -- on the command line: fieldChecks off (`--fieldChecks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_cl_field")

suite "S8cu: --fieldChecks:off":

  test "the named check declines":
    check native(clField(4)) == "hit"
    ## RFC-0016 PRC-07: the build is walked as compiled, so a check that is off is a modelled
    ## unchecked operation (exact, or a halt of its own kind), not a feCheckOption decline.
    pinExact(clField, declKey)

  test "the rule is per routine: one that never meets the check declines too":
    check native(clOver(high(int))) == "OverflowDefect"
    decides(clOver, sxRaised)
    check native(clBound(3)) == "IndexDefect"
    decides(clBound, sxRaised)
    check native(clPure(7)) == "hit"
    pinExact(clPure, declKey)

  test "a routine under `push fieldChecks: on` has it back (control)":
    check native(clFieldOn(4)) == "FieldDefect"
    ## pushed back on in a build with the check off: the deviation declines
    pinDecline(clFieldOn, declKey, feCheckOption)

  test "a routine under `push checks: on` has it back (control)":
    check native(clAllOn(4)) == "FieldDefect"
    pinDecline(clAllOn, declKey, feCheckOption)
