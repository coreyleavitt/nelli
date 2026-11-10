## RFC-0005 S8cu -- on the command line: `-d:danger` (`-d:danger` `--opt:none`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_cl_danger")

suite "S8cu: -d:danger --opt:none":

  test "every check declines":
    check native(clField(4)) == "hit"
    ## RFC-0016 PRC-07: the build is walked as compiled, so a check that is off is a modelled
    ## unchecked operation (exact, or a halt of its own kind), not a feCheckOption decline.
    discard pinExact(clField, declKey)
    check native(clOver(high(int))) == "hit"
    ## RFC-0016 W1-d2 (rule a): the build has signed overflow checks off, so
    ## the overflow is an `ubSignedOverflow` halt (not `feOverflowCheckOption`);
    ## `feCheckOption` stays, from the field/range/bound/obj checks this
    ## routine is also compiled without.
    pinDecline(clOver, declKey, ubSignedOverflow)
    check native(clRange(300)) == "hit"
    discard pinExact(clRange, declKey)
    check native(clBound(3)) == "hit"
    pinDecline(clBound, declKey, ubArrayOutOfBounds)
    check native(clObj(4)) == "hit"
    pinDecline(clObj, declKey, ubInvalidObjConversion)
    check native(clPure(7)) == "hit"
    discard pinExact(clPure, declKey)

  test "turning one back on leaves the rest off":
    check native(clOverOn(high(int))) == "OverflowDefect"
    decides(clOverOn, sxRaised)

  test "`push checks: on` turns them all back on (control)":
    check native(clAllOn(4)) == "FieldDefect"
    ## RFC-0016 PRC-07: walked under its own, checked options (per routine).
    decides(clAllOn, sxRaised)
