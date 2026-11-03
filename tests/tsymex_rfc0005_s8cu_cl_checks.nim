## RFC-0005 S8cu -- on the command line: the umbrella off (`--checks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

suite "S8cu: --checks:off":

  test "every check declines":
    check native(clField(4)) == "hit"
    declines(clField, feCheckOption)
    check native(clOver(high(int))) == "hit"
    declines(clOver, feOverflowCheckOption)
    check native(clRange(300)) == "hit"
    declines(clRange, feCheckOption)
    check native(clBound(3)) == "hit"
    declines(clBound, feCheckOption)
    check native(clObj(4)) == "hit"
    declines(clObj, feCheckOption)
    check native(clPure(7)) == "hit"
    declines(clPure, feCheckOption)

  test "turning one back on leaves the rest off":
    check native(clFieldOn(4)) == "FieldDefect"
    declines(clFieldOn, feCheckOption)

  test "`push checks: on` turns them all back on (control)":
    check native(clAllOn(4)) == "FieldDefect"
    decides(clAllOn, sxRaised)
