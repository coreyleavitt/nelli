## RFC-0005 S8cu -- on the command line: fieldChecks off (`--fieldChecks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

suite "S8cu: --fieldChecks:off":

  test "the named check declines":
    check native(clField(4)) == "hit"
    declines(clField, feCheckOption)

  test "the rule is per routine: one that never meets the check declines too":
    check native(clOver(high(int))) == "OverflowDefect"
    declines(clOver, feCheckOption)
    check native(clBound(3)) == "IndexDefect"
    declines(clBound, feCheckOption)
    check native(clPure(7)) == "hit"
    declines(clPure, feCheckOption)

  test "a routine under `push fieldChecks: on` has it back (control)":
    check native(clFieldOn(4)) == "FieldDefect"
    decides(clFieldOn, sxRaised)

  test "a routine under `push checks: on` has it back (control)":
    check native(clAllOn(4)) == "FieldDefect"
    decides(clAllOn, sxRaised)
