## RFC-0005 S8cu -- on the command line: range, bound and object checks off (`--rangeChecks:off` `--boundChecks:off` `--objChecks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

suite "S8cu: --rangeChecks:off --boundChecks:off --objChecks:off":

  test "each declines":
    check native(clRange(300)) == "hit"
    declines(clRange, feCheckOption)
    check native(clBound(3)) == "hit"
    declines(clBound, feCheckOption)
    check native(clObj(4)) == "hit"
    declines(clObj, feCheckOption)

  test "the rule is per routine: one that never meets the check declines too":
    check native(clField(4)) == "FieldDefect"
    declines(clField, feCheckOption)
    check native(clPure(7)) == "hit"
    declines(clPure, feCheckOption)

  test "a routine under `push checks: on` has them back (control)":
    check native(clAllOn(4)) == "FieldDefect"
    decides(clAllOn, sxRaised)
