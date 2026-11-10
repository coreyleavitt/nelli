## RFC-0005 S8cu -- on the command line: range, bound and object checks off (`--rangeChecks:off` `--boundChecks:off` `--objChecks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_cl_rbo")

suite "S8cu: --rangeChecks:off --boundChecks:off --objChecks:off":

  test "each declines":
    check native(clRange(300)) == "hit"
    ## RFC-0016 PRC-07: the build is walked as compiled; an off check is exact or a halt of its own kind.
    discard pinExact(clRange, declKey)
    check native(clBound(3)) == "hit"
    pinDecline(clBound, declKey, ubArrayOutOfBounds)
    check native(clObj(4)) == "hit"
    pinDecline(clObj, declKey, ubInvalidObjConversion)

  test "the rule is per routine: one that never meets the check declines too":
    check native(clField(4)) == "FieldDefect"
    decides(clField, sxRaised)
    check native(clPure(7)) == "hit"
    discard pinExact(clPure, declKey)

  test "a routine under `push checks: on` has them back (control)":
    check native(clAllOn(4)) == "FieldDefect"
    decides(clAllOn, sxRaised)
