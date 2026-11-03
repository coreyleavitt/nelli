## RFC-0005 S8cu -- on the command line: `--assertions:off`.
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_helpers

proc aPlain(v: int) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
proc daPlain(v: int) =
  if v == 4:
    doAssert v != 4
    symexTarget("hit")
{.push assertions: on.}
proc aOn(v: int) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
{.pop.}
{.push checks: on.}
proc aChecksOn(v: int) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
{.pop.}
proc mitemsGrow(v: int) =
  if v == 4:
    var s = @[1'i16, 2, 3]
    for x in s.mitems:
      if s.len == 3: s.add 9
    symexTarget("hit")

suite "S8cu: --assertions:off":

  test "assert is compiled out":
    check native(aPlain(4)) == "hit"
    decides(aPlain, sxSat)

  test "doAssert is not":
    check native(daPlain(4)) == "AssertionDefect"
    decides(daPlain, sxRaised)

  test "`push assertions: on` and `push checks: on` bring it back":
    check native(aOn(4)) == "AssertionDefect"
    decides(aOn, sxRaised)
    check native(aChecksOn(4)) == "AssertionDefect"
    decides(aChecksOn, sxRaised)

  test "an iterator's length check is gone, and the iteration on declines":
    check native(mitemsGrow(4)) == "hit"
    declines(mitemsGrow, feUnsupportedOp)
