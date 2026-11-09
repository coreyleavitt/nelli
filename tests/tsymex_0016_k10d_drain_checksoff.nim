## RFC-0016 K10d follow-up: a drain for a check the build lacks returns the
## path. Built with `--overflowChecks:off` (its `.nim.cfg`): the build does not
## compile in the overflow check, so `arithChecksFor()` has no `acOverflow` and
## the overflow drain must leave the path as it found it. No `OverflowDefect`
## fork exists to reach: a search for the raise is a clean `sxUnsat`, and the
## surviving continuation is the ordinary one.
##
## The operand is `int8` so the addition is a defined wrap (below `int`'s
## width, `(NI8)(a + b)`) and the definedness axis has no `ubSignedOverflow`
## halt to confuse with a Defect fork: what is pinned is the drain, not the
## axis.
import std/unittest
import nelli/symex
import nelli/smt/types
import ./s8cu_helpers

proc sutAddInt8(x: int8) =
  let y = x + 1
  if y < x: symexTarget("wrapped")

proc sutAddHandler(x: int8) =
  try:
    let y = x + 1
    if y == 0: symexTarget("zero")
  except OverflowDefect:
    symexTarget("overflow-handler")

suite "K10d: a drain for a check the build lacks returns the path (checks off)":
  test "the build has no overflow check":
    check acOverflow notin arithChecksFor()

  test "no OverflowDefect is reachable: a clean unsat, no Defect fork":
    let r = symexFind(sutAddInt8, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.errors.len == 0

  test "a handler for the unforked raise is unreachable":
    let r = symexFind(sutAddHandler, tLabel("overflow-handler"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check not r.errors.named(ubSignedOverflow)

  test "the path continues unchanged: the wrap is the exact witness":
    let r = symexFind(sutAddInt8, tLabel("wrapped"))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 127'i8

proc sutAddWide(a: int) =
  let y = a + 1
  if y == 0: symexTarget("zero")

suite "K10d: the wide overflow is the axis's halt, never a Defect fork (checks off)":
  test "a search for OverflowDefect does not find one":
    let r = symexFind(sutAddWide, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status != sxRaised
    check r.status == sxUnknown
    check r.errors.named(ubSignedOverflow)

  test "the continuation is the ordinary one, tainted by the halt only":
    let r = symexFind(sutAddWide, tLabel("zero"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == -1
