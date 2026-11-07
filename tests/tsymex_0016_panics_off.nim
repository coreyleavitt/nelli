## RFC-0016 W1-c2 -- the panics-off twin of `tsymex_0016_panics`: on the
## default build a Defect IS catchable, so `except Defect` still catches the
## overflow and the handler label is reachable, checked against the native run.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutCatchDefect(v: int) =
  try:
    discard v + 1
  except Defect:
    symexTarget("h")

proc sutFinally(v: int) =
  try:
    discard v + 1
  except Defect:
    discard
  finally:
    symexTarget("f")

suite "W1-c2: a Defect is caught on a panics-off build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 274

  test "the build is not a panics build":
    check not defined(nimPanics)

  test "except Defect catches the overflow":
    let r = pinExact(sutCatchDefect, cellKey(axConstruct, "nopanic-catch-defect"),
                     target = tLabel("h"))
    check r.status == sxSat

  test "the finally runs after the caught Defect":
    let r = pinExact(sutFinally, cellKey(axConstruct, "nopanic-finally-defect"),
                     target = tLabel("f"))
    check r.status == sxSat

  test "the caught overflow is not an escaping raise":
    let r = pinExact(sutCatchDefect, cellKey(axConstruct, "nopanic-defect-not-escaping"),
                     target = tRaisedExn("OverflowDefect"))
    check r.status == sxUnsat
