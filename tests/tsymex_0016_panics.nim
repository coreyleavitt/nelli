## RFC-0016 W1-c2 -- under `--panics:on` a Defect is not catchable (W-03,
## INT-27). It prints its report and ends the process: no `except` arm (named,
## bare, `Defect` or the concrete subtype) and no `finally` sees it. The walker
## routes it down the S8cu crash channel (`crashRaise`).
##
## This is the suite's first panics row (`.nim.cfg` carries `--panics:on`).
## Only `symexFind` and the K9a pins are used: the native witness of a Defect
## claim ends the process, so nothing here runs one in the host.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutCatchDefect(v: int) =
  try:
    discard v + 1
  except Defect:
    symexTarget("h")

proc sutCatchSubtype(v: int) =
  try:
    discard v + 1
  except OverflowDefect:
    symexTarget("h")

proc sutCatchBare(v: int) =
  try:
    discard v + 1
  except:
    symexTarget("h")

proc sutFinally(v: int) =
  try:
    discard v + 1
  finally:
    if v == high(int): symexTarget("f")   # only the overflowing input

proc sutEscape(v: int) =
  discard v + 1

proc sutRaiseParamUnderTry(ex: ref Exception) =
  try:
    raise ex
  except ValueError:
    discard

const overflowProbe = """
import std/os
proc f(v: int) =
  try:
    discard v + 1
  except Defect:
    echo "CAUGHT"
  finally:
    echo "FINALLY"
f(high(int) - paramCount())
"""

template mustCrashNotReach(res: untyped) =
  ## The label is not reached (never `sxSat`); the overflow instead leaves the
  ## SUT as a Defect finding (E6 surfaces every Defect), a crash claim whose
  ## witness no consumer runs in the host.
  let r = res
  check r.status == sxRaised
  check r.raisedTypeId == "OverflowDefect"
  check r.soundness.witnessUnsafe

suite "W1-c2: a Defect under --panics:on crashes":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 274

  test "the build is a panics build":
    check defined(nimPanics)

  test "except Defect does not catch the overflow":
    mustCrashNotReach(symexFind(sutCatchDefect, tLabel("h")))

  test "except OverflowDefect does not catch it":
    mustCrashNotReach(symexFind(sutCatchSubtype, tLabel("h")))

  test "a bare except does not catch it":
    mustCrashNotReach(symexFind(sutCatchBare, tLabel("h")))

  test "a finally does not run":
    mustCrashNotReach(symexFind(sutFinally, tLabel("f")))

  test "the overflow escapes the try: a crash claim, never host-run":
    # The handler does not catch it, so it leaves the SUT: S8cu's crash
    # outcome (as tNilAccess reports one), whose witness ends any process.
    let r = symexFind(sutCatchDefect, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check r.soundness.witnessUnsafe
    check not hostRunnable(r.soundness)

  test "a Defect claim's witness is not host-runnable":
    let r = symexFind(sutEscape, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check r.soundness.witnessUnsafe

  test "native: the overflow ends the process, no arm or finally runs":
    pinCrash(cellKey(axConstruct, "panic-overflow-defect"), overflowProbe,
             [], ceDefect)

  test "raise of an unknown-typed ref Exception under a try declines":
    pinDecline(sutRaiseParamUnderTry, cellKey(axConstruct, "panic-raise-unknown"),
               eeUnknownExnType, target = tRaisedExn("ValueError"))
