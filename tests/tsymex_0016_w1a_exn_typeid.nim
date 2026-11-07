## RFC-0016 W1-a -- one exception type id for raise sites and handlers
## (W-01, W-33), checked against the native run.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutAsE(k: int) =
  try:
    if k == 3: raise newException(ValueError, "x")
  except ValueError as e:
    symexTarget("h")

proc sutAsEOnly(k: int) =
  try:
    if k == 3: raise newException(ValueError, "x")
  except ValueError as e:
    discard

proc sutPlain(k: int) =
  try:
    if k == 3: raise newException(ValueError, "x")
  except ValueError:
    symexTarget("h")

proc sutRaiseLet(k: int) =
  if k == 3:
    let e = newException(ValueError, "x")
    raise e

proc sutRaiseParam(ex: ref Exception) =
  raise ex

const dom3 = sampled([-1, 0, 1, 2, 3, 4, 7])

suite "W1-a exception type id":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 273

  test "except T as e: the handler label is reachable":
    let r = pinExact(sutAsE, cellKey(axConstruct, "except-as-label"),
                     target = tLabel("h"), domain = dom3)
    check r.status == sxSat

  test "except T as e: the raise is caught, not escaping":
    let r = pinExact(sutAsEOnly, cellKey(axConstruct, "except-as-raise"),
                     target = tRaisedExn("ValueError"), domain = dom3)
    check r.status == sxUnsat

  test "except T (no binding) agrees":
    let r = pinExact(sutPlain, cellKey(axConstruct, "except-plain-label"),
                     target = tLabel("h"), domain = dom3)
    check r.status == sxSat

  test "raise of a let-bound exception has its static type":
    let r = pinExact(sutRaiseLet, cellKey(axConstruct, "raise-let-value"),
                     target = tRaisedExn("ValueError"), domain = dom3)
    check r.status == sxRaised

  test "raise of a ref Exception parameter declines":
    pinDecline(sutRaiseParam, cellKey(axConstruct, "raise-ref-exception"),
               eeUnknownExnType, target = tRaisedExn("ValueError"))
