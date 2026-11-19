## RFC-0005 S8cu -- a routine compiled under a check pragma in its own file.
##
## The routine runs without the check; the walker modelled it and reported a raise
## that never happens. It now declines by name (`check_options.nim`). Each row runs
## the routine natively on this build, so a wrong expectation fails here too.
##
## RFC-0016 int6: a check of `rangeChecks`, `boundChecks`, `fieldChecks`,
## `objChecks` pushed off is now modelled (the routine is walked as a build
## with it off walks it), so those rows are judged against the native binary
## (`pinFind`) or as the build route's undefined access. int6-o: so is
## `overflowChecks` off in a checked build; the pushed region walks as an
## off build does, a signed overflow there is an `ubSignedOverflow` halt.
import std/[unittest, sets, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/definedness
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_push")

template writesExact(fn: untyped) =
  ## RFC-0016 int6-f: a wrong-branch write under a pushed-off `fieldChecks`
  ## is the off build's: a store into the union's bytes (c), the member it
  ## makes active (cpp). Exact, its witness run natively; no `FieldDefect`
  ## on any input of the domain.
  block:
    let r = pinExact(fn, declKey)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted
    let d = pinFind(fn, tFieldDefect())
    checkpoint show(d.errors)
    check d.status == sxUnsat
const idxKey = cellKey(axDefinedness, "index/unchecked")
const objKey = cellKey(axDefinedness, "conv/objDowncast")

type K = enum kA, kB, kC, kD
type P = object
  case k: K
  of kA, kB: x: int
  of kC: y: int
  else: discard
type Par = ref object of RootObj
  a: int
type Ch = ref object of Par
  b: int

# ---- the row each check got wrong -------------------------------------------

proc fieldOn(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")

{.push fieldChecks: off.}
proc fieldOff(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")
{.pop.}

proc fieldAfterPop(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")

{.push overflowChecks: off.}
proc overOff(v: int) =
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("hit")
{.pop.}

{.push rangeChecks: off.}
proc rangeOff(v: int) =
  if v == 300:
    let w = int8(v)
    if w == 44'i8: symexTarget("hit")
{.pop.}

{.push boundChecks: off.}
proc boundOff(v: int) =
  var a = [1, 2, 3]
  if v == 3:
    a[v - 1] = 9
    discard a[v]
    symexTarget("hit")
{.pop.}

{.push objChecks: off.}
proc objOff(v: int) =
  let p = Par(a: v)
  let c = Ch(p)
  if c.a == v: symexTarget("hit")
{.pop.}

{.push checks: off.}
proc umbrella(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  let w = v + 1
  if w == low(int): symexTarget("hit")
{.pop.}

# Where the model's raise ends the walk before the label: only the run's own channel
# keeps these from a false `sxUnsat`.
{.push overflowChecks: off.}
proc caughtOff(v: int) =
  if v == high(int):
    try:
      let w = v + 1
      if w < 0: symexTarget("hit")
    except OverflowDefect:
      discard

proc neverRaisesHere(v: int) =
  ## No wrap can reach the label in the model, and the run has no raise to report.
  if v == high(int):
    try:
      let w = v + 1
      if w == low(int): symexTarget("hit")
    except CatchableError, Defect:
      discard
{.pop.}

suite "S8cu: the push form":

  test "a checked routine keeps its raise (control)":
    check native(fieldOn(4)) == "FieldDefect"
    let r = symexFind(fieldOn, tFieldDefect())
    check r.status == sxRaised

  test "fieldChecks":
    check native(fieldOff(4)) == "hit"
    # The wrong-branch write is the off build's (int6-f).
    writesExact(fieldOff)

  test "a routine after the pop has the check back (control)":
    check native(fieldAfterPop(4)) == "FieldDefect"
    check symexFind(fieldAfterPop, tFieldDefect()).status == sxRaised

  test "overflowChecks, with the settings modelling them on":
    check native(overOff(high(int))) == "hit"
    pinDecline(overOff, declKey, ubSignedOverflow)

  test "rangeChecks":
    check native(rangeOff(300)) == "hit"
    let r = pinFind(rangeOff, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    let x = pinFind(rangeOff, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxUnsat

  test "boundChecks":
    check native(boundOff(3)) == "hit"
    # `a[3]` of a 3-array is a C access outside it, as in a
    # `--boundChecks:off` build (`tsymex_0016_boundoff`).
    pinDecline(boundOff, idxKey, ubArrayOutOfBounds, excluding = {feCheckOption})

  test "objChecks":
    check native(objOff(1)) == "hit"
    # `Ch(p)` of a `Par` is an invalid down-conversion, as in an
    # `--objChecks:off` build (`tsymex_0016_objoff`).
    pinDecline(objOff, objKey, ubInvalidObjConversion,
               excluding = {feCheckOption})

  test "checks":
    check native(umbrella(high(int))) == "hit"
    let r = symexFind(umbrella, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    # int6: the four are modelled off (the field write declines on its own
    # path); int6-o: so is the overflow push, whose `v + 1` at `high(int)`
    # is a signed-overflow halt, as in an off build.
    check not r.errors.named(feCheckOption)
    check not r.errors.named(feOverflowCheckOption)
    check r.errors.named(feUnsupportedOp)
    check r.errors.named(ubSignedOverflow)

  test "a raise the model catches is no `sxUnsat`":
    check native(caughtOff(high(int))) == "hit"
    pinDecline(caughtOff, declKey, ubSignedOverflow)
    check native(neverRaisesHere(high(int))) == "hit"
    pinDecline(neverRaisesHere, declKey, ubSignedOverflow)

  test "a decline is never trusted":
    let r = symexFind(caughtOff, tLabel("hit"))
    check not r.trusted

  test "the walker's floor":
    check parseInt(symexWalkerVersion) >= 260
