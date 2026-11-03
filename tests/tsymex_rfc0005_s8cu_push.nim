## RFC-0005 S8cu -- a routine compiled under a check pragma in its own file.
##
## The routine runs without the check; the walker modelled it and reported a raise
## that never happens. It now declines by name (`check_options.nim`). Each row runs
## the routine natively on this build, so a wrong expectation fails here too.
import std/[unittest, sets, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

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
    declines(fieldOff, feCheckOption)
    let d = symexFind(fieldOff, tFieldDefect())
    check d.status == sxUnknown

  test "a routine after the pop has the check back (control)":
    check native(fieldAfterPop(4)) == "FieldDefect"
    check symexFind(fieldAfterPop, tFieldDefect()).status == sxRaised

  test "overflowChecks, with the settings modelling them on":
    check native(overOff(high(int))) == "hit"
    declines(overOff, feOverflowCheckOption)

  test "overflowChecks, with the settings modelling the wrap, decide (S8w)":
    let r = symexFind(overOff, tLabel("hit"),
                      SymexSettings(arithChecks: {acDivByZero, acRange}))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check native(overOff(r.witness[0])) == "hit"

  test "rangeChecks":
    check native(rangeOff(300)) == "hit"
    declines(rangeOff, feCheckOption)

  test "rangeChecks with `acRange` out: the conversion's value is not modelled":
    let r = symexFind(rangeOff, tLabel("hit"),
                      SymexSettings(arithChecks: {acOverflow, acDivByZero}))
    checkpoint show(r.errors)
    check r.status == sxUnknown

  test "boundChecks":
    check native(boundOff(3)) == "hit"
    declines(boundOff, feCheckOption)

  test "objChecks":
    check native(objOff(1)) == "hit"
    declines(objOff, feCheckOption)

  test "checks":
    check native(umbrella(high(int))) == "hit"
    let r = symexFind(umbrella, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feCheckOption)
    check r.errors.named(feOverflowCheckOption)

  test "a raise the model catches is no `sxUnsat`":
    check native(caughtOff(high(int))) == "hit"
    declines(caughtOff, feOverflowCheckOption)
    check native(neverRaisesHere(high(int))) == "hit"
    declines(neverRaisesHere, feOverflowCheckOption)

  test "a decline is never trusted":
    let r = symexFind(caughtOff, tLabel("hit"))
    check not r.trusted

  test "the walker's floor":
    check parseInt(symexWalkerVersion) >= 260
