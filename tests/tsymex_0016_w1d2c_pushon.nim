## RFC-0016 W1-d2c. This file builds with `--overflowChecks:off` (its
## `.nim.cfg`): the build's signed `+`, `-` and `*` are unchecked (undefined on
## overflow, W1-d2). A routine under `{.push overflowChecks: on.}` is checked
## natively: its signed overflow raises `OverflowDefect`. Checked-ness is per
## routine (`ArithScope`, stamped by `withCheckDeclines`, set per body block by
## the walker), so such a routine is modelled as a checked build models it, and
## a call across the boundary keeps each side's own arithmetic.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

{.push overflowChecks: on.}
proc checkedOver(v: int) =
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("hit")

proc checkedPlain(v: int) =
  if v + 1 == 8: symexTarget("hit")

proc checkedOverCallee(v: int): int =
  v + 1
{.pop.}

proc uncheckedOverCallee(v: int): int =
  v + 1

proc uncheckedCallsChecked(v: int) =
  ## Build arithmetic here, the callee's own checked arithmetic there.
  if v == high(int):
    let w = checkedOverCallee(v)
    if w < 0: symexTarget("hit")

{.push overflowChecks: on.}
proc checkedCallsUnchecked(v: int) =
  ## The callee's build arithmetic: its overflow is undefined, and a halt.
  if v == high(int):
    let w = uncheckedOverCallee(v)
    if w < 0: symexTarget("hit")

proc checkedAfterCall(v: int) =
  ## Its own checked arithmetic is back after the unchecked callee returns.
  discard uncheckedOverCallee(0)
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("hit")
{.pop.}

suite "W1-d2c push overflowChecks: on in a checks-off build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 283

  test "the build is checks-off":
    check buildWraps()

  test "native: the pushed-on routine raises, the plain one is not checked":
    check native(checkedOver(high(int))) == "OverflowDefect"
    check native(checkedPlain(7)) == "hit"
    check native(uncheckedCallsChecked(high(int))) == "OverflowDefect"
    check native(checkedAfterCall(high(int))) == "OverflowDefect"

  test "the overflow of a pushed-on routine is an exact sxRaised OverflowDefect":
    let r = pinExact(checkedOver, cellKey(axDefinedness, "add/signed/pushOnRaise"))
    check r.status == sxRaised
    check r.trusted
    check "OverflowDefect" in r.raisedTypeId
    check not r.errors.named(feOverflowCheckOption)

  test "a pushed-on routine that cannot overflow is decided and trusted":
    let r = pinExact(checkedPlain, cellKey(axDefinedness, "add/signed/pushOnPlain"))
    check r.status == sxSat
    check r.trusted

  test "an unchecked caller's call into a pushed-on callee raises":
    let r = pinExact(uncheckedCallsChecked,
                     cellKey(axDefinedness, "add/signed/pushOnCallee"))
    check r.status == sxRaised
    check r.trusted

  test "a pushed-on caller's call into an unchecked callee still halts":
    declines(checkedCallsUnchecked, ubSignedOverflow)

  test "a pushed-on caller is checked again after an unchecked callee returns":
    let r = pinExact(checkedAfterCall,
                     cellKey(axDefinedness, "add/signed/pushOnAfterCall"))
    check r.status == sxRaised
    check r.trusted
