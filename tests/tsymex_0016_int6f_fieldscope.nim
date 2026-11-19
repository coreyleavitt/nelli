## RFC-0016 int6-f: `fieldChecks` belongs to the code region it was compiled
## under. This file builds with Nim's default checks (field checks on), on the
## c backend and on cpp; the routines under `{.push fieldChecks: off.}` are
## compiled without the check, the rest with it.
##
## Native, on the pinned toolchain (each judged against the native binary by
## `pinFind`; a C++-undefined access by `pinDecline` on its UB kind):
##   * under the push, `x.b` of a `ka` object is a plain union member access:
##     on c it reads the bytes of the active `a` (C11 6.5.2.3 note 95), so
##     `x.b == v`; on cpp reading a member that is not the active one is
##     undefined (`ubInactiveVariantField`, row `field/inactiveBranch`);
##   * a write `x.b = 5` under the push stores into the union: on c `a` reads
##     the same bytes back; on cpp `b` becomes the active member, so `x.b`
##     reads 5 and `x.a` is an inactive read (undefined);
##   * a checked caller of an unchecked callee that wrote `b` raises
##     `FieldDefect` on its own `x.b`: the check reads the discriminator
##     (still `ka`), never the member last written; its `x.a` after the call
##     reads the written bytes (c) or is an inactive read (cpp);
##   * a routine declared under the push keeps it when called from a checked
##     caller: its `x.b` raises nothing;
##   * a nested `push fieldChecks: on` raises `FieldDefect`, and after its
##     `pop` the outer push is back.
## The variant's memory is the same C struct in both regions, so the walker
## carries the off build's union image (c) and active member (cpp) for the
## whole program once any region in it accesses a field unchecked.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/definedness
import ./s8cu_helpers

type
  K = enum ka, kb
  V = object
    case k: K
    of ka: a: int
    of kb: b: int
  RV = ref object
    case k: K
    of ka: a: int
    of kb: b: int

const uk = cellKey(axDefinedness, "field/inactiveBranch")

proc checkedRead(v: int) =
  let x = V(k: ka, a: v)
  if x.b == 3: symexTarget("hit")

{.push fieldChecks: off.}
proc offRead(v: int) =
  let x = V(k: ka, a: v)
  if x.b == 3: symexTarget("hit")

proc offWrite(v: int) =
  var x = V(k: ka, a: v)
  x.b = 5
  if x.b == 5 and v == 3: symexTarget("hit")

proc offWriteReadOwn(v: int) =
  var x = V(k: ka, a: v)
  x.b = v
  if x.a == 3: symexTarget("hit")

proc offRefRead(v: int) =
  let x = RV(k: ka, a: v)
  if x.b == 3: symexTarget("hit")

proc offRefWrite(v: int) =
  let x = RV(k: ka, a: v)
  x.b = 5
  if x.b == 5 and v == 3: symexTarget("hit")

proc setB(x: var V; n: int) = x.b = n

proc getB(x: V): int = x.b

{.push fieldChecks: on.}
proc nestedOn(v: int) =
  let x = V(k: ka, a: v)
  if x.b == 3: symexTarget("hit")
{.pop.}

proc afterNested(v: int) =
  let x = V(k: ka, a: v)
  if x.b == 3: symexTarget("hit")
{.pop.}

proc callerAfter(v: int) =
  var x = V(k: ka, a: 1)
  setB(x, v)
  if x.b == 3: symexTarget("hit")

proc callerReadsOwn(v: int) =
  var x = V(k: ka, a: 1)
  setB(x, v)
  if x.a == 3: symexTarget("hit")

proc callsGetB(v: int) =
  let x = V(k: ka, a: v)
  if getB(x) == 3: symexTarget("hit")

template exactHit(fn: untyped) =
  ## c: the read is the active arm's bytes, exact; no `FieldDefect`.
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  check r.trusted
  check not r.errors.named(feUnsupportedOp)
  let d = pinFind(fn, tFieldDefect())
  checkpoint show(d.errors)
  check d.status == sxUnsat

template inactiveRead(fn: untyped) =
  ## cpp: the read is of a member that is not the active one.
  pinDecline(fn, uk, ubInactiveVariantField,
             excluding = {feCheckOption, feUnsupportedOp})
  let d = pinFind(fn, tFieldDefect())
  checkpoint show(d.errors)
  check d.status != sxRaised

template unchecked(fn: untyped) =
  when defined(cpp): inactiveRead(fn)
  else: exactHit(fn)

template raisesField(fn: untyped) =
  let d = pinFind(fn, tFieldDefect())
  checkpoint show(d.errors)
  check d.status == sxRaised
  # every path raises before the label: the label search reports the raise
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status in {sxUnsat, sxRaised}

suite "int6-f field check scopes: natively":
  test "the build checks fields":
    check coField in buildSemantics.checks
  test "the native runs this file pins":
    check native(checkedRead(3)) == "FieldDefect"
    check native(offRead(3)) == "hit"
    check native(offWrite(3)) == "hit"
    check native(offWriteReadOwn(3)) == "hit"
    check native(offRefRead(3)) == "hit"
    check native(offRefWrite(3)) == "hit"
    check native(nestedOn(3)) == "FieldDefect"
    check native(afterNested(3)) == "hit"
    check native(callerAfter(3)) == "FieldDefect"
    check native(callerReadsOwn(3)) == "hit"
    check native(callsGetB(3)) == "hit"

suite "int6-f field check scopes: a pushed-off region in a checked build":
  test "a checked routine raises (control)":
    raisesField(checkedRead)
  test "a wrong-branch read under the push":
    unchecked(offRead)
    unchecked(offRefRead)
  test "a wrong-branch write under the push":
    # defined on both backends: c stores the union's bytes, cpp makes `b`
    # the active member, so reading `b` back is exact
    exactHit(offWrite)
    exactHit(offRefWrite)
    unchecked(offWriteReadOwn)
  test "a checked caller after the call raises on its own access":
    raisesField(callerAfter)
    unchecked(callerReadsOwn)
  test "a callee declared under the push keeps it":
    unchecked(callsGetB)
  test "a nested push on raises, and its pop restores the push off":
    raisesField(nestedOn)
    unchecked(afterNested)

suite "int6-f field check scopes: walker version":
  test "walker version floor >= 469":
    check parseInt(symexWalkerVersion) >= 469
