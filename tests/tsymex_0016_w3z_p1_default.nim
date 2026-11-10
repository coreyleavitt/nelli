## RFC-0016 W3-z P1 (wiring audit A1) -- the default build.
##
## With `overflowChecks` on (the default) an opaque callee's signed `+` raises
## `OverflowDefect`; it is not undefined. The opaque scan must not say
## `ubSignedOverflow`. A routine that pushes a check off inside a checks-on
## build is the other direction (`ownerChecked`): its index is unchecked.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers
import nelli/smt/definedness

proc oAdd(a: int64) {.symexOpaque.} =
  discard a + 1

proc sutOpaqueTail(x: int64) =
  if x == 5: symexTarget("hit")
  oAdd(x)

{.push overflowChecks: off.}
proc oAddOff(a: int64) {.symexOpaque.} =
  discard a + 1
{.pop.}

proc sutOpaquePushedOff(x: int64) =
  if x == 5: symexTarget("hit")
  oAddOff(x)

proc oIdx(i: int) {.symexOpaque.} =
  var a: array[4, int]
  discard a[i]

proc sutIdxChecked(x: int) =
  if x == 5: symexTarget("hit")
  oIdx(x)

{.push boundChecks: off.}
proc oIdxOff(i: int) {.symexOpaque.} =
  var a: array[4, int]
  discard a[i]
{.pop.}

proc sutIdxPushedOff(x: int) =
  if x == 5: symexTarget("hit")
  oIdxOff(x)

suite "W3-z P1: opaque scan, default build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 312

  test "a checked opaque overflow is not undefined: no ubSignedOverflow":
    let r = symexFind(sutOpaqueTail, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds

  test "a routine pushed overflowChecks:off is unchecked: ubSignedOverflow":
    let r = symexFind(sutOpaquePushedOff, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

  test "a checked opaque index is an IndexDefect, not undefined":
    let r = symexFind(sutIdxChecked, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check uncheckedIndexUb() notin r.soundness.undefinedKinds

  test "a routine pushed boundChecks:off has an unchecked index (ownerChecked)":
    let r = symexFind(sutIdxPushedOff, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check uncheckedIndexUb() in r.soundness.undefinedKinds
