## RFC-0016 W3-z P1 (wiring audit A1) -- the opaque-call scan reads the
## routine's own overflow check, not the deviation set.
##
## `scanOpaqueDefects` answers the whole-run gate with `ubSignedOverflow` for
## an overflow-capable magic in an opaque callee when the owner's
## `overflowChecks` are off. It used to read `RoutineChecks.checks` (the
## options that DEVIATE from the walker's model) as "on", which inverts the
## answer: a checks-off build said "checked", a pushed-on routine said
## "unchecked". This file builds with `--overflowChecks:off` (its `.nim.cfg`).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

proc oAdd(a: int64) {.symexOpaque.} =
  ## An inert opaque callee with a Nim body: it overflows for `a == high`.
  discard a + 1

{.push overflowChecks: on.}
proc oAddOn(a: int64) {.symexOpaque.} =
  discard a + 1
{.pop.}

proc sutOpaqueTail(x: int64) =
  if x == 5: symexTarget("hit")
  oAdd(x)

proc sutOpaquePushedOn(x: int64) =
  if x == 5: symexTarget("hit")
  oAddOn(x)

suite "W3-z P1: opaque scan, checks-off build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 312

  test "an opaque Nim body that may overflow: the sat is untrusted":
    let r = symexFind(sutOpaqueTail, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

  test "the same callee pushed overflowChecks:on is checked: no ubSignedOverflow":
    let r = symexFind(sutOpaquePushedOn, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds
