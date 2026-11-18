## RFC-0016 0.10.0 review, finding H2: the whole-run tail walk
## (`verifyTailDefinedKinds`) of a clean `sxSat` keeps `ubIndeterminateRead`.
##
## A `{.noinit.}` read past the label records a `feGlobalHavoc`
## (`dcFreshSymbol`) whose kind rides only the degrade token (`Degrade.ub`,
## then `Path.undefined`). The tail walk discarded the paths it walked,
## `noteUbAtFork` returned at once on it, and the error loop exempted the
## fresh-symbol record without a kind of its own: the read was a trusted
## `sxSat`, `rsNotNeeded`, with `witnessUndefined` empty, at a witness that
## natively reads uninitialised memory. Built with the default overflow
## checks, as the finding was: `a + 1` raises, it is not undefined.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

var sink: int

proc noinitTail(x: int) =
  ## The finding's trigger: the label first, then a read of `a` that is
  ## indeterminate whenever `x <= 5`.
  symexTarget("hit")
  var a {.noinit.}: int
  if x > 5: a = 1
  sink = a + 1

proc noinitTailForced(x: int) =
  ## The label only for `x == 0`, so every witness reads `a` unwritten.
  if x == 0: symexTarget("hit")
  var a {.noinit.}: int
  if x > 5: a = 1
  sink = a + 1

proc noinitTailBranch(x: int) =
  ## The indeterminate read feeds a branch.
  if x == 0: symexTarget("hit")
  var a {.noinit.}: int
  if x > 5: a = 1
  if a == 7: sink = 1

proc noinitTailWritten(x: int) =
  ## Control: every path past the label writes `a` before the read.
  if x == 0: symexTarget("hit")
  var a {.noinit.}: int
  a = x
  sink = a + 1

suite "CR2 H2: the tail walk keeps ubIndeterminateRead":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 355

  test "the finding's trigger: a witness that reads `a` unwritten is not trusted":
    let r = pinFind(noinitTail, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    # Natively `a` is written only when x > 5.
    let readsUnwritten = not (r.witness[0] > 5)
    if readsUnwritten:
      check not r.trusted
      check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds

  test "every witness reads `a` unwritten: ubIndeterminateRead, untrusted":
    let r = pinFind(noinitTailForced, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.witness[0] == 0
    check not r.trusted
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds

  test "the read feeds a branch: ubIndeterminateRead, untrusted":
    let r = pinFind(noinitTailBranch, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.witness[0] == 0
    check not r.trusted
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds

  test "control: a written `a` keeps the verdict trusted":
    let r = pinFind(noinitTailWritten, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.trusted
    check r.soundness.undefinedKinds == {}
