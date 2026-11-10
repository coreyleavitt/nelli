## RFC-0016 W3-z R2 (wiring finding U1) -- whole-run definedness for a
## replay-confirmed candidate.
##
## K10b checks the tail of a clean `sxSat` winner (`verifyTailDefined`). A
## label reached only on a path a fresh symbol taints (a global havoc, an
## opaque call's result) is a CANDIDATE: replay runs its witness and a
## confirming replay makes it a trusted `sxSat` (`settleCandidate`). Replay is
## no evidence for undefined behaviour (section 9), so the candidate's tail
## must be checked the same way, while its model pins are still live inside
## `runSymexImpl`. An undefined op after the label untrusts the confirmed
## verdict; a defined tail keeps it trusted.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

# The file builds with `--overflowChecks:off` (its `.nim.cfg`), as the K10b
# round does: a signed overflow is `ubSignedOverflow`.

const gateOff = block:
  var s = pinSettingsConst
  s.wholeRunDefinedness = false
  s

var freshGlobal = false
  ## A module-level `var` nothing writes: a fresh symbol at its read
  ## (`feGlobalHavoc`, `dcFreshSymbol`) that really holds false.

proc freshFalse(a: bool): bool {.inline.} = freshGlobal and (a or not a)

proc candTailOverflow(a: bool; x: int64): int64 =
  ## The label on a havoc-tainted path, then a signed overflow every input
  ## past the label takes.
  let o = freshFalse(a)
  if not o:
    if x > 100:
      symexTarget("hit")
  result = x + high(int64)

proc candTailDefined(a: bool; x: int64): int64 =
  ## The same shape with a tail the witness keeps defined.
  let o = freshFalse(a)
  if not o:
    if x == 7:
      symexTarget("hit")
  result = x + 1

proc candBranchOverflow(a: bool; x: int64): int64 =
  ## The tail branches on the fresh symbol itself: the pins do not decide
  ## it, so the candidate's tail walk forks both arms. Really `o` is false
  ## and the run overflows.
  let o = freshFalse(a)
  if not o:
    if x > 100:
      symexTarget("hit")
  if not o: result = x + high(int64)
  else: result = x

proc candBranchDefined(a: bool; x: int64): int64 =
  ## The same open branch in the tail, defined on both arms.
  let o = freshFalse(a)
  if not o:
    if x == 7:
      symexTarget("hit")
  if not o: result = x + 1
  else: result = x - 1

suite "W3-z R2: a replay-confirmed candidate's tail is checked":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 313

  test "(a) a havoc-tainted candidate, undefined tail: confirmed but untrusted":
    let r = symexFind(candTailOverflow, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check not r.trusted
    check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds
    check r.witness[1] > 100

  test "(b) a havoc-tainted candidate, defined tail: stays trusted":
    let r = symexFind(candTailDefined, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check r.witness[1] == 7

  test "(c) an open branch in the tail forks: the undefined arm is found":
    let r = symexFind(candBranchOverflow, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubSignedOverflow)}

  test "(d) an open branch in the tail, defined on both arms: stays trusted":
    let r = symexFind(candBranchDefined, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check r.witness[1] == 7

  test "(e) gate off: the confirmed candidate is trusted on its prefix":
    let r = symexFind(candTailOverflow, tLabel("hit"), gateOff)
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check r.trusted
    check r.soundness.undefinedKinds == {}
