## RFC-0016 WA-B S4 under `--panics:on` (`.nim.cfg`). A Defect is not
## catchable there, so it is a crash claim whose witness ends the process.
## When that witness renders lossily the replay is out of scope
## (`replayNotRun`, `endsChild` false) and used to overwrite the claim's own
## `witnessUnsafe`: `hostRunnable` was true and `assertCoveredBy` ran it in the
## host, which killed the process.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types

type
  WpDist = object
    x: int
    ys: seq[(int, int)]   # no heap cell holds this: the witness is lossy
  WpBox = object
    n: int
    s: WpDist

proc lossyOverflow(p: ref WpBox) =
  if p != nil and p.n == high(int):
    discard p.n + 1

suite "WA-B S4: a lossy Defect claim under --panics:on":
  test "the build is a panics build":
    check defined(nimPanics)
    check parseInt(symexWalkerVersion) >= 286

  test "the verdict is unsafe and not host-runnable":
    let r = symexFind(lossyOverflow, tRaisedExn("OverflowDefect"))
    checkpoint $r.status & " " & $r.soundness
    check r.status == sxRaised
    check r.soundness.witnessUnsafe
    check not hostRunnable(r.soundness)

proc lossyAssert(p: ref WpBox) =
  ## An auto-discovered `AssertionDefect` target (`symexFindAllWitnesses`),
  ## with a witness no heap cell holds.
  if p != nil and p.n == 5:
    assert p.n != 5

var wpFreshGlobal = false
proc wpFreshFalse(a: bool): bool {.inline.} = wpFreshGlobal and (a or not a)

proc candidateOverflow(a: bool; x: int) =
  ## `wpFreshFalse` is a fresh symbol to the walker, so the overflow below is
  ## a crash claim on an `scSpurious` path: a candidate, settled by replay.
  let o = wpFreshFalse(a)
  if not o and x == high(int):
    discard x + 1

suite "WA-B S4: the cached crash claim":
  test "a cold and a warm finding both stay witnessUnsafe":
    let db = inMemoryDatabase()
    let cold = symexFindAllWitnesses(lossyAssert, db)
    check cold.len == 1
    checkpoint $cold[0].status & " " & $cold[0].soundness
    check cold[0].status == sfRaised
    check not cold[0].fromCache
    check cold[0].soundness.witnessUnsafe
    check not hostRunnable(cold[0].soundness)
    let warm = symexFindAllWitnesses(lossyAssert, db)
    check warm.len == 1
    check warm[0].status == sfRaised
    check warm[0].fromCache
    check warm[0].soundness.witnessUnsafe
    check not hostRunnable(warm[0].soundness)

suite "WA-B S4: a crash candidate is never settled into a claim":
  ## `settleCandidate` ORs the claim's own `witnessUnsafe` into the replay's
  ## `endsChild`, but only after a CONFIRMING replay, and no crash claim can
  ## be confirmed: `replayInScope` is false for every target under
  ## `--panics:on` (the only build where a Defect is a crash claim), and for
  ## `NilAccessDefect` anywhere. So a crash claim on a replay-eligible
  ## (`scSpurious`) path stays `sxUnknown`: it is never reported, and its
  ## flag has nothing to clear. This pins that. If a change makes such a
  ## candidate replayable, this fails, and that change has to carry the
  ## claim's `witnessUnsafe` through `settleCandidate` (a confirmed crash
  ## claim would otherwise be `hostRunnable`).
  test "an scSpurious crash claim is declined, not settled":
    check defined(nimPanics)
    let r = symexFind(candidateOverflow, tRaisedExn("OverflowDefect"))
    checkpoint $r.status & " " & $r.soundness
    check r.status == sxUnknown
    check scSpurious in r.soundness.runTaint
    check r.soundness.replay == rsNotNeeded
