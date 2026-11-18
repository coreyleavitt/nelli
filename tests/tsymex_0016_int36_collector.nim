## RFC-0016 INT-36 (0005 review R3-17): a finding filed mid-statement is
## stamped with the statement's stray taint.
##
## A statement whose lowering left taint queued with no owner (a raw `lower`
## with no drain of its own; `claimStrayPendingTaint` finds it at the next
## lowering's entry) puts that taint on every path it produced: the ones it
## returns and the ones it parked on an exit channel (R1-04, R2 SD2). A hit
## the statement filed before its end (a target label in a body it walked, a
## raise routed to the SUT boundary) was solved and filed from a path that
## did not yet carry it, and the end-of-statement stamp did not reach it: a
## clean `sxSat` winner from a path the statement says is not modelled. Now
## the stamp reaches the findings filed since the statement began too, and
## one the stray makes `scSpurious` is a candidate, as `admitSolvedHit`
## would have filed it.
##
## As with `stmtExitTaintProbe` (`tsymex_rfc0005_r2_walktaint`), no source
## shape is known to leave stray taint (each producer drains or sets the
## calling expression's queue aside), so the probe drives the statement
## stamp itself, the one the walk runs at a statement's end.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
from nelli/smt/admission import cellKey, axConstruct
import ./s8cu_helpers

suite "INT-36 R3-17: a finding filed mid-statement carries the stray taint":

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 413

  test "a clean hit filed before the stray is found is a candidate":
    let probe = strayFindingProbe()
    check probe.foundBefore == 2          # one before the statement, one in it
    check probe.foundAfterExitsOnly == 2  # before INT-36: still a winner
    check probe.foundAfter == 1
    check probe.earlierFoundKept          # filed before the statement began
    check probe.candidatesAfter == 2      # the statement's candidate, then it
    check probe.movedTaint == {scSpurious, scIncomplete}
    check probe.stmtCandidateTaint == {scSpurious, scIncomplete}
    pinNever(cellKey(axConstruct, "walk/stmt/stray-findings"),
      probe.foundAfter == 1 and scSpurious in probe.movedTaint,
      "a statement's stray taint reaches the findings it filed, not only " &
      "the paths it produced")
