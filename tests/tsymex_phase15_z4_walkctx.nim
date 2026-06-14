import std/unittest
import proptest/symex

# Phase 15 — Z4: WalkCtx.found Option[RawResult] -> seq[RawResult]
# (see docs/symex/RFC-phase15-reconciliation.md §F / Cluster Z, ADR-0007).
#
# WalkCtx is private, so the field-type change is verified behaviorally: the
# found-as-seq path (add / [0] / shouldStop / empty-init) must preserve verdicts.
# WalkerStatics/CallFrameCtx are empty records introduced here (populated by E/C/R);
# their existence is verified by the engine compiling.

proc z4sat(x: int) =
  if x == 123: symexTarget("hit")

proc z4unsat(x: int) =
  if x == 1 and x == 2: symexTarget("never")   # contradiction -> unreachable

proc z4branchy(x: int) =
  # two branches; only the second reaches the target — exercises path
  # accumulation into `found` before shouldStop fires.
  if x < 0: discard
  elif x == 77: symexTarget("deep")

suite "symex Phase 15 — Z4 found:seq migration (behavioral)":

  test "sat path: found accumulates an sxSat finding":
    let r = symexFind(z4sat, tLabel("hit"))
    check r.status == sxSat

  test "unreachable target: empty found -> sxUnsat":
    let r = symexFind(z4unsat, tLabel("never"))
    check r.status == sxUnsat

  test "branchy SUT: target on a later branch still found":
    let r = symexFind(z4branchy, tLabel("deep"))
    check r.status == sxSat
