## Phase 16 R16-6 — ADR-0012 Slice 2: diagnostics channel (DefectFinding[T],
## RawDiagnostic, allRaiseFindings).
##
## Verifies that non-winning sxRaised entries collected during a symexFind walk
## are surfaced via `SymexResult.diagnostics`, and that `allRaiseFindings` unions
## the winning raise (when the result is sxRaised) with those diagnostics.

import std/unittest
import nelli/symex

proc satWithSiblingOverflow(n: int) =
  ## SUT: `n+1` always forks an overflow path (max_int overflows).
  ## The label gate `n == 5` is on the non-overflow surviving path.
  ## With target-aware shouldStop (Slice 1), the overflow path goes
  ## to diagnostics; the label hit n=5 wins as sxSat.
  let y = n + 1   ## overflow fork: n == high(int64) → sxRaised(OverflowDefect)
  if n == 5:
    symexTarget("hit")
  discard y

proc directOverflow(a, b: int) =
  ## SUT: `a * b` always forks an overflow path.
  ## Used to verify allRaiseFindings on a sxRaised winner.
  let c = a * b
  discard c

suite "symex Phase 16 R16-6 — diagnostics channel (ADR-0012 Slice 2)":

  test "R16-6-1: sxSat with sibling overflow → diagnostics populated":
    let r = symexFind(satWithSiblingOverflow, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 5
    check r.diagnostics.len >= 1
    check r.diagnostics[0].raisedTypeId == "OverflowDefect"
    check r.diagnostics[0].defectKind == dkOverflowDefect

  test "R16-6-2: allRaiseFindings on sxRaised winner unions winning + diagnostics":
    let r = symexFind(directOverflow, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    let all = allRaiseFindings(r)
    check all.len >= 1
    check all[0].raisedTypeId == "OverflowDefect"
