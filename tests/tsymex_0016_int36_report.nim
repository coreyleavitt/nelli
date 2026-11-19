## RFC-0016 INT-36 (0005 review R5-07, R4-09): the finding collector's edges
## on the report.
##
## R5-07. `recordSymexFinding` outside any engine frame (a thread the property
## started, a test body) records nothing and counts the drop. The count was
## per thread, so a worker thread's drops were invisible to the run that
## started it, and nothing read it but tests. It is now one count for the
## process; a run's `Report.droppedSymexFindings` is how far it moved during
## the run, and every renderer shows it when it is non-zero.
##
## R4-09. A nested run's findings reach the frame it was opened in (review R3
## E3). A nested run that re-finds the enclosing run's finding under another
## key (its own call site) must not make the enclosing report show the one
## claim twice: the merge keeps one entry per finding, the strongest
## (`claimRank`, after `severity`).
import std/[unittest, strutils, json, tables, sequtils]
import nelli
import nelli/symex
import nelli/engine/frame
import ./s8cu_helpers
from nelli/smt/admission import cellKey, axConstruct

proc i36Alpha(x: int) =
  if x == 42: symexTarget("alpha")

proc dropOne() {.thread.} =
  recordSymexFinding(FindingOrigin(site: "i36.nim(1, 1)", fnId: "i36"),
                     SymexFinding(targetDesc: "label(\"t\")", status: sfSat))

suite "INT-36 R5-07: a drop on a worker thread reaches the report":

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 413

  test "the count is the process's, and the run's change rides its report":
    let before = droppedSymexFindings()
    let rep = forAll(integers(0, 3), proc (x: int) =
      var th: Thread[void]
      createThread(th, dropOne)
      joinThread(th),
      Settings(maxExamples: 2))
    checkpoint $rep.outcome
    check droppedSymexFindings() == before + 2
    check rep.droppedSymexFindings == 2
    let text = renderReport(rep, ofText)
    check "2 symex findings were dropped" in text
    let j = parseJson(renderReport(rep, ofJson))
    check j.hasKey("droppedSymexFindings")
    if j.hasKey("droppedSymexFindings"):
      check j["droppedSymexFindings"].getInt == 2
    check "2 symex findings were dropped" in renderReport(rep, ofJunit)
    check "symex findings dropped" in renderReport(rep, ofGithubAnnotation)
    pinNever(cellKey(axConstruct, "report/findings/dropped"),
      rep.droppedSymexFindings == 2 and "dropped" in text,
      "a finding recorded outside any engine frame, on any thread, is " &
      "counted on the report of the run it happened during, and shown")

  test "a run with no drop shows none":
    let rep = forAll(integers(0, 3), proc (x: int) = discard,
                     Settings(maxExamples: 2))
    check rep.droppedSymexFindings == 0
    check "dropped" notin renderReport(rep, ofText)
    check not parseJson(renderReport(rep, ofJson)).hasKey("droppedSymexFindings")
    check "dropped" notin renderReport(rep, ofJunit)
    check "dropped" notin renderReport(rep, ofGithubAnnotation)

  test "one drop is singular":
    let rep = forAll(integers(0, 3), proc (x: int) =
      var th: Thread[void]
      createThread(th, dropOne)
      joinThread(th),
      Settings(maxExamples: 1))
    check rep.droppedSymexFindings == 1
    check "1 symex finding was dropped" in renderReport(rep, ofText)

proc sameClaim(x: int) =
  ## One call site for the enclosing run and the nested one.
  discard assertCoveredBy(i36Alpha, tLabel("alpha"))

suite "INT-36 R4-09: a nested run's re-found finding is reported once":

  test "the nested run re-finds the enclosing run's finding at its own site":
    let rep = forAll(integers(0, 3), proc (x: int) =
      discard assertCoveredBy(i36Alpha, tLabel("alpha"))
      discard forAll(integers(0, 3), proc (y: int) =
        discard assertCoveredBy(i36Alpha, tLabel("alpha")),
        Settings(maxExamples: 2)),
      Settings(maxExamples: 2))
    var descs: seq[string]
    for f in rep.symexFindings: descs.add f.targetDesc
    checkpoint $descs
    check rep.outcome == otPassed
    check descs == @["label(\"alpha\")"]
    pinNever(cellKey(axConstruct, "report/findings/nested-merge"),
      descs.len == 1,
      "a nested run that re-finds its enclosing run's finding adds no " &
      "second entry to the enclosing report")

  test "the same call site, nested: one entry":
    let rep = forAll(integers(0, 3), proc (x: int) =
      sameClaim(x)
      discard forAll(integers(0, 3), proc (y: int) = sameClaim(y),
                     Settings(maxExamples: 2)),
      Settings(maxExamples: 2))
    check rep.symexFindings.len == 1

  test "two call sites in one run are still two entries (R3 E2)":
    let rep = forAll(integers(0, 3), proc (x: int) =
      discard assertCoveredBy(i36Alpha, tLabel("alpha"))
      discard assertCoveredBy(i36Alpha, tLabel("alpha")),
      Settings(maxExamples: 2))
    check rep.symexFindings.len == 2

  test "the nested run's own report keeps its finding":
    var inner: seq[SymexFinding]
    discard forAll(integers(0, 3), proc (x: int) =
      discard assertCoveredBy(i36Alpha, tLabel("alpha"))
      inner = forAll(integers(0, 3), proc (y: int) =
        discard assertCoveredBy(i36Alpha, tLabel("alpha")),
        Settings(maxExamples: 2)).symexFindings,
      Settings(maxExamples: 1))
    check inner.len == 1

  test "when duplicates meet, the strongest claim stays":
    var weak = SymexFinding(targetDesc: "label(\"a\")", status: sfSat,
                            covered: true)
    weak.soundness.replay = rsUnconfirmed
    var strong = weak
    strong.soundness = Soundness(replay: rsNotNeeded)
    check trusted(strong) and not trusted(weak)
    withEngineFrame:
      recordSymexFinding(FindingOrigin(site: "p.nim(1, 1)", fnId: "fn"), strong)
      withEngineFrame:
        recordSymexFinding(FindingOrigin(site: "p.nim(2, 1)", fnId: "fn"), weak)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      if got.len == 1: check got[0].soundness.replay == rsUnconfirmed
    # Severity first (R4 U1): an unconfirmed covered claim is more severe than
    # a trusted one, so it is the one kept above. Among equals, claimRank.
    var hostSafe = weak
    var unsafe = weak
    unsafe.soundness.witnessUnsafe = true
    check claimRank(hostSafe.soundness) > claimRank(unsafe.soundness)
    withEngineFrame:
      recordSymexFinding(FindingOrigin(site: "p.nim(1, 1)", fnId: "fn"), hostSafe)
      withEngineFrame:
        recordSymexFinding(FindingOrigin(site: "p.nim(2, 1)", fnId: "fn"), unsafe)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      if got.len == 1: check not got[0].soundness.witnessUnsafe
    # The other way round: the nested run's stronger claim replaces the
    # enclosing run's weaker one of equal severity.
    withEngineFrame:
      recordSymexFinding(FindingOrigin(site: "p.nim(1, 1)", fnId: "fn"), unsafe)
      withEngineFrame:
        recordSymexFinding(FindingOrigin(site: "p.nim(2, 1)", fnId: "fn"), hostSafe)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      if got.len == 1: check not got[0].soundness.witnessUnsafe
    # Another fn or another target is another claim: no merge.
    withEngineFrame:
      recordSymexFinding(FindingOrigin(site: "p.nim(1, 1)", fnId: "fn"), weak)
      withEngineFrame:
        recordSymexFinding(FindingOrigin(site: "p.nim(2, 1)", fnId: "fn2"), weak)
        var other = weak
        other.targetDesc = "label(\"b\")"
        recordSymexFinding(FindingOrigin(site: "p.nim(2, 1)", fnId: "fn"), other)
      check engineStack[^1].symexFindings.len == 3
