## RFC-0005 review, round 1 -- the finding API (R1-10, R1-15, R1-16, R1-17).
##
## * R1-10. Findings went through a thread-local sink that only `symexForAll`
##   drained, so an `assertCoveredBy` earlier on the thread showed up in a later
##   `symexForAll`'s `Report.symexFindings`. A finding now belongs to the call
##   that made it: `assertCoveredBy` returns it (and carries it on its failure),
##   `symexFindAllWitnesses` returns them, and `symexForAll`'s report holds its
##   own.
## * R1-15. `assertCoveredBy` acted on `status` alone: an untrusted `sxSat`
##   (a lossy witness no replay confirmed) was run through `testFn`, and a miss
##   blamed `testFn`. It now reads `trusted()`: a miss on an untrusted witness
##   is reported as unconfirmed, as an UNKNOWN is.
## * R1-16. A zero `Soundness` read as trusted, so a record whose producer
##   forgot it failed open. Its zero is now `rsUnsettled`, which nothing trusts.
## * R1-17. `SymexFinding` dropped the budget an `sxUnsat` is a proof under. It
##   now carries `bounds`, and every renderer shows them.
import std/[unittest, strutils, options, json]
import nelli
import nelli/symex

# ---- SUTs ---------------------------------------------------------------------

proc r1Alpha(x: int) =
  if x == 42: symexTarget("alpha")

proc r1Beta(x: int) =
  if x == 7: symexTarget("beta")

type
  R1Stub = object
    ## A plain object that looks like a variant (a leading `kind` and more than
    ## two fields): the witness reader renders it as `default(R1Stub)`, not as
    ## the model (`rendersAsDefaultObject`, `wfLossy`).
    kind: int
    a: int
    b: int

proc r1LossyMiss(v: R1Stub) =
  ## The path is clean, but the witness renders `a` as 0: it misses.
  if v.a == 5:
    symexTarget("lm")

proc r1LossyMissToo(v: R1Stub) =
  if v.a == 5:
    symexTarget("lm")

proc r1Never(x: int) =
  if x > 5 and x < 3: symexTarget("never")

# ---- R1-10 --------------------------------------------------------------------

suite "R1-10: a finding belongs to the call that made it":
  test "an earlier assertCoveredBy does not leak into a later symexForAll":
    assertCoveredBy(r1Alpha, tLabel("alpha"))
    let report = symexForAll(integers(0, 1000), r1Beta, inMemoryDatabase())
    var descs: seq[string]
    for f in report.symexFindings: descs.add f.targetDesc
    checkpoint $descs
    check descs.len == 1
    check descs[0] == "label(\"beta\")"

  test "assertCoveredBy returns its own finding":
    let f = assertCoveredBy(r1Alpha, tLabel("alpha"))
    check f.targetDesc == "label(\"alpha\")"
    check f.status == sfSat
    check f.covered
    check trusted(f)

  test "a failing assertCoveredBy carries its finding":
    proc skip(x: int) = discard
    var got: seq[SymexFinding]
    try:
      assertCoveredBy(r1Alpha, tLabel("alpha"), skip)
    except SymexCoverageDefect as e:
      got = e.findings
    check got.len == 1
    check got[0].status == sfSat
    check not got[0].covered

  test "the multi-target form returns every target's finding":
    let fs = assertCoveredBy(r1Alpha, [tLabel("alpha"), tLabel("alpha")])
    check fs.len == 2
    proc skip(x: int) = discard
    var got: seq[SymexFinding]
    try:
      assertCoveredBy(r1Alpha, [tLabel("alpha")], skip)
    except SymexCoverageDefect as e:
      got = e.findings
      check "1 of 1 targets uncovered" in e.msg
    check got.len == 1

# ---- R1-15 --------------------------------------------------------------------

suite "R1-15: assertCoveredBy decides on trusted()":
  test "probe: the lossy witness is an untrusted sxSat":
    let r = symexFind(r1LossyMiss, tLabel("lm"))
    checkpoint $r.status & " " & $r.soundness.replay
    check r.status == sxSat
    check r.soundness.replay == rsUnconfirmed
    check not trusted(r)

  test "an untrusted witness that misses does not blame testFn":
    var msg = ""
    var got: seq[SymexFinding]
    try:
      assertCoveredBy(r1LossyMiss, tLabel("lm"), r1LossyMissToo)
    except SymexCoverageDefect as e:
      msg = e.msg
      got = e.findings
    checkpoint msg
    check msg.len > 0                       # coverage is not proven
    check "unconfirmed" in msg
    check "testFn did not" notin msg        # was: "testFn did not reach ..."
    check "not blamed" in msg
    check got.len == 1
    check got[0].status == sfSat
    check not got[0].covered
    check not trusted(got[0])

  test "the same with no testFn: native fn on the witness misses too":
    var msg = ""
    try:
      assertCoveredBy(r1LossyMiss, tLabel("lm"))
    except SymexCoverageDefect as e:
      msg = e.msg
    checkpoint msg
    check "unconfirmed" in msg
    check "testFn did not" notin msg

  test "with acceptUnknownAsCovered it passes, as an UNKNOWN does":
    let f = assertCoveredBy(r1LossyMiss, tLabel("lm"), r1LossyMissToo,
                            SymexSettings(acceptUnknownAsCovered: true))
    check not f.covered
    check not trusted(f)

  test "control: a trusted witness that testFn misses still blames testFn":
    proc skip(x: int) = discard
    var msg = ""
    try:
      assertCoveredBy(r1Alpha, tLabel("alpha"), skip)
    except SymexCoverageDefect as e:
      msg = e.msg
    check "testFn did not reach" in msg

# ---- R1-16 --------------------------------------------------------------------

suite "R1-16: a zero Soundness is not trusted":
  test "a finding built without a soundness is not trusted":
    check not trusted(SymexFinding(status: sfSat))
    check not trusted(SymexFinding(status: sfRaised))
    check not trusted(SymexFinding(status: sfUnsat))

  test "a real run still is":
    let r = symexFind(r1Alpha, tLabel("alpha"))
    check r.status == sxSat
    check trusted(r)
    let u = symexFind(r1Never, tLabel("never"))
    check u.status == sxUnsat
    check trusted(u)

  test "the cache keeps both readings: an unsettled record stays unsettled":
    let db = inMemoryDatabase()
    saveSymexVerdict(db, r1Never, tLabel("never"), defaultSymexSettings(),
                     sfUnsat, Soundness())
    let v = loadSymexVerdict(db, r1Never, tLabel("never"),
                             defaultSymexSettings())
    check v.isSome
    check v.get.soundness.replay == rsUnsettled
    check not trusted(SymexFinding(status: v.get.status,
                                   soundness: v.get.soundness))

  test "every settled record round-trips (encoding version 3)":
    for rs in [rsNotNeeded, rsConfirmed, rsUnconfirmed]:
      for unsafe in [false, true]:
        let db = inMemoryDatabase()
        let snd = Soundness(replay: rs, witnessUnsafe: unsafe)
        saveSymexVerdict(db, r1Never, tLabel("never"), defaultSymexSettings(),
                         sfUnsat, snd)
        let v = loadSymexVerdict(db, r1Never, tLabel("never"),
                                 defaultSymexSettings())
        check v.isSome
        if v.isSome: check v.get.soundness == snd

# ---- R1-17 --------------------------------------------------------------------

const r1Tight = SymexSettings(budget: ResourceBudget(maxLoopUnwind: 7))

proc r1ReportWith(fs: seq[SymexFinding]): Report[int] =
  Report[int](outcome: otPassed, examples: 1, symexFindings: fs)

suite "R1-17: a finding carries the bounds it was decided under":
  test "a cold and a warm sfUnsat carry the run's budget":
    let db = inMemoryDatabase()
    let cold = symexFindAllWitnesses(r1Never, db, r1Tight)
    check cold.len == 1
    check cold[0].status == sfUnsat
    check not cold[0].fromCache
    check cold[0].bounds == r1Tight.budget
    let warm = symexFindAllWitnesses(r1Never, db, r1Tight)
    check warm[0].fromCache
    check warm[0].bounds == r1Tight.budget

  test "every renderer shows them":
    let f = symexFindAllWitnesses(r1Never, inMemoryDatabase(), r1Tight)[0]
    let r = r1ReportWith(@[f])
    let t = renderReport(r, ofText)
    checkpoint t
    check "bounds " in t
    check "maxLoopUnwind=7" in t
    let j = parseJson(renderReport(r, ofJson))
    check j["symexFindings"][0]["bounds"]["maxLoopUnwind"].getInt == 7
    check "maxLoopUnwind=7" in renderReport(r, ofJunit)
    let g = renderReport(r, ofGithubAnnotation, "p")
    checkpoint g
    check "::notice title=symex bounds::" in g
    check "maxLoopUnwind=7" in g

  test "witnessUnsafe is rendered":
    let f = SymexFinding(targetDesc: "label(\"u\")", status: sfSat,
                         soundness: Soundness(replay: rsConfirmed,
                                              witnessUnsafe: true))
    let r = r1ReportWith(@[f])
    check "witnessUnsafe=true" in renderReport(r, ofText)
    let j = parseJson(renderReport(r, ofJson))
    check j["symexFindings"][0]["soundness"]["witnessUnsafe"].getBool
    check "::warning title=symex witness unsafe::" in
      renderReport(r, ofGithubAnnotation, "p")

# ---- Review round 2 -----------------------------------------------------------
#
# * DD1. Whether a witness may run in the host was read off the finding's
#   hints, which a cache hit rebuilds from the best-effort `:notes` record. A
#   hit whose notes were missing let a witness whose replay ended its child
#   run in the host. It is now a typed `Soundness` fact, stored with the
#   verdict.
# * DD3. `assertCoveredBy` inside a property returned its finding to the
#   property, which discards it: no report showed it. The engine now collects
#   them for the run, on a pass and on a failure.
# * LV3. The seed phase's `sfNotApplicable` entry was unsettled, and JSON
#   printed the zero bounds of a finding that has none.

type
  R2Stub = object
    ## Renders as `default(R2Stub)` (see `R1Stub`): `a` is 0 on replay.
    kind: int
    a: int
    b: int

proc r2LossyCrash(v: R2Stub) =
  ## A clean path to the label; the rendered witness takes the other branch,
  ## which ends the process.
  if v.a == 5:
    symexTarget("lc")
  else:
    quit(9)

proc r2Skip(x: int) = discard

proc dropNotes(db: ExampleDatabase): ExampleDatabase =
  ## `db`, with every `:notes` record gone (missing, or written by a reader
  ## that does not know the encoding).
  result = db
  let inner = db.loadPrimaryWithMetaImpl
  result.loadPrimaryWithMetaImpl = proc (k: string): seq[PrimaryEntry] =
    if ":notes" in k: @[] else: inner(k)

proc lcFinding(fs: seq[SymexFinding]): SymexFinding =
  for f in fs:
    if f.targetDesc == "label(\"lc\")": return f
  doAssert false, "no label(\"lc\") finding"

suite "R2 DD1: host safety is typed, not read off hints":
  test "probe: the lossy winner's replay ended its child":
    let f = lcFinding(symexFindAllWitnesses(r2LossyCrash, inMemoryDatabase()))
    var kinds: seq[string]
    for h in f.hints: kinds.add h.kind
    checkpoint $f.status & " " & $f.soundness & " " & $kinds
    check f.status == sfSat
    check f.soundness.replay == rsUnconfirmed
    check "feReplayCrashed" in kinds
    check not hostRunnable(f.soundness)

  test "a cache hit without its notes still refuses the host":
    let db = inMemoryDatabase()
    let cold = lcFinding(symexFindAllWitnesses(r2LossyCrash, db))
    check not cold.fromCache
    let warm = lcFinding(symexFindAllWitnesses(r2LossyCrash, dropNotes(db)))
    checkpoint $warm.soundness
    check warm.fromCache
    check warm.hints.len == 0
    check warm.soundness.replay == rsUnconfirmed
    check not hostRunnable(warm.soundness)

suite "R2 DD3: assertCoveredBy inside a property reaches the report":
  test "on a pass":
    let rep = forAll(integers(0, 3), proc (x: int) =
      discard assertCoveredBy(r1Alpha, tLabel("alpha")),
      Settings(maxExamples: 3))
    var descs: seq[string]
    for f in rep.symexFindings: descs.add f.targetDesc
    checkpoint $rep.outcome & " " & $descs
    check rep.outcome == otPassed
    check descs == @["label(\"alpha\")"]

  test "on a failure":
    let rep = forAll(integers(0, 3), proc (x: int) =
      assertCoveredBy(r1Alpha, tLabel("alpha"), r2Skip),
      Settings(maxExamples: 3))
    checkpoint $rep.outcome & " " & $rep.symexFindings.len
    check rep.outcome == otFalsified
    check rep.symexFindings.len == 1
    if rep.symexFindings.len == 1:
      check rep.symexFindings[0].targetDesc == "label(\"alpha\")"
      check not rep.symexFindings[0].covered

  test "nothing carries into the next run":
    let rep = forAll(integers(0, 3), proc (x: int) = discard,
                     Settings(maxExamples: 3))
    check rep.symexFindings.len == 0

suite "R2 LV3: a seed that does not fit":
  test "its sfNotApplicable entry is settled and shows no bounds":
    let rep = forAllWithSymexSeeds(@[newSeq[ChoiceNode]()], integers(0, 10),
                                   proc (x: int) = discard)
    var na: seq[SymexFinding]
    for f in rep.symexFindings:
      if f.status == sfNotApplicable: na.add f
    check na.len == 1
    if na.len == 1:
      check na[0].soundness.replay != rsUnsettled
      let j = parseJson(renderReport(rep, ofJson))
      check not j["symexFindings"][0].hasKey("bounds")

# ---- Review round 3 -----------------------------------------------------------
#
# * E2. The run's collector kept one entry per distinct finding, the whole
#   finding compared: two call sites with equal findings collapsed into one,
#   and one call site whose finding moved (a cache hit after a cold run, a
#   replay of the run's) was recorded once per variant. An entry is now one
#   call site's for one target, holding its latest finding.
# * E3. A finding made in a nested `forAll` reached only the inner report,
#   which a caller may discard (`laws`). A frame's findings now also reach the
#   frame it was opened in.

proc descsOf(fs: seq[SymexFinding]): seq[string] =
  for f in fs: result.add f.targetDesc

suite "R3 E2: one entry per call site and target":
  test "two call sites with equal findings are two entries":
    let rep = forAll(integers(0, 3), proc (x: int) =
      discard assertCoveredBy(r1Alpha, tLabel("alpha"))
      discard assertCoveredBy(r1Alpha, tLabel("alpha")),
      Settings(maxExamples: 3))
    checkpoint $descsOf(rep.symexFindings)
    check rep.outcome == otPassed
    check descsOf(rep.symexFindings) ==
      @["label(\"alpha\")", "label(\"alpha\")"]

  test "one call site whose finding moves keeps the latest, once":
    withEngineFrame:
      let cold = SymexFinding(targetDesc: "label(\"a\")", status: sfSat)
      var warm = cold
      warm.fromCache = true
      var other = cold
      other.soundness.runDependence = {rdReplay}
      recordSymexFinding("f.nim(1, 2)", cold)
      recordSymexFinding("f.nim(1, 2)", warm)
      recordSymexFinding("f.nim(3, 4)", cold)
      recordSymexFinding("f.nim(1, 2)", other)
      let got = engineStack[^1].symexFindings
      check got.len == 2
      if got.len == 2:
        check got[0].soundness.runDependence == {rdReplay}
        check not got[0].fromCache
        check got[1].targetDesc == "label(\"a\")"

  test "the multi-target form is one entry per target":
    let rep = forAll(integers(0, 3), proc (x: int) =
      discard assertCoveredBy(r1Alpha, [tLabel("alpha"), tLabel("alpha")]),
      Settings(maxExamples: 3))
    checkpoint $descsOf(rep.symexFindings)
    check descsOf(rep.symexFindings) == @["label(\"alpha\")"]

suite "R3 E3: a nested run's findings reach the enclosing run":
  test "an inner forAll whose report is discarded":
    let rep = forAll(integers(0, 3), proc (x: int) =
      discard forAll(integers(0, 3), proc (y: int) =
        discard assertCoveredBy(r1Alpha, tLabel("alpha")),
        Settings(maxExamples: 2)),
      Settings(maxExamples: 2))
    checkpoint $descsOf(rep.symexFindings)
    check rep.outcome == otPassed
    check descsOf(rep.symexFindings) == @["label(\"alpha\")"]

  test "the inner report keeps them too":
    var inner: seq[SymexFinding]
    discard forAll(integers(0, 3), proc (x: int) =
      inner = forAll(integers(0, 3), proc (y: int) =
        discard assertCoveredBy(r1Alpha, tLabel("alpha")),
        Settings(maxExamples: 2)).symexFindings,
      Settings(maxExamples: 1))
    check descsOf(inner) == @["label(\"alpha\")"]
