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

  test "a record written before keeps its meaning (code 0 is rsNotNeeded)":
    let db = inMemoryDatabase()
    saveSymexVerdict(db, r1Never, tLabel("never"), defaultSymexSettings(),
                     sfUnsat, Soundness(replay: rsNotNeeded))
    let v = loadSymexVerdict(db, r1Never, tLabel("never"),
                             defaultSymexSettings())
    check v.isSome
    check v.get.soundness == Soundness(replay: rsNotNeeded)
    check trusted(SymexFinding(status: v.get.status,
                               soundness: v.get.soundness))

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
