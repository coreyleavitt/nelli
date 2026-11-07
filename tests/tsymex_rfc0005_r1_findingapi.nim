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
import std/[unittest, strutils, options, json, tables, sequtils]
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

  test "review R3 (E8): the stored encoding, golden":
    # Version 3 writes enum ordinals; a reordered enum would still round-trip
    # above, so the bytes are pinned here as well.
    let db = inMemoryDatabase()
    saveSymexVerdict(db, r1Never, tLabel("never"), defaultSymexSettings(),
                     sfUnsat, Soundness(pathTaint: {scSpurious},
                                        runTaint: {scIncomplete},
                                        replay: rsUnconfirmed,
                                        witnessUnsafe: true,
                                        runDependence: {rdQueryTimeout}))
    let key = symexCacheKeyForFn(r1Never, tLabel("never")) & cacheKeyUnsat
    let got = db.loadPrimaryWithMetaImpl(key)
    check got.len == 1
    if got.len == 1:
      check got[0].meta.getOrDefault("soundness") == "4:1:2:3:1:0:1"

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
      recordSymexFinding(FindingOrigin(site: "f.nim(1, 2)", fnId: "fn"), cold)
      recordSymexFinding(FindingOrigin(site: "f.nim(1, 2)", fnId: "fn"), warm)
      recordSymexFinding(FindingOrigin(site: "f.nim(3, 4)", fnId: "fn"), cold)
      recordSymexFinding(FindingOrigin(site: "f.nim(1, 2)", fnId: "fn"), other)
      let got = toSeq(engineStack[^1].symexFindings.values)
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

# ---- Review round 4 -------------------------------------------------------------
#
# * U1/X1. The collector kept the latest finding per key, so a later passing
#   example (or shrink candidate) overwrote an earlier failing one, and a
#   template or helper shared one key among several `fn`s. A key is now the
#   fn, the call site and the target; an entry keeps its most severe finding.
# * X8. A finding recorded outside any engine frame is counted, not just lost.

var r4Calls = 0
proc r4Late(x: int) =
  ## Not covering on its first call, covering on every call after.
  inc r4Calls
  if r4Calls > 1: r1Alpha(x)

template r4Check(f: untyped) =
  ## One call site shared by every `f`.
  try:
    discard assertCoveredBy(f, tLabel("alpha"), r4Late)
  except SymexCoverageDefect:
    discard

suite "R4 U1: a failing finding is not overwritten by a later pass":
  test "a later covered finding does not replace an earlier uncovered one":
    withEngineFrame:
      var bad = SymexFinding(targetDesc: "t", status: sfSat, covered: false)
      var good = bad
      good.covered = true
      good.soundness.replay = rsConfirmed
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fn"), bad)
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fn"), good)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      check not got[0].covered

  test "an unconfirmed covered finding beats a trusted covered one":
    withEngineFrame:
      var unconf = SymexFinding(targetDesc: "t", status: sfSat, covered: true)
      var good = unconf
      good.soundness.replay = rsConfirmed
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fn"), unconf)
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fn"), good)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      check not trusted(got[0])

  test "R5 D3a: a later unknown does not replace an earlier coverage failure":
    withEngineFrame:
      let o = FindingOrigin(site: "s", fnId: "fn")
      var bad = SymexFinding(targetDesc: "t", status: sfSat, covered: false)
      var unk = SymexFinding(targetDesc: "t", status: sfUnknown,
                             covered: false)
      recordSymexFinding(o, bad)
      recordSymexFinding(o, unk)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      check got[0].status == sfSat
      check not got[0].covered

  test "R5 D3a: an unknown still beats an unconfirmed or trusted covered one":
    withEngineFrame:
      let o = FindingOrigin(site: "s", fnId: "fn")
      var unk = SymexFinding(targetDesc: "t", status: sfUnknown,
                             covered: false)
      var good = SymexFinding(targetDesc: "t", status: sfSat, covered: true)
      good.soundness.replay = rsConfirmed
      recordSymexFinding(o, unk)
      recordSymexFinding(o, good)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      check got[0].status == sfUnknown

  test "R6 N2: a later unconfirmed uncovered finding keeps an earlier trusted failure":
    withEngineFrame:
      let o = FindingOrigin(site: "s", fnId: "fn")
      var bad = SymexFinding(targetDesc: "t", status: sfSat, covered: false)
      bad.soundness.replay = rsConfirmed
      check trusted(bad)
      var weak = SymexFinding(targetDesc: "t", status: sfSat, covered: false)
      check not trusted(weak)
      recordSymexFinding(o, bad)
      recordSymexFinding(o, weak)
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      check trusted(got[0])

  test "R6 N2: an audit entry never replaces a verdict":
    withEngineFrame:
      let o = FindingOrigin(site: "s", fnId: "fn")
      var good = SymexFinding(targetDesc: "t", status: sfSat, covered: true)
      good.soundness.replay = rsConfirmed
      recordSymexFinding(o, good)
      for st in [sfNotApplicable, sfReplayMiss]:
        recordSymexFinding(o, SymexFinding(targetDesc: "t", status: st))
      let got = toSeq(engineStack[^1].symexFindings.values)
      check got.len == 1
      check got[0].status == sfSat

  test "two fns through one call site are two entries":
    withEngineFrame:
      let f = SymexFinding(targetDesc: "t", status: sfSat)
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fnA"), f)
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fnB"), f)
      check engineStack[^1].symexFindings.len == 2

  test "a failure on the first example survives later passes in the report":
    r4Calls = 0
    let rep = forAll(integers(0, 3), proc (x: int) =
      try:
        assertCoveredBy(r1Alpha, tLabel("alpha"), r4Late)
      except SymexCoverageDefect:
        discard,
      Settings(maxExamples: 4))
    check rep.outcome == otPassed
    check rep.symexFindings.len == 1
    if rep.symexFindings.len == 1:
      check not rep.symexFindings[0].covered

  test "two fns through one template call site are two entries":
    r4Calls = 0
    let rep = forAll(integers(0, 3), proc (x: int) =
      r4Check(r1Alpha)
      r4Check(r1Beta),
      Settings(maxExamples: 2))
    check rep.symexFindings.len == 2

suite "R4 X8: a finding recorded outside a frame is counted":
  test "the drop counter moves":
    resetDroppedSymexFindings()
    let before = droppedSymexFindings()
    check before == 0
    recordSymexFinding(FindingOrigin(site: "s", fnId: "fn"),
                       SymexFinding(targetDesc: "t"))
    check droppedSymexFindings() == before + 1
    withEngineFrame:
      recordSymexFinding(FindingOrigin(site: "s", fnId: "fn"),
                       SymexFinding(targetDesc: "t"))
    check droppedSymexFindings() == before + 1

suite "R5 3d: the fn identity":
  test "a local proc variable and a proc parameter are refused, not crashed":
    # Neither is a routine symbol, so neither has a body to hash: the entry
    # macro refuses them ("expected a `proc` symbol", before the identity is
    # built), a clean compile error, not a macro crash.
    let local = r1Alpha
    proc viaParam(p: proc (x: int)): bool =
      compiles(assertCoveredBy(p, tLabel("alpha")))
    check not compiles(assertCoveredBy(local, tLabel("alpha")))
    check not viaParam(r1Alpha)
    check compiles(assertCoveredBy(r1Alpha, tLabel("alpha")))

  test "two routines at one site keep distinct entries":
    let rep = forAll(integers(0, 1), proc (x: int) =
      try: assertCoveredBy(r1Alpha, tLabel("alpha"), r4Late)
      except SymexCoverageDefect: discard
      try: assertCoveredBy(r1Beta, tLabel("beta"), r4Late)
      except SymexCoverageDefect: discard,
      Settings(maxExamples: 2))
    check rep.symexFindings.len == 2
