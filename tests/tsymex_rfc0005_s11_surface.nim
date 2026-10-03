## RFC-0005 (soundness channels) slice S11 -- the public surface (§8.1, §8.2,
## §7). Everything here is read from a consumer's seat: the file imports the
## public modules (`nelli`, `nelli/symex`) and no internals.
##
##   (a) `Soundness` on every `SymexResult`: the winning path's taint, the run
##       coordinate, and how a SAT claim was settled (`ReplayStatus`). The
##       `forcedBy` shape: an `sxUnknown` always carries a non-empty
##       `runTaint` (Invariant-7 extension).
##   (b) `trusted()` -- the predicate the RFC exists to license.
##   (c) `gaps()` -- the per-cause view, and the walkthrough: read the gap,
##       pull the lever it names, watch the verdict move.
##   (d) the bound echo (`SymexResult.bounds`): the budget the run used, on
##       every status, including the `sxUnsat` that has no error to carry it.
##   (e) `SymexFinding` carries the same soundness, its gaps, and the
##       annotation violations; the cache stores and serves the soundness.
##   (f) the render layer: text / JSON / JUnit / GitHub output show the
##       findings, their trust, their gaps and the annotation violations.
import std/[unittest, strutils, options, json]
import nelli
import nelli/symex

var sideEffects = 0   ## counts REAL executions of the SUTs: symex never runs
                      ## `fn`, so an increment during a `symexFind` is a replay

proc tick() {.symexTransparent.} =
  inc sideEffects

# =============================================================================
# SUTs
# =============================================================================

proc s11Clean(x: int) =
  if x == 42:
    symexTarget("s11_clean")

proc s11Dead(x: int) =
  if x > 5 and x < 3:
    symexTarget("s11_dead")

proc s11Confirm(a: bool; x: int) =
  ## `a < a` on a bool is modelled as a FRESH symbol (`dcFreshSymbol`), so
  ## the only path to the target is `scSpurious`-tainted and replay decides.
  ## Reality: `a < a` is false, so `not o` holds and the replay confirms.
  tick()
  let o = a < a
  if not o:
    if x == 42:
      symexTarget("s11_confirm")

proc s11Raises(x: int) =
  if x == 9:
    raise newException(ValueError, "s11")

proc s11Asserts(x: int) =
  ## A raw `assert`: auto-discovered by `symexFindAllWitnesses` as
  ## `tRaisedExn("AssertionDefect")`, so it yields an `sfRaised` finding.
  assert x != 9, "s11"

proc s11Sensor(): int {.symexOpaque.} = 7
  ## Opaque and USED: `feOpaqueCallUnmodelled`, `dcSubstituted`.

proc s11Opaque(x: int) =
  if s11Sensor() + x == 50:
    symexTarget("s11_opaque")

proc s11Deep(n: int) =
  ## The target needs 8 iterations; the default `maxLoopUnwind` is 5.
  var i = 0
  while i < n:
    i = i + 1
  if i == 8:
    symexTarget("s11_deep")

proc s11Both(n: int) =
  ## Both levers at once: the RFC's "one `echo` and one deep loop" SUT, whose
  ## run coordinate is ⊤ and whose `gaps()` names each cause separately.
  ## RFC-0005 S8bl: the sensor is read before the loop. Read behind
  ## `i == 8 and`, it is reached only on a path whose `i` is a literal
  ## other than 8 (every exit within the bound), and a guard that folds to
  ## `false` no longer walks its arm: the substitution decided nothing.
  let k = s11Sensor()
  var i = 0
  while i < n:
    i = i + 1
  if i == 8 and k == 7:
    symexTarget("s11_both")

var s11ProbeState = 11

proc s11Probe(): int {.symexTransparent.} = s11ProbeState
  ## A FALSE transparency claim: the result is used. An annotation violation.

proc s11Claimed(x: int) =
  let p = s11Probe()
  if x + p == 0x5A4D:
    symexTarget("s11_claimed")

const deepSettings = SymexSettings(budget: ResourceBudget(maxLoopUnwind: 12))

proc kindsOf(gs: seq[tuple[class: DegradeClass, e: SymexErrorInfo]]):
    seq[SymexErrorKind] =
  for g in gs: result.add g.e.kind

proc classesOf(gs: seq[tuple[class: DegradeClass, e: SymexErrorInfo]]):
    seq[DegradeClass] =
  for g in gs:
    if g.class notin result: result.add g.class

# =============================================================================
# (a) Soundness on every SymexResult
# =============================================================================

suite "RFC-0005 S11 (a) -- Soundness on the result":

  test "walker version floor: S11 widened the cache value (soundness metadata)":
    check parseInt(symexWalkerVersion) >= 188

  test "forcedBy shape: an sxUnknown through symexFind carries a non-empty runTaint":
    let r = symexFind(s11Opaque, tLabel("s11_opaque"))
    check r.status == sxUnknown
    check r.soundness.runTaint != {}
    check scIncomplete in r.soundness.runTaint   # dcSubstituted is ⊤ on the run
    check r.soundness.pathTaint == {}            # no winning path
    check r.soundness.replay == rsNotNeeded

  test "forcedBy shape: a budget-bound sxUnknown names scIncomplete in runTaint":
    let r = symexFind(s11Deep, tLabel("s11_deep"))
    check r.status == sxUnknown
    check scIncomplete in r.soundness.runTaint

  test "a clean sxSat: pathTaint {}, replay rsNotNeeded":
    let r = symexFind(s11Clean, tLabel("s11_clean"))
    check r.status == sxSat
    check r.witness[0] == 42
    check r.soundness.pathTaint == {}
    check r.soundness.replay == rsNotNeeded

  test "a replay-confirmed sxSat: pathTaint keeps scSpurious, replay rsConfirmed":
    let before = sideEffects
    let r = symexFind(s11Confirm, tLabel("s11_confirm"))
    check r.status == sxSat
    check sideEffects > before                    # the replay really ran fn
    check scSpurious in r.soundness.pathTaint
    check r.soundness.replay == rsConfirmed

  test "replay off: the same candidate stays sxUnknown, replay never claimed":
    const noReplay = SymexSettings(replay: false)
    let r = symexFind(s11Confirm, tLabel("s11_confirm"), noReplay)
    check r.status == sxUnknown
    check r.soundness.replay == rsNotNeeded
    check r.soundness.runTaint != {}

  test "an sxUnsat: runTaint lacks scIncomplete":
    let r = symexFind(s11Dead, tLabel("s11_dead"))
    check r.status == sxUnsat
    check scIncomplete notin r.soundness.runTaint
    check r.soundness.pathTaint == {}

  test "an sxRaised carries the same common-section soundness":
    let r = symexFind(s11Raises, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedWitness[0] == 9
    check r.soundness.pathTaint == {}
    check r.soundness.replay == rsNotNeeded

# =============================================================================
# (b) trusted()
# =============================================================================

suite "RFC-0005 S11 (b) -- trusted()":

  test "clean sxSat, confirmed sxSat, sxRaised and sxUnsat are trusted; sxUnknown never is":
    check trusted(symexFind(s11Clean, tLabel("s11_clean")))
    check trusted(symexFind(s11Confirm, tLabel("s11_confirm")))
    check trusted(symexFind(s11Raises, tRaisedExn("ValueError")))
    check trusted(symexFind(s11Dead, tLabel("s11_dead")))
    check not trusted(symexFind(s11Opaque, tLabel("s11_opaque")))
    check not trusted(symexFind(s11Deep, tLabel("s11_deep")))

  test "the predicate reads the soundness, not the status alone":
    # A hand-built result with a spurious, UNconfirmed winning path is a SAT
    # the verdict rule never ships -- trusted() says so.
    var r = symexFind(s11Clean, tLabel("s11_clean"))
    r.soundness.pathTaint = {scSpurious}
    check not trusted(r)
    r.soundness.replay = rsConfirmed
    check trusted(r)
    var u = symexFind(s11Dead, tLabel("s11_dead"))
    u.soundness.runTaint = {scIncomplete}
    check not trusted(u)
    u.soundness.runTaint = {scSpurious}         # over-approximation only
    check trusted(u)

# =============================================================================
# (c) gaps() and the walkthrough
# =============================================================================

suite "RFC-0005 S11 (c) -- gaps(): read the cause, pull its lever":

  test "a clean run has no gaps":
    check symexFind(s11Clean, tLabel("s11_clean")).gaps().len == 0
    check symexFind(s11Dead, tLabel("s11_dead")).gaps().len == 0

  test "gaps() lists exactly the declines the run coordinate was built from":
    let r = symexFind(s11Both, tLabel("s11_both"))
    var joined: Taint
    for g in r.gaps():
      check g.class == classOf(g.e.kind)
      joined = joined + runTaint(g.class)
    check joined == r.soundness.runTaint

  test "walkthrough 1 -- a bound: dcFabricated names maxLoopUnwind, raising it moves the verdict":
    let r = symexFind(s11Deep, tLabel("s11_deep"))
    check r.status == sxUnknown
    let gs = r.gaps()
    check gs.len > 0
    check classesOf(gs) == @[dcFabricated]
    check beBudgetExhausted in kindsOf(gs)
    check r.bounds.maxLoopUnwind == 5
    # The lever: the bound the gap names.
    let r2 = symexFind(s11Deep, tLabel("s11_deep"), deepSettings)
    check r2.status == sxSat
    check r2.witness[0] >= 8
    check r2.bounds.maxLoopUnwind == 12
    check trusted(r2)
    # A SAT is a fact about ONE path: deeper paths (n > 12) still hit the new
    # bound, and gaps() still says so -- they just no longer decide anything.
    for g in r2.gaps(): check g.e.kind == beBudgetExhausted

  test "walkthrough 2 -- a model gap: dcSubstituted names the opaque call":
    let r = symexFind(s11Opaque, tLabel("s11_opaque"))
    let gs = r.gaps()
    check classesOf(gs) == @[dcSubstituted]
    check feOpaqueCallUnmodelled in kindsOf(gs)
    var named = false
    for g in gs:
      if "s11Sensor" in g.e.msg: named = true
    check named

  test "walkthrough 3 -- two causes, two levers: ⊤ on the run, two classes in gaps()":
    let r = symexFind(s11Both, tLabel("s11_both"))
    check r.status == sxUnknown
    check r.soundness.runTaint == {scSpurious, scIncomplete}
    let cs = classesOf(r.gaps())
    check dcFabricated in cs
    check dcSubstituted in cs

  test "gaps() leaves out what did not decide anything (hints, warnings)":
    let r = symexFind(s11Confirm, tLabel("s11_confirm"))
    for g in r.gaps():
      check g.e.severity == sevError or g.e.kind == eeUnknownExnType

# =============================================================================
# (d) the bound echo
# =============================================================================

suite "RFC-0005 S11 (d) -- bound provenance is a settings echo on the result":

  test "an sxUnsat echoes the budget it was proved under":
    const s = SymexSettings(budget: ResourceBudget(maxLoopUnwind: 8,
                                                   maxCallDepth: 4))
    let r = symexFind(s11Dead, tLabel("s11_dead"), s)
    check r.status == sxUnsat
    check r.bounds == s.budget
    check r.bounds.maxLoopUnwind == 8
    check r.bounds.maxCallDepth == 4

  test "every status echoes the budget, defaults included":
    check symexFind(s11Clean, tLabel("s11_clean")).bounds == ResourceBudget()
    check symexFind(s11Opaque, tLabel("s11_opaque")).bounds == ResourceBudget()
    check symexFind(s11Raises, tRaisedExn("ValueError")).bounds == ResourceBudget()
    check symexFind(s11Confirm, tLabel("s11_confirm")).bounds == ResourceBudget()

# =============================================================================
# (e) SymexFinding and the cache
# =============================================================================

proc findingFor(fs: seq[SymexFinding]; desc: string): SymexFinding =
  for f in fs:
    if f.targetDesc == desc: return f
  raiseAssert "no finding " & desc

suite "RFC-0005 S11 (e) -- SymexFinding carries soundness, gaps, violations; the cache keeps them":

  test "a cold finding carries the result's soundness, its gaps and trusted()":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(s11Opaque, db)
    let f = findingFor(fs, "label(\"s11_opaque\")")
    check f.status == sfUnknown
    check not f.fromCache
    check f.soundness.runTaint != {}
    check not trusted(f)
    var kinds: seq[string]
    for g in f.gaps: kinds.add g.kind
    check "feOpaqueCallUnmodelled" in kinds
    for g in f.gaps:
      if g.kind == "feOpaqueCallUnmodelled": check g.class == dcSubstituted

  test "a confirmed finding: soundness carries rsConfirmed, and so does its cache hit":
    let db = inMemoryDatabase()
    let cold = findingFor(symexFindAllWitnesses(s11Confirm, db),
                          "label(\"s11_confirm\")")
    check cold.status == sfSat
    check cold.soundness.replay == rsConfirmed
    check scSpurious in cold.soundness.pathTaint
    check trusted(cold)
    let before = sideEffects
    let warm = findingFor(symexFindAllWitnesses(s11Confirm, db),
                          "label(\"s11_confirm\")")
    check warm.fromCache
    check sideEffects == before                 # a served entry never replays
    check warm.soundness == cold.soundness      # served unchanged
    check warm.gaps.len == 0                    # errors are not cached
    check trusted(warm)

  test "an unknown and an unsat verdict serve their stored soundness":
    let db = inMemoryDatabase()
    let coldU = findingFor(symexFindAllWitnesses(s11Opaque, db),
                           "label(\"s11_opaque\")")
    let warmU = findingFor(symexFindAllWitnesses(s11Opaque, db),
                           "label(\"s11_opaque\")")
    check warmU.fromCache
    check warmU.status == sfUnknown
    check warmU.soundness == coldU.soundness
    check warmU.soundness.runTaint != {}
    let coldD = findingFor(symexFindAllWitnesses(s11Dead, db),
                           "label(\"s11_dead\")")
    let warmD = findingFor(symexFindAllWitnesses(s11Dead, db),
                           "label(\"s11_dead\")")
    check coldD.status == sfUnsat
    check warmD.fromCache
    check warmD.soundness == coldD.soundness
    check trusted(warmD)

  test "a raised finding serves its stored soundness":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(s11Asserts, db)
    var cold: SymexFinding
    for f in fs:
      if f.status == sfRaised: cold = f
    check cold.status == sfRaised
    check not cold.fromCache
    check trusted(cold)
    var warm: SymexFinding
    for f in symexFindAllWitnesses(s11Asserts, db):
      if f.status == sfRaised: warm = f
    check warm.fromCache
    check warm.soundness == cold.soundness

  test "the verdict cache primitives round-trip the soundness":
    let db = inMemoryDatabase()
    let s = Soundness(runTaint: {scSpurious, scIncomplete})
    saveSymexVerdict(db, s11Opaque, tLabel("s11_opaque"),
                     defaultSymexSettings(), sfUnknown, s)
    let got = loadSymexVerdict(db, s11Opaque, tLabel("s11_opaque"),
                               defaultSymexSettings())
    check got.isSome
    check got.get.status == sfUnknown
    check got.get.soundness == s

  test "an entry without soundness metadata is a miss, not a clean verdict":
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(s11Dead, tLabel("s11_dead"),
                                 defaultSymexSettings())
    db.save(key & cacheKeyUnsat, @[], verdictCacheMaxEntries)   # pre-S11 shape
    let got = loadSymexVerdict(db, s11Dead, tLabel("s11_dead"),
                               defaultSymexSettings())
    check got.isNone

  test "a backend without the metadata closures degrades to a miss, never a crash":
    # S11 routes the symex cache through `saveWithMetaImpl` /
    # `loadPrimaryWithMetaImpl`. A hand-built `ExampleDatabase` that predates
    # them leaves both nil; calling a nil closure is not catchable, so the
    # cache must check, report it on the run, and analyse cold.
    var legacy = inMemoryDatabase()
    legacy.saveWithMetaImpl = nil
    legacy.loadPrimaryWithMetaImpl = nil
    let s = Soundness(runTaint: {scSpurious, scIncomplete})
    saveSymexVerdict(legacy, s11Opaque, tLabel("s11_opaque"),
                     defaultSymexSettings(), sfUnknown, s)
    check loadSymexVerdict(legacy, s11Opaque, tLabel("s11_opaque"),
                           defaultSymexSettings()).isNone
    let cold = findingFor(symexFindAllWitnesses(s11Dead, legacy),
                          "label(\"s11_dead\")")
    check cold.status == sfUnsat and not cold.fromCache
    let again = findingFor(symexFindAllWitnesses(s11Dead, legacy),
                           "label(\"s11_dead\")")
    check again.status == sfUnsat and not again.fromCache

  test "a finding carries the annotation violations, cold and from cache":
    let db = inMemoryDatabase()
    let cold = findingFor(symexFindAllWitnesses(s11Claimed, db),
                          "label(\"s11_claimed\")")
    check cold.annotationViolations.len == 1
    check cold.annotationViolations[0].kind == avResultUsed
    check cold.annotationViolations[0].callee == "s11Probe"
    let warm = findingFor(symexFindAllWitnesses(s11Claimed, db),
                          "label(\"s11_claimed\")")
    check warm.fromCache
    check warm.annotationViolations == cold.annotationViolations

  test "not-applicable and replay-miss findings are never trusted":
    check not trusted(SymexFinding(status: sfNotApplicable))
    check not trusted(SymexFinding(status: sfReplayMiss))

# =============================================================================
# (f) the render layer
# =============================================================================

suite "RFC-0005 S11 (f) -- the render layer shows trust, gaps and violations":

  proc reportWith(fs: seq[SymexFinding]): Report[int] =
    Report[int](outcome: otPassed, examples: 1, symexFindings: fs)

  let db = inMemoryDatabase()
  let opaqueF = findingFor(symexFindAllWitnesses(s11Opaque, db),
                           "label(\"s11_opaque\")")
  let claimedF = findingFor(symexFindAllWitnesses(s11Claimed, db),
                            "label(\"s11_claimed\")")
  let cleanF = findingFor(symexFindAllWitnesses(s11Clean, db),
                          "label(\"s11_clean\")")

  test "no findings: every format is byte-identical to before":
    let r = reportWith(@[])
    check "symex" notin renderReport(r, ofText)
    check "symex" notin renderReport(r, ofJson)
    check "symex" notin renderReport(r, ofJunit)
    check "symex" notin renderReport(r, ofGithubAnnotation, "p")

  test "text: a [symex] section with status, trust, soundness and each gap":
    let t = renderReport(reportWith(@[cleanF, opaqueF]), ofText)
    check "[symex]" in t
    check "label(\"s11_clean\")" in t
    check "sfSat" in t
    check "trusted=true" in t
    check "trusted=false" in t
    check "dcSubstituted" in t
    check "feOpaqueCallUnmodelled" in t
    check "runTaint=" in t

  test "text: an annotation violation is rendered on its own line":
    let t = renderReport(reportWith(@[claimedF]), ofText)
    check "annotation violation" in t
    check "s11Probe" in t
    check "avResultUsed" in t

  test "json: a symexFindings array with soundness, trusted, gaps and violations":
    let j = parseJson(renderReport(reportWith(@[opaqueF, claimedF]), ofJson))
    check j.hasKey("symexFindings")
    let arr = j["symexFindings"]
    check arr.len == 2
    check arr[0]["status"].getStr == "sfUnknown"
    check arr[0]["trusted"].getBool == false
    check arr[0]["soundness"]["runTaint"].len > 0
    check arr[0]["soundness"]["replay"].getStr == "rsNotNeeded"
    check arr[0]["gaps"].len > 0
    check arr[0]["gaps"][0].hasKey("class")
    check arr[1]["annotationViolations"].len == 1
    check arr[1]["annotationViolations"][0]["callee"].getStr == "s11Probe"

  test "junit: the findings ride <system-out>":
    let x = renderReport(reportWith(@[opaqueF]), ofJunit)
    check "<system-out>" in x
    check "label(&quot;s11_opaque&quot;)" in x
    check "trusted=false" in x

  test "github: an annotation violation is an ::error, an untrusted finding a ::warning":
    let g = renderReport(reportWith(@[cleanF, opaqueF, claimedF]),
                         ofGithubAnnotation, "p")
    check "::error title=symex annotation violation::" in g
    check "::warning title=symex untrusted::" in g
    check g.splitLines()[0].startsWith("::notice::p")   # the report line is first

  test "live: symexForAll's report renders its own findings":
    let rep = symexForAll(integers(0, 100), s11Opaque, inMemoryDatabase())
    check rep.symexFindings.len > 0
    check "[symex]" in renderReport(rep, ofText)
