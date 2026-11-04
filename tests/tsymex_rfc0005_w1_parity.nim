## RFC-0005 wiring slice W1 (0.9.1) -- entry-point parity. Each capability
## below existed on ONE entry point (`symexFind`); these pins make
## `symexFindAllWitnesses` (and so `symexForAll`) reach it too.
##
##   WA-1   the user exception hierarchy reaches `symexFindAllWitnesses`'s
##          program, and the cache key covers it.
##   WA-6   the run's hints (the `feReplay*` ones with the crashing input among
##          them) and the non-winning diagnostics reach `SymexFinding` and the
##          render layer, cold and from the cache alike.
##   WA-10  a cached `sfRaised` hit is the cold finding: `targetDesc`,
##          `defectTypeId` and the witness.
##   WA-11  `SymexResult.fromCache` is false: `symexFind` has no cache.
##   WA-12  the no-targets finding carries `soundness`, `gaps` and
##          `annotationViolations`, as every finding does (§8.1, S11).
import std/[unittest, strutils, json, tables]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc findingFor(fs: seq[SymexFinding]; desc: string): SymexFinding =
  for f in fs:
    if f.targetDesc == desc: return f
  raiseAssert "no finding " & desc & " in " & $fs

proc reportWith(fs: seq[SymexFinding]): Report[int] =
  Report[int](outcome: otPassed, examples: 1, symexFindings: fs)

# =============================================================================
# WA-1 -- user exception types
# =============================================================================

type W1Err = object of ValueError

proc w1Guarded(x: int) =
  ## The only raise is caught by its own named handler, so `r >= 0` holds on
  ## every input: the assert can never fail (native truth below).
  var r = 0
  try:
    if x < 0: raise newException(W1Err, "negative")
    r = x
  except W1Err:
    r = 0
  doAssert r >= 0, "w1Guarded"

proc w1Escapes(x: int) =
  ## A user exception escapes on `x == 7` and nowhere else.
  if x == 7: raise newException(W1Err, "seven")

suite "WA-1 -- symexFindAllWitnesses sees the user exception hierarchy":

  test "native truth: w1Guarded never fails its assert; w1Escapes raises on 7 only":
    for x in [-5, -1, 0, 1, 7, high(int)]:
      w1Guarded(x)   # an AssertionDefect here would end the test
    var raised = 0
    for x in [-1, 0, 6, 7, 8]:
      try: w1Escapes(x)
      except W1Err: inc raised
    check raised == 1

  test "symexFind decides the assert behind a named except: sxUnsat":
    let r = symexFind(w1Guarded, tRaisedExn("AssertionDefect"))
    check r.status == sxUnsat

  test "symexFindAllWitnesses agrees: sfUnsat, not sfUnknown":
    let fs = symexFindAllWitnesses(w1Guarded, inMemoryDatabase())
    checkpoint($fs)
    for f in fs:
      check f.status == sfUnsat
      for g in f.gaps: check g.kind != "eeUnknownExnType"

  test "symexForAll's report agrees":
    let rep = symexForAll(integers(-10, 10), w1Guarded, inMemoryDatabase())
    checkpoint($rep.symexFindings)
    check rep.symexFindings.len > 0
    for f in rep.symexFindings:
      check f.status == sfUnsat

  test "symexFind: an escaping user exception is a clean sxRaised":
    let r = symexFind(w1Escapes, tRaisedExn("W1Err"))
    check r.status == sxRaised
    check r.raisedTypeId == "W1Err"
    check trusted(r)

  test "the cache key covers the hierarchy: a changed parent is a new key":
    var a = SymexProgram(body: IRStmt(kind: isBlock))
    a.userExnHierarchy = {"E": "ValueError"}.toTable
    var b = a
    b.userExnHierarchy = {"E": "IOError"}.toTable
    let c = SymexProgram(body: IRStmt(kind: isBlock))
    proc key(p: SymexProgram): string =
      symexCacheKey(p, tAssertionViolation(), defaultSymexSettings(),
                    z3Version = "z", nimVersion = "n", walkerVersion = "w",
                    renderingVersion = "r")
    check key(a) != key(b)
    check key(a) != key(c)
    ## An empty hierarchy keys as before.
    check canonicalize(c) == canonicalize(SymexProgram(body: IRStmt(kind: isBlock)))

  test "the cache helpers key the program as symexFindAllWitnesses does":
    let db = inMemoryDatabase()
    discard symexFindAllWitnesses(w1Guarded, db)
    let key = symexCacheKeyForFn(w1Guarded, tRaisedExn("AssertionDefect"))
    check db.loadPrimaryWithMeta(key & cacheKeyUnsat).len == 1
    let v = loadSymexVerdict(db, w1Guarded, tRaisedExn("AssertionDefect"),
                             defaultSymexSettings())
    check v.isSome and v.get.status == sfUnsat

# =============================================================================
# WA-6 -- hints and diagnostics reach the finding
# =============================================================================

var gW1: int   ## nothing writes it: a fresh symbol to the walker, really 0

proc w1QuitFirst(k: int) =
  ## The model reaches the label only with `gW1 != 0`; the real fn quits
  ## before it. Replay ends its child: `feReplayCrashed` (or, where a child
  ## cannot be handed this state, `feReplayDeclined`).
  if gW1 == 0:
    quit(7)
  symexTarget("w1_quit")

proc w1Refuted(k: int) =
  ## The model reaches the label only with `gW1 != 0`; the real fn runs to
  ## completion without it: `feReplayRefuted`. Harmless to run, so the
  ## property phase of `symexForAll` can call it.
  if gW1 != 0:
    symexTarget("w1_refuted")

proc w1SiblingOverflow(n: int) =
  ## `n + 1` forks an overflow path the label search does not win on: a
  ## non-winning diagnostic (ADR-0012 D2) beside the `sxSat`.
  let y = n + 1
  if n == 5:
    symexTarget("w1_hit")
  discard y

proc hasHint(f: SymexFinding; kinds: openArray[string]): bool =
  for h in f.hints:
    if h.kind in kinds: return true
  false

const replayHintKinds = ["feReplayCrashed", "feReplayDeclined"]

suite "WA-6 -- symexFindAllWitnesses carries hints and diagnostics":

  test "symexFind: the replay hint is on the result":
    let r = symexFind(w1QuitFirst, tLabel("w1_quit"))
    check r.status == sxUnknown
    var found = false
    for e in r.errors:
      if $e.kind in replayHintKinds: found = true
    check found

  test "cold: the replay hint, with its message, is on the finding and rendered":
    let db = inMemoryDatabase()
    let f = findingFor(symexFindAllWitnesses(w1QuitFirst, db),
                       "label(\"w1_quit\")")
    check f.status == sfUnknown
    check f.hasHint(replayHintKinds)
    for h in f.hints:
      if h.kind == "feReplayCrashed":
        check h.severity == "sevHint"
        check "on the input" in h.msg   # the crashing input is named
    let t = renderReport(reportWith(@[f]), ofText)
    check "feReplay" in t
    let j = parseJson(renderReport(reportWith(@[f]), ofJson))
    check j["symexFindings"][0]["hints"].len > 0
    let g = renderReport(reportWith(@[f]), ofGithubAnnotation, "p")
    check "feReplay" in g

  test "warm: a cache hit serves the same hints":
    let db = inMemoryDatabase()
    let cold = findingFor(symexFindAllWitnesses(w1QuitFirst, db),
                          "label(\"w1_quit\")")
    let warm = findingFor(symexFindAllWitnesses(w1QuitFirst, db),
                          "label(\"w1_quit\")")
    check warm.fromCache
    check warm.hints == cold.hints

  test "symexForAll's report carries the replay hint":
    ## `w1QuitFirst` would end this process in the property phase, which runs
    ## the real fn in-process; the refuted row is harmless to run.
    let rep = symexForAll(integers(-5, 5), w1Refuted, inMemoryDatabase())
    let f = findingFor(rep.symexFindings, "label(\"w1_refuted\")")
    check f.status == sfUnknown
    check f.hasHint(["feReplayRefuted"])
    check "feReplayRefuted" in renderReport(rep, ofText)

  test "cold and warm: the non-winning diagnostic is on the finding and rendered":
    let r = symexFind(w1SiblingOverflow, tLabel("w1_hit"))
    check r.status == sxSat
    check r.diagnostics.len >= 1
    let db = inMemoryDatabase()
    let cold = findingFor(symexFindAllWitnesses(w1SiblingOverflow, db),
                          "label(\"w1_hit\")")
    check cold.status == sfSat
    check cold.diagnostics.len == r.diagnostics.len
    check cold.diagnostics[0].raisedTypeId == "OverflowDefect"
    check cold.diagnostics[0].isDefect
    check cold.diagnostics[0].witnessChoices.len > 0
    check "OverflowDefect" in renderReport(reportWith(@[cold]), ofText)
    let j = parseJson(renderReport(reportWith(@[cold]), ofJson))
    check j["symexFindings"][0]["diagnostics"][0]["raisedTypeId"].getStr ==
      "OverflowDefect"
    let warm = findingFor(symexFindAllWitnesses(w1SiblingOverflow, db),
                          "label(\"w1_hit\")")
    check warm.fromCache
    check warm.diagnostics == cold.diagnostics
    check warm.hints == cold.hints

# =============================================================================
# WA-10 -- a cached raise is the cold finding
# =============================================================================

proc w1Asserts(x: int) =
  assert x != 3, "w1Asserts"

proc w1RaisesThenAsserts(x: int) =
  if x == 7: raise newException(W1Err, "seven")
  assert x != 3, "w1RaisesThenAsserts"

suite "WA-10 -- a cached sfRaised hit matches the cold finding":

  test "targetDesc, defectTypeId and the witness survive the cache":
    let db = inMemoryDatabase()
    let cold = symexFindAllWitnesses(w1Asserts, db)
    let warm = symexFindAllWitnesses(w1Asserts, db)
    checkpoint("cold " & $cold)
    checkpoint("warm " & $warm)
    check cold.len == warm.len
    var raisedSeen = false
    for i in 0 ..< min(cold.len, warm.len):
      check warm[i].fromCache
      check warm[i].targetDesc == cold[i].targetDesc
      check warm[i].status == cold[i].status
      check warm[i].defectTypeId == cold[i].defectTypeId
      check warm[i].witnessChoices == cold[i].witnessChoices
      check warm[i].soundness == cold[i].soundness
      check warm[i].gaps == cold[i].gaps
      if cold[i].status == sfRaised:
        raisedSeen = true
        check cold[i].targetDesc == "raised(AssertionDefect)"
        check cold[i].defectTypeId == "AssertionDefect"
        check cold[i].witnessChoices.len > 0
    check raisedSeen

  test "a SUT that also raises a user exception: the cached raise is the cold one":
    ## WA-1 and WA-10 together: the W1Err path neither taints the run (the
    ## hierarchy is known) nor survives the cache differently.
    let r = symexFind(w1RaisesThenAsserts, tRaisedExn("AssertionDefect"))
    check r.status == sxRaised
    check trusted(r)
    let db = inMemoryDatabase()
    let cold = symexFindAllWitnesses(w1RaisesThenAsserts, db)
    let warm = symexFindAllWitnesses(w1RaisesThenAsserts, db)
    checkpoint("cold " & $cold)
    let c = findingFor(cold, "raised(AssertionDefect)")
    check c.status == sfRaised
    check trusted(c)
    let w = findingFor(warm, "raised(AssertionDefect)")
    check w.fromCache
    check w.witnessChoices == c.witnessChoices
    check w.defectTypeId == c.defectTypeId
    check w.hints == c.hints
    check w.diagnostics == c.diagnostics

# =============================================================================
# WA-11 -- SymexResult.fromCache
# =============================================================================

suite "WA-11 -- symexFind has no cache, so its result is never fromCache":

  test "every status reports fromCache = false":
    check not symexFind(w1Guarded, tRaisedExn("AssertionDefect")).fromCache
    check not symexFind(w1Escapes, tRaisedExn("W1Err")).fromCache
    check not symexFind(w1SiblingOverflow, tLabel("w1_hit")).fromCache

# =============================================================================
# WA-12 -- the no-targets finding
# =============================================================================

var w1ProbeState = 3

proc w1Probe(): int {.symexTransparent.} = w1ProbeState
  ## A false transparency claim (the result is used): an annotation violation.

proc w1NoTargets(x: int): int =
  ## No marker, no assert, no index, no variant field: nothing to target.
  result = w1Probe() + x

suite "WA-12 -- the no-targets finding carries soundness, gaps and violations":

  test "the violation reaches the no-targets finding, cold and again":
    let db = inMemoryDatabase()
    for round in 0 .. 1:
      let fs = symexFindAllWitnesses(w1NoTargets, db)
      check fs.len == 1
      let f = fs[0]
      check f.targetDesc == "no-targets-discovered"
      check f.status == sfNotApplicable
      check not trusted(f)
      check f.annotationViolations.len == 1
      check f.annotationViolations[0].kind == avResultUsed
      check f.annotationViolations[0].callee == "w1Probe"
      ## Nothing ran: its run coordinate is the join of its gaps.
      var joined: Taint
      for g in f.gaps: joined = joined + runTaint(g.class)
      check f.soundness.runTaint == joined
      check f.soundness.pathTaint == {}
      check f.soundness.replay == rsNotNeeded

  test "the walker version is at least W1's":
    check parseInt(symexWalkerVersion) >= 265
