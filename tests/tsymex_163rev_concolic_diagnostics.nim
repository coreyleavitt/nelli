## Issue #163 review finding R26 (continued) + the parse-error gap.
##
## `runConcolicCollectImpl` (`smt/runtime.nim`) builds a diagnostics story
## richer than what it hands back through the public `concolicCollect` macro.
## Two channels were discarded outright:
##
## 1. The obligation log. R26 (`tsymex_163rev_concolic_flip_width.nim`)
##    stamped `ziWidth`/`ziSigned` onto a concolic-bound Z3Int param
##    specifically so #161's signed-overflow obligation would FIRE on the
##    concolic (`wmFollowConcrete`) path -- and that suite proved it fires,
##    but only by reading the `obligationLog` threadvar directly, because
##    `ConcolicCollectResult` had no field for it at all. `SymexResult`
##    already carries exactly this as `obligations*: ObligationLog`
##    (`smt/types.nim`; `runSymexImpl` assigns it at `smt/runtime.nim:13551`/
##    `13588`/`13591`). This suite adds the same field to
##    `ConcolicCollectResult`, assigned from the SAME threadvar at the SAME
##    place `result.counters` already is -- no new machinery, just a wire
##    that was never run.
##
## 2. Parse errors. `runConcolicCollectImpl` never read `prog.parseErrors`,
##    so a program whose IR carries a parse-time decline (e.g.
##    `feTransparentResultUsed`, `tsymex_163rev_transparent_result.nim`'s own
##    `usesProbeR` shape) collected "successfully" through `concolicCollect`
##    with no indication that part of the program was never modelled at all.
##    `runSymexImpl` already unions `prog.parseErrors` into `r.errors` on
##    every verdict branch (`smt/runtime.nim:13571`/`13581`/`13593`); this
##    suite adds a `parseErrors*: seq[SymexErrorInfo]` field to
##    `ConcolicCollectResult`, read directly off `prog.parseErrors`.
##
## Both are diagnostic-only additions, exactly like `counters.walkDegradeCount`
## (issue #163 audit W10 / review R9, `tsymex_163audit_w10.nim`): neither
## touches a verdict, and neither is a raise channel.
##
## Round 10 review (Design F1/F3, Liveness F1, High): `obligations`/
## `parseErrors` themselves DO reach `fuzz.nim` -- as a LIVE COUNT, not as
## the two detail seqs directly. `ConcolicYieldCounters` (`smt/
## concolictaxonomy.nim`) gained `obligationsLive`/`parseDeclines`, populated
## in `runConcolicCollectImpl` from the SAME `obligationLog`/`prog.
## parseErrors` these two fields already read, folded by `foldFlipResult`
## exactly like every sibling counter, and so reaching
## `Orchestrator.concolicYield`/`CampaignStats.concolicYield` on every real
## fuzzing flip. Section 3 below proves the counters travel that whole
## chain, not just that a field exists on `ConcolicCollectResult`. The two
## detail seqs stay: they are the "what obligation, what error" drill-down
## BEHIND the live count, a legitimate role distinct from being the only
## surface.
##
## Method note (inherited from #162/#163): every symbolic expectation below
## is paired with the SAME computation run for real in this file where one
## is meaningful.
##
## Round 11 review added two more findings on this same chain, both closed
## below:
##
## L1(a) (Critical) -- the chain's last hop, "user-visible at campaign end",
## was FALSE: nothing in the repo rendered `FuzzReport`/`CampaignStats` at
## all (`report.stats.<field>` assertions in tests were the only reader of
## ANY field, not just `concolicYield`'s two round-10 counters). Fixed by
## `formatCampaignSummary*(s: CampaignStats): string` (`fuzz.nim`) -- a
## renderer covering the WHOLE struct, never called from the library's own
## loop (printing on the caller's behalf is the caller's decision, not
## this one's). The corrected claim -- "returned to the caller, and now
## formattable" -- lives in `tsymex_163rev_concolic_flip_width.nim`'s own
## header, the file that originally overstated it.
##
## D5 (High) -- `foldFlipResult` (`smt/concolictaxonomy.nim`) summed each
## `ConcolicYieldCounters` scalar with a hand-written `+=` line, now eight of
## them: the SAME "producer exists, a human must remember to wire the
## consumer" hazard round 10 closed one layer up. Replaced with a
## `fieldPairs` walk that sums any `int` field automatically and fails the
## BUILD (`{.error.}`) on an unhandled field type, so a future field cannot
## silently vanish from the fold the way this one nearly did three times.
## `ambiguousByConstruct` (the one non-`int`, `Table`-valued field) keeps its
## explicit per-key merge -- a generic `+=` cannot express it, and the `when`
## names it explicitly rather than falling through to the `{.error.}` arm.
##
## Round 12 review closed two more findings on this same chain:
##
## Q2 (High) -- D5's own fix then hand-listed the SAME field set three more
## times with no equivalent protection: both `` `$` `` overloads in
## `smt/concolictaxonomy.nim` and `formatCampaignSummary` in `fuzz.nim`
## named every field, plus this file's own completeness test re-typed the
## sixteen `CampaignStats` names a THIRD time as a runtime substring check.
## Every renderer is now `fieldPairs`-driven with the same `{.error.}`
## escape, matching bespoke-formatted fields BY NAME (not type, for the
## same reason Q5 below matches by name). The completeness test below no
## longer hand-lists field names either -- it derives the expected key set
## from `fieldPairs(stats)` itself, so it cannot drift from the type any
## more than the renderer can. Also added the structured JSON sibling
## `engine/render.nim`'s `renderReport`/`ofJson` precedent actually has
## (round 11's doc comment overstated that precedent as text-only):
## `toJson*(s: CampaignStats): string` and matching `toJson` overloads on
## every `smt/concolictaxonomy.nim` type it nests, in the same hand-built
## `"key":value` style `renderJson` uses.
##
## Q5/L12-3 (Medium) -- `foldFlipResult`'s `when` matched
## `ambiguousByConstruct` by its concrete TYPE
## (`dst is Table[WalkerConstructKind, int]`), not by field identity, with
## `name` already bound and unused. A second field of that same `Table`
## type -- the taxonomy's own natural per-construct shape, so a plausible
## future addition -- would have silently matched the same branch and
## never reached the fold, with no compile error: the exact hazard D5
## closed, reintroduced for one case. Switched to `name ==
## "ambiguousByConstruct"`.
import std/[unittest, strutils, json]
import nelli/smt/canonicalize
import nelli/symex
import nelli/fuzz

# =============================================================================
# Channel 1 -- the obligation log
# =============================================================================
#
# Verbatim shape of `tsymex_163rev_concolic_flip_width.nim`'s R26 SUT/trace/
# bindings -- that suite already proved (via the `obligationLog` threadvar
# directly) that the signed-overflow obligation fires on this exact concolic
# collect. This suite proves the SAME fact is now visible through the public
# `ConcolicCollectResult` itself.

proc concolicOverflowGate(a, b: range[0'i64..9_000_000_000_000_000_000'i64]) =
  let c = a + b
  symexTarget("t")
  discard c

proc cleanGate(x: int) =
  if x > 5:
    symexTarget("hi")
  else:
    symexTarget("lo")

suite "#163 review R26 -- ConcolicCollectResult.obligations surfaces the obligation log":

  test "oracle: 9e18 + 9e18 really overflows int64":
    proc rt(a, b: range[0'i64..9_000_000_000_000_000_000'i64]): int64 = a + b
    expect OverflowDefect:
      discard rt(9_000_000_000_000_000_000'i64, 9_000_000_000_000_000_000'i64)

  test "a concolic collect over a live signed-overflow obligation reports a non-empty obligations, with an odLive entry":
    let trace = @[integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0),
                  integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concolicOverflowGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.obligations.len >= 1
    var anyLive = false
    for o in r.obligations:
      if o.disposition == odLive: anyLive = true
    check anyLive
    # The live-count companion: `counters.obligationsLive` mirrors the SAME
    # `obligationLog` this test just read directly, so it must count the
    # SAME live entries -- not just be nonzero.
    var wantLive = 0
    for o in r.obligations:
      if o.disposition == odLive: inc wantLive
    check r.counters.obligationsLive == wantLive
    check r.counters.obligationsLive >= 1

  test "a clean SUT reports an empty obligations -- the field is not trivially always-on":
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cleanGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.obligations.len == 0
    check r.counters.obligationsLive == 0

# =============================================================================
# Channel 2 -- parse errors
# =============================================================================
#
# Verbatim shape of `tsymex_163rev_transparent_result.nim`'s R10 SUT: a
# `{.symexTransparent.}` callee whose result IS used, which that suite proved
# emits a parse-time `feTransparentResultUsed` decline (alongside the generic
# `feOpaqueCallUnmodelled`) on the `wmExplore` (`symexFind`) path. Parse
# errors are attached to `SymexProgram.parseErrors` at PARSE time -- the same
# `parseEntryImplWarned` call both `symexFind` and `concolicCollect` route
# through (`nelli/symex.nim`) -- independent of which walker mode later
# processes the body, so the same decline is expected to reach a concolic
# collect over the identical shape.

var probeRDState = 11   ## module-level: unmodellable, and deliberately so

proc probeRD(): int {.symexTransparent.} = probeRDState

proc usesProbeRD(x: int) =
  let p = probeRD()             ## result is USED: the promise is NOT honoured
  if x + p == 0x5A4D:
    symexTarget("hit_rd")

suite "#163 review -- ConcolicCollectResult.parseErrors surfaces prog.parseErrors":

  test "oracle: usesProbeRD really gates on x + 11 == Magic":
    doAssert probeRDState == 11
    usesProbeRD(0)
    usesProbeRD(0x5A4D - 11)

  test "a concolic collect over a SUT carrying a parse-time decline reports it in parseErrors":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(usesProbeRD, trace, bindings)
    var specific = false
    for e in r.parseErrors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feTransparentResultUsed and "probeRD" in e.msg:
        specific = true
    check specific
    # The live-count companion: `counters.parseDeclines` counts the SAME
    # `sevError` entries `capForcedUnknown` (`runSymexImpl`) already treats
    # as a blanket "this program was not fully modelled" switch -- NOT
    # every entry in `parseErrors` (some parse-time records are warnings/
    # hints, not declines).
    var wantDeclines = 0
    for e in r.parseErrors:
      if e.severity == sevError: inc wantDeclines
    check r.counters.parseDeclines == wantDeclines
    check r.counters.parseDeclines >= 1

  test "a clean SUT reports an empty parseErrors -- the field is not trivially always-on":
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cleanGate, trace, bindings)
    check r.parseErrors.len == 0
    check r.counters.parseDeclines == 0

# =============================================================================
# Channel 3 -- the counters travel the REAL production chain, not just
# ConcolicCollectResult
# =============================================================================
#
# Round 10 finding (Design F1/F3, Liveness F1): the only in-repo production
# caller of `runConcolicCollectImpl` is `runConcolicFlipImpl`
# (`ConcolicFlipResult.collectCounters`), folded by `foldFlipResult`
# (`smt/concolictaxonomy.nim`) into `Orchestrator.concolicYield` /
# `CampaignStats.concolicYield` -- `fuzz.nim:1695`. `concolicCollect`'s macro
# itself has zero call sites in `src/`. So proving a field exists on
# `ConcolicCollectResult` proves nothing about the fuzzer; these tests drive
# `concolicFlip` (which calls `runConcolicCollectImpl` internally, exactly
# `runConcolicFlipImpl` does) and `foldFlipResult` instead.

suite "#163 review round 10 -- obligationsLive/parseDeclines travel the concolicFlip/foldFlipResult chain":

  test "concolicFlip surfaces obligationsLive on ConcolicFlipResult.collectCounters":
    # `concolicOverflowGate` has no `if` at all, so `branchTrace` is empty and
    # ANY `targetBranchIndex` is out of range -- `cfoUnmodelable`. That is
    # fine: `runConcolicFlipImpl` assigns `result.collectCounters` from its
    # OWN internal `runConcolicCollectImpl` call before it ever inspects
    # `targetBranchIndex`, so the counter is populated on every outcome, not
    # only a solved one.
    let trace = @[integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0),
                  integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicFlip(concolicOverflowGate, trace, bindings, 0)
    check r.outcome == cfoUnmodelable
    check r.collectCounters.obligationsLive >= 1

  test "concolicFlip surfaces parseDeclines on ConcolicFlipResult.collectCounters":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(usesProbeRD, trace, bindings, 0)
    check r.collectCounters.parseDeclines >= 1

  test "a clean SUT's concolicFlip reports both new counters at zero":
    let trace = @[integerChoice(5, 0, 201, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(cleanGate, trace, bindings, 0)
    check r.collectCounters.obligationsLive == 0
    check r.collectCounters.parseDeclines == 0

  test "foldFlipResult carries obligationsLive into CampaignStats.concolicYield's own accumulator type":
    let trace = @[integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0),
                  integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicFlip(concolicOverflowGate, trace, bindings, 0)
    var y: ConcolicYield
    check y.collect.obligationsLive == 0   ## zero value before any fold
    foldFlipResult(y, r)
    check y.collect.obligationsLive == r.collectCounters.obligationsLive
    check y.collect.obligationsLive >= 1

  test "foldFlipResult carries parseDeclines into CampaignStats.concolicYield's own accumulator type":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(usesProbeRD, trace, bindings, 0)
    var y: ConcolicYield
    check y.collect.parseDeclines == 0   ## zero value before any fold
    foldFlipResult(y, r)
    check y.collect.parseDeclines == r.collectCounters.parseDeclines
    check y.collect.parseDeclines >= 1

  test "foldFlipResult accumulates obligationsLive across TWO calls, not just the last":
    let trace = @[integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0),
                  integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r1 = concolicFlip(concolicOverflowGate, trace, bindings, 0)
    let r2 = concolicFlip(concolicOverflowGate, trace, bindings, 0)
    var y: ConcolicYield
    foldFlipResult(y, r1)
    foldFlipResult(y, r2)
    check y.collect.obligationsLive == r1.collectCounters.obligationsLive +
                                       r2.collectCounters.obligationsLive
    check y.collect.obligationsLive >= 2

suite "#163 review round 11 -- foldFlipResult's generic fieldPairs fold (Finding D5)":

  test "every scalar ConcolicYieldCounters field sums correctly across two folds":
    let counters1 = ConcolicYieldCounters(
      tracesTruncated: 1, drawsSymbolicated: 2, paramsConcretized: 3,
      unsupportedDrawKinds: 4, nonInt64Draws: 5, ambiguousBranches: 6,
      walkDegradeCount: 7, obligationsLive: 8, parseDeclines: 9)
    let counters2 = ConcolicYieldCounters(
      tracesTruncated: 10, drawsSymbolicated: 20, paramsConcretized: 30,
      unsupportedDrawKinds: 40, nonInt64Draws: 50, ambiguousBranches: 60,
      walkDegradeCount: 70, obligationsLive: 80, parseDeclines: 90)
    let r1 = oneShotFlip(cfoSolvedExact, ccoIntendedCovered, collectCounters = counters1)
    let r2 = oneShotFlip(cfoUnsat, ccoNotApplicable, collectCounters = counters2)
    var y: ConcolicYield
    foldFlipResult(y, r1)
    foldFlipResult(y, r2)
    check y.collect.tracesTruncated == 11
    check y.collect.drawsSymbolicated == 22
    check y.collect.paramsConcretized == 33
    check y.collect.unsupportedDrawKinds == 44
    check y.collect.nonInt64Draws == 55
    check y.collect.ambiguousBranches == 66
    check y.collect.walkDegradeCount == 77
    check y.collect.obligationsLive == 88
    check y.collect.parseDeclines == 99

  test "the table-valued field (ambiguousByConstruct) still merges per-key, independent of the scalar fold":
    var c1 = ConcolicYieldCounters(ambiguousBranches: 5)
    c1.ambiguousByConstruct[wckIf] = 3
    c1.ambiguousByConstruct[wckWhile] = 2
    var c2 = ConcolicYieldCounters(ambiguousBranches: 4)
    c2.ambiguousByConstruct[wckIf] = 1
    c2.ambiguousByConstruct[wckIndex] = 3
    let r1 = oneShotFlip(cfoSolvedExact, ccoIntendedCovered, collectCounters = c1)
    let r2 = oneShotFlip(cfoUnsat, ccoNotApplicable, collectCounters = c2)
    var y: ConcolicYield
    foldFlipResult(y, r1, wckIf)
    foldFlipResult(y, r2, wckWhile)
    # Per-key accumulation on the flat table: wckIf gets both calls' wckIf
    # entries (3+1), wckWhile and wckIndex each get their own single entry --
    # keyed by what the COLLECT counters recorded, not by the `construct`
    # argument passed to foldFlipResult (that argument attributes the FLIP
    # side below, a genuinely different axis).
    check y.collect.ambiguousByConstruct[wckIf] == 4
    check y.collect.ambiguousByConstruct[wckWhile] == 2
    check y.collect.ambiguousByConstruct[wckIndex] == 3
    check y.byConstruct[wckIf].ambiguousBranches == 4
    check y.byConstruct[wckWhile].ambiguousBranches == 2
    check y.byConstruct[wckIndex].ambiguousBranches == 3
    # The `construct` argument's own axis (flip outcomes) still attributes
    # correctly alongside the table merge above -- proving the two folds
    # (generic scalar loop + explicit table merge) didn't step on each other.
    check y.byConstruct[wckIf].flipOutcomes[cfoSolvedExact] == 1
    check y.byConstruct[wckWhile].flipOutcomes[cfoUnsat] == 1

suite "#163 review round 11 -- CampaignStats.formatCampaignSummary (Finding L1a)":

  test "formatCampaignSummary is deterministic -- the same stats render identically twice":
    var y: ConcolicYield
    let r = oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                        collectCounters = ConcolicYieldCounters(obligationsLive: 3, parseDeclines: 1))
    foldFlipResult(y, r, wckWhile)
    let stats = CampaignStats(execs: 42, corpusSize: 5, coverageEdges: 7,
                              crashCount: 1, totalMutationOps: 9, cullCount: 2,
                              operatorPulls: @[1.5, 2.25],
                              provenanceCounts: [pvMutation: 3, pvConcolic: 1, pvI2S: 0, pvImported: 0],
                              concolicYield: y)
    check formatCampaignSummary(stats) == formatCampaignSummary(stats)

  test "formatCampaignSummary covers every top-level CampaignStats field, not only concolicYield":
    ## #163 review round 12, Finding Q2: this used to hand-list the sixteen
    ## `CampaignStats` field names a THIRD time (after `foldFlipResult` and
    ## `formatCampaignSummary` itself), as a runtime substring-presence
    ## check that could drift from the type just like the other two.
    ## Deriving the expected marker set from `fieldPairs(stats)` means a
    ## field added to `CampaignStats` automatically joins this test's own
    ## expectations -- the guard cannot go stale by omission the way a
    ## hand-typed list can. `concolicYield` is the one field
    ## `formatCampaignSummary` renders as a nested block (`"name:"`) rather
    ## than a flat `"name="` pair; every other field, whatever its type,
    ## renders as `"name="`.
    let stats = CampaignStats(execs: 42, corpusSize: 5, coverageEdges: 7,
                              crashCount: 1, totalMutationOps: 9, cullCount: 2,
                              operatorPulls: @[1.5, 2.25],
                              provenanceCounts: [pvMutation: 3, pvConcolic: 1, pvI2S: 0, pvImported: 0])
    let s = formatCampaignSummary(stats)
    for name, _ in fieldPairs(stats):
      let marker = if name == "concolicYield": name & ":" else: name & "="
      checkpoint("missing field: " & marker)
      check marker in s
    check "execs=42" in s
    check "corpusSize=5" in s
    check "coverageEdges=7" in s
    check "crashCount=1" in s
    check "totalMutationOps=9" in s
    check "cullCount=2" in s
    check "pvMutation=3" in s
    check "pvConcolic=1" in s

  test "formatCampaignSummary's concolicYield section reflects the L1/D5 counters, nested and correct":
    var y: ConcolicYield
    let r = oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                        collectCounters = ConcolicYieldCounters(obligationsLive: 4, parseDeclines: 2))
    foldFlipResult(y, r, wckIf)
    let stats = CampaignStats(concolicYield: y)
    let s = formatCampaignSummary(stats)
    check "obligationsLive=4" in s
    check "parseDeclines=2" in s
    check "cfoSolvedExact=1" in s
    check "ccoIntendedCovered=1" in s

  test "a zero-value CampaignStats still renders (no crash, every section present)":
    let s = formatCampaignSummary(CampaignStats())
    check "execs=0" in s
    check "concolicYield:" in s
    check "byConstruct={}" in s   ## empty Table[WalkerConstructKind, ConstructTally]

suite "#163 review round 12 -- CampaignStats/ConcolicYield toJson (Finding Q2 JSON sibling)":
  ## The structured sibling `engine/render.nim`'s real `ofJson` precedent
  ## has, and round 11's `formatCampaignSummary` doc comment claimed but
  ## never built. Parsed back with `std/json` (rather than only checked as
  ## a substring, the way `formatCampaignSummary`'s tests above work) so
  ## these tests actually prove the output is well-formed JSON, not merely
  ## text that happens to contain the right characters.

  test "toJson(CampaignStats) parses as JSON and covers every top-level field":
    let stats = CampaignStats(execs: 42, corpusSize: 5, coverageEdges: 7,
                              crashCount: 1, totalMutationOps: 9, cullCount: 2,
                              operatorPulls: @[1.5, 2.25],
                              provenanceCounts: [pvMutation: 3, pvConcolic: 1, pvI2S: 0, pvImported: 0])
    let j = parseJson(toJson(stats))
    for name, _ in fieldPairs(stats):
      checkpoint("missing JSON key: " & name)
      check j.hasKey(name)
    check j["execs"].getInt() == 42
    check j["corpusSize"].getInt() == 5
    check j["coverageEdges"].getInt() == 7
    check j["crashCount"].getInt() == 1
    check j["totalMutationOps"].getInt() == 9
    check j["cullCount"].getInt() == 2
    check j["operatorPulls"].getElems().len == 2
    check j["provenanceCounts"]["pvMutation"].getInt() == 3
    check j["provenanceCounts"]["pvConcolic"].getInt() == 1

  test "toJson(CampaignStats) nests concolicYield structurally, not as an escaped string":
    var y: ConcolicYield
    let r = oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                        collectCounters = ConcolicYieldCounters(obligationsLive: 4, parseDeclines: 2))
    foldFlipResult(y, r, wckIf)
    let stats = CampaignStats(concolicYield: y)
    let j = parseJson(toJson(stats))
    check j["concolicYield"].kind == JObject
    check j["concolicYield"]["collect"]["obligationsLive"].getInt() == 4
    check j["concolicYield"]["collect"]["parseDeclines"].getInt() == 2
    check j["concolicYield"]["flip"]["byOutcome"]["cfoSolvedExact"].getInt() == 1
    check j["concolicYield"]["flip"]["byCoverage"]["ccoIntendedCovered"].getInt() == 1
    check j["concolicYield"]["byConstruct"]["wckIf"]["flipOutcomes"]["cfoSolvedExact"].getInt() == 1

  test "a zero-value CampaignStats.toJson still parses (no crash, byConstruct is an empty object)":
    let j = parseJson(toJson(CampaignStats()))
    check j["execs"].getInt() == 0
    check j["concolicYield"]["byConstruct"].kind == JObject
    check j["concolicYield"]["byConstruct"].len == 0

  test "toJson(ConcolicYieldCounters) round-trips ambiguousByConstruct as a keyed object":
    var c = ConcolicYieldCounters(ambiguousBranches: 5)
    c.ambiguousByConstruct[wckIf] = 3
    c.ambiguousByConstruct[wckWhile] = 2
    let j = parseJson(toJson(c))
    check j["ambiguousBranches"].getInt() == 5
    check j["ambiguousByConstruct"]["wckIf"].getInt() == 3
    check j["ambiguousByConstruct"]["wckWhile"].getInt() == 2
    check not j["ambiguousByConstruct"].hasKey("wckIndex")   ## zero entries omitted, same as the text renderer

suite "#163 review -- walker version pin":

  test "walker version floor >= 140 -- this suite is diagnostics-only, no walker semantics moved":
    check parseInt(symexWalkerVersion) >= 140
