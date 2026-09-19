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
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

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

suite "#163 review -- walker version pin":

  test "walker version floor >= 140 -- this suite is diagnostics-only, no walker semantics moved":
    check parseInt(symexWalkerVersion) >= 140
