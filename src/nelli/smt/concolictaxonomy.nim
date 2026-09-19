## Shared concolic-bridge yield taxonomy (RFC-fuzzer-nextgen G2/G3 — R28/R29b
## hardening).
##
## `ConcolicFlipOutcome`/`ConcolicCoverageOutcome`/`ConcolicYieldCounters`/
## `ConcolicFlipCounters`/`ConcolicFlipResult` started life in
## `smt/runtime.nim` (the walker, which computes them — every field here is
## plain data, never a Z3 type). `fuzz.nim` (the orchestrator, which
## accumulates them into `CampaignStats.concolicYield`) needs the SAME
## types, but cannot `import ./smt/runtime` — that module `import z3`s, and
## `fuzz.nim` stays Z3-free so a plain `import nelli`/`import nelli/fuzz`
## never pulls the Z3 dependency in. Previously `fuzz.nim` hand-maintained
## an erased MIRROR of this taxonomy (`ConcolicOutcomeTag`/
## `ConcolicCoverageTag`/`ConcolicYieldTotals`), translated field-by-field
## in `fuzzmacro.nim` at every bridge call site — two independently-edited
## copies of the same enum arms, kept in sync by hand.
##
## Since none of these types actually reference Z3 (`ConcolicFlipResult`'s
## `materialized: seq[ChoiceNode]` is the only externally-defined type it
## touches, and `choice.nim` is itself Z3-free), the mirror was never
## necessary — moving them here, a leaf module that imports only
## `std/tables` and `../choice`, lets `smt/runtime.nim` (which re-exports
## this module, so its own public surface is unchanged) and `fuzz.nim`
## (which imports it directly) share the ONE taxonomy. Same technique
## `smt/transparency.nim` established for G6, and `../bootstrapbreaker.nim`
## for R29a's sibling import-cycle fix.
##
## `WalkerConstructKind` and `ConcolicAdmitOutcome` are new (R28/R29b —
## the RFC's own `Table[WalkerConstructKind, FailureCounts]` taxonomy plus
## the round-2 `solved-but-superseded` outcome); `ConcolicYield` is the
## campaign-level accumulator (`Orchestrator.concolicYield`/
## `CampaignStats.concolicYield`) that folds one call's `ConcolicFlipResult`
## (`foldFlipResult`) or one admission decision (`recordAdmitOutcome`) at a
## time, keyed by construct.

import std/[tables, strutils]
import ../choice

type
  WalkerConstructKind* = enum
    ## The walker-dispatch constructs `wmFollowConcrete` (RFC-fuzzer-nextgen
    ## G1b, widened by R14 — see `docs/rfc/0003-fuzzer-nextgen.handoff.md`'s R14
    ## entry) actually distinguishes today. Deliberately NOT "every IR node
    ## kind" — R14 narrowed exactly these five call sites (`isIf`, `isWhile`,
    ## `isIndex`, `isVariantField`, `isVariantReassignSymbolic`) with
    ## concrete-guidance logic; `isCall` and the static-tag
    ## `isVariantReassign` are mode-agnostic (correct by construction, per
    ## R14's own handoff note) and so earn no slot here. A construct is
    ## added only once the walker can actually attribute an outcome to it —
    ## an arm nothing ever increments would be exactly the dark-mechanism
    ## class this taxonomy exists to avoid.
    wckIf
      ## `walkIfFollowConcrete` — also the ONLY source of
      ## `ConcolicBranchRecord`s (`smt/runtime.nim`), i.e. today the only
      ## construct a G2 branch-flip solve can target. Every
      ## `ConcolicFlipCounters`/`ConcolicAdmitOutcome` attribution is
      ## therefore `wckIf` until the walker grows a second flip-targetable
      ## construct.
    wckWhile
      ## `walkWhileFollowConcrete` guard resolution.
    wckIndex
      ## `maybeForkDefect` via `isIndex` (OOB seq/array access).
    wckVariantField
      ## `maybeForkDefect` via `isVariantField` (out-of-arm field access).
    wckVariantReassign
      ## `followConcreteTag` via `isVariantReassignSymbolic`.

  ConcolicFlipOutcome* = enum
    ## RFC §G-concolic G2 yield taxonomy (typed, not stringly). One value
    ## per `runConcolicFlipImpl` call.
    cfoSolvedExact
      ## `prefix AND (not observedTruth)` was SAT with no relaxation needed.
    cfoSolvedOptimistic
      ## The exact formula was UNSAT/timed-out; a bounded relaxation attempt
      ## (dropped prefix conjuncts) found a model instead.
    cfoUnsat
      ## The exact formula, and every relaxation attempt up to
      ## `maxRelaxationAttempts`, came back UNSAT (proven infeasible; Z3
      ## never returned "unknown").
    cfoUnmodelable
      ## `targetBranchIndex` does not name a recorded decision: either it is
      ## out of range, or collection degraded (an ambiguous branch, G1b's
      ## `concolicAmbiguousBranches`) before the replay ever reached it — so
      ## the designated branch was never modeled in the first place.
    cfoTimedOut
      ## At least one attempt (exact or optimistic) returned Z3 "unknown"
      ## and no attempt ever returned SAT — reported as timed-out rather
      ## than unsat because Z3 never actually proved infeasibility.
    cfoSolverUnavailable
      ## RFC-z3-optional S1b2: the solver could not be reached at all — the
      ## lazy `libz3` load failed (`SoftlinkError`), so no query was ever
      ## posed. Distinct from every arm above, each of which reports what
      ## Z3 *answered*; this one reports that Z3 was never asked.
      ##
      ## Only `nelli/concolic`'s `guardSolverUnavailable` produces it: the
      ## catch cannot live in `fuzz.nim`, which must not name softlink.
      ## Appended rather than inserted so no existing ordinal shifts.

  ConcolicCoverageOutcome* = enum
    ## The intended-branch-covered vs unrelated-coverage split: does
    ## replaying the MATERIALIZED seed actually take the previously-untaken
    ## arm at the targeted decision, or not?
    ccoNotApplicable
      ## No seed was materialized (`cfoUnsat`/`cfoTimedOut`/`cfoUnmodelable`).
    ccoIntendedCovered
      ## Re-collecting on the materialized seed reaches the SAME decision
      ## index and takes a DIFFERENT arm than the original replay did.
    ccoUnrelatedCoverage
      ## A seed WAS materialized, but replaying it does not flip the
      ## targeted decision (same arm as before, or the decision is no
      ## longer reached at all) — solved, but not the intended edge.

  ConcolicAdmitOutcome* = enum
    ## R28/round-2: what happened when a SOLVED, materialized seed was
    ## offered to the frontier for admission — a dimension
    ## `ConcolicFlipOutcome`/`ConcolicCoverageOutcome` cannot compute (both
    ## finish entirely inside `runConcolicFlipImpl`, before the orchestrator
    ## ever sees the seed). Owned by `fuzz.nim`'s `tryConcolicBridge`, the
    ## only site that calls `admit`.
    caoAdmitted
      ## The materialized seed earned a corpus slot.
    caoRejectedAtReplay
      ## Replaying the materialized seed (`orchestrator.run`) returned
      ## `vRejected` (a filter/precondition failure) — never reached
      ## `admit` at all.
    caoSupersededByRace
      ## The seed replayed cleanly (never hit `caoRejectedAtReplay`) and
      ## was offered to `admit`, but earned no corpus slot for any reason
      ## OTHER than a rejected replay. Most concretely: whatever edge it
      ## covers, something else (ordinary mutation, or an earlier concolic
      ## admission this same campaign) already got there first — the RFC's
      ## literal "sibling worker" framing, reproducible today within a
      ## single-worker campaign since the bridge only ever fires after many
      ## prior admits (it is stall-gated). The SAME bucket also covers a
      ## `reVerify`-enabled campaign whose independent fresh-worker replay
      ## never confirms the bridge's claimed coverage — mechanically
      ## identical from the bridge's own vantage point (solved, replayed,
      ## not admitted). Distinct from `cfoUnsat`/`cfoUnmodelable` — without
      ## this bucket a non-admission here reads as an unexplained
      ## `newEdges: 0`, indistinguishable from "the solver is bad at this
      ## construct" when the solver was actually fine and simply lost the
      ## race (or was never independently confirmed).

  ConcolicYieldCounters* = object
    ## RFC §G-concolic "Yield" subsection — G1b's collection-phase counters
    ## (draw-symbolication + concrete-trace following, no branch-flipping;
    ## that's G2's `ConcolicFlipCounters` below).
    tracesTruncated*:     int   ## 1 iff `trace.len > maxDraws` (bounded
                                ## trace length: graceful truncation, not a
                                ## crash or an unbounded Z3 formula)
    drawsSymbolicated*:   int   ## ChoiceNodes turned into fresh symbolic vars
    paramsConcretized*:   int   ## property params bound to a fixed value
                                ## rather than a symbolic draw (opaque
                                ## combinator, OR a draw referenced by index
                                ## that fell past the truncation cap)
    unsupportedDrawKinds*: int  ## ckFloat/ckBytes/ckString draws — not yet
                                ## symbolicated in G1b's fragment
    nonInt64Draws*:        int  ## a `ckInteger` draw whose `min`/`max`/
                                ## `shrinkTowards`/concrete value does not fit
                                ## `int64` — see `concolicIntRepresentable`
                                ## (`smt/runtime.nim`).
    ambiguousBranches*:   int   ## `wmFollowConcrete` hit an `if`/`while`
                                ## decision whose concrete outcome the
                                ## symbolicated-draws fragment alone could
                                ## not determine (walker-boundary
                                ## concretization for CONTROL FLOW;
                                ## collection stops there, gracefully, on
                                ## that path). Flat total across every
                                ## construct — see `ambiguousByConstruct`
                                ## for the R28 breakdown.
    ambiguousByConstruct*: Table[WalkerConstructKind, int]
      ## R28: the SAME degrade as `ambiguousBranches`, keyed by which
      ## construct actually produced it (`wckIf` from
      ## `walkIfFollowConcrete`, `wckWhile` from
      ## `walkWhileFollowConcrete` — the only two constructs whose
      ## concrete-outcome resolution can currently go ambiguous; `isIndex`/
      ## `isVariantField`/`isVariantReassignSymbolic` degrade to a
      ## conservative fork-every-arm instead of stopping the walk, so they
      ## have no ambiguity count to attribute). Additive-only: summing
      ## every value in this table always equals `ambiguousBranches`.
    walkDegradeCount*:    int   ## Issue #163 audit finding W10. Distinct
                                ## classified in-walk degrades
                                ## (`w.walkDegradeErrors`, deduped by
                                ## message — same rule `runSymexImpl`'s own
                                ## `exnWarnings` drain uses) that occurred
                                ## while following the concrete trace, e.g.
                                ## `feOpaqueCallUnmodelled` (#163) for an
                                ## opaque call whose result is used or that
                                ## takes a `var` argument. `runSymexImpl`
                                ## drains this sink into every verdict via
                                ## `exnWarnings`; `runConcolicCollectImpl`
                                ## walks the SUT the same way but, before
                                ## W10, never read it — a degrade silently
                                ## weakened the collected `branchTrace`/
                                ## `drawVars` with no way for a caller to
                                ## tell a clean collect from a tainted one.
                                ## Diagnostics only, never soundness: Track E
                                ## re-verifies every candidate concretely, so
                                ## a tainted collect can waste a candidate
                                ## but never produce a wrong verdict. Zero
                                ## for a SUT that reaches no opaque/
                                ## unmodelled call, and for a `{.cover.}`-
                                ## instrumented SUT (#163 slice 4 made
                                ## nelli's own instrumentation transparent).
    obligationsLive*:     int   ## Issue #163 round 10 (Design F1/F3,
                                ## Liveness F1). Count of `ObligationEntry`s
                                ## with `disposition == odLive` recorded in
                                ## `obligationLog` (`smt/types.nim`) during
                                ## THIS collect — the same threadvar
                                ## `runConcolicCollectImpl`'s
                                ## `ConcolicCollectResult.obligations` is
                                ## assigned from (see that field's own doc
                                ## comment, `smt/runtime.nim`), just counted
                                ## instead of copied wholesale. `obligations`
                                ## is the detail seq (which obligation, what
                                ## width/signedness); this is the live count
                                ## that actually reaches the fuzzer — folded
                                ## by `foldFlipResult` below into
                                ## `Orchestrator.concolicYield`/
                                ## `CampaignStats.concolicYield` on every real
                                ## fuzzing flip. An obligation going live
                                ## never flips `pcSatByConcreteInputs` or any
                                ## other verdict-shaped field — this counter
                                ## is diagnostics only, exactly like
                                ## `walkDegradeCount` above.
    parseDeclines*:       int   ## Issue #163 round 10 companion. Count of
                                ## `prog.parseErrors` entries with
                                ## `severity == sevError` for the program
                                ## THIS collect ran — the exact same
                                ## predicate `runSymexImpl`'s
                                ## `capForcedUnknown` (`smt/runtime.nim`)
                                ## uses to force `sxUnknown` on the
                                ## `wmExplore` path. Deliberately NOT mirrored
                                ## here as an admission gate: a parse decline
                                ## means the SYMBOLIC MODEL of part of the
                                ## program is incomplete, but the materialized
                                ## seed this collect is following is a REAL
                                ## concrete input the fuzzer executes for real
                                ## against the SUT — rejecting it on account
                                ## of an incomplete model would cost coverage
                                ## and buy no soundness (Track E re-verifies
                                ## every candidate concretely regardless).
                                ## Count it, surface it, never refuse it on
                                ## this basis alone. `parseErrors`
                                ## (`ConcolicCollectResult`) is the detail
                                ## seq this counts; see its own doc comment.

  ConcolicFlipCounters* = object
    ## Keyed by outcome enum (never a string) — `array[Enum, int]` indexing
    ## is exhaustive at compile time, so every taxonomy value has a slot.
    byOutcome*:  array[ConcolicFlipOutcome, int]
    byCoverage*: array[ConcolicCoverageOutcome, int]
    relaxationAttemptsUsed*: int
      ## How many optimistic attempts this call actually ran (0 when the
      ## exact attempt already solved, or when there was nothing to target).

  ConcolicFlipResult* = object
    outcome*:         ConcolicFlipOutcome
    coverage*:        ConcolicCoverageOutcome
    materialized*:    seq[ChoiceNode]
      ## Empty unless `outcome in {cfoSolvedExact, cfoSolvedOptimistic}`.
    collectCounters*: ConcolicYieldCounters   ## From the initial (G1b) collection pass.
    flipCounters*:    ConcolicFlipCounters

  ConstructTally* = object
    ## Per-construct-kind slice of a campaign's yield taxonomy —
    ## `ConcolicYield.byConstruct`'s value type. Only the fields a
    ## construct can actually produce are ever nonzero; see
    ## `WalkerConstructKind`'s doc for which constructs reach which fields.
    ambiguousBranches*:  int
    flipOutcomes*:       array[ConcolicFlipOutcome, int]
    coverageOutcomes*:   array[ConcolicCoverageOutcome, int]
    admitOutcomes*:      array[ConcolicAdmitOutcome, int]

  ConcolicYield* = object
    ## RFC §G-concolic: `Table[WalkerConstructKind, FailureCounts]` — the
    ## walker-widening work-list the mechanism section calls for, not a
    ## flat set of counters. `collect`/`flip`/`admitOutcomes` mirror the
    ## campaign-wide totals (summed across every construct) so a caller
    ## reading only the top level still sees the full picture; `byConstruct`
    ## is the R28 breakdown that drives which construct to widen next.
    collect*: ConcolicYieldCounters
    flip*:    ConcolicFlipCounters
    admitOutcomes*: array[ConcolicAdmitOutcome, int]
    byConstruct*: Table[WalkerConstructKind, ConstructTally]

proc oneShotFlip*(outcome: ConcolicFlipOutcome, coverage: ConcolicCoverageOutcome,
                  materialized: seq[ChoiceNode] = @[],
                  collectCounters: ConcolicYieldCounters = ConcolicYieldCounters()
                 ): ConcolicFlipResult =
  ## Convenience constructor matching `runConcolicFlipImpl`'s own `finish`
  ## invariant (exactly one `byOutcome`/`byCoverage` slot set per call,
  ## consistent with the top-level `outcome`/`coverage` fields) — for a
  ## fake/test bridge that only needs to name the outcome, not hand-roll a
  ## `ConcolicFlipCounters` that could drift from it.
  result = ConcolicFlipResult(outcome: outcome, coverage: coverage,
                              materialized: materialized, collectCounters: collectCounters)
  inc result.flipCounters.byOutcome[outcome]
  inc result.flipCounters.byCoverage[coverage]

proc foldFlipResult*(y: var ConcolicYield, r: ConcolicFlipResult,
                     construct: WalkerConstructKind = wckIf) =
  ## Fold ONE `runConcolicFlipImpl` call's result into a running campaign
  ## total (`Orchestrator.concolicYield`) — the one site
  ## `tryConcolicBridge` calls this, for every attempt, whether or not it
  ## goes on to solve or admit. `construct` defaults to `wckIf` because
  ## `if` is, today, the only construct whose decisions become
  ## `ConcolicBranchRecord`s a flip-solve can target (see
  ## `WalkerConstructKind`'s doc) — a caller targeting a future construct
  ## passes it explicitly once G2 grows past `if`.
  # #163 review round 11, Finding D5: this used to be nine hand-written
  # `+=` lines (eight scalars plus the table loop below), the SAME hazard
  # round 10 spent a commit closing one layer up in `ConcolicYieldCounters`
  # itself — a field can be added there and never wired here, because
  # wiring it is a thing a human must remember. `fieldPairs` walks BOTH
  # objects' fields in lockstep by declaration order (verified identical
  # since both operands are the same type, `ConcolicYieldCounters`) so a
  # future scalar `int` field sums automatically; the `when` covers every
  # field type that exists today and the `else` branch is a compile-time
  # error rather than a silent drop, so a field of some OTHER type (should
  # one ever be added) fails the build instead of vanishing from the fold.
  # `ambiguousByConstruct` (the one non-scalar field, a
  # `Table[WalkerConstructKind, int]`) keeps its own explicit merge below —
  # a per-key accumulation `+=` cannot express — including the
  # `byConstruct.ambiguousBranches` side-effect the flat scalar fields have
  # no equivalent of.
  for name, dst, src in fieldPairs(y.collect, r.collectCounters):
    when dst is int:
      dst += src
    elif dst is Table[WalkerConstructKind, int]:
      discard "handled explicitly below"
    else:
      {.error: "ConcolicYieldCounters gained a field of type " & $typeof(dst) &
               " (" & name & ") -- teach foldFlipResult how to fold it".}
  for k, v in r.collectCounters.ambiguousByConstruct:
    y.collect.ambiguousByConstruct.mgetOrPut(k, 0) += v
    y.byConstruct.mgetOrPut(k, ConstructTally()).ambiguousBranches += v
  y.flip.relaxationAttemptsUsed += r.flipCounters.relaxationAttemptsUsed
  for o in ConcolicFlipOutcome:
    y.flip.byOutcome[o] += r.flipCounters.byOutcome[o]
    y.byConstruct.mgetOrPut(construct, ConstructTally()).flipOutcomes[o] += r.flipCounters.byOutcome[o]
  for c in ConcolicCoverageOutcome:
    y.flip.byCoverage[c] += r.flipCounters.byCoverage[c]
    y.byConstruct.mgetOrPut(construct, ConstructTally()).coverageOutcomes[c] += r.flipCounters.byCoverage[c]

proc recordAdmitOutcome*(y: var ConcolicYield, outcome: ConcolicAdmitOutcome,
                         construct: WalkerConstructKind = wckIf) =
  ## Fold in ONE admission decision for a solved/materialized concolic seed
  ## — the R28 fix for the missing "solved but superseded" outcome. See
  ## `ConcolicAdmitOutcome`'s doc for the three buckets and `construct`'s
  ## default for why it is `wckIf` today.
  inc y.admitOutcomes[outcome]
  inc y.byConstruct.mgetOrPut(construct, ConstructTally()).admitOutcomes[outcome]

# ---- Rendering --------------------------------------------------------------
#
# #163 review round 11, Finding L1(a): `fuzz.nim`'s `formatCampaignSummary`
# needs to render `CampaignStats.concolicYield` as part of covering the WHOLE
# `CampaignStats` struct, not just its own two newest fields. These live here
# rather than in `fuzz.nim` because the types they render do — matching this
# module's own reasoning for why the taxonomy types themselves live in this
# leaf module instead of being hand-mirrored downstream. Enum-driven
# iteration (declared order), never raw `Table` iteration, so the output is
# deterministic regardless of insertion history — the same reason
# `engine/render.nim`'s event-stats renderer sorts its `Table` keys before
# walking them.

proc `$`*(c: ConcolicYieldCounters): string =
  var lines: seq[string] = @[]
  lines.add("tracesTruncated=" & $c.tracesTruncated)
  lines.add("drawsSymbolicated=" & $c.drawsSymbolicated)
  lines.add("paramsConcretized=" & $c.paramsConcretized)
  lines.add("unsupportedDrawKinds=" & $c.unsupportedDrawKinds)
  lines.add("nonInt64Draws=" & $c.nonInt64Draws)
  lines.add("ambiguousBranches=" & $c.ambiguousBranches)
  var byConstruct: seq[string] = @[]
  for k in WalkerConstructKind:
    let v = c.ambiguousByConstruct.getOrDefault(k, 0)
    if v != 0: byConstruct.add($k & "=" & $v)
  lines.add("ambiguousByConstruct={" & byConstruct.join(", ") & "}")
  lines.add("walkDegradeCount=" & $c.walkDegradeCount)
  lines.add("obligationsLive=" & $c.obligationsLive)
  lines.add("parseDeclines=" & $c.parseDeclines)
  result = lines.join("\n")

proc `$`*(c: ConcolicFlipCounters): string =
  var byOutcome: seq[string] = @[]
  for o in ConcolicFlipOutcome:
    byOutcome.add($o & "=" & $c.byOutcome[o])
  var byCoverage: seq[string] = @[]
  for cv in ConcolicCoverageOutcome:
    byCoverage.add($cv & "=" & $c.byCoverage[cv])
  result = @[
    "byOutcome={" & byOutcome.join(", ") & "}",
    "byCoverage={" & byCoverage.join(", ") & "}",
    "relaxationAttemptsUsed=" & $c.relaxationAttemptsUsed
  ].join("\n")

proc `$`*(t: ConstructTally): string =
  var flipOutcomes: seq[string] = @[]
  for o in ConcolicFlipOutcome:
    if t.flipOutcomes[o] != 0: flipOutcomes.add($o & "=" & $t.flipOutcomes[o])
  var coverageOutcomes: seq[string] = @[]
  for cv in ConcolicCoverageOutcome:
    if t.coverageOutcomes[cv] != 0: coverageOutcomes.add($cv & "=" & $t.coverageOutcomes[cv])
  var admitOutcomes: seq[string] = @[]
  for a in ConcolicAdmitOutcome:
    if t.admitOutcomes[a] != 0: admitOutcomes.add($a & "=" & $t.admitOutcomes[a])
  result = "ambiguousBranches=" & $t.ambiguousBranches &
           " flipOutcomes={" & flipOutcomes.join(", ") & "}" &
           " coverageOutcomes={" & coverageOutcomes.join(", ") & "}" &
           " admitOutcomes={" & admitOutcomes.join(", ") & "}"

proc `$`*(y: ConcolicYield): string =
  var lines: seq[string] = @["collect:"]
  for l in ($y.collect).splitLines(): lines.add("  " & l)
  lines.add("flip:")
  for l in ($y.flip).splitLines(): lines.add("  " & l)
  var admitOutcomes: seq[string] = @[]
  for a in ConcolicAdmitOutcome:
    admitOutcomes.add($a & "=" & $y.admitOutcomes[a])
  lines.add("admitOutcomes={" & admitOutcomes.join(", ") & "}")
  var byConstruct: seq[string] = @[]
  for k in WalkerConstructKind:
    if y.byConstruct.hasKey(k):
      byConstruct.add($k & ": " & $y.byConstruct[k])
  if byConstruct.len > 0:
    lines.add("byConstruct:")
    for l in byConstruct: lines.add("  " & l)
  else:
    lines.add("byConstruct={}")
  result = lines.join("\n")

# ---- Backward-compatible flat accessors ------------------------------------
#
# `CampaignStats.concolicYield`'s public surface predates the construct-keyed
# taxonomy (R28) and the shared-type merge (R29b) — these project the SAME
# underlying counters through the one real type instead of a second
# hand-maintained flat struct, so `report.stats.concolicYield.solvedExact`
# (and friends) keep compiling, unchanged, for every existing caller.

proc solvedExact*(y: ConcolicYield): int = y.flip.byOutcome[cfoSolvedExact]
proc solvedOptimistic*(y: ConcolicYield): int = y.flip.byOutcome[cfoSolvedOptimistic]
proc unsat*(y: ConcolicYield): int = y.flip.byOutcome[cfoUnsat]
proc unmodelable*(y: ConcolicYield): int = y.flip.byOutcome[cfoUnmodelable]
proc timedOut*(y: ConcolicYield): int = y.flip.byOutcome[cfoTimedOut]
proc solverUnavailable*(y: ConcolicYield): int = y.flip.byOutcome[cfoSolverUnavailable]
proc intendedCovered*(y: ConcolicYield): int = y.flip.byCoverage[ccoIntendedCovered]
proc unrelatedCoverage*(y: ConcolicYield): int = y.flip.byCoverage[ccoUnrelatedCoverage]
proc notApplicable*(y: ConcolicYield): int = y.flip.byCoverage[ccoNotApplicable]
proc relaxationAttemptsUsed*(y: ConcolicYield): int = y.flip.relaxationAttemptsUsed
proc tracesTruncated*(y: ConcolicYield): int = y.collect.tracesTruncated
proc drawsSymbolicated*(y: ConcolicYield): int = y.collect.drawsSymbolicated
proc paramsConcretized*(y: ConcolicYield): int = y.collect.paramsConcretized
proc unsupportedDrawKinds*(y: ConcolicYield): int = y.collect.unsupportedDrawKinds
proc ambiguousBranches*(y: ConcolicYield): int = y.collect.ambiguousBranches
