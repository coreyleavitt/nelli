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

import std/tables
import ../choice

type
  WalkerConstructKind* = enum
    ## The walker-dispatch constructs `wmFollowConcrete` (RFC-fuzzer-nextgen
    ## G1b, widened by R14 — see `docs/RFC-fuzzer-nextgen.handoff.md`'s R14
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
  y.collect.tracesTruncated += r.collectCounters.tracesTruncated
  y.collect.drawsSymbolicated += r.collectCounters.drawsSymbolicated
  y.collect.paramsConcretized += r.collectCounters.paramsConcretized
  y.collect.unsupportedDrawKinds += r.collectCounters.unsupportedDrawKinds
  y.collect.nonInt64Draws += r.collectCounters.nonInt64Draws
  y.collect.ambiguousBranches += r.collectCounters.ambiguousBranches
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
proc intendedCovered*(y: ConcolicYield): int = y.flip.byCoverage[ccoIntendedCovered]
proc unrelatedCoverage*(y: ConcolicYield): int = y.flip.byCoverage[ccoUnrelatedCoverage]
proc notApplicable*(y: ConcolicYield): int = y.flip.byCoverage[ccoNotApplicable]
proc relaxationAttemptsUsed*(y: ConcolicYield): int = y.flip.relaxationAttemptsUsed
proc tracesTruncated*(y: ConcolicYield): int = y.collect.tracesTruncated
proc drawsSymbolicated*(y: ConcolicYield): int = y.collect.drawsSymbolicated
proc paramsConcretized*(y: ConcolicYield): int = y.collect.paramsConcretized
proc unsupportedDrawKinds*(y: ConcolicYield): int = y.collect.unsupportedDrawKinds
proc ambiguousBranches*(y: ConcolicYield): int = y.collect.ambiguousBranches
