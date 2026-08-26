## Fuzz integration — the bytes-as-DataSource entry point and (in a
## later issue) the coverage-guided runner.
##
## This module is the **partitioned-fuzz half** of nelli: it shares
## the choice-sequence IR, Strategy[T], DataSource, ExampleDatabase,
## and shrinker with the PBT runner, but lives behind its own entry
## points so a user who only wants property tests never touches the
## fuzz API. Per the M12 design discussion, the partitioning is the
## architecture that lets us combine PBT and structured fuzzing in
## one library without entangling them.
##
## The first capability here is `fuzzOnce(s, prop, bytes)`: run a
## strategy + property against an externally-supplied byte buffer.
## This is the integration point for libFuzzer / AFL / custom mutator
## harnesses — they hand us bytes, we hand them back a verdict.

import std/[options, times, monotimes, os, strutils, sets, tables]
import ./strategy, ./datasource, ./engine, ./rng, ./coverage, ./choice, ./fuzzir, ./db, ./bandit
export fuzzir
export bandit
# The coverage runtime + `{.cover.}` pragma live in a dedicated leaf
# module (`./coverage`) so the PBT engine can depend on them (for #107
# coverage-guided forAll) without a fuzz↔engine cycle. Re-exported here
# so existing `import nelli/fuzz` callers don't break.
export coverage

# --- fuzzOnce: bytes → value → property -------------------------------------

type
  FuzzOnceOutcome* = enum
    foOk,         ## strategy produced a value; property held
    foRejected,   ## the byte buffer was too short to satisfy the strategy
                  ## (or a `filter`/`assume` rejected the example); the
                  ## fuzzer should drop this input from its corpus
    foFalsified   ## the property raised `FalsifiedError`; the bytes
                  ## are a crash-reproducing input (libFuzzer keeps it)

  FuzzOnceResult*[T] = object
    outcome*: FuzzOnceOutcome
    value*: Option[T]
    message*: string

proc fuzzOnce*[T](s: Strategy[T], prop: proc(x: T),
                  bytes: seq[byte]): FuzzOnceResult[T] =
  ## Run `s` then `prop` against a byte buffer. Insufficient bytes or
  ## strategy-side rejection both map to `foRejected` — the fuzzer drops
  ## the input. A property failure (`foFalsified`) is what the fuzzer
  ## corpus retains.
  var ds = newReplaySourceFromBytes(bytes)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return FuzzOnceResult[T](outcome: foRejected)
  result.value = some(x)
  try:
    prop(x)
    result.outcome = foOk
  except Rejection:
    result.outcome = foRejected
  except FalsifiedError as e:
    result.outcome = foFalsified
    result.message = e.msg
  except CatchableError as e:
    result.outcome = foFalsified
    result.message = $e.name & ": " & e.msg
  except Defect as e:
    result.outcome = foFalsified
    result.message = "crashed: " & $e.name & ": " & e.msg

proc fuzzOnceIR*[T](s: Strategy[T], prop: proc(x: T),
                    choices: seq[ChoiceNode]): FuzzOnceResult[T] =
  ## IR-level peer of `fuzzOnce`. Replays `choices` through the strategy
  ## (no byte-decode in the loop) and runs the property. The architectural
  ## entry point for IR-aware mutation: a mutator hands us a mutated
  ## sequence directly and we check it without ever round-tripping through
  ## bytes. Insufficient/misaligned choices map to `foRejected` per the
  ## same convention as `fuzzOnce`.
  var ds = newReplaySource(choices)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return FuzzOnceResult[T](outcome: foRejected)
  result.value = some(x)
  try:
    prop(x)
    result.outcome = foOk
  except Rejection:
    result.outcome = foRejected
  except FalsifiedError as e:
    result.outcome = foFalsified
    result.message = e.msg
  except CatchableError as e:
    result.outcome = foFalsified
    result.message = $e.name & ": " & e.msg
  except Defect as e:
    result.outcome = foFalsified
    result.message = "crashed: " & $e.name & ": " & e.msg

# --- FuzzSettings / FuzzReport / fuzzWith ------------------------------------

type
  FuzzMutationMode* = enum
    ## Selects the mutation kernel. `fmIR` is enum-position 0 so an
    ## un-initialized `FuzzSettings` defaults to IR mode — the structural
    ## payoff of the M12 typed-IR decision (#110). `fmBytes` retains the
    ## libFuzzer/AFL byte path for harnesses that hand us raw bytes.
    fmIR,
    fmBytes

  FuzzCorpusKind* = enum fckIR, fckBytes

  FuzzCorpus* = object
    ## Sum type at the collection level: one corpus, one representation.
    ## Matches `FuzzMutationMode` so the type system enforces that a
    ## byte-mode run produces a byte corpus and IR-mode produces an IR
    ## corpus — no mixing, no parallel-field convention.
    case kind*: FuzzCorpusKind
    of fckIR:    irEntries*:   seq[seq[ChoiceNode]]
    of fckBytes: byteEntries*: seq[seq[byte]]

  FuzzSettings* = object
    ## Configuration for the coverage-guided fuzz runner. Deliberately
    ## distinct from PBT `Settings` per the M12 partitioning: a PBT user
    ## should never see fuzz fields, and a fuzz user shouldn't pay for
    ## PBT-only fields they don't need.
    maxIterations*: int
      ## Hard cap on `fuzzOnce` calls. `0` = no cap (controlled by
      ## `timeBudget` alone).
    timeBudget*: Duration
      ## Wall-clock budget. The loop exits when this is exceeded or
      ## when `maxIterations` is hit, whichever first. `0` (the default
      ## via `initDuration()`) means no wall-clock cap.
    seed*: uint64
      ## Master seed for the fuzzer's own RNG (drives random initial
      ## seeds and mutation choices). Deterministic in this seed when
      ## the SUT is deterministic.
    mutationMode*: FuzzMutationMode
      ## Selects byte vs IR mutation kernel. Defaults to `fmIR` (enum
      ## position 0) for the structural-validity payoff — #110.
    initialCorpus*: seq[seq[byte]]
      ## Seed inputs for `fmBytes` mode (e.g., from a previous AFL run).
      ## Ignored in `fmIR` mode; IR-mode seeds itself by generating one
      ## random input through the strategy.
    initialIRCorpus*: seq[seq[ChoiceNode]]
      ## Seed IR sequences for `fmIR` mode (e.g., persisted from a
      ## previous fuzz run, or hand-crafted regression seeds).
    initialInputSize*: int
      ## Bytes per random initial input in `fmBytes` mode. Defaults to 64.
    integerBias*: IntegerBiasConfig
      ## Distribution bias for `drawInteger` in the IR runner's seed
      ## input (#103 follow-up). Narrow effect by design: the byte-mode
      ## adapter draws via `bytesMode` (bias-irrelevant) and corpus
      ## entries after the seed come from IR mutators (which use their
      ## own log-scaled perturbation kernel, also bias-irrelevant).
      ## So this field only affects the one fresh-RNG seed input that
      ## `fuzzWithIR` generates when `initialIRCorpus` is empty.
      ## Zero-init resolves to `defaultIntegerBias` via `resolved()`.
    keepAllCrashes*: bool
      ## By default the loop de-dups crashes by `crashKey` (keep-first), so the
      ## same bug reached many ways is reported once (FUZZ_PLAN 6a). Set this to
      ## record every `vInteresting`/`vTimedOut` run, dupes included.
    crashKey*: proc(cov: Coverage; message: string): string {.closure.}
      ## Crash-identity fingerprint for de-dup. `nil` (the default) keys on the
      ## coverage edge-set plus the crash message — input-representation
      ## independent, so it is stable under shrinking. Override to key on, e.g.,
      ## a sanitizer stack hash parsed from the message.
    database*: ExampleDatabase
      ## Optional corpus persistence (FUZZ_PLAN 6b). When set (a non-nil backend),
      ## the loop loads any prior corpus as seeds on start and saves every
      ## new-coverage input, keyed by `fuzzCorpusKey(persistKey, frontier.targetId)`.
      ## Folding the `targetId` into the key means a changed binary re-keys cleanly:
      ## the stale corpus (tied to a now-invalid coverage map) is simply missed.
      ## Persists via `saveCorpus`/`loadCorpus` (F1, RFC-chapulin-hardening) — a
      ## dedicated, never-pruned DB section, so the corpus survives even a run
      ## that shares its testId with a `forAll` regression suite (`dbReusePhase`
      ## only ever reads/prunes the `primary` section).
    persistKey*: string
      ## User half of the persistence key — names the campaign (e.g. "nim-parser").
    corpusLimit*: int
      ## Cap on persisted corpus entries (keep-most-recent). `0` → 256.
    uniformSchedule*: bool
      ## RFC-fuzzer-nextgen S1: opt OUT of the default Entropic (Böhme
      ## information-gain) power schedule and fall back to pure uniform
      ## random parent selection — reproduces the pre-S1 default trajectory
      ## byte-for-byte (same RNG consumption, same mutation/admission
      ## sequence; `FrontierStats` still updates as inert bookkeeping the
      ## loop simply doesn't consult). Also doubles as Track S's ablation-
      ## harness uniform baseline (RFC §Evaluation). Off by default:
      ## Entropic (`entropicEnergy`, coverage.nim) is now the schedule —
      ## this SUBSUMES the old opt-in `powerSchedule` flag and its coarse
      ## recency/lineage `2.0`/`+1.0` scheme, which is gone.
    minimizeCorpus*: bool
      ## Opt-in (FUZZ_PLAN 6c): after the run, reduce the reported/persisted corpus
      ## to a minimal subset whose per-entry coverage still spans the same edges
      ## (greedy set cover). The frontier and `coverageHits` are unaffected.
    stallRounds*: int
      ## RFC-fuzzer-nextgen G3: K — invoke the call-site concolic bridge
      ## (when one is wired; see `fuzz(...)`'s macro entry) once the
      ## shared frontier has gone this many admits with no coverage
      ## improvement. `0` (the default) disables stall-triggered concolic
      ## invocation entirely — byte-for-byte the pre-G3 loop trajectory,
      ## the same additive-knob convention as `uniformSchedule`/`reVerify`.
    concolicMaxBranchAttempts*: int
      ## RFC-fuzzer-nextgen G3: bounded recorded-branch-index attempts per
      ## stall round (see `Orchestrator.concolicMaxBranchAttempts`). `0`
      ## (the zero-value default) resolves to 8 in the loop, matching
      ## `tryConcolicBridge`'s own default.
    stopOnFirstCrash*: bool
      ## Opt-in (F4, RFC-chapulin-hardening): halt the loop as soon as the first
      ## NEW crash is recorded — i.e. the first `vInteresting`/`vTimedOut` run whose
      ## `crashKey` is not already in `seenCrashKeys` (a duplicate of an
      ## already-seen crash is not a new finding and does not trigger the stop; see
      ## `keepAllCrashes`/`crashKey` above for the de-dup this keys off of). The
      ## report then contains exactly that one crash and `iterations` reflects the
      ## early exit rather than `maxIterations`. Post-loop bookkeeping (corpus
      ## `minimizeCorpus`, `result.coverageHits`) still runs against whatever the
      ## loop admitted before stopping, so the report stays well-formed. Default
      ## `false`: the loop always runs its full iteration/time budget, unchanged.
    enableI2S*: bool
      ## RFC-fuzzer-nextgen G5: opt IN to the I2S (input-to-state) replacement
      ## mutator + auto-dictionary — G4's `{.covercmp.}` operand log mapped
      ## back to choice nodes (`mutateIRI2SReplace`, fuzzir.nim), a 6th
      ## mutation operator alongside the existing five. `false` (the default)
      ## is byte-for-byte the pre-G5 loop: the pick distribution stays
      ## `mod 5`, the cmp log is never parsed, and the dictionary is never
      ## harvested — the same additive-knob convention as `stallRounds`/
      ## `uniformSchedule`/`reVerify`. Needs no `{.covercmp.}` instrumentation
      ## on the property to be harmless when on (an uninstrumented property's
      ## cmp log is simply always empty, so the operator degrades to identity/
      ## dictionary-only, exactly like an uninstrumented `{.cover.}`-less
      ## property degrades mutation-guidance to "random fuzzing").

  FuzzReport* = object
    iterations*: int
      ## Number of `fuzzOnce` / `fuzzOnceIR` calls performed before exit.
    coverageHits*: int
      ## Distinct edges discovered across the whole run. Approximates
      ## "what fraction of the SUT did we explore."
    corpus*: FuzzCorpus
      ## Inputs that found new coverage. Variant tag matches the run's
      ## `mutationMode`; persistent across runs.
    crashes*: seq[tuple[bytes: seq[byte], message: string]]
      ## Falsifying byte-mode inputs (carries the exact bytes for repro).
      ## IR-mode crashes go to `irCrashes` instead.
    irCrashes*: seq[tuple[choices: seq[ChoiceNode], message: string]]
      ## Falsifying IR-mode inputs (carries the choice sequence).
    timedOut*: bool
      ## True iff the loop exited because `timeBudget` was hit (vs.
      ## `maxIterations`).
    droppedSeeds*: int
      ## F7 (RFC-chapulin-hardening ~line 638): count of *preloaded* seeds
      ## (`FuzzSettings.initialIRCorpus` entries, plus any resumed from the
      ## `ExampleDatabase`'s `loadCorpus`) that `captureIR` could not replay
      ## against `s` (`ok: false`) and were therefore dropped before the
      ## corpus was assembled — see `lists`' "2N+1" draw-order doc
      ## (`strategy.nim`) for exactly what makes a seed replay succeed vs.
      ## get dropped. A nonzero count tells a caller loading an external or
      ## stale corpus how many of its seeds were misaligned with the current
      ## strategy shape and silently discarded, rather than that being
      ## invisible. Scoped to preloaded seeds only: it does *not* count the
      ## single generated fallback seed `fuzz` adds when no seeds were
      ## preloaded (that seed is always well-formed by construction, never
      ## "dropped"), and it does *not* count mutants rejected mid-loop
      ## (`fuzz.nim`'s main loop `captureIR` call) — those are mutation
      ## outcomes, not seed-loading outcomes.
    dictionary*: Dictionary
      ## RFC-fuzzer-nextgen G5 deliverable 3: the auto-dictionary harvested
      ## from every non-rejected run's cmp log over the campaign — empty
      ## unless `FuzzSettings.enableI2S` is set (see that field's doc).

  Verdict* = enum
    ## What the oracle made of one run (FUZZ_PLAN D14). Generic over in-process
    ## and external targets; an external `Oracle` maps exit/signal/stderr to it.
    vOk               ## ran, nothing of interest
    vRejected         ## the input was malformed/filtered — drop from corpus
    vInteresting      ## a finding (crash / sanitizer report / differential mismatch)
    vTimedOut         ## a hang — a first-class finding, not a drop
    vResourceExceeded ## RFC-fuzzer-nextgen E1: a resource-limit kill (memory/CPU/
                       ## wall-clock). Distinct from `vInteresting` so an unbounded-
                       ## allocation non-bug doesn't flood the crash corpus. Not yet
                       ## produced anywhere at E1 — fleshed out at E2/E4 (Track E).
    vCrashed          ## RFC-fuzzer-nextgen E1: a worker-level crash (process death
                       ## the oracle never got to judge, e.g. the child died before
                       ## reporting). Distinct from `vInteresting` (an oracle-judged
                       ## finding); wiring lands with the Track E worker pool.

  CrashKind* = enum
    ## RFC-fuzzer-nextgen E1 (C1): the taxonomy `Observation.crash` is matched
    ## on. De-dup, oracle matching, and reporting key on `kind`, never parse
    ## `Observation.message` prose — `message` is a human rendering ONLY.
    ckException  ## in-process: a Nim `Defect`/`CatchableError` propagated out
                 ## of the property (includes a failed `doAssert`).
    ckSignal     ## external: the child died on a signal (SIGSEGV, SIGABRT, ...).
    ckExitCode   ## external: the child exited with a nonzero/bug status code.
    ckWinException ## external, Windows: a structured-exception code from a
                    ## crashed child. Not populated until the Windows worker
                    ## (Track E) lands — the case exists so `CrashInfo` doesn't
                    ## need another breaking shape change then.

  RespawnStormError* = object of CatchableError
    ## RFC-fuzzer-nextgen E-cleanup: raised by `run` when the steady-state
    ## respawn-storm breaker trips in its default (abort) mode — see
    ## `Orchestrator.stormWindow`/`stormBackoff`. Distinct from the (E4a,
    ## not yet built) bootstrap circuit-breaker's diagnostic: THIS one
    ## means "a worker that booted fine keeps dying the SAME way on every
    ## recycle" (an environment fault), not "no worker of the pool could
    ## ever start."

  CrashInfo* = object
    ## Typed crash identity (round-1 design fix, RFC-fuzzer-nextgen §Appendix
    ## C): before this, crash identity/dedup was a stringly-typed `message`
    ## grep. `message` is a human rendering DERIVED from the variant below —
    ## it is never itself matched on. Common field precedes the `case` per
    ## Nim's object-variant rule.
    message*: string
    case kind*: CrashKind
    of ckException:    defect*: string      ## the raising Nim Defect/exception name
    of ckSignal:        signal*: int
    of ckExitCode:      exitCode*: int
    of ckWinException:  code*: uint32

  RunResult* = object
    ## The raw mechanical result of one external run — the oracle's input (D14).
    ## Defined here (ahead of the execution contract) so `Observation` can carry it,
    ## which is what lets `differentialTarget` compose `Target`s on their raw results.
    exitCode*: int
    signal*: int            ## 0 == exited normally; else the terminating signal
    stdout*, stderr*: seq[byte]
    timedOut*: bool
    durationNs*: int64

  Observation*[T] = object
    ## The result of executing one value via a `Target` (D3): the verdict, the
    ## run's coverage, a message for crash retention, and (for external targets)
    ## the raw `RunResult` so composers like `differentialTarget` can compare children.
    verdict*: Verdict
    coverage*: Coverage
    message*: string
      ## Human-rendered crash text. Kept for backward compatibility (existing
      ## `crashKey`/report consumers read this) — DERIVED from `crash.get.message`
      ## when `crash.isSome`, never the other way around (RFC-fuzzer-nextgen E1 C1).
    crash*: Option[CrashInfo]
      ## Typed crash identity (E1 C1) — `none` for `vOk`/`vRejected` runs and for
      ## any `vInteresting`/`vTimedOut` a `Target` doesn't (yet) classify. Dedup
      ## and oracle logic should prefer this over parsing `message`.
    runResult*: RunResult

  Target*[T] = object
    ## Execute-and-observe as one round trip (D3). `inProcessTarget` runs a `prop`;
    ## `externalTarget`/`differentialTarget` (Phase 5) run a child. Closed under
    ## composition, so the `fuzz` loop is target-agnostic.
    run*: proc(x: T): Observation[T] {.closure.}

  ChoiceSeq* = seq[ChoiceNode]
    ## RFC-fuzzer-nextgen E1: alias for the choice-sequence IR a `Worker`
    ## submits/replays (Appendix C). Identical to the type the fuzz loop has
    ## always mutated (`fuzzir.nim`'s `mutateIR*` family, `captureIR` below) —
    ## named so the Worker/Orchestrator seam reads the same in prose and code.

  WorkerHandle*[T] = object
    ## RFC-fuzzer-nextgen E1 (C2): an in-flight ticket returned by
    ## `submitAsync`, carrying the input it was submitted with — so a caller
    ## (eventually the Orchestrator's completion loop) can match a later
    ## completion back to its input without a side table. E1's single-worker
    ## reference impl resolves synchronously (see `submitAsync`); a real async
    ## dispatch is Track E's worker-pool follow-on, not precluded here.
    input*: ChoiceSeq

  Worker*[T] = ref object
    ## RFC-fuzzer-nextgen E1 (C2): a dumb execute-and-observe seam — 1:1 with a
    ## process wrapper in the full design (Appendix C). At E1 the only
    ## implementation is `newInProcessWorker`, which wraps a `(Strategy[T],
    ## Target[T])` pair: `submit` replays a `ChoiceSeq` through the strategy to
    ## a value, then runs it through the target. This IS the load-bearing
    ## execution path the hot `fuzz` loop drives (via the `Orchestrator` seam,
    ## C3) — `ChoiceSeq` is the Worker's currency (Appendix C), not a
    ## materialized value, so E2a can swap in a real process worker without
    ## rewiring the loop.
    submitImpl: proc(input: ChoiceSeq): Observation[T] {.closure.}

  ConcolicOutcomeTag* = enum
    ## RFC-fuzzer-nextgen G3: a type-erased mirror of G2's
    ## `ConcolicFlipOutcome` (`smt/runtime.nim`) — fuzz.nim stays Z3-free
    ## (no `import ./symex`, so a plain `import nelli`/`import nelli/fuzz`
    ## never pulls in the Z3 dependency); the call-site macro
    ## (`fuzzmacro.nim`, which DOES import the walker) translates the real
    ## typed taxonomy into this one when it builds a `ConcolicBridgeEntry`.
    ## Not a "parallel bookkeeping object" in the S1 sense — S1's rule was
    ## about never re-deriving frontier statistics outside the one fold
    ## site; this is a dependency-boundary erasure, the same technique
    ## `WorkerEntry`'s `Observation[void]` already uses to keep this
    ## module generic-free.
    coSolved, coUnsat, coTimedOut, coUnmodelable

  ConcolicCoverageTag* = enum
    ## Mirrors G2's `ConcolicCoverageOutcome` — see `ConcolicOutcomeTag`.
    ccNotApplicable, ccIntendedCovered, ccUnrelatedCoverage

  ConcolicBridgeResult* = object
    ## RFC-fuzzer-nextgen G3: what a `ConcolicBridgeEntry` call hands back
    ## to the orchestrator — just enough to attempt admission and surface
    ## the yield taxonomy, without fuzz.nim needing the walker's own types.
    materialized*: seq[ChoiceNode]  ## empty unless outcome is coSolved
    outcome*: ConcolicOutcomeTag
    coverage*: ConcolicCoverageTag

  ConcolicBridgeEntry* = proc(trace: seq[ChoiceNode];
                              targetBranchIndex: int): ConcolicBridgeResult {.closure.}
    ## RFC-fuzzer-nextgen G3 (design-gate finding): the call-site's
    ## concolic bridge. `fuzz(...)` (fuzzmacro.nim) is the ONLY place that
    ## has a walkable typed proc symbol for the property (the same "macro
    ## captures the AST at the call site" contract E1 uses for worker
    ## re-entry) — so, exactly like `WorkerEntry`, the macro builds this
    ## closure once per call site, closing over the captured property
    ## symbol, and hands it to the `Orchestrator` (here, as a constructor
    ## parameter — no cross-process registry/lookup needed, unlike
    ## `WorkerEntry`: the concolic bridge only ever runs inside the SAME
    ## long-lived orchestrator process that already holds the closure, so
    ## there's no argv-style "find myself by id" problem to solve). `nil`
    ## (the default) makes the bridge entirely inert — see `stallRounds`.
    ## Not generic over T: `ChoiceNode`/`ConcolicBridgeResult` never
    ## mention it, so one non-generic type serves every `Orchestrator[T]`.

  Provenance* = enum
    ## RFC-fuzzer-nextgen E1: which mechanism produced an admitted input.
    ## Threads through `Orchestrator.admit` so a later ablation harness can
    ## attribute corpus growth per-mechanism. At E1 the fuzz loop drives only
    ## `pvMutation` — the other three are wired by their owning tracks (G2
    ## concolic, G5 I2S, corpus-import interop).
    pvMutation, pvConcolic, pvI2S, pvImported

  FindingId* = distinct int
    ## RFC-fuzzer-nextgen E1: a handle into the orchestrator-owned finding
    ## record (Appendix C). `AdmitResult.findingId` is set once admission and
    ## crash-finding tracking unify — RFC-fuzzer-nextgen E3a (C1) is that:
    ## `reportFinding`/`reproRate`/`divergentReproduction` read/write the
    ## record a `FindingId` handle points at.

  AdmitResult* = object
    ## RFC-fuzzer-nextgen E1 (C3): returned ONCE by `admit` — no async fields
    ## here (round-3 fix: `reproRate`/`divergentReproduction` live on the
    ## orchestrator-owned finding record, read back by `FindingId`, never
    ## smuggled onto this one-shot return).
    admitted*: bool
    findingId*: Option[FindingId]  ## set iff a finding/corpus record was opened
    provenance*: Provenance

  FindingRecord[T] = ref object
    ## RFC-fuzzer-nextgen E3a (C1): the orchestrator-owned finding record
    ## Appendix C's `reproRate`/`divergentReproduction` read back by
    ## `FindingId` handle — never smuggled onto `admit`'s one-shot
    ## `AdmitResult` (round-3 design fix). `primary` is fixed at
    ## `reportFinding` time and NEVER rewritten (round-2 depth fix: the
    ## first report is immutable); a re-verify or reproRate sample whose
    ## `CrashInfo.kind` differs is recorded into `variants` instead.
    id: FindingId
    primary: CrashInfo
    variants: seq[CrashInfo]      ## divergentReproduction: distinct kinds only
    reproHits: int                ## N
    reproTotal: int               ## M-so-far (bounded by `Orchestrator.reproSamples`)

  Orchestrator*[T] = ref object
    ## RFC-fuzzer-nextgen E1 (C3) / E3a: the singleton that owns the one
    ## frontier/corpus/dedup/scheduler in the full design (Appendix C) — "the
    ## worker pool is the `seq[Worker[T]]` it owns," not the Orchestrator
    ## itself. It drives execution through its current `Worker` (`run` is
    ## `worker.submit`, currency `ChoiceSeq` — Appendix C) and owns the
    ## coverage-admission decision (`admit`), hiding both the `Worker` and
    ## the `CoverageFrontier` behind this one seam so the fuzz loop stays
    ## execution-agnostic.
    worker: Worker[T]
    frontier: ptr CoverageFrontier
      ## Raw pointer, not a captured `var` (Nim forbids capturing a `var`
      ## param in a closure — memory-safety check). `newOrchestrator` takes
      ## `frontier` by `var` from its caller (matching `fuzz`'s own `var
      ## CoverageFrontier` parameter) and this points AT that same storage —
      ## `admit` below mutates the caller's frontier directly, not a copy.
      ## Sound as long as the `Orchestrator` doesn't outlive its caller's
      ## stack frame, true for every E1 use (constructed and consumed within
      ## one `fuzz()` call, or a test's own local `frontier`).
    spawnFreshWorker: proc(): Worker[T] {.closure.}
      ## RFC-fuzzer-nextgen E3a: the "get me a freshly spawned worker" seam —
      ## shared by admission re-verify (C2), the reproRate sampler (C1/C3),
      ## and worker recycling (C4). `nil` (the default) makes all three
      ## inert: `admit` falls back to its E1/E2 direct in-memory fold,
      ## `sampleReproduction` is a no-op, and `run` never recycles the
      ## current worker. This is the enable/disable knob's mechanism — see
      ## `reVerify` for the admission-gating half of it.
    reVerify: bool
      ## RFC-fuzzer-nextgen E3a (C2): when true (and `spawnFreshWorker` is
      ## set), `admit` re-executes `input` in a freshly spawned worker before
      ## admitting — the candidate observation becomes a cheap pre-filter
      ## only. Default `false`: `admit` keeps its exact E1/E2 direct-fold
      ## behavior, so every existing caller (including `fuzz()` itself) is
      ## byte-for-byte unchanged unless it opts in.
    reVerifyBudget: int
      ## RFC-fuzzer-nextgen E3a (C2/C1): bounded slot budget (round-3, "like
      ## shrink") shared by every fresh-worker spawn this orchestrator does
      ## for VERIFICATION purposes — both admission re-verify and reproRate
      ## sampling draw from it. Decremented per spawn; at 0, `admit`
      ## degrades to the cheap direct fold and `sampleReproduction` is a
      ## no-op, rather than either ever blocking on an unbounded spawn
      ## queue. A single-threaded orchestrator has exactly one such budget
      ## to share between the two mechanisms.
    reproSamples: int
      ## RFC-fuzzer-nextgen E3a (C1): M, the per-finding cap on
      ## `sampleReproduction` calls (Appendix C precondition-1: "bounded,
      ## asynchronous N-of-M sample").
    recycleAfterInputs: int
      ## RFC-fuzzer-nextgen E3a (C4): retire the current worker (replace it
      ## via `spawnFreshWorker`) after it has served this many inputs — `0`
      ## (the default) never auto-recycles on a count, matching pre-E3a
      ## behavior. A worker is ALSO always retired immediately after any
      ## `vCrashed` observation, regardless of this count (bounds the
      ## contamination window on the crash side unconditionally).
    workerInputsServed: int
      ## RFC-fuzzer-nextgen E3a (C4): inputs served by the CURRENT worker
      ## since it was (re)spawned.
    stormWindow: int
      ## RFC-fuzzer-nextgen E-cleanup: the steady-state respawn-storm
      ## breaker, distinct from the (E4a, not yet built) BOOTSTRAP circuit-
      ## breaker (which only catches dead-before-first-read). `0` (the
      ## default) disables it entirely — byte-for-byte pre-E-cleanup
      ## behavior. When > 0, tracks the `CrashInfo.kind` of the most recent
      ## `stormWindow` crash-triggered recycles (`recentCrashKinds`, a
      ## sliding window of CRASH EVENTS specifically, not every input —
      ## count-based rather than wall-clock, so the breaker stays fully
      ## deterministic/testable over a fabricated sequence, matching E3a's
      ## "pure algebra, not raced processes" precedent). Once that window
      ## is full AND every kind in it is IDENTICAL — crashes that are NOT
      ## diversifying, the environment-fault signature — the breaker trips:
      ## the desirable "found a good crash lineage" case has VARIED/new
      ## kinds and must never trip it.
    stormBackoff: bool
      ## RFC-fuzzer-nextgen E-cleanup: the trip ACTION. `false` (default):
      ## `run` raises `RespawnStormError` (a distinct diagnostic) the
      ## moment the breaker trips — the campaign aborts rather than burn
      ## process-creation cost respawning into the same fault forever.
      ## `true`: `run` does NOT raise — it still recycles (the campaign
      ## continues, degraded) and instead only sets `stormTripped`/bumps
      ## `stormBackoffLevel`, for a caller/driver to read back and pace its
      ## own respawn loop (e.g. sleep an increasing backoff between `run`
      ## calls) — this layer never sleeps itself, keeping it deterministic.
    recentCrashKinds: seq[CrashKind]
      ## RFC-fuzzer-nextgen E-cleanup: the sliding window `stormWindow`
      ## bounds — oldest evicted as new crashes arrive.
    stormTripped: bool
      ## RFC-fuzzer-nextgen E-cleanup: true iff the CURRENT window (once
      ## full) is non-diversifying. Continuously recomputed on every
      ## crash — a later diversifying crash slides a non-diversifying
      ## entry out and un-trips it (self-correcting, matching "steady
      ## state": this is about the campaign's CURRENT crash character, not
      ## a one-shot latch).
    stormDiagnostic: string
      ## RFC-fuzzer-nextgen E-cleanup: set alongside `stormTripped`; empty
      ## when not tripped. The distinct diagnostic text (also `raise`'s
      ## message in abort mode).
    stormBackoffLevel: int
      ## RFC-fuzzer-nextgen E-cleanup: incremented each time `run` observes
      ## the breaker tripped in `stormBackoff` mode — a caller/driver's
      ## signal to pace/backoff progressively rather than respawn in a
      ## tight loop. Never read or acted on by this layer itself.
    concolicBridge: ConcolicBridgeEntry
      ## RFC-fuzzer-nextgen G3: the call-site concolic bridge (see
      ## `ConcolicBridgeEntry`'s doc) — `nil` (the default) makes
      ## `tryConcolicBridge` an inert no-op, matching every other
      ## additive-knob convention here.
    stallRounds: int
      ## RFC-fuzzer-nextgen G3: K — invoke the concolic bridge once the
      ## shared frontier has gone `stallRounds` admits with no coverage
      ## improvement (`CoverageFrontier.stalled`). `0` (the default)
      ## disables stall detection entirely, independent of whether
      ## `concolicBridge` is set — so a caller can wire the bridge without
      ## yet opting into automatic invocation.
    concolicMaxBranchAttempts: int
      ## RFC-fuzzer-nextgen G3: bounded number of recorded branch-trace
      ## indices `tryConcolicBridge` will offer the bridge per stall
      ## round (0, 1, 2, ... in encounter order) before giving up for this
      ## round — mirrors G2's own `maxRelaxationAttempts` bounding
      ## philosophy (a fixed, deterministic attempt count, never an
      ## unbounded/exhaustive search).
    findings: seq[FindingRecord[T]]
    findingByKind: Table[CrashKind, FindingId]
      ## RFC-fuzzer-nextgen E3a (C1): dedup index — a finding is opened once
      ## per distinct primary `CrashKind`; a later `reportFinding` call for
      ## an already-open kind returns the existing handle.
    db: ExampleDatabase
      ## RFC-fuzzer-nextgen E3b (C4): the orchestrator's single `.bin`
      ## write funnel (F-1 invariant). `saveCorpus`/`loadCorpus` already
      ## bypass this — the corpus delta log (`db.nim`) is its own
      ## single-writer transport, split out precisely so it never shares a
      ## rewrite target with `.bin`. What's left racing on `.bin`
      ## (primary+secondary) is >1 *shrink* slot RMW-ing the same file
      ## concurrently (E0-findings mandate item 4) — closed the same way:
      ## a shrink job never constructs its own `ExampleDatabase` or calls
      ## `save`/`remove`/`saveSecondary` directly, it calls
      ## `requestSave`/`requestRemove`/`requestSaveSecondary` below, which
      ## apply through this ONE handle the orchestrator was constructed
      ## with. Zero value (`db.saveImpl == nil`) makes every funnel proc a
      ## no-op — the default, byte-for-byte pre-E3b behavior for a caller
      ## that never opts in.

proc `==`*(a, b: FindingId): bool {.borrow.}
  ## RFC-fuzzer-nextgen E3a (C1): equality on the handle — needed the moment
  ## a caller wants to compare two `reportFinding`/`AdmitResult.findingId`
  ## results (e.g. to confirm dedup-by-kind returned the SAME handle).

proc mutateByteFlip(rng: var SplitMix64, base: seq[byte]): seq[byte] =
  ## One-bit-flip mutation. Picks a random bit position in `base` and
  ## flips it. The simplest AFL-style mutation; lots of crashes are
  ## one bit away from a benign input.
  result = base
  if result.len == 0: return
  let idx = int(rng.next mod uint64(result.len))
  let bit = uint64(rng.next mod 8'u64)
  result[idx] = result[idx] xor byte(1'u8 shl bit)

proc mutateByteReplace(rng: var SplitMix64, base: seq[byte]): seq[byte] =
  ## Replace a random byte with a random value. Bigger steps than
  ## bit-flip; useful for crossing wide integer thresholds.
  result = base
  if result.len == 0: return
  let idx = int(rng.next mod uint64(result.len))
  result[idx] = byte(rng.next and 0xff'u64)

proc randomBytes(rng: var SplitMix64, n: int): seq[byte] =
  result = newSeq[byte](n)
  for i in 0 ..< n:
    result[i] = byte(rng.next and 0xff'u64)

proc captureIR[T](s: Strategy[T], choices: seq[ChoiceNode]):
    tuple[ok: bool, choices: seq[ChoiceNode], spans: seq[Span]] =
  ## Replay `choices` through `s` to recover the structural spans the
  ## strategy emits. Used during corpus promotion: a mutator hands us a
  ## new choice sequence; before the loop can splice/delete against it
  ## later, it needs the spans the strategy *would* draw under those
  ## choices. Falls back to `(false, ...)` on misalignment (the mutant
  ## is structurally invalid for this strategy and gets dropped).
  var ds = newReplaySource(choices)
  try:
    discard s.generate(ds)
  except Rejection, Overrun:
    return (ok: false, choices: choices, spans: @[])
  except CatchableError, Defect:
    return (ok: false, choices: choices, spans: @[])
  (ok: true, choices: ds.recorded, spans: ds.spans)

proc observeInProcess[T](prop: proc(x: T); probe: CoverageProbe; x: T): Observation[T] =
  ## Shared execute-and-observe body (RFC-fuzzer-nextgen E1 C1/C2): reset the
  ## {.cover.} bitmap (per-run isolation — the probe is `resetsPerRun`, D8), run
  ## `prop`, map the same exceptions `fuzzOnce` does to a `Verdict` AND a typed
  ## `CrashInfo` (`kind: ckException` — the in-process taxonomy, C1), snapshot
  ## the bitmap, and restore the prior coverage mode. Used by both
  ## `inProcessTarget` (value-level) and the in-process `Worker` (C2,
  ## choice-sequence-level) so the exception→Verdict/CrashInfo mapping lives
  ## in exactly one place.
  let prior = currentCoverageMode()
  setCoverageMode(cmRecording)
  resetCoverage()
  # RFC-fuzzer-nextgen G4: the cmp-log's OWN recording gate, toggled at the
  # SAME per-run boundary as coverage's — a `{.covercmp.}`'d property only
  # ever gets `logCmp` calls injected in the first place, so enabling this
  # unconditionally (mirroring `coverageMode`) costs nothing for the common
  # case of a property that never used the pragma (its body has no `logCmp`
  # calls to gate at all).
  let priorCmp = currentCmpLogMode()
  setCmpLogMode(clRecording)
  resetCmpLog()
  var verdict = vOk
  var msg = ""
  var crash = none(CrashInfo)
  # RFC-fuzzer-nextgen S1: real wall-clock timing around the run — this is
  # the ONLY execution-cost signal S1's `entropicEnergy` gets for the
  # in-process path (the overwhelming majority of `fuzz()` callers), so
  # measuring it here (rather than leaving `runResult.durationNs` at its
  # external-target-only zero default) is what makes the exec-cost term
  # real rather than dead for the common case.
  let startedAt = getMonoTime()
  try:
    prop(x)
  except Rejection:
    verdict = vRejected
  except FalsifiedError as e:
    verdict = vInteresting; msg = e.msg
    crash = some(CrashInfo(kind: ckException, defect: $e.name, message: msg))
  except CatchableError as e:
    verdict = vInteresting; msg = $e.name & ": " & e.msg
    crash = some(CrashInfo(kind: ckException, defect: $e.name, message: msg))
  except Defect as e:
    verdict = vInteresting; msg = "crashed: " & $e.name & ": " & e.msg
    crash = some(CrashInfo(kind: ckException, defect: $e.name, message: msg))
  let elapsedNs = (getMonoTime() - startedAt).inNanoseconds
  let cov = probe.read()
  setCoverageMode(prior)
  setCmpLogMode(priorCmp)
  Observation[T](verdict: verdict, coverage: cov, message: msg, crash: crash,
                 runResult: RunResult(durationNs: elapsedNs))

proc inProcessTarget*[T](prop: proc(x: T)): Target[T] =
  ## A `Target` over an in-process property (FUZZ_PLAN D3). The default target
  ## for `fuzz`, preserving the in-process behavior of the shipped `fuzzWith*`
  ## loops. See `observeInProcess` for the per-run mechanics.
  let probe = inProcessProbe()
  Target[T](run: proc(x: T): Observation[T] = observeInProcess(prop, probe, x))

proc submit*[T](w: Worker[T]; input: ChoiceSeq): Observation[T] =
  ## Blocking convenience wrapper (Appendix C) over `submitAsync` — E1's
  ## single-worker reference impl; `forAll`'s future Pool-of-1 (U0) use is the
  ## other sanctioned caller of this synchronous form.
  w.submitImpl(input)

proc submitAsync*[T](w: Worker[T]; input: ChoiceSeq): WorkerHandle[T] =
  ## RFC-fuzzer-nextgen E1 (C2): NOT a real async dispatch yet — no worker
  ## pool exists to dispatch to. Records the input as an in-flight ticket;
  ## `submit` above resolves it synchronously. A future multi-worker
  ## Orchestrator replaces this body with a real non-blocking submit and
  ## drives completions via `poll`; the signature is shaped so that swap
  ## doesn't touch call sites.
  WorkerHandle[T](input: input)

proc newWorker*[T](submitImpl: proc(input: ChoiceSeq): Observation[T] {.closure.}): Worker[T] =
  ## RFC-fuzzer-nextgen E2a (C4): the general `Worker[T]` constructor over a
  ## raw submit closure. `submitImpl` stays a private field of `Worker[T]` —
  ## a module OUTSIDE fuzz.nim (e.g. `fuzzworker.nim`'s real process
  ## `newProcessWorker`) cannot construct `Worker[T](submitImpl: ...)`
  ## directly, so a public constructor is the seam. `newInProcessWorker`
  ## below is this module's own use of it.
  Worker[T](submitImpl: submitImpl)

proc choiceSeqTargetWorker[T](s: Strategy[T]; target: Target[T]): Worker[T] =
  ## RFC-fuzzer-nextgen E1/E5: the shared ChoiceSeq->value->`Target.run`
  ## bridge — a `Worker[T]` over ANY `Target[T]`, in-process (E1) or an
  ## out-of-process `externalTarget` (E5). `submit` replays `input` — a
  ## `ChoiceSeq`, the Worker's currency per Appendix C — through `s` to a
  ## value, then runs it via `target.run`. An `Overrun`/`Rejection` raised by
  ## `s.generate` (too-short or filtered choices — generation-time rejection)
  ## is caught HERE and mapped to a `vRejected` `Observation` rather than
  ## escaping `submit`; this is behavior-identical to the fuzz loop's
  ## pre-refactor `if not generated: continue` skip, now folded into the same
  ## `verdict == vRejected` check the loop already used for a target-level
  ## rejection. Wrapping whatever `target` the caller supplies (rather than a
  ## raw `prop`) is what lets a stub/custom `Target[T]` — or `externalTarget`
  ## itself — keep working once routed through the Worker.
  newWorker(proc(input: ChoiceSeq): Observation[T] =
    var ds = newReplaySource(input)
    var x: T
    try:
      x = s.generate(ds)
    except Rejection, Overrun:
      return Observation[T](verdict: vRejected)
    target.run(x))

proc newInProcessWorker*[T](s: Strategy[T]; target: Target[T]): Worker[T] =
  ## The in-process `Worker` (C2): `choiceSeqTargetWorker` over an in-process
  ## `Target[T]` (typically `inProcessTarget`, but any `Target[T]` composes).
  choiceSeqTargetWorker(s, target)

proc newOrchestrator*[T](worker: Worker[T]; frontier: var CoverageFrontier;
                         spawnFreshWorker: proc(): Worker[T] {.closure.} = nil;
                         reVerify = false; reVerifyBudget = 8; reproSamples = 5;
                         recycleAfterInputs = 0;
                         db: ExampleDatabase = ExampleDatabase();
                         stormWindow = 0; stormBackoff = false;
                         concolicBridge: ConcolicBridgeEntry = nil;
                         stallRounds = 0;
                         concolicMaxBranchAttempts = 8): Orchestrator[T] =
  ## RFC-fuzzer-nextgen E2a (C4) / E3a: the general `Orchestrator` constructor
  ## over an ARBITRARY `Worker[T]` — E1's in-process worker and E2a's real
  ## `newProcessWorker` (fuzzworker.nim) drive identically through here; the
  ## `(s, target, frontier)` overload below is sugar over this for the
  ## in-process case. `admit` mutates the exact `CoverageFrontier` passed
  ## in, the same one a caller reads back via `frontier.coveredEdges`.
  ##
  ## `spawnFreshWorker`/`reVerify`/`reVerifyBudget`/`reproSamples`/
  ## `recycleAfterInputs` are the E3a freshness-machinery knobs — every one
  ## defaults to its pre-E3a-equivalent no-op value (`spawnFreshWorker: nil`,
  ## `reVerify: false`, `recycleAfterInputs: 0`), so an existing call site
  ## naming only `(worker, frontier)` is byte-for-byte unchanged. Opting in
  ## requires supplying `spawnFreshWorker` AND `reVerify: true` (or calling
  ## `sampleReproduction`/relying on recycling) explicitly.
  ##
  ## `db` (E3b C4, default the zero-value `ExampleDatabase()` — every
  ## closure field `nil`) is the F-1 single-writer `.bin` handle:
  ## constructed ONCE here, by whichever caller owns the orchestrator, and
  ## never re-constructed by a worker slot or shrink job. See
  ## `requestSave`/`requestRemove`/`requestSaveSecondary`.
  ##
  ## `stormWindow`/`stormBackoff` (E-cleanup) are the steady-state respawn-
  ## storm breaker's knobs — `stormWindow: 0` (default) disables it, same
  ## additive-knob convention as every other E3a/E-cleanup parameter here.
  Orchestrator[T](worker: worker, frontier: addr frontier,
                  spawnFreshWorker: spawnFreshWorker, reVerify: reVerify,
                  reVerifyBudget: reVerifyBudget, reproSamples: reproSamples,
                  recycleAfterInputs: recycleAfterInputs, db: db,
                  stormWindow: stormWindow, stormBackoff: stormBackoff,
                  concolicBridge: concolicBridge, stallRounds: stallRounds,
                  concolicMaxBranchAttempts: concolicMaxBranchAttempts)

proc newOrchestrator*[T](s: Strategy[T]; target: Target[T]; frontier: var CoverageFrontier;
                         spawnFreshWorker: proc(): Worker[T] {.closure.} = nil;
                         reVerify = false; reVerifyBudget = 8; reproSamples = 5;
                         recycleAfterInputs = 0;
                         db: ExampleDatabase = ExampleDatabase();
                         stormWindow = 0; stormBackoff = false;
                         concolicBridge: ConcolicBridgeEntry = nil;
                         stallRounds = 0;
                         concolicMaxBranchAttempts = 8): Orchestrator[T] =
  ## RFC-fuzzer-nextgen E1 (C3) / E3a: a single-worker reference `Orchestrator`
  ## owning one in-process `Worker` built from `(s, target)` for execution.
  ## `worker` stands in for a `seq[Worker[T]]` pool; it is the one execution
  ## path routed through here — the fuzz loop never calls `target.run`
  ## directly once routed through the `Orchestrator` (E1 stage-1 fix: the
  ## Worker seam is the load-bearing path, not a dead parallel one). See the
  ## `(worker, frontier)` overload above for the E3a/E-cleanup knobs and
  ## E3b's `db`.
  newOrchestrator(newInProcessWorker(s, target), frontier, spawnFreshWorker,
                  reVerify, reVerifyBudget, reproSamples, recycleAfterInputs, db,
                  stormWindow, stormBackoff, concolicBridge, stallRounds,
                  concolicMaxBranchAttempts)

proc stormTripped*[T](o: Orchestrator[T]): bool =
  ## RFC-fuzzer-nextgen E-cleanup: true iff the steady-state respawn-storm
  ## breaker currently sees a full, non-diversifying crash-kind window. Only
  ## ever meaningful (can only ever be true) when `stormWindow > 0` and
  ## `stormBackoff == true` — in abort mode `run` raises instead of
  ## returning, so a caller wouldn't observe this flag at the trip moment.
  o.stormTripped

proc stormDiagnostic*[T](o: Orchestrator[T]): string =
  ## RFC-fuzzer-nextgen E-cleanup: the distinct diagnostic text set
  ## alongside `stormTripped` (also `RespawnStormError.msg` in abort mode).
  ## Empty when not tripped.
  o.stormDiagnostic

proc stormBackoffLevel*[T](o: Orchestrator[T]): int =
  ## RFC-fuzzer-nextgen E-cleanup: how many times `run` has observed the
  ## breaker tripped while in `stormBackoff` mode — a caller/driver's own
  ## signal to pace an increasing backoff between respawns. This layer
  ## never sleeps itself; it only counts.
  o.stormBackoffLevel

proc run*[T](o: Orchestrator[T]; input: ChoiceSeq): Observation[T] =
  ## Execute `input` — a replayable `ChoiceSeq`, the Worker's currency
  ## (Appendix C) — on the orchestrator's CURRENT Worker. The
  ## execution-agnostic entry point the fuzz loop uses instead of replaying
  ## `input` itself and calling `target.run` directly. Generation-time
  ## rejection is already folded into `vRejected` by `worker.submit`, so
  ## callers only need the one `verdict == vRejected` check.
  ##
  ## RFC-fuzzer-nextgen E3a (C4): worker recycling. When `spawnFreshWorker`
  ## is configured, the current worker is retired (replaced via
  ## `spawnFreshWorker`) immediately after ANY `vCrashed` observation, or
  ## once it has served `recycleAfterInputs` inputs (if that count is > 0) —
  ## bounding the contamination window a long-lived worker can accumulate.
  ## `spawnFreshWorker == nil` (the default) leaves this proc's behavior
  ## byte-for-byte pre-E3a: the same worker serves every `run` call.
  ##
  ## RFC-fuzzer-nextgen E-cleanup: the steady-state respawn-storm breaker.
  ## Distinct from the (E4a, not yet built) BOOTSTRAP circuit-breaker, which
  ## only catches dead-before-first-read — this one catches a worker that
  ## boots fine and then dies SYSTEMICALLY on every recycle. Every
  ## crash-triggered recycle's `CrashInfo.kind` slides into a `stormWindow`-
  ## sized window; once that window is full and every kind in it is
  ## IDENTICAL (not diversifying — an environment fault, not a productive
  ## crash-finding campaign, which has varied/new kinds), the breaker trips:
  ## `stormBackoff == false` (default) raises `RespawnStormError`;
  ## `stormBackoff == true` degrades instead — `run` keeps returning
  ## normally and the campaign continues, with `stormTripped`/
  ## `stormBackoffLevel` set for a caller/driver to pace its own respawn
  ## loop. `stormWindow == 0` (the default) leaves this whole block inert.
  result = o.worker.submit(input)
  if o.spawnFreshWorker != nil:
    inc o.workerInputsServed
    let crashed = result.verdict == vCrashed
    if crashed and o.stormWindow > 0 and result.crash.isSome:
      o.recentCrashKinds.add result.crash.get.kind
      if o.recentCrashKinds.len > o.stormWindow:
        o.recentCrashKinds = o.recentCrashKinds[1 .. ^1]
      if o.recentCrashKinds.len == o.stormWindow:
        var nonDiversifying = true
        for k in o.recentCrashKinds:
          if k != o.recentCrashKinds[0]:
            nonDiversifying = false
            break
        if nonDiversifying:
          o.stormTripped = true
          o.stormDiagnostic = "respawn-storm: " & $o.stormWindow &
            " consecutive " & $o.recentCrashKinds[0] &
            " crashes with no diversification (environment fault suspected, not a crash-finding campaign)"
          if o.stormBackoff:
            inc o.stormBackoffLevel
          else:
            raise newException(RespawnStormError, o.stormDiagnostic)
        else:
          o.stormTripped = false
          o.stormDiagnostic = ""
    let mustRecycle = crashed or
      (o.recycleAfterInputs > 0 and o.workerInputsServed >= o.recycleAfterInputs)
    if mustRecycle:
      o.worker = o.spawnFreshWorker()
      o.workerInputsServed = 0

# --- .bin single-writer funnel (E3b C4) ---------------------------------------
#
# F-1 invariant (E0-findings): `directoryBasedDatabase(path)`'s constructor
# sweeps stray `.tmp.*` files on startup, so two CONCURRENT constructions
# against the same directory race on that sweep (one's in-flight tmp file can
# get deleted out from under it). The centralized orchestrator already
# implies a single long-lived handle — `db` above is constructed exactly
# once, by whoever builds the `Orchestrator` (never by a worker slot) — and
# these three procs are the ONLY sanctioned way anything downstream (a shrink
# job's `save`/`remove`/`saveSecondary`) touches `.bin`. Corpus writes never
# go through here: `saveCorpus`/`loadCorpus` are already single-writer via
# the corpus delta log (`db.nim`, E3b C1-C3), which is a different file
# entirely and was split out precisely so it never shares a rewrite target
# with `.bin`. What's left racing on `.bin` (primary+secondary) is >1 shrink
# slot RMW-ing it concurrently (E0-findings mandate item 4) — funneling every
# shrink write through this one already-constructed handle closes it the same
# way the corpus split closed race (a): one writer per file, no new lock.
#
# A zero-value `db` (every closure field `nil`, the default from
# `newOrchestrator`) makes all three of these silent no-ops — a caller that
# never opts in sees no behavior change.

proc requestSave*[T](o: Orchestrator[T]; testId: string; choices: ChoiceSeq;
                     maxEntries = 16) =
  ## A shrink job's `.bin` write, funneled through the orchestrator's one
  ## `db` handle instead of the caller constructing (or reaching for) its
  ## own `ExampleDatabase` on the shared directory.
  if o.db.saveImpl != nil: o.db.save(testId, choices, maxEntries)

proc requestRemove*[T](o: Orchestrator[T]; testId: string; choices: ChoiceSeq) =
  if o.db.removeImpl != nil: o.db.remove(testId, choices)

proc requestSaveSecondary*[T](o: Orchestrator[T]; testId: string;
                              entries: openArray[ScoredEntry]; maxEntries = 16) =
  if o.db.saveSecondaryImpl != nil: o.db.saveSecondary(testId, entries, maxEntries)

proc hasDb*[T](o: Orchestrator[T]): bool =
  ## Whether this orchestrator was constructed with a real `db` (vs. the
  ## zero-value default) — lets a caller tell "funnel is wired" from "no
  ## database configured" without probing closure fields itself.
  o.db.saveImpl != nil

proc reportFinding*[T](o: Orchestrator[T]; crash: CrashInfo): FindingId =
  ## RFC-fuzzer-nextgen E3a (C1): open (or return the existing) finding
  ## record for `crash.kind` — crash REPORTING is never gated by re-verify
  ## (§0 precondition 1): this is the un-gated "first observation" hook a
  ## caller (the fuzz loop, or `admit`'s re-verify path below) uses the
  ## moment it sees a crashing `Observation`, independent of whether that
  ## input ever earns a corpus slot. Dedup is by `CrashKind` — a second call
  ## for an already-open kind returns the SAME handle, `reportFinding` is
  ## idempotent per kind so a caller need not pre-check. The primary
  ## `CrashInfo` is fixed at open time and NEVER rewritten afterward (round-2
  ## depth fix: the first report is immutable) — a later divergent kind is
  ## recorded via `recordDivergentReproduction` instead, never by mutating
  ## `primary`. Seeds `reproTotal`/`reproHits` at 1/1: the observation that
  ## opened the finding IS its first successful reproduction sample, so a
  ## freshly opened finding's `reproRate` reads `1.0` ("always") until a
  ## flaky `sampleReproduction` call lowers it.
  if crash.kind in o.findingByKind:
    return o.findingByKind[crash.kind]
  let id = FindingId(o.findings.len)
  o.findings.add FindingRecord[T](id: id, primary: crash, reproHits: 1, reproTotal: 1)
  o.findingByKind[crash.kind] = id
  id

proc recordDivergentReproduction*[T](o: Orchestrator[T]; id: FindingId; variant: CrashInfo) =
  ## RFC-fuzzer-nextgen E3a (C1/C2): record a re-verify or reproRate-sample
  ## observation whose `CrashInfo.kind` differs from the finding's immutable
  ## `primary` — never overwrites `primary` (round-2 depth fix), and is
  ## idempotent per distinct variant kind (round-3: the dedup index is a SET
  ## of observed variants, not a growing duplicate log).
  let rec = o.findings[int(id)]
  for v in rec.variants:
    if v.kind == variant.kind: return
  rec.variants.add variant

proc reproRate*[T](o: Orchestrator[T]; id: FindingId): float =
  ## RFC-fuzzer-nextgen E3a (C1) / Appendix C: N/M bounded reproduction
  ## sample rate for a finding; `1.0` == always reproduced. A finding with no
  ## samples at all (`reproTotal == 0`; unreachable via `reportFinding`,
  ## which always seeds 1/1, but defensive) reads `1.0`.
  let rec = o.findings[int(id)]
  if rec.reproTotal == 0: return 1.0
  rec.reproHits.float / rec.reproTotal.float

proc divergentReproduction*[T](o: Orchestrator[T]; id: FindingId): seq[CrashInfo] =
  ## RFC-fuzzer-nextgen E3a (C1) / Appendix C: the observed variant
  ## `CrashInfo` set for a finding — empty until a re-verify or reproRate
  ## sample diverges from the primary kind.
  o.findings[int(id)].variants

proc sampleReproduction*[T](o: Orchestrator[T]; id: FindingId; input: ChoiceSeq): bool =
  ## RFC-fuzzer-nextgen E3a (C1/C3) / Appendix C precondition-1 (round-2
  ## depth fix): one bounded, off-the-hot-path reproduction sample — spawns a
  ## FRESH worker (never the campaign's live worker), re-executes `input`,
  ## and folds the outcome into the finding's N/M `reproRate`. This is a
  ## DISTINCT mechanism from `admit`'s admission re-verify (C2): "N-of-M
  ## fresh replays is not a by-product of the single admission re-verify; it
  ## is an explicit sampler" (RFC §0). Bounded two ways: `reproSamples` caps
  ## M PER FINDING, and every spawn also draws from the orchestrator's
  ## shared `reVerifyBudget` slot count — the same bounded resource
  ## admission re-verify draws from (both are "spawn one fresh worker to
  ## verify," and a single-threaded orchestrator has exactly one budget to
  ## share). Returns `false` (a no-op — never blocks or stalls) when the
  ## finding id is unknown, `M` is already reached, `spawnFreshWorker` isn't
  ## configured, or the shared budget is exhausted.
  if int(id) < 0 or int(id) >= o.findings.len: return false
  let rec = o.findings[int(id)]
  if rec.reproTotal >= o.reproSamples: return false
  if o.spawnFreshWorker == nil: return false
  if o.reVerifyBudget <= 0: return false
  dec o.reVerifyBudget
  let w = o.spawnFreshWorker()
  let obs = w.submit(input)
  inc rec.reproTotal
  if obs.crash.isSome and obs.crash.get.kind == rec.primary.kind:
    inc rec.reproHits
  elif obs.crash.isSome:
    recordDivergentReproduction(o, id, obs.crash.get)
  true

proc admit*[T](o: Orchestrator[T]; input: ChoiceSeq; candidate: Observation[T];
               provenance = pvMutation): AdmitResult =
  ## RFC-fuzzer-nextgen E1 (C3) / E3a (C2): admission decision for `input`.
  ##
  ## Default (`reVerify == false`, or no `spawnFreshWorker` configured): a
  ## direct in-memory frontier fold over the CANDIDATE's own coverage —
  ## byte-for-byte the E1/E2 behavior, so `fuzz()` and every existing caller
  ## that doesn't opt in are unchanged.
  ##
  ## Opted in (`reVerify == true` AND `spawnFreshWorker` set): re-verify
  ## GATES ADMISSION, never REPORTING (RFC §0 precondition 1) — a crash is
  ## already reported by the caller off the CANDIDATE observation the moment
  ## it's seen, independent of this call's outcome. This proc only decides
  ## whether `input` earns a corpus/frontier slot, and that decision is
  ## AUTHORITATIVE from a freshly spawned worker's re-execution of `input`
  ## (§0 precondition 2) — a contaminated candidate that claimed
  ## `vInteresting`/new coverage is silently discarded here if the fresh
  ## worker doesn't confirm it. The candidate's own coverage is used ONLY as
  ## a cheap pre-filter (`score`, non-mutating) so an ordinary, boring run
  ## never pays for a fresh spawn. A kind-mismatch between the candidate's
  ## crash and the fresh re-verify's is recorded as a `divergentReproduction`
  ## variant on the finding, never overwriting the immutable primary
  ## (`reportFinding`/`recordDivergentReproduction`, round-2 depth fix).
  ##
  ## `provenance` (RFC-fuzzer-nextgen G3): which mechanism produced `input`
  ## — defaults to `pvMutation` (byte-for-byte unchanged for every existing
  ## caller); the concolic bridge (`tryConcolicBridge`) passes `pvConcolic`
  ## so a re-verified concolic seed's `AdmitResult`/corpus entry carries
  ## that attribution through to the SAME frontier-fold/energy machinery
  ## every other admission uses.
  if not o.reVerify or o.spawnFreshWorker == nil:
    let a = o.frontier[].admit(candidate.coverage)
    return AdmitResult(admitted: a.interesting, findingId: none(FindingId), provenance: provenance)
  let candidateLooksInteresting =
    score(o.frontier[], candidate.coverage) > 0 or
    candidate.verdict in {vInteresting, vTimedOut, vCrashed}
  if not candidateLooksInteresting:
    return AdmitResult(admitted: false, findingId: none(FindingId), provenance: provenance)
  if o.reVerifyBudget <= 0:
    # Bounded slot budget exhausted (round-3): never stall on an unbounded
    # spawn queue — degrade to the cheap direct fold instead.
    let a = o.frontier[].admit(candidate.coverage)
    return AdmitResult(admitted: a.interesting, findingId: none(FindingId), provenance: provenance)
  dec o.reVerifyBudget
  let freshWorker = o.spawnFreshWorker()
  let freshObs = freshWorker.submit(input)
  # The fresh observation is authoritative for everything persisted — the
  # candidate's coverage is NEVER folded into the frontier on this path.
  let a = o.frontier[].admit(freshObs.coverage)
  var findingId = none(FindingId)
  if candidate.crash.isSome:
    let fid = reportFinding(o, candidate.crash.get)
    findingId = some(fid)
    if freshObs.crash.isSome and freshObs.crash.get.kind != candidate.crash.get.kind:
      recordDivergentReproduction(o, fid, freshObs.crash.get)
  AdmitResult(admitted: a.interesting, findingId: findingId, provenance: provenance)

proc tryConcolicBridge*[T](o: Orchestrator[T]; trace: ChoiceSeq
                           ): tuple[ar: AdmitResult, choices: ChoiceSeq, obs: Observation[T]] =
  ## RFC-fuzzer-nextgen G3 (deliverables 2/3): on a shared-frontier stall,
  ## hand `trace` — a border corpus entry the caller selected — to the
  ## call-site's concolic bridge, admitting the first materialized seed
  ## that earns a corpus slot.
  ##
  ## Inert (returns a not-admitted `AdmitResult` without ever touching the
  ## bridge or the frontier) unless BOTH `concolicBridge` is configured
  ## AND `stallRounds > 0` AND the shared frontier is currently stalled
  ## (`CoverageFrontier.stalled`, reading the ONE orchestrator-wide
  ## `FrontierStats` — never a per-worker view, per G3's round-2 depth
  ## fix). This is the "select a border input, invoke the bridge, feed
  ## results back through re-verification into the corpus" mechanism
  ## (RFC §G-concolic step order): the walker's own trace identifies which
  ## recorded branch to flip, not the frontier/coverage map (bitmap
  ## collisions have no adjacency concept) — so this tries a bounded
  ## sequence of recorded branch-trace indices (0, 1, 2, ..., up to
  ## `concolicMaxBranchAttempts`, mirroring G2's own bounded-attempt
  ## philosophy) and takes the first one whose materialized seed
  ## RE-VERIFIES as admissible.
  ##
  ## Every admitted seed is fed through the EXACT SAME `orchestrator.run`
  ## + `admit(..., provenance = pvConcolic)` path a mutation-admitted
  ## candidate uses — so it earns real S1 Entropic energy the moment its
  ## caller folds it into the corpus bookkeeping the same way (no separate
  ## G3b placeholder-energy path exists to need rewiring later).
  result.ar = AdmitResult(admitted: false, findingId: none(FindingId), provenance: pvConcolic)
  if o.concolicBridge == nil or o.stallRounds <= 0: return
  if not stalled(o.frontier[], o.stallRounds): return
  for branchIdx in 0 ..< o.concolicMaxBranchAttempts:
    let flip = o.concolicBridge(trace, branchIdx)
    if flip.outcome != coSolved or flip.materialized.len == 0: continue
    let obs = o.run(flip.materialized)
    if obs.verdict == vRejected: continue
    let ar = admit(o, flip.materialized, obs, provenance = pvConcolic)
    if ar.admitted:
      return (ar: ar, choices: flip.materialized, obs: obs)

proc coverageFingerprint*(c: Coverage): string =
  ## A stable key over the SET of covered slots — the default `crashKey` (D11): two
  ## crashes reaching the same novel edges are likely one bug.
  var h = 2166136261'u32
  for i in 0 ..< c.counters.len:
    if c.counters[i] > 0'u8:
      h = (h xor uint32(i and 0xffff)) * 16777619'u32
      h = (h xor uint32((i shr 16) and 0xffff)) * 16777619'u32
  $h

proc defaultCrashKey(cov: Coverage; message: string): string =
  ## Crash identity (FUZZ_PLAN 6a) when the user supplies no `crashKey`: the
  ## coverage edge-set fingerprint plus the message. The message carries the
  ## crash signal/exit for external targets and the exception text in-process, so
  ## two genuinely different bugs at the same site (or with no coverage at all)
  ## still separate. Keyed on observable behavior, not input bytes → shrinker-safe.
  coverageFingerprint(cov) & "\x00" & message

proc defaultCrashKey(cov: Coverage; message: string; crash: Option[CrashInfo]): string =
  ## RFC-fuzzer-nextgen E1 (C1): the loop-internal default key, folding
  ## `crash.kind` in on top of `defaultCrashKey(cov, message)` so two crashes
  ## with the same coverage+message but a different `CrashKind` (e.g. a
  ## `ckSignal` and a `ckExitCode` that happen to render the same message)
  ## don't collide. Additive-only: an `Observation` with no `crash` (every
  ## pre-C1 caller, and any stub `Target` that never sets the field) produces
  ## the EXACT same string as the two-argument overload above, so existing
  ## `crashKey`/dedup pins (`tfuzzdedup`, `tfuzzstopcrash`) are untouched. The
  ## user-facing `FuzzSettings.crashKey` override keeps the plain
  ## `(cov, message)` signature — this overload is internal, used only when
  ## no override is supplied.
  result = defaultCrashKey(cov, message)
  if crash.isSome:
    result.add "\x00" & $crash.get.kind

proc energyWeightedIndex(rng: var SplitMix64; energy: seq[float]): int =
  ## Pick a corpus index with probability proportional to its energy (6c power
  ## schedule). Falls back to uniform if all energy is zero. Deterministic in `rng`.
  var total = 0.0
  for e in energy: total += e
  if total <= 0.0: return int(rng.next mod uint64(energy.len))
  let r = (rng.next.float / 18446744073709551616.0) * total   # u64 range → [0,total)
  var acc = 0.0
  for i, e in energy:
    acc += e
    if r < acc: return i
  energy.high

proc minimalCovering*(entries: seq[seq[ChoiceNode]]; covs: seq[Coverage]): seq[seq[ChoiceNode]] =
  ## Greedy set cover (6c corpus minimization): the fewest entries whose covered
  ## edges still union to the whole corpus's edge set. Entries covering nothing
  ## (e.g. unrun seeds) drop out. Deterministic: ties break to the lowest index.
  ##
  ## F3 (RFC-chapulin-hardening): exported so callers can minimize an external
  ## corpus offline (entry choice-IRs + their observed `Coverage`) without
  ## driving a full `fuzz` run — the same greedy set-cover the in-loop
  ## `minimizeCorpus` path uses.
  var remaining = initHashSet[int]()
  for c in covs:
    for i in 0 ..< c.counters.len:
      if c.counters[i] > 0'u8: remaining.incl i
  var used = newSeq[bool](entries.len)
  while remaining.len > 0:
    var best = -1
    var bestGain = 0
    for k in 0 ..< entries.len:
      if used[k]: continue
      var gain = 0
      for i in 0 ..< covs[k].counters.len:
        if covs[k].counters[i] > 0'u8 and i in remaining: inc gain
      if gain > bestGain: bestGain = gain; best = k
    if best < 0: break
    used[best] = true
    result.add entries[best]
    for i in 0 ..< covs[best].counters.len:
      if covs[best].counters[i] > 0'u8: remaining.excl i

proc fuzzCorpusKey*(persistKey, targetId: string): string =
  ## The `ExampleDatabase` testId the fuzz loop persists its corpus under (6b):
  ## the campaign `persistKey` folded with the target's `targetId`. A changed
  ## binary carries a new `targetId`, so it misses the stale corpus and re-keys
  ## cleanly. Public so a caller can pre-seed (or inspect) the persisted corpus.
  ##
  ## Post-0.3.0 (chapulin soakrunner finding): an EMPTY `targetId` — what the
  ## in-process `fuzzWith` path always produces (its frontier is constructed
  ## without one) — used to yield the dangling-separator key
  ## `"<persistKey>#"`, which the directory backend's `safeKey` escapes into
  ## a SURPRISE SIBLING FILE (`…%23.bin`) instead of the persistKey's own
  ## corpus section. This was a load-bearing reason chapulin hand-rolled its
  ## `.soak-corpus` persistence. An empty `targetId` now folds to the bare
  ## `persistKey`, so the corpus lands in the SAME testId file's dedicated
  ## (never-pruned, F1) corpus section — safely co-resident with a
  ## `fuzzProperty` regression channel of the same name. The resume path
  ## reads the legacy dangling key once (see `fuzz`) so an existing
  ## campaign's corpus migrates instead of being orphaned.
  if targetId.len == 0: persistKey
  else: persistKey & "#" & targetId

proc fuzz*[T](s: Strategy[T]; target: Target[T]; frontier: var CoverageFrontier;
              settings: FuzzSettings; concolicBridge: ConcolicBridgeEntry = nil): FuzzReport =
  ## The coverage-guided fuzz loop, generalized over an arbitrary `Target` and a
  ## `CoverageFrontier` (FUZZ_PLAN D10). The corpus is choice-IR; each iteration
  ## mutates a parent, replays it to a value (split from the run, so any `Target`
  ## can execute it), runs the target, ADMITS the input iff its coverage raised a
  ## new edge bucket, and retains `vInteresting` findings. `fuzzWith*` is this loop
  ## with `inProcessTarget`; `externalTarget` (Phase 5) drives a child process.
  ## The `target`/`frontier` signature is UNCHANGED (RFC-fuzzer-nextgen E1
  ## C3): internally the loop builds a single-worker `Orchestrator` — owning
  ## an in-process `Worker` over `(s, target)` — and drives execution/
  ## admission through it, so it never touches `target` or `frontier`
  ## directly below this point — but no caller sees that seam.
  ##
  ## `concolicBridge` (RFC-fuzzer-nextgen G3, default `nil`): the call-site
  ## concolic bridge — see `ConcolicBridgeEntry`'s doc. `fuzz(...)`
  ## (fuzzmacro.nim) is the only caller that ever supplies one (it has a
  ## walkable typed proc symbol for the property; this generic proc does
  ## not). Combined with `settings.stallRounds == 0` (the default), this
  ## parameter existing changes nothing for any pre-G3 caller.
  # RFC-fuzzer-nextgen E1 (C3, corrected in the stage-1 follow-up): the loop
  # is rerouted through a single-worker `Orchestrator`, whose `Worker` is the
  # load-bearing execution seam — `orchestrator.run` now takes the `ChoiceSeq`
  # directly (the Worker's currency per Appendix C) and does the
  # replay-to-value + target.run internally, instead of the loop generating a
  # value itself and handing it to `target.run`. `orchestrator` wraps the
  # exact `s`/`target`/`frontier` this call was given, so behavior (including
  # what the caller reads back via `frontier.coveredEdges`) is unchanged.
  let orchestrator = newOrchestrator(s, target, frontier,
    concolicBridge = concolicBridge, stallRounds = settings.stallRounds,
    concolicMaxBranchAttempts = (if settings.concolicMaxBranchAttempts > 0:
                                   settings.concolicMaxBranchAttempts else: 8))
  var rng = initSplitMix64(settings.seed)
  # R4 (code review): gate corpus load/save on their OWN closure fields, not
  # `saveImpl` — a hand-built `ExampleDatabase` can populate `saveImpl` /
  # `loadPrimaryImpl` while leaving the newer `saveCorpusImpl` /
  # `loadCorpusImpl` fields nil (db.nim's documented "unset section degrades
  # to empty" philosophy), and dispatching through a nil closure crashes.
  let loadCorpusActive = settings.database.loadCorpusImpl != nil
  let saveCorpusActive = settings.database.saveCorpusImpl != nil
  let testId = fuzzCorpusKey(settings.persistKey, frontier.targetId)
  let corpusLimit = if settings.corpusLimit > 0: settings.corpusLimit else: 256
  var corpus: seq[tuple[choices: seq[ChoiceNode], spans: seq[Span]]]
  for seed in settings.initialIRCorpus:
    let cap = captureIR(s, seed)
    if cap.ok: corpus.add (choices: cap.choices, spans: cap.spans)
    else: inc result.droppedSeeds   # F7: misaligned seed, dropped before assembly
  if loadCorpusActive:                           # resume: persisted corpus as seeds (6b)
    # F1: the fuzz corpus lives in the DB's dedicated `corpus` section, not
    # `primary` — `primary` is the regression-replay channel `dbReusePhase`
    # prunes on pass/reject, which is the wrong lifecycle for coverage seeds
    # that keep earning their keep even once they stop crashing.
    for choices in settings.database.loadCorpus(testId):
      let cap = captureIR(s, choices)
      if cap.ok: corpus.add (choices: cap.choices, spans: cap.spans)
      else: inc result.droppedSeeds   # F7: same, for DB-resumed seeds
    # Legacy-key migration (see `fuzzCorpusKey`): campaigns persisted before
    # the dangling-`#` fix live under `"<persistKey>#"`. Read them once and
    # fold in; saves go to the new key only, so the legacy file simply goes
    # stale rather than being rewritten forever.
    if frontier.targetId.len == 0 and settings.persistKey.len > 0:
      for choices in settings.database.loadCorpus(settings.persistKey & "#"):
        let cap = captureIR(s, choices)
        if cap.ok: corpus.add (choices: cap.choices, spans: cap.spans)
        else: inc result.droppedSeeds
  let preloadedCount = corpus.len   # F2: entries above are real seeds (user- or
                                     # DB-supplied); the fallback single random
                                     # entry added just below is not — it keeps
                                     # its pre-F2 "empty = unrun" coverage so the
                                     # no-preloaded-seeds trajectory is untouched.
  if corpus.len == 0:
    var ds = newDataSource(initSplitMix64(rng.next))
    ds.integerBias = resolved(settings.integerBias)
    try:
      discard s.generate(ds)
      corpus.add (choices: ds.recorded, spans: ds.spans)
    except CatchableError, Defect:
      discard
  result.corpus = FuzzCorpus(kind: fckIR, irEntries: @[])
  for entry in corpus: result.corpus.irEntries.add entry.choices

  # Parallel per-entry bookkeeping for the scheduler (RFC-fuzzer-nextgen S1)
  # and the 6c minimizer (cheap when unused).
  var energy = newSeq[float](corpus.len)       # entropic-schedule weight per entry
  var corpusCov = newSeq[Coverage](corpus.len) # coverage each entry produced (empty = seed)
  var corpusNanos = newSeq[int64](corpus.len)  # S1 exec-cost term input (0 = seed/no timing)
  var corpusSlots = newSeq[seq[int]](corpus.len)
    ## S1: each entry's OWN sparse covered-slot list (frozen at admission) —
    ## `entropicEnergy` walks this against the frontier's LIVE `stats` each
    ## time energy is refreshed, so a slot's rarity contribution decays
    ## naturally as more of the campaign's runs reach it, without this loop
    ## ever recomputing rarity inline itself (coverage.nim owns that).
  var corpusCmpLog = newSeq[seq[CmpLogEntry]](corpus.len)
    ## RFC-fuzzer-nextgen G5: each entry's OWN cmp-log, captured at the exact
    ## moment ITS run produced it (see `captureCmpLog` below) — the parent
    ## driving `mutateIRI2SReplace` at mutation time is always matched
    ## against the log ITS OWN concrete values produced, never a stale or
    ## unrelated run's. Stays all-empty (and every `captureCmpLog` call a
    ## no-op) when `settings.enableI2S` is off — see that field's doc.
  var dictionary: Dictionary
    ## RFC-fuzzer-nextgen G5 deliverable 3: the per-campaign auto-dictionary,
    ## folded via `captureCmpLog` at the same sites `corpusCmpLog` is.

  proc captureCmpLog(): seq[CmpLogEntry] =
    ## The ONE site `currentCmpLog()` is read from (RFC-fuzzer-nextgen G5) —
    ## called immediately after an `orchestrator.run`/`tryConcolicBridge`
    ## call whose `Observation.verdict != vRejected` (a rejected run may
    ## never have reached `observeInProcess`'s reset/record, in which case
    ## the thread-local buffer would still hold a PRIOR run's stale log —
    ## callers must only invoke this right after a confirmed non-rejected
    ## run). A no-op returning `@[]` when `settings.enableI2S` is off, so an
    ## opted-out campaign never even parses the log or touches `dictionary`.
    if not settings.enableI2S: return @[]
    result = parseCmpLog(currentCmpLog())
    harvestDictionary(dictionary, result)

  # F2 (RFC-chapulin-hardening ~line 632): up-front coverage-replay pass over
  # preloaded seeds. Without this, `corpusCov[i]` for a seed stays empty until
  # (if ever) it's picked as a mutation parent and its *mutant* gets run — the
  # seed's OWN coverage is never captured, so `minimalCovering` (6c) can't tell
  # which seeds cover which edges and can't minimize a preloaded/external
  # corpus losslessly. Fix: replay each preloaded seed through the exact same
  # replay→generate→run path the mutation loop uses per iteration — now just
  # `orchestrator.run(choices)`, which internally does the
  # `newReplaySource` + `s.generate` + `target.run` sequence behind the
  # Worker seam (RFC-fuzzer-nextgen E1 stage-1 fix: `ChoiceSeq` in, not a
  # materialized value) — and record the result.
  #
  # Also admit each seed's coverage into the frontier, matching what the loop
  # would do had that seed's coverage been observed via mutation — this isn't
  # optional bookkeeping: `admit` is what the loop's `newEdge` admission check
  # (`admit(orchestrator, ...).admitted`) is keyed on.
  # Leaving seeds un-admitted means a mutant that only reproduces its parent
  # seed's already-known edges would misreport as "new coverage" simply
  # because the frontier had never seen the seed run — i.e. skipping this
  # would both under-report `coverageHits` for a resumed/external corpus AND
  # bias early admission toward non-novel mutants. `admit` is order-independent
  # (coverage.nim: a bucket only ever rises), so folding seeds in before the
  # loop starts is safe and matches admitting them "in mutation order" would
  # have produced.
  #
  # Scope: coverage only, not crash detection — a preloaded seed that itself
  # falsifies isn't reported as a crash here (F2 is `minimizeCorpus`-focused
  # per the RFC; crash surfacing for preloaded seeds is out of scope).
  # Deliberately excludes the single random fallback seed added just above
  # (index >= preloadedCount) — that path is unchanged from pre-F2, so a run
  # with no preloaded corpus keeps its exact prior trajectory/determinism.
  for i in 0 ..< preloadedCount:
    let obs = orchestrator.run(corpus[i].choices)
    if obs.verdict == vRejected: continue
    corpusCov[i] = obs.coverage
    corpusNanos[i] = obs.runResult.durationNs
    corpusSlots[i] = coveredSlots(obs.coverage)
    corpusCmpLog[i] = captureCmpLog()
    discard admit(orchestrator, corpus[i].choices, obs)

  let started = getMonoTime()
  let hasDeadline = settings.timeBudget.inNanoseconds > 0
  var seenCrashKeys = initHashSet[string]()    # crash de-dup, keep-first (6a)
  var iter = 0

  proc recordCorpusGrowth(choices: seq[ChoiceNode]; obs: Observation[T]; report: var FuzzReport;
                          cmpLog: seq[CmpLogEntry] = @[]) =
    ## Shared by the mutation-admit path and G3's concolic-bridge path
    ## (RFC-fuzzer-nextgen G3): fold one newly-admitted entry into the
    ## SAME corpus bookkeeping — `corpusSlots`/`corpusNanos` feed S1's
    ## `entropicEnergy` at the top of the NEXT iteration regardless of
    ## which mechanism produced the entry, so a concolic-admitted seed
    ## earns real Entropic energy with no separate G3b path.
    ##
    ## `cmpLog` (RFC-fuzzer-nextgen G5, default `@[]`): the SAME run's cmp
    ## log, already captured by the caller via `captureCmpLog()` — never
    ## re-read here, since by the time this runs another `orchestrator.run`
    ## may already have overwritten the thread-local buffer.
    let cap = captureIR(s, choices)
    if cap.ok:
      corpus.add (choices: cap.choices, spans: cap.spans)
      corpusCov.add obs.coverage
      corpusNanos.add obs.runResult.durationNs
      corpusSlots.add coveredSlots(obs.coverage)
      corpusCmpLog.add cmpLog
      energy.add 0.0   # placeholder — refreshed at the top of the next iteration
      report.corpus.irEntries.add cap.choices
      if saveCorpusActive: settings.database.saveCorpus(testId, cap.choices, corpusLimit)

  proc recordCrashIfInteresting(choices: seq[ChoiceNode]; obs: Observation[T];
                                report: var FuzzReport): bool =
    ## Returns true iff the loop should stop (`stopOnFirstCrash` and this
    ## crash is new). Shared by the mutation and concolic-bridge paths —
    ## a concolic-materialized seed that happens to falsify the property
    ## is exactly as reportable as a mutation-found one.
    if obs.verdict notin {vInteresting, vTimedOut}: return false
    let key = if settings.crashKey != nil: settings.crashKey(obs.coverage, obs.message)
              else: defaultCrashKey(obs.coverage, obs.message, obs.crash)
    let isNewCrash = not seenCrashKeys.containsOrIncl(key)
    if settings.keepAllCrashes or isNewCrash:
      report.irCrashes.add (choices: choices, message: obs.message)
    # F4: only a NEW (de-duped) crash triggers the stop — `containsOrIncl` above
    # always records the key first, so a duplicate leaves `isNewCrash` false and
    # the loop continues even under `keepAllCrashes` (which retains dupes but
    # isn't itself a new finding).
    settings.stopOnFirstCrash and isNewCrash

  while corpus.len > 0:
    if settings.maxIterations > 0 and iter >= settings.maxIterations: break
    if hasDeadline:
      let elapsed = getMonoTime() - started
      if elapsed.inNanoseconds > settings.timeBudget.inNanoseconds:
        result.timedOut = true
        break
    inc iter
    # RFC-fuzzer-nextgen S1: energy is recomputed fresh from the frontier's
    # LIVE stats every tick, not maintained incrementally — a slot's rarity
    # denominator (`totalAdmitted`) moves every admit, so a cached energy
    # value would silently go stale. `uniformSchedule` skips this entirely
    # (perf-neutral fallback: the old default path never touched `energy`).
    if not settings.uniformSchedule:
      for i in 0 ..< corpus.len:
        energy[i] = entropicEnergy(corpusSlots[i], frontier.stats,
                                    corpus[i].choices.len, corpusNanos[i])
    let parentIdx = if settings.uniformSchedule: int(rng.next mod uint64(corpus.len))
                    else: energyWeightedIndex(rng, energy)
    let parent = corpus[parentIdx]

    # RFC-fuzzer-nextgen G3 (deliverables 2/3): on a shared-frontier stall,
    # hand the ALREADY energy-selected `parent` — the entry the schedule
    # itself judges most informative right now, i.e. the closest thing to
    # a "border" entry this loop tracks — to the call-site concolic bridge
    # before this round's ordinary mutation. Inert (see
    # `tryConcolicBridge`'s doc) unless `concolicBridge` is wired AND
    # `stallRounds > 0` AND the frontier is actually stalled, so a
    # pre-G3/non-opted-in campaign's trajectory (RNG consumption included:
    # this touches no `rng` state) is byte-for-byte unchanged. Additive to
    # this round's mutation, never a replacement — a stalled campaign still
    # gets its ordinary mutation shot this same iteration.
    if concolicBridge != nil:
      let bridged = tryConcolicBridge(orchestrator, parent.choices)
      if bridged.ar.admitted:
        recordCorpusGrowth(bridged.choices, bridged.obs, result, captureCmpLog())
        if recordCrashIfInteresting(bridged.choices, bridged.obs, result): break

    # RFC-fuzzer-nextgen G5: the 6th operator (I2S replacement + dictionary
    # insertion) is additive — `enableI2S` off keeps the pick distribution
    # at `mod 5`, byte-for-byte the pre-G5 RNG-consumption/mutation
    # trajectory for every existing caller (same convention `uniformSchedule`/
    # `stallRounds` use).
    let pickMax = if settings.enableI2S: 6'u64 else: 5'u64
    let pick = rng.next mod pickMax
    var mutant: seq[ChoiceNode]
    case pick
    of 0: mutant = mutateIRPerturbInteger(rng, parent.choices)
    of 1: mutant = mutateIRKindBoundary(rng, parent.choices)
    of 2:
      let donor = corpus[int(rng.next mod uint64(corpus.len))]
      mutant = mutateIRSpanSplice(rng, parent.choices, donor.choices,
                                  parent.spans, donor.spans)
    of 3: mutant = mutateIRSpanDelete(rng, parent.choices, parent.spans)
    of 4: mutant = mutateIRSpanDuplicate(rng, parent.choices, parent.spans)
    else: mutant = mutateIRI2SReplace(rng, parent.choices, corpusCmpLog[parentIdx], dictionary)

    let obs = orchestrator.run(mutant)           # replay + run behind the Worker seam
    if obs.verdict == vRejected: continue
    let mutCmpLog = captureCmpLog()
    if admit(orchestrator, mutant, obs).admitted:
      recordCorpusGrowth(mutant, obs, result, mutCmpLog)
    if recordCrashIfInteresting(mutant, obs, result): break
  if settings.minimizeCorpus:                    # 6c: reduce to a minimal covering subset
    var choices: seq[seq[ChoiceNode]]
    for entry in corpus: choices.add entry.choices
    result.corpus.irEntries = minimalCovering(choices, corpusCov)
  result.iterations = iter
  result.coverageHits = frontier.coveredEdges
  result.dictionary = dictionary

proc fuzzWithBytes[T](s: Strategy[T], prop: proc(x: T),
                      settings: FuzzSettings): FuzzReport =
  ## The byte-mutation kernel. Retained for libFuzzer / AFL compatibility:
  ## when a harness mutates outside our process and feeds us raw bytes,
  ## we have no choice but to byte-fuzz. Internal callers should prefer
  ## the IR kernel (`fmIR`).
  let priorMode = currentCoverageMode()
  setCoverageMode(cmRecording)
  defer: setCoverageMode(priorMode)
  resetCoverage()
  var rng = initSplitMix64(settings.seed)
  let initSize = if settings.initialInputSize > 0: settings.initialInputSize
                 else: 64
  var corpus: seq[seq[byte]] = settings.initialCorpus
  if corpus.len == 0:
    corpus.add randomBytes(rng, initSize)
  result.corpus = FuzzCorpus(kind: fckBytes, byteEntries: corpus)

  let started = getMonoTime()
  let hasDeadline = settings.timeBudget.inNanoseconds > 0
  var iter = 0
  while true:
    if settings.maxIterations > 0 and iter >= settings.maxIterations: break
    if hasDeadline:
      let elapsed = getMonoTime() - started
      if elapsed.inNanoseconds > settings.timeBudget.inNanoseconds:
        result.timedOut = true
        break
    inc iter
    let parent = result.corpus.byteEntries[
      int(rng.next mod uint64(result.corpus.byteEntries.len))]
    let bytes = if rng.next mod 2'u64 == 0: mutateByteFlip(rng, parent)
                else: mutateByteReplace(rng, parent)
    let covBefore = currentCoverage()
    let r = fuzzOnce(s, prop, bytes)
    let covAfter = currentCoverage()
    if covAfter > covBefore:
      result.corpus.byteEntries.add bytes
    case r.outcome
    of foOk, foRejected: discard
    of foFalsified:
      result.crashes.add (bytes: bytes, message: r.message)
  result.iterations = iter
  result.coverageHits = currentCoverage()

proc fuzzWithIR[T](s: Strategy[T], prop: proc(x: T),
                   settings: FuzzSettings): FuzzReport =
  ## The IR-mutation kernel — #110's architectural payoff. Now the in-process
  ## instance of the generalized `fuzz` loop: `inProcessTarget(prop)` over a fresh
  ## in-process `CoverageFrontier`. Admission on a new edge bucket (in the 0/1
  ## {.cover.} bitmap a new slot is exactly a new distinct edge) is equivalent to
  ## the old `covAfter > covBefore` scalar — the shipped fuzz/coverage suites pin it.
  var frontier = newCoverageFrontier()
  fuzz(s, inProcessTarget(prop), frontier, settings)

proc fuzzWith*[T](s: Strategy[T], prop: proc(x: T),
                  settings: FuzzSettings): FuzzReport =
  ## Coverage-guided fuzz loop. Dispatches on `settings.mutationMode`:
  ## `fmIR` (default) uses the IR mutators — the architectural payoff
  ## of the typed-IR decision; `fmBytes` retains the libFuzzer/AFL
  ## byte path for harnesses that hand us raw bytes.
  ##
  ## The fuzz runner uses `recordEdge` calls from `{.cover.}`'d code,
  ## so for coverage signal to fire, the SUT must be instrumented.
  ## An uninstrumented SUT degrades gracefully to "random fuzzing".
  ## Saves and restores the caller's `CoverageMode` so the recording
  ## state is scoped to this call.
  case settings.mutationMode
  of fmIR:    fuzzWithIR(s, prop, settings)
  of fmBytes: fuzzWithBytes(s, prop, settings)


# --- external coverage probe: parse a dumped sancov map (FUZZ_PLAN D5/D9) ----

proc covLe32(s: string; off: int): uint32 {.inline.} =
  uint32(s[off].byte) or (uint32(s[off+1].byte) shl 8) or
  (uint32(s[off+2].byte) shl 16) or (uint32(s[off+3].byte) shl 24)

proc parseCoverageMap*(raw: string): Coverage =
  ## Parse the nelli_cov dump (docs/fuzz/INTERFACE.md wire format). Raises
  ## `ValueError` on any mismatch (bad magic / version / length / checksum) — a
  ## present-but-invalid map is NEVER returned as coverage (D5), so a torn write or
  ## a crash-poisoned counter section cannot be mistaken for a real observation.
  if raw.len < 20 or raw[0..3] != "PCOV":
    raise newException(ValueError, "coverage map: bad magic")
  let version = covLe32(raw, 4)
  if version != 1'u32:
    raise newException(ValueError, "coverage map: unsupported version " & $version)
  let length = int(covLe32(raw, 12))
  if raw.len != 16 + length + 4:
    raise newException(ValueError, "coverage map: truncated (length mismatch)")
  var counters = newSeq[uint8](length)
  var sum = 0'u32
  for i in 0 ..< length:
    counters[i] = raw[16 + i].byte
    sum += uint32(counters[i])
  if sum != covLe32(raw, 16 + length):
    raise newException(ValueError, "coverage map: checksum mismatch")
  Coverage(counters: counters)

proc sancovFileProbe*(path: string): CoverageProbe =
  ## A `CoverageProbe` reading a child's dumped sancov map from `path`. An ABSENT
  ## file → empty `Coverage` (no-coverage; D7 — absent is never stale); a
  ## present-but-invalid file raises (D5). `resetsPerRun = false`: each dump is a
  ## fresh-exec absolute snapshot (D2 [INV-fresh-exec]).
  CoverageProbe(
    read: proc(): Coverage =
      if not fileExists(path): Coverage(counters: @[])
      else: parseCoverageMap(readFile(path)),
    resetsPerRun: false)

# --- external-execution contract: delivery, oracle, limits (FUZZ_PLAN D13/D14/D16) ---
#
# Pure descriptions of how an input reaches a child and how its result is judged.
# `externalTarget` (Phase 5) executes them against a real subprocess; here they are
# data + closures, testable with no child.

type
  InputPlan* = object
    ## A complete, pure description of one external run: the argv to exec, stdin to
    ## feed, env to set, files to write before and clean after. Produced by an
    ## `InputDelivery` from (input bytes, base argv, a per-run dir).
    argv*: seq[string]
    stdin*: seq[byte]
    env*: seq[(string, string)]
    filesToWrite*: seq[tuple[path: string; content: seq[byte]]]
    filesToClean*: seq[string]

  InputDelivery* = object
    plan*: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan {.closure.}

  Oracle*[T] = object
    judge*: proc(r: RunResult; x: T): Verdict {.closure.}

  ResourceLimits* = object  ## per-run caps (D16), applied by externalTarget via setrlimit
    perRunTimeout*: Duration ## drives SIGTERM → grace → SIGKILL (D7); 0 == none
    addressSpaceBytes*: int  ## 0 == unset
    cpuSeconds*: int         ## 0 == unset
    stdoutBytes*: int        ## 0 == unset

proc bytesToStr(b: seq[byte]): string =
  result = newString(b.len)
  for i in 0 ..< b.len: result[i] = char(b[i])

proc strToBytes(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  for i in 0 ..< s.len: result[i] = byte(s[i])

# --- input delivery built-ins (D13) ---
proc stdinDelivery*(): InputDelivery =
  ## Feed the input on the child's stdin; argv unchanged (filters, codecs, jq...).
  InputDelivery(plan: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan =
    InputPlan(argv: baseArgv, stdin: bytes))

proc argvFileDelivery*(suffix = ""): InputDelivery =
  ## Write the input to a temp file in `runDir` and substitute it for the `@@`
  ## placeholder in argv (libFuzzer/AFL convention; hunt's "write a .nim, pass its
  ## path" is this with `suffix = ".nim"`). The file is listed for cleanup.
  InputDelivery(plan: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan =
    let path = runDir / ("ptinput" & suffix)
    var argv = baseArgv
    for i in 0 ..< argv.len:
      if argv[i] == "@@": argv[i] = path
    InputPlan(argv: argv, filesToWrite: @[(path, bytes)], filesToClean: @[path]))

proc envVarDelivery*(name: string): InputDelivery =
  ## Pass the input as the value of env var `name` (small configs).
  InputDelivery(plan: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan =
    InputPlan(argv: baseArgv, env: @[(name, bytesToStr(bytes))]))

# --- oracle built-ins (D14) ---
proc signalOracle*[T](): Oracle[T] =
  ## The default crash oracle: a terminating signal or non-zero exit is a finding,
  ## a timeout is a hang. (An expected non-zero exit is NOT a bug for tools that
  ## use it as a status — those want `exitCodeOracle`.)
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: vTimedOut
    elif r.signal != 0 or r.exitCode != 0: vInteresting
    else: vOk)

proc sanitizerOracle*[T](): Oracle[T] =
  ## A finding iff stderr carries a sanitizer report (ASan/UBSan), regardless of
  ## exit code — sanitizers often exit 0 with the report on stderr (hunt's O2).
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: return vTimedOut
    let err = bytesToStr(r.stderr)
    if "==ERROR:" in err or "runtime error:" in err or "AddressSanitizer" in err: vInteresting
    else: vOk)

proc exitCodeOracle*[T](bugCodes: set[uint8]): Oracle[T] =
  ## A finding on a signal or an exit code in `bugCodes` — for tools where only
  ## *some* non-zero exits mean a bug.
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: vTimedOut
    elif r.signal != 0: vInteresting
    elif r.exitCode in 0..255 and uint8(r.exitCode) in bugCodes: vInteresting
    else: vOk)

proc stderrPatternOracle*[T](pattern: string): Oracle[T] =
  ## A finding iff `pattern` appears in stderr.
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: vTimedOut
    elif pattern in bytesToStr(r.stderr): vInteresting
    else: vOk)

# --- corpus interop: AFL/libFuzzer-style directories of one-file-per-input (6d) ---
proc importCorpusDir*(dir: string): seq[seq[byte]] =
  ## Read every regular file in `dir` as one raw byte input — the on-disk format
  ## AFL and libFuzzer use. Feed the result to `FuzzSettings.initialCorpus` (or to
  ## `fuzzBinary` as seeds). A missing directory yields no inputs.
  if not dirExists(dir): return
  for kind, path in walkDir(dir):
    if kind == pcFile: result.add strToBytes(readFile(path))

proc exportCorpusDir*(dir: string; inputs: seq[seq[byte]]) =
  ## Write each input as its own file under `dir` (created if absent), so an
  ## external fuzzer can pick up where a nelli run left off. Names are
  ## zero-padded indices for stable ordering.
  createDir(dir)
  for i, inp in inputs:
    writeFile(dir / ("input-" & align($i, 6, '0')), bytesToStr(inp))

proc replayInput*[T](s: Strategy[T]; choices: seq[ChoiceNode]): Option[T] =
  ## Re-materialize the value a recorded choice-sequence produces. Used to turn a
  ## report's IR-mode crash back into its concrete input for repro/export.
  var ds = newReplaySource(choices)
  try: some(s.generate(ds))
  except CatchableError, Defect: none(T)

proc exportCrashes*(dir: string; report: FuzzReport; s: Strategy[seq[byte]]) =
  ## Write each retained crash's bytes to `dir` (created if absent) for repro.
  ## Crashes are stored as choice-IR; replaying through `s` recovers the exact
  ## input that was delivered to the target.
  createDir(dir)
  for i, cr in report.irCrashes:
    let inp = replayInput(s, cr.choices)
    if inp.isSome:
      writeFile(dir / ("crash-" & align($i, 6, '0')), bytesToStr(inp.get))

# --- differential / N-target oracle (FUZZ_PLAN D15) ---
proc differentialTarget*[T](targets: seq[Target[T]];
                            compare: proc(rs: seq[RunResult]; x: T): Verdict): Target[T] =
  ## Fan one input across N child `Target`s and reduce their `RunResult`s to a single
  ## verdict via `compare` (D15) — the generic output-equivalence / differential oracle
  ## (two parsers, gcc-vs-clang, encode→decode round-trip). Still a `Target[T]`, so the
  ## `fuzz` loop is unchanged and this composes with everything. Corpus coverage is the
  ## children's maps concatenated in order, so each child's edges stay distinct frontier
  ## slots; a child's width is pinned on its first non-empty map so a later crash (absent
  ## map → zeros) keeps the joint vector aligned.
  var widths = newSeq[int](targets.len)
  Target[T](run: proc(x: T): Observation[T] =
    var rrs = newSeq[RunResult](targets.len)
    var covs = newSeq[Coverage](targets.len)
    for i, t in targets:
      let obs = t.run(x)
      rrs[i] = obs.runResult
      covs[i] = obs.coverage
    for i in 0 ..< covs.len:
      if widths[i] == 0 and covs[i].counters.len > 0: widths[i] = covs[i].counters.len
    var joint: seq[byte]
    for i in 0 ..< covs.len:
      let base = joint.len
      joint.setLen(base + widths[i])
      for j in 0 ..< min(widths[i], covs[i].counters.len): joint[base + j] = covs[i].counters[j]
    let verdict = compare(rrs, x)
    var msg = ""
    if verdict in {vInteresting, vTimedOut}:
      for i, rr in rrs: msg.add "child " & $i & " exit=" & $rr.exitCode & " sig=" & $rr.signal & "\n"
    Observation[T](verdict: verdict, coverage: Coverage(counters: joint), message: msg))

# --- external target: run an instrumented child process (FUZZ_PLAN D3/D5/D7/D16) ---
when defined(posix):
  import std/posix

  let
    PT_RLIMIT_AS {.importc: "RLIMIT_AS", header: "<sys/resource.h>".}: cint
    PT_RLIMIT_CPU {.importc: "RLIMIT_CPU", header: "<sys/resource.h>".}: cint
    PT_RLIMIT_CORE {.importc: "RLIMIT_CORE", header: "<sys/resource.h>".}: cint

  proc ptSetLimit(res: cint; cap: int) =
    var rl = RLimit(rlim_cur: cap, rlim_max: cap)
    discard setrlimit(res, rl)

  var ptChildCtr = 0
  proc runChild*(argv: seq[string]; env: seq[(string, string)]; stdin: seq[byte];
                 limits: ResourceLimits): RunResult =
    ## fork/exec `argv` with `stdin` fed from a temp file and stdout/stderr captured to
    ## temp files, under `limits`. On timeout: SIGTERM → ~200ms grace → SIGKILL, so a
    ## sancov-instrumented child still dumps its map (D7). Precise signal vs exit code.
    inc ptChildCtr
    let stem = getTempDir() / ("ptfz_" & $getCurrentProcessId() & "_" & $ptChildCtr)
    let inPath = stem & ".in"
    let outPath = stem & ".out"
    let errPath = stem & ".err"
    writeFile(inPath, bytesToStr(stdin))
    var envv: seq[string]
    for k, v in envPairs(): envv.add k & "=" & v
    for kv in env: envv.add kv[0] & "=" & kv[1]
    let ca = allocCStringArray(argv)              # alloc before fork (no malloc in the child)
    let ce = allocCStringArray(envv)
    let timeoutMs = int(limits.perRunTimeout.inMilliseconds)
    let t0 = epochTime()
    let pid = fork()
    if pid < 0:
      deallocCStringArray(ca); deallocCStringArray(ce)
      raiseOSError(osLastError(), "fork failed")
    if pid == 0:
      ptSetLimit(PT_RLIMIT_CORE, 0)
      if limits.addressSpaceBytes > 0: ptSetLimit(PT_RLIMIT_AS, limits.addressSpaceBytes)
      if limits.cpuSeconds > 0: ptSetLimit(PT_RLIMIT_CPU, limits.cpuSeconds)
      let ifd = posix.open(inPath.cstring, O_RDONLY)
      let ofd = posix.open(outPath.cstring, O_WRONLY or O_CREAT or O_TRUNC, 0o644)
      let efd = posix.open(errPath.cstring, O_WRONLY or O_CREAT or O_TRUNC, 0o644)
      discard dup2(ifd, 0); discard dup2(ofd, 1); discard dup2(efd, 2)
      discard close(ifd); discard close(ofd); discard close(efd)
      discard execvpe(argv[0].cstring, ca, ce)
      exitnow(127)                                # exec failed
    var status: cint = 0
    if timeoutMs <= 0:
      discard waitpid(pid, status, cint(0))
    else:
      let deadline = t0 + timeoutMs.float / 1000.0
      var reaped = false
      while not reaped:
        if waitpid(pid, status, WNOHANG) == pid:
          reaped = true
        elif epochTime() >= deadline:
          discard kill(pid, SIGTERM)              # let nelli_cov.c dump
          let graceEnd = epochTime() + 0.2
          while epochTime() < graceEnd:
            if waitpid(pid, status, WNOHANG) == pid: reaped = true; break
            sleep(5)
          if not reaped:
            discard kill(pid, SIGKILL)
            discard waitpid(pid, status, cint(0))
            reaped = true
          result.timedOut = true
        else:
          sleep(5)
    deallocCStringArray(ca); deallocCStringArray(ce)
    result.durationNs = int64((epochTime() - t0) * 1e9)
    if WIFSIGNALED(status):
      result.signal = int(WTERMSIG(status))
      result.exitCode = -1
    else:
      result.exitCode = int(WEXITSTATUS(status))
    result.stdout = strToBytes(if fileExists(outPath): readFile(outPath) else: "")
    result.stderr = strToBytes(if fileExists(errPath): readFile(errPath) else: "")
    removeFile(inPath); removeFile(outPath); removeFile(errPath)

  var ptRunCtr = 0
  proc externalTarget*[T](argv: seq[string]; delivery: InputDelivery; oracle: Oracle[T];
                          limits = ResourceLimits();
                          encode: proc(x: T): seq[byte]): Target[T] =
    ## A `Target` over an instrumented external binary (D3). Per input: encode → `delivery`
    ## plans the run → write its files + set a per-run `$NELLI_COV_FILE` → `runChild` under
    ## `limits` → `oracle` judges the `RunResult` → read the dumped sancov map (absent or
    ## torn/poisoned → empty, advisory; D7) → clean up.
    Target[T](run: proc(x: T): Observation[T] =
      inc ptRunCtr
      let runDir = getTempDir() / ("ptrun_" & $getCurrentProcessId() & "_" & $ptRunCtr)
      createDir(runDir)
      let covFile = runDir / "cov.bin"
      let plan = delivery.plan(encode(x), argv, runDir)
      for fw in plan.filesToWrite: writeFile(fw.path, bytesToStr(fw.content))
      var env = plan.env
      env.add ("NELLI_COV_FILE", covFile)
      let rr = runChild(plan.argv, env, plan.stdin, limits)
      let verdict = oracle.judge(rr, x)
      var cov = Coverage(counters: @[])
      if fileExists(covFile):
        try: cov = parseCoverageMap(readFile(covFile))
        except ValueError: discard            # crash-poisoned / torn → advisory empty (D7)
      var msg = ""
      var crash = none(CrashInfo)
      if verdict in {vInteresting, vTimedOut}:
        # Lead with the crash descriptor so a bare signal (no stderr, no coverage)
        # still keys distinctly per crash type for de-dup (6a).
        msg = "exit=" & $rr.exitCode & " signal=" & $rr.signal &
              (if rr.timedOut: " timedout" else: "") & "\n" & bytesToStr(rr.stderr)
        # RFC-fuzzer-nextgen E1 (C1): typed crash identity for the external path.
        # A signal takes precedence (it's what actually killed the child, including
        # the SIGTERM/SIGKILL `runChild` sends on a timeout); an exit-code-only
        # finding (e.g. `exitCodeOracle`'s bug-code set) falls back to `ckExitCode`.
        # `rr.signal == 0 and rr.exitCode == 0` (a pure hang the oracle called
        # `vTimedOut` before the child could be reaped with a nonzero status) leaves
        # `crash` unset — `CrashKind` has no "hang" case; the `Verdict` already says so.
        if rr.signal != 0:
          crash = some(CrashInfo(kind: ckSignal, signal: rr.signal, message: msg))
        elif rr.exitCode != 0:
          crash = some(CrashInfo(kind: ckExitCode, exitCode: rr.exitCode, message: msg))
      try: removeDir(runDir)
      except CatchableError: discard
      Observation[T](verdict: verdict, coverage: cov, message: msg, crash: crash, runResult: rr))

  proc newExternalWorker*[T](s: Strategy[T]; argv: seq[string]; delivery: InputDelivery;
                             oracle: Oracle[T]; limits = ResourceLimits();
                             encode: proc(x: T): seq[byte]): Worker[T] =
    ## RFC-fuzzer-nextgen E5: the external (out-of-process, instrumented-binary)
    ## tier as a `Worker[T]`, so an `Orchestrator[T]` drives it identically to
    ## the in-process (E1) and persistent-process (E2a) workers — one seam for
    ## all three execution modes. `submit` does exactly what `externalTarget.run`
    ## does today (encode the replayed value, run the child via `runChild`,
    ## judge via `oracle`, read the sancov file-dump coverage, compose the
    ## `Observation` with typed `CrashInfo` and signal precedence) — routed
    ## through `choiceSeqTargetWorker`'s ChoiceSeq->value bridge (the same one
    ## `newInProcessWorker` uses), since `externalTarget` is already an
    ## ordinary `Target[T]` and needs no bridging logic of its own.
    ##
    ## Windows: out of scope here. The RFC's E5 bullet states this explicitly
    ## as a documented throughput asymmetry, not an equivalence — Windows
    ## N-inputs-per-worker (persistent mode) requires the target binary to
    ## expose a libFuzzer-driver-style persistent loop (no `fork` to lean on,
    ## unlike this POSIX tier); an ordinary one-shot Windows `main()` target
    ## stays spawn-per-input via the file-dump path once E4's Windows
    ## `CreateProcess`/named-pipe worker glue lands. Neither is implemented by
    ## this proc, which only exists inside `when defined(posix)`.
    choiceSeqTargetWorker(s, externalTarget[T](argv, delivery, oracle, limits, encode))

  proc fuzzBinary*(s: Strategy[seq[byte]]; argv: seq[string];
                   settings = FuzzSettings(); limits = ResourceLimits()): FuzzReport =
    ## The 1-line happy path: fuzz `argv`, feeding each generated input on stdin, treating a
    ## crash / non-zero exit as a finding. For a structured target, build an `externalTarget`
    ## with a custom delivery / oracle / encode instead.
    var frontier = newCoverageFrontier()
    let target = externalTarget[seq[byte]](argv, stdinDelivery(), signalOracle[seq[byte]](),
                                           limits, proc(x: seq[byte]): seq[byte] = x)
    fuzz(s, target, frontier, settings)
