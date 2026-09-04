# Fuzz — frozen interface (Phase 0)

> The **contract** the coverage-guided-external-fuzzing build implements against.
> Rationale lives in [`../FUZZ_PLAN.md`](../FUZZ_PLAN.md) (decisions D1–D17); this
> file freezes the *signatures* so every `/tdd` slice has a fixed target and the
> Phase-0 interface freeze is a real artifact, not prose. Changes here are spec
> changes — escalate, don't drift.
>
> **This document is checked, not merely asserted.** `tests/tfuzzpackaging.nim`
> carries a compile-level pin of the surfaces frozen here, so a signature that
> drifts from this file fails a test instead of sitting stale. (Before
> RFC-z3-optional it was normative by convention only — nothing in the tree
> referenced it, and it had gone stale in exactly the way that predicts.)

All new public symbols live in `nelli/fuzz` (the existing module) unless noted.
`Coverage*`/`CoverageProbe*`/`CoverageFrontier*` may move to a `nelli/coverage`
leaf so the engine can depend on them without a fuzz↔engine cycle (as `#107`'s
`coverage.nim` already does); decided at Phase 1b.

## Coverage (D6, D8, D9)

```nim
type
  Coverage* = object
    ## One run's per-edge observation. For an external fresh-exec target (D2
    ## [INV-fresh-exec]) `counters` is an absolute sancov snapshot; for the
    ## in-process probe it is the post-run `{.cover.}` bitmap (0/1). Value type,
    ## no history.
    counters*: seq[uint8]

  CoverageProbe* = object
    ## The ONLY execution-mode-polymorphic surface (D9): read the map the
    ## just-finished run produced. `resetsPerRun` tells the frontier the model:
    ## true  → caller/probe snapshot-and-clears each run (in-process bitmap, D8),
    ## false → each `read()` is a self-contained absolute snapshot (external).
    read*: proc(): Coverage {.closure.}
    resetsPerRun*: bool

  Admission* = object
    ## Result of folding one `Coverage` into the frontier (D9): the admission
    ## decision plus the numbers the report and the power schedule (D-6c) consume,
    ## so the caller never sequences a snapshot()/newEdges() pair.
    interesting*: bool      ## raised at least one edge's bucket → keep the input
    newEdges*: int          ## edges whose bucket this run raised
    globalEdges*: int       ## frontier population after folding

  CoverageFrontier* = object  ## opaque: accumulated bucket map + targetId (D12)

func bucketOf*(count: uint8): uint8
  ## AFL 8-bucket classifier (D6). INVARIANT: bucketOf(0) == 0 (the unique
  ## "unseen" bucket) and bucketOf(n >= 1) >= 1 (any execution outranks unseen).
  ## Boundaries: {0:unseen, 1, 2, 3, 4-7, 8-15, 16-31, 32-127, 128+}.

proc newCoverageFrontier*(targetId: string): CoverageFrontier
  ## targetId = hash(binary ‖ counter-section-size ‖ dump-ABI-version ‖ campaignId)
  ## (D12). A mismatch on resume discards the frontier (inputs kept as seeds).

proc admit*(f: var CoverageFrontier; c: Coverage): Admission
  ## Fold + order-independent diff (D6): an edge is new iff this run's bucket
  ## exceeds the stored bucket; re-observing at a lower count never flips it.

proc coveredEdges*(f: CoverageFrontier): int
proc totalEdges*(f: CoverageFrontier): int   ## counter-array size for this target
```

## Execution: delivery, oracle, target (D3, D13, D14, D15, D16)

```nim
type
  Verdict* = enum
    vOk          ## ran, nothing of interest
    vRejected    ## the input was malformed/filtered (drop from corpus)
    vInteresting ## a finding (crash / sanitizer report / differential mismatch)
    vTimedOut    ## a hang — a first-class finding (D7), not a drop

  RunResult* = object
    ## The raw mechanical result of one external run; the oracle's input (D14).
    exitCode*: int
    signal*: int            ## 0 == exited normally; else the terminating signal
    stdout*, stderr*: seq[byte]
    timedOut*: bool
    durationNs*: int64

  Oracle*[T] = object
    judge*: proc(r: RunResult; x: T): Verdict {.closure.}

  InputPlan* = object
    ## How one run's bytes reach the child (D13). The transport executes it.
    stdin*: seq[byte]
    argv*: seq[string]              ## delivery substitutions already applied
    env*: seq[(string, string)]
    tempFiles*: seq[string]         ## paths to remove after the run

  InputDelivery* = object
    plan*: proc(bytes: seq[byte]; runDir: string): InputPlan {.closure.}

  ResourceLimits* = object          ## per-run caps (D16), best-effort POSIX setrlimit
    perRunTimeout*: Duration        ## drives SIGTERM → grace → SIGKILL (D7)
    addressSpaceBytes*: int         ## 0 == unset
    cpuSeconds*: int                ## 0 == unset
    stdoutBytes*: int               ## 0 == unset

  Observation*[T] = object
    verdict*: Verdict
    coverage*: Coverage

  Target*[T] = object
    ## Execute-and-observe as one round trip (D3). Composable; closed under
    ## composition (differentialTarget).
    run*: proc(x: T): Observation[T] {.closure.}

# --- delivery built-ins (D13) ---
proc stdinDelivery*(): InputDelivery
proc argvFileDelivery*(argvTemplate: seq[string]; suffix = ""): InputDelivery
  ## a "@@" element in argvTemplate is replaced by a temp file (suffix e.g. ".nim")
proc envVarDelivery*(name: string): InputDelivery

# --- oracle built-ins (D14) ---
proc signalOracle*[T](): Oracle[T]               ## default: signal/non-zero exit → vInteresting
proc sanitizerOracle*[T](): Oracle[T]            ## stderr =~ "==ERROR:" / "runtime error:"
proc exitCodeOracle*[T](bugCodes: set[uint8]): Oracle[T]
proc stderrPatternOracle*[T](pattern: string): Oracle[T]

# --- target constructors (D3, D15) ---
proc inProcessTarget*[T](prop: proc(x: T)): Target[T]
  ## adapts the existing prop path; maps FalsifiedError→vInteresting at the
  ## boundary; probe = the in-process snapshot-and-clear probe (resetsPerRun=true).
proc externalTarget*[T](argv: seq[string]; delivery: InputDelivery; oracle: Oracle[T];
                        probe: CoverageProbe; limits: ResourceLimits): Target[T]
proc differentialTarget*[T](targets: seq[Target[T]];
                            compare: proc(rs: seq[RunResult]; x: T): Verdict): Target[T]
  ## fans x across N children, reduces RunResults → one Verdict. Observation
  ## coverage = the union of the children's coverage (most diversity).
```

## Loop entry points (D3, D10)

```nim
proc fuzz*[T](s: Strategy[T]; target: Target[T]; frontier: var CoverageFrontier;
              settings: FuzzSettings; assist: ConcolicAssist = ConcolicAssist();
              spawnFreshWorker: proc(): Worker[T] {.closure.} = nil): FuzzReport
  ## the generalized loop `fuzzWith` runs: corpus + mutateIR* + admission via
  ## frontier + crashKey de-dup. fuzzOnce and #107 are untouched.
  ## (RFC-fuzzer-nextgen U3: this Phase-0 doc originally described a
  ## fuzzWithIR/fuzzWithBytes pair — byte-mutation was demoted to
  ## import/export-only interop and its coverage-guided loop removed, so
  ## IR is the one mutation kernel `fuzz`/`fuzzWith` drive.)

macro fuzz*(stratExpr, propExpr: typed): untyped
macro fuzz*(stratExpr, propExpr, settingsExpr: typed): untyped
macro fuzz*(stratExpr, propExpr, settingsExpr: typed; assist: untyped): untyped
  ## fuzzmacro.nim. Captures the CONSTRUCTION EXPRESSIONS at the call site
  ## (worker re-entry needs to re-run them from scratch; a closure value
  ## cannot be re-run). Nim resolves a 4-argument call to the concrete
  ## `proc fuzz*[T]` above, not to the 4-arg macro -- pinned by tfuzzloop
  ## and tfuzzmacro. `assist` is `untyped` so the macro can align an inline
  ## `concolicAssist(...)` with its own captured pair before typechecking.

# nelli/concolic -- the opt-in door; the ONLY module in the fuzz stack that
# imports the walker, and the only producer of a non-nil ConcolicAssist.bridge.
macro concolicAssist*(strat, prop: typed;
                      stallRounds: untyped = 1;
                      maxBranchAttempts: untyped = 8): ConcolicAssist

template fuzzConcolic*(s, p: untyped; settings: untyped = FuzzSettings();
                       stallRounds: untyped = 1;
                       maxBranchAttempts: untyped = 8): FuzzReport
  ## The documented default form: names (s, p) once, generates both uses,
  ## so the campaign's pair and the assist's pair cannot diverge.

proc guardSolverUnavailable*(inner: ConcolicBridgeEntry): ConcolicBridgeEntry
  ## Missing-libz3 degradation: catches SoftlinkError ONLY (never bare
  ## CatchableError -- walker ValueError/AssertionDefect are real bugs and
  ## must propagate), latches once per assist, reports cfoSolverUnavailable.

proc fuzzBinary*[T](s: Strategy[T]; argv: seq[string]; settings: FuzzSettings): FuzzReport
  ## the 1-line happy path: fuzz `argv` on stdin, crash = bug. Internally
  ##   fuzz(s, externalTarget(argv, stdinDelivery(), signalOracle(),
  ##                          sancovFileProbe(...), settings.limits), newFrontier(...), settings)
```

### Additive extensions to existing types (D10, D11, D16, D17) — no breaking changes
- `FuzzSettings` gains (all defaulted): `crashKey: proc(o: Observation): string` (default = coverage-edge-set fingerprint, D11), `limits: ResourceLimits`, `persistDir: string`/`campaignId: string` (D12). D4's byte-level `dictionary: seq[seq[byte]]` extension point was never built at this layer (doc/code drift reconciled by RFC-fuzzer-nextgen U3): the auto-dictionary that shipped lives at the IR level instead — `FuzzReport.dictionary: Dictionary`, gated by `FuzzSettings.guidance.enableI2S` (Track G/S3, see "Configuration surface" below) — which supersedes the byte-level D4 idea, so it is dropped from this contract rather than built.
- `FuzzReport` gains `coverage: CoverageSummary` where `CoverageSummary = object { totalEdges, coveredEdges: int; newEdgesPerPhase: seq[int] }`. Existing `coverageHits: int` = in-process bitmap count; `coverage.coveredEdges` = external frontier population (defined so they never drift, D10). **No `FuzzReport[T]`.**

## Configuration surface (ADR-0031, RFC-fuzzer-nextgen round-3 + post-implementation closure)

Ground truth #6 (this doc's own history, one paragraph up): D4's `dictionary`
extension point was spec'd here yet never wired into the real `FuzzSettings` —
a doc/code drift born of adding a setting nowhere coherent. As Tracks E/G/S
landed a dozen-plus new knobs on top of that same flat `FuzzSettings`/
`Orchestrator[T]`, the surface started repeating the pattern at a larger
scale. **Binding rule (ADR-0031):** each track's knobs live in exactly one
nested config object, and any slice adding a knob updates this document and
the real settings type in the same slice.

```nim
type
  ExecutorConfig* = object      ## Track E — execution mechanics
    processIsolation*: bool     ## opt in to real OS-process worker isolation

  GuidanceConfig* = object      ## Track G — I2S
    enableI2S*: bool                  ## input-to-state replacement mutator + auto-dictionary

  ConcolicAssist* = object      ## RFC-z3-optional — the reified concolic assist
    bridge*: ConcolicBridgeEntry      ## nil ⇒ no assist (the zero value); built by nelli/concolic
    stallRounds*: int                 ## admits-with-no-new-edge before invoking the bridge (<=0 with a bridge ⇒ 1)
    maxBranchAttempts*: int           ## bounded per-stall-round branch attempts (<=0 ⇒ 8)

  ConcolicAssistError* = object of CatchableError
    ## Raised at campaign start when `stallRounds > 0` but `bridge` is nil.

# The activation rule above ("assist present ⇒ assist active") is owned by
# one proc, beside the type, rather than inlined at the call sites:
proc resolveAssist*(assist: ConcolicAssist):
       tuple[stallRounds, maxBranchAttempts: int] {.raises: [ConcolicAssistError].}
  ## Raises `ConcolicAssistError` for a policy with no bridge; otherwise
  ## resolves the two knobs (no bridge ⇒ 0; `stallRounds <= 0` with a bridge
  ## ⇒ 1; `maxBranchAttempts <= 0` ⇒ 8). `fuzz` calls it once at campaign
  ## start. The loop-body gate deliberately does NOT consult it — it keys on
  ## `assist.bridge` alone.

type
  SchedulingConfig* = object    ## Track S — power schedule / operator selection / havoc / culling
    uniformSchedule*: bool      ## opt OUT of Entropic power-schedule parent selection (S1)
    uniformOperators*: bool     ## opt OUT of the UCB1 operator bandit (S2)
    uniformHavoc*: bool         ## opt OUT of havoc stacking + the widened operator space (S3)
    cullCadence*: int           ## in-campaign corpus-culling cadence (0 -> defaultCullCadence)
    uniformCorpus*: bool        ## opt OUT of periodic in-campaign corpus culling (S4)
    checkpointCadence*: int     ## LearnedState checkpoint/resume cadence (0 = disabled) (S6)

  FuzzSettings* = object
    # ... core loop-control fields (maxIterations, timeBudget, seed,
    # initialIRCorpus, integerBias, keepAllCrashes, crashKey, database,
    # persistKey, corpusLimit, minimizeCorpus, stopOnFirstCrash) stay flat —
    # see fuzz.nim's own doc comment for the full field-by-field contract.
    executor*: ExecutorConfig
    guidance*: GuidanceConfig
    scheduling*: SchedulingConfig
```

Every field on all three group types zero-defaults to the pre-ADR-0031
behavior, so `FuzzSettings()` and `FuzzSettings(maxIterations: 10_000)` are
unaffected: the common case never has to name a group.

This is one of the two ways a configuration type in this library satisfies the
rule that `T()` **is** the documented default (RFC-0010): design every knob so
that zero is correct. The other is to declare the defaults on the fields, which
is what `Settings`, `SymexSettings`, `ResourceBudget`, `BmcSettings`,
`IntegerBiasConfig` and `OrchestratorPolicy` do. Both give the caller the same
guarantee — a partial literal differs from the default only in what it lists —
and which one a type uses is visible where it belongs, as the presence or
absence of `= expr` on each field.

One exception is worth knowing about, because it is an exception by nesting
rather than by choice: `FuzzSettings.integerBias` is an `IntegerBiasConfig`,
which declares its own field defaults, so that one field of `FuzzSettings()` is
not the zero value. Behaviour is unchanged — the value it now carries is the
one the old sentinel resolved to at the point of use. A caller opting into a
track knob nests it: `FuzzSettings(maxIterations: 10_000,
scheduling: SchedulingConfig(uniformOperators: true))`.

The four `uniformXxx` fields on `SchedulingConfig` look like duplicates of one
"reproduce the legacy trajectory" concept but are deliberately kept
independent, not collapsed: the RFC's ablation methodology (`Evaluation`)
toggles energy-schedule / operator-bandit / havoc as separate cells, and the
existing suites (`tfuzzschedule`/`tfuzzoperatorbandit`/`tfuzzhavoc`/
`tfuzzcull`) each isolate exactly one axis per test. Grouping them under one
type (rather than four unrelated flat `FuzzSettings` fields) still gives the
"these are siblings" legibility ADR-0031 wants.

`Orchestrator[T]`'s slot budgets and freshness-machinery knobs — re-verify,
the reproRate sampler cap, worker recycling, the storm/bootstrap circuit
breakers, and the concolic-bridge stall trigger — are `newOrchestrator`-only
settings (no `fuzz()`/`FuzzSettings` caller threads them through; `fuzz()`
only ever surfaces `executor.processIsolation`, wiring the isolated path's
breaker thresholds to fixed internal constants). They live on
`OrchestratorPolicy`, built via the `orchestratorPolicy(...)` constructor
(not a bare object literal — three fields have non-zero defaults, matching
`newOrchestrator`'s pre-ADR-0031 parameter defaults exactly):

```nim
type
  OrchestratorPolicy* = object
    reVerify*, stormBackoff*: bool
    reVerifyBudget*, reproSamples*, recycleAfterInputs*: int
    stormWindow*, bootstrapWindow*, stallRounds*, concolicMaxBranchAttempts*: int

func orchestratorPolicy*(reVerify = false; reVerifyBudget = 8; reproSamples = 5;
                         recycleAfterInputs = 0; stormWindow = 0;
                         stormBackoff = false; bootstrapWindow = 0;
                         stallRounds = 0; concolicMaxBranchAttempts = 8): OrchestratorPolicy

proc newOrchestrator*[T](worker: Worker[T]; frontier: var CoverageFrontier;
                         policy = orchestratorPolicy();
                         spawnFreshWorker: proc(): Worker[T] {.closure.} = nil;
                         db: ExampleDatabase = ExampleDatabase();
                         concolicBridge: ConcolicBridgeEntry = nil): Orchestrator[T]
```

**The raw seam deliberately keeps `concolicBridge` and `stallRounds` as
independent knobs** (RFC-z3-optional). The high-level `fuzz` entry points
fused them into `ConcolicAssist` because bridge-without-policy there was a
silent no-op; here it is the documented contract — `tfuzzconcolicbridge.nim`
pins "bridge configured, `stallRounds` 0 ⇒ inert" as this layer's
behavior. A caller wiring a real bridge to this seam writes
`concolicBridge = concolicAssist(s, p).bridge`.

`newOrchestrator(worker, frontier)` — the common construction path — is
unchanged; the full-control path names `policy` once:
`newOrchestrator(worker, frontier, policy = orchestratorPolicy(reVerify = true,
reproSamples = 10), spawnFreshWorker = fresh)`.

## Dump wire format (D5) — `nelli_cov.c` → `$NELLI_COV_DIR/<worker>-<pid>-<iter>.cov`

Little-endian, written to a temp name then `rename()`d (atomic). The probe **raises** on any mismatch (D5).

| offset | size | field | notes |
|--------|------|-------|-------|
| 0 | 4 | `magic` | ASCII `"PCOV"` |
| 4 | 4 | `version` | `u32`; bump on any layout change |
| 8 | 4 | `targetId` | `u32` (low bits of the campaign targetId hash, D12) |
| 12 | 4 | `len` | `u32`; number of counter bytes |
| 16 | `len` | `counters` | `uint8` per slot — clang: per-edge, union of all `__sanitizer_cov_8bit_counters_init` regions; gcc: a fixed-size PC-hash AFL bitmap (D1) |
| 16+`len` | 4 | `checksum` | `u32` over `counters` (D5/D7 — detects truncation/poisoning) |

A SIGKILL'd / dump-less run leaves **no file**; the loop treats absent-after-reap as no-coverage (D7), never stale.
