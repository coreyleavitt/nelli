# Fuzz — frozen interface (Phase 0)

> The **contract** the coverage-guided-external-fuzzing build implements against.
> Rationale lives in [`../FUZZ_PLAN.md`](../FUZZ_PLAN.md) (decisions D1–D17); this
> file freezes the *signatures* so every `/tdd` slice has a fixed target and the
> Phase-0 interface freeze is a real artifact, not prose. Changes here are spec
> changes — escalate, don't drift.

All new public symbols live in `proptest/fuzz` (the existing module) unless noted.
`Coverage*`/`CoverageProbe*`/`CoverageFrontier*` may move to a `proptest/coverage`
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
              settings: FuzzSettings): FuzzReport
  ## the generalized fuzzWithIR/fuzzWithBytes: corpus + mutateIR* + admission via
  ## frontier + crashKey de-dup. fuzzOnce and #107 are untouched.

proc fuzzBinary*[T](s: Strategy[T]; argv: seq[string]; settings: FuzzSettings): FuzzReport
  ## the 1-line happy path: fuzz `argv` on stdin, crash = bug. Internally
  ##   fuzz(s, externalTarget(argv, stdinDelivery(), signalOracle(),
  ##                          sancovFileProbe(...), settings.limits), newFrontier(...), settings)
```

### Additive extensions to existing types (D10, D11, D16, D17) — no breaking changes
- `FuzzSettings` gains (all defaulted): `crashKey: proc(o: Observation): string` (default = coverage-edge-set fingerprint, D11), `limits: ResourceLimits`, `dictionary: seq[seq[byte]]` (byte-mode, D4), `persistDir: string`/`campaignId: string` (D12).
- `FuzzReport` gains `coverage: CoverageSummary` where `CoverageSummary = object { totalEdges, coveredEdges: int; newEdgesPerPhase: seq[int] }`. Existing `coverageHits: int` = in-process bitmap count; `coverage.coveredEdges` = external frontier population (defined so they never drift, D10). **No `FuzzReport[T]`.**

## Dump wire format (D5) — `proptest_cov.c` → `$PROPTEST_COV_DIR/<worker>-<pid>-<iter>.cov`

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
