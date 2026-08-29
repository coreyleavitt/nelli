# Fuzzing an external target — usage guide

This is the how-to for driving a separate instrumented binary with nelli's
coverage-guided loop. The contract is in [`INTERFACE.md`](INTERFACE.md); the rationale
is in [`../FUZZ_PLAN.md`](../FUZZ_PLAN.md). Here we just get you fuzzing.

## The model in one paragraph

nelli already has a coverage-guided loop (`fuzzWith*`) that mutates a corpus and keeps
any input that lights a new edge. External fuzzing swaps the coverage source: instead of
in-process `{.cover.}` counters, it reads the **target process's** SanitizerCoverage map,
dumped to a file on exit. A `Target[T]` bundles three pluggable pieces — how the input
reaches the child (`InputDelivery`), how a run is judged (`Oracle` over a `RunResult`), and
the coverage probe — behind one `run(x): Observation`. Everything composes: the same loop
drives an in-process property, a single external binary, or N binaries compared against each
other, with no change to `fuzz` itself.

```
fuzzOnce  ── one input, one run                 (the kernel)
fuzz      ── corpus loop over a Target[T]        (this layer)
fuzzBinary ── fuzz + externalTarget(stdin,crash) (the one-liner)
```

## The one-liner

```nim
import nelli

let report = fuzzBinary(
  bytes(),                 # any Strategy[seq[byte]]
  @["./parser"],                   # argv; input arrives on stdin
  FuzzSettings(maxIterations: 100_000),
  ResourceLimits(perRunTimeout: initDuration(seconds = 1)))

echo report.coverageHits, " edges; ", report.irCrashes.len, " crashes"
exportCrashes("./crashes", report, bytes())
```

A crash, non-zero exit, or timeout is a finding; a new edge grows the corpus. That is the
whole happy path. Everything below is for when the default isn't enough.

## Composing a custom Target

```nim
let target = externalTarget[seq[byte]](
  argv      = @["./nim", "c", "@@"],         # @@ = the input file (argvFileDelivery)
  delivery  = argvFileDelivery(".nim"),       # stdin / argv-file / env are built in
  oracle    = sanitizerOracle[seq[byte]](),   # stderr sanitizer report = finding, even on exit 0
  limits    = ResourceLimits(perRunTimeout: initDuration(seconds = 5)),
  encode    = proc(x: seq[byte]): seq[byte] = x)

var frontier = newCoverageFrontier(targetId = "nim-2.2.10")
let report = fuzz(bytes(), target, frontier, FuzzSettings(maxIterations: 50_000))
```

- **Delivery**: `stdinDelivery()`, `argvFileDelivery(suffix)`, `envVarDelivery(name)`.
- **Oracle**: `signalOracle()`, `sanitizerOracle()`, `exitCodeOracle({codes})`,
  `stderrPatternOracle(pattern)`.
- **Differential**: `differentialTarget(@[t1, t2], compare)` fans one input across children
  and reduces their `RunResult`s to one verdict — output-equivalence, gcc-vs-clang, or
  encode→decode round-trips. Still a `Target[T]`.

## Instrumentation recipe (normative)

The target must be compiled with SanitizerCoverage **and** linked against the vendored
runtime `src/nelli/nelli_cov.c`, which dumps the coverage map to
`$NELLI_COV_FILE` on exit (and on a fatal signal). The runtime is a **separate object,
compiled WITHOUT the coverage flag** — otherwise gcc instruments its own callback and
recurses into a crash, and you avoid pulling in compiler-rt.

Two backends, same wire format (the loop auto-detects from the dump):

| Backend | Coverage flag | Runtime define | Notes |
|---------|---------------|----------------|-------|
| clang   | `-fsanitize-coverage=inline-8bit-counters` | *(none)* | precise per-edge counters |
| gcc     | `-fsanitize-coverage=trace-pc`             | `-DNELLI_COV_GCC` | PC-hash AFL bitmap; needs `-no-pie` |

### C / C++ — single translation unit (clang)

```sh
clang -fsanitize-coverage=inline-8bit-counters -c target.c -o target.o
clang -c src/nelli/nelli_cov.c -o nelli_cov.o      # NO coverage flag
clang target.o nelli_cov.o -o target
```

### C / C++ — single translation unit (gcc)

```sh
gcc -fsanitize-coverage=trace-pc -fno-pie -c target.c -o target.o
gcc -DNELLI_COV_GCC -fno-pie -c src/nelli/nelli_cov.c -o nelli_cov.o
gcc -no-pie target.o nelli_cov.o -o target               # -no-pie pins addresses (ASLR)
```

### C / C++ — multiple translation units

Instrument every TU of the code under test; compile the runtime once, unflagged. The clang
section-union and gcc PC-hash both merge TUs automatically.

```sh
clang -fsanitize-coverage=inline-8bit-counters -c a.c -o a.o
clang -fsanitize-coverage=inline-8bit-counters -c b.c -o b.o
clang -c src/nelli/nelli_cov.c -o nelli_cov.o
clang a.o b.o nelli_cov.o -o target
```

### Rust

```sh
RUSTFLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=3 \
  -Cllvm-args=-sanitizer-coverage-inline-8bit-counters" cargo build --release
clang -c src/nelli/nelli_cov.c -o nelli_cov.o
# link nelli_cov.o into the final binary (build.rs or a wrapper crate)
```

### Nim

Nim drives the C backend (gcc by default), so use the gcc/trace-pc variant. Build the
runtime object first, then link it in. For the clang counters instead, add `--cc:clang` and
swap the flag/define to the clang row.

```sh
gcc -DNELLI_COV_GCC -fno-pie -c src/nelli/nelli_cov.c -o nelli_cov.o
nim c --passC:"-fsanitize-coverage=trace-pc -fno-pie" \
      --passL:"-no-pie nelli_cov.o" -d:release target.nim
```

For the matrix/CI image, build the runtime object once and reuse it across targets.

## Resuming a campaign

Point a run at an `ExampleDatabase` and give it a `persistKey`; the corpus persists and
reloads automatically. The key folds in the frontier's `targetId`, so rebuilding the target
with new instrumentation transparently starts a fresh corpus instead of replaying inputs
against a coverage map that no longer lines up.

```nim
let db = directoryBasedDatabase("./fuzzdb")
var frontier = newCoverageFrontier(targetId = "nim-2.2.10")
let report = fuzz(bytes(), target, frontier,
  FuzzSettings(maxIterations: 100_000, database: db, persistKey: "nim-parser",
               minimizeCorpus: true))
```

`importCorpusDir` / `exportCorpusDir` interoperate with an AFL or libFuzzer corpus directory
(one file per input); `exportCrashes` writes each finding's exact bytes for repro.

## Tuning the guided loop (executor / guidance / scheduling)

`FuzzSettings`'s core fields (`maxIterations`, `database`, `persistKey`, ...) stay flat, so
the one-liner above never has to change. Everything the guided-fuzzing tracks (Track
E/G/S — process isolation, concolic assist, power scheduling) added since sits on three
nested config objects instead of growing the flat list further — see `INTERFACE.md`'s
"Configuration surface" section for the full field list and the reasoning:

```nim
let report = fuzz(bytes(), target, frontier,
  FuzzSettings(maxIterations: 200_000,
    guidance: GuidanceConfig(enableI2S: true),
    scheduling: SchedulingConfig(checkpointCadence: 5_000)))
```

Every field on `ExecutorConfig`/`GuidanceConfig`/`SchedulingConfig` defaults to the
pre-Track-E/G/S behavior, so naming a group is opt-in, never required.

## Concolic assist — one extra import, and why

Concolic fuzzing hands a stalled campaign to a symbolic-execution engine, which solves
for an input that takes a branch mutation cannot reach — a `x == 0xCAFEBABE` gate needs
up to 2^32 random tries and one solve. That engine needs Z3.

`import nelli` is Z3-free, so the assist lives behind a second import:

```nim
import nelli
import nelli/concolic

proc magicGate(x: int) {.cover.} =
  if x == 0xCAFEBABE: discard "gate"
  else:               discard "miss"

let report = fuzzConcolic(integers(0, 0xFFFFFFFF), magicGate,
                          FuzzSettings(seed: 42'u64, maxIterations: 60))
```

**`fuzzConcolic` is the default form**, and not merely as a convenience. The assist has
to classify the strategy's combinator chain to know what equation to solve, so it needs
the same `(strategy, property)` pair the campaign draws from. `fuzzConcolic` takes that
pair once and generates both uses, so they cannot diverge. Written out by hand, the
strategy expression — realistically something like
`integers(0, 1000).map(proc(x: int): int = x * 2 + 1)` — appears twice at one call site.

`stallRounds` (how many admits with no new coverage before the assist fires, default 1)
and `maxBranchAttempts` (bounded branch-index attempts per stall round, default 8) are
optional trailing arguments. **The defaults are the ACTIVE values**: calling
`fuzzConcolic` and getting an inert campaign is not a state this API can spell.

### The advanced seam

`concolicAssist` builds the assist as a value, for composition:

```nim
fuzz(strat, prop, settings, assist = concolicAssist(strat, prop))
```

The argument order is `(strategy, property)` everywhere, matching `fuzz`. When the assist
is written inline like this, `fuzz` rewrites its strategy/property arguments to the pair
it captured, so a transposition or a copy-paste mismatch is corrected rather than
silently solving the wrong equation. A **pre-built** `ConcolicAssist` value cannot be
checked that way — there is no call to rewrite — so if you bind one to a variable, make
sure it names the pair you are fuzzing. A mismatch there is bounded, not unsound: the
campaign completes and admits nothing falsely, but the solver work is wasted.

`concolicAssist`'s `strat`/`prop` are `typed` macro arguments, so they carry the same
overloaded-proc / generic-proc resolution constraints `fuzz(...)`'s own arguments carry:
a bare overloaded name with no disambiguating context can fail to resolve. Pre-existing,
but it applies to this entry point too.

At the lowest level, `newOrchestrator` keeps `concolicBridge` and
`OrchestratorPolicy.stallRounds` as independent knobs — that is the raw seam, and
`concolicBridge = concolicAssist(s, p).bridge` is how you feed it.

### When Z3 cannot be loaded

An opted-in concolic campaign on a machine where `libz3` will not load **degrades, it
does not abort**. The first failed load is caught, latched so it is not retried on every
subsequent stall round, and reported as `cfoSolverUnavailable`:

```nim
check report.stats.concolicYield.solverUnavailable > 0
```

The campaign runs to completion on ordinary mutation. Only the missing-library failure
is absorbed this way — a solver that computes something wrong still raises, because that
is a bug and must not be silently swallowed.

### Consumer build matrix

| You write | Needs Z3 at compile time | Needs libz3 at runtime |
|---|---|---|
| `import nelli` | no | no |
| `import nelli` + `{.cover.}` fuzzing | no | no |
| `import nelli` + symex markers (`symexTarget`/`symexAssert`/`symexAssume`) | no | no |
| `import nelli/concolic`, `fuzzConcolic(...)` | yes | yes, or the campaign degrades as above |
| `import nelli/symex`, `symexFind(...)` | yes | yes |

The symex markers are deliberately in the Z3-free row: they are annotations for
production code, so annotating a SUT must never drag a solver into its build.

## Reproducing a finding

`report.irCrashes` holds the choice-IR of each retained crash; `replayInput(strategy, choices)`
re-materializes the concrete input, and `exportCrashes` writes them all to a directory. Feed a
file straight back to the target to reproduce:

```sh
NELLI_COV_FILE=/dev/null ./target < ./crashes/crash-000000
```
