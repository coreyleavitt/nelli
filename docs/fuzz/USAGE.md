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
               powerSchedule: true, minimizeCorpus: true))
```

`importCorpusDir` / `exportCorpusDir` interoperate with an AFL or libFuzzer corpus directory
(one file per input); `exportCrashes` writes each finding's exact bytes for repro.

## Reproducing a finding

`report.irCrashes` holds the choice-IR of each retained crash; `replayInput(strategy, choices)`
re-materializes the concrete input, and `exportCrashes` writes them all to a directory. Feed a
file straight back to the target to reproduce:

```sh
NELLI_COV_FILE=/dev/null ./target < ./crashes/crash-000000
```
