# Coverage-guided fuzzing of external targets

proptest can fuzz a **separate instrumented binary** — a parser, codec, interpreter,
CLI, or compiler — evolving its existing `fuzzWith*` corpus loop against the *target's*
SanitizerCoverage instead of in-process `{.cover.}` coverage. Generic by mandate:
`fuzzBinary(strings(), @["./target"], settings)` is the one-line happy path; a custom
oracle, input delivery, or a differential N-target comparison compose from there.

## Documents

- [`../FUZZ_PLAN.md`](../FUZZ_PLAN.md) — the build plan: motivation, scope, decisions
  **D1–D17**, architecture, and the phase-by-phase slices. The rationale lives here.
- [`INTERFACE.md`](INTERFACE.md) — the **frozen interface** (Phase 0): the exact type
  signatures and the dump wire format every slice implements against.
- [`USAGE.md`](USAGE.md) — the **how-to** (Phase 7): the one-liner, composing a custom
  `Target`, the normative per-language instrumentation recipe, resume, and repro.

## Decisions index (rationale in FUZZ_PLAN.md)

| D | Decision |
|---|----------|
| D1 | Dual SanitizerCoverage backend: clang `inline-8bit-counters` (precise) + gcc `trace-pc` (PC-hash AFL bitmap); same wire format |
| D2 | AFL external-binary model; `[INV-fresh-exec]` (fresh process per run) |
| D3 | `Target[T]` = transport + delivery + oracle + probe; `fuzzOnce` unchanged |
| D4 | Coverage = corpus *admission*, not directed search; `mutateIR*` reused; byte-mode `dictionary` extension point |
| D5 | Per-run-unique, self-describing (magic/version/targetId/len) + checksummed, atomic, fail-loud file transport |
| D6 | `inline-8bit-counters` + AFL bucketing; `bucketOf(0)==0`; order-independent novelty |
| D7 | Dump-on-signal (async-safe), `waitpid`-reap before read, advisory crash-coverage, `vTimedOut` hangs |
| D8 | Snapshot/reset is a *per-probe* contract; in-process snapshot-and-clears, external is absolute |
| D9 | Three coverage types: `Coverage` / `CoverageProbe` / `CoverageFrontier`; `admit()` → `Admission` |
| D10 | Generalize `fuzzWith*`; `#107` stays decoupled; `FuzzReport` extended additively |
| D11 | Crash de-dup via `crashKey` (default = coverage-edge-set); keep-first, shrinker-safe |
| D12 | Persistence: sibling flat-file store (frontier/byte-corpus) + `ExampleDatabase` (IR/crashes); `targetId` folds in invocation |
| D13 | Pluggable `InputDelivery` (stdin / argv-file / env / fixed-path) |
| D14 | Pluggable `Oracle` over `RunResult`; generic `Verdict` enum |
| D15 | `differentialTarget` (N children → one verdict); still a `Target[T]` |
| D16 | Per-run timeout + `ResourceLimits`, provided by proptest |
| D17 | libFuzzer/AFL corpus-dir import/export + crash-dir export (byte-mode) |

## Status

**All phases complete (0–7).** Interface freeze → C-build scaffold → dump runtimes →
`CoverageFrontier` → probes → `Target[T]` → execution contract → `externalTarget`/`fuzzBinary`
→ `differentialTarget` → operational hardening (crash de-dup, persistence/resume, power
schedule + minimization, corpus interop) → packaging. Each phase ships a `tfuzz*` suite.
Fuzz tests run in `ghcr.io/coreyleavitt/nim:2.2.10` (nim + gcc + clang):
`podman run --rm -v "$PWD":/app:z -w /app ghcr.io/coreyleavitt/nim:2.2.10 nimble test`.
The one validation gap (a koch-built `nim`'s early-`quit`/fork behavior) lives in `hunt`.
