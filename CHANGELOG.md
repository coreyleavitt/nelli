# Changelog

Notable changes to nelli. Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
versioning is [semantic](https://semver.org/spec/v2.0.0.html).

> **Why this file now.** Releases through 0.6.0 carried their notes in the
> release commit message alone. That works while the surface is additive; it
> stops working the moment a downstream maintainer has to migrate. 0.7.0 is
> breaking in three separate ways, and the one real downstream (chapulin) has
> **not yet absorbed 0.6.0's own breaking change** — so it must migrate across
> two releases at once, from a document it can actually find. 0.6.0 is
> reconstructed below from its release commit for exactly that reason.
> RFC-z3-optional S5 adopted this as a deliberate practice, not a one-off.

## [0.8.0] — unreleased

### Changed

- **A partial object literal now carries its type's defaults.** This is the
  headline and it is a *silent* behaviour change: every literal that compiled
  before compiles after, and means something different. Nim zero-fills the
  fields an object literal does not list, and nelli's configuration objects
  carry meaningful non-zero defaults — so the documented idiom shipped a
  different engine than `defaultSettings()`, with no warning, no error and no
  symptom except worse testing. `Settings`, `SymexSettings`, `ResourceBudget`,
  `BmcSettings`, `IntegerBiasConfig` and `OrchestratorPolicy` now declare their
  defaults on the fields, so `T()` **is** the documented default configuration
  and a partial literal differs from it only in what it lists.

  An explicitly-written zero still means zero. That is what makes this
  mechanism viable where every sentinel and merge scheme failed:
  `maxShrinks: 0` (unbounded), `targetedSAIters: 0` (SA off) and
  `useSA: false` all keep saying what they look like they say.

  **Read `docs/rfc/0010-config-discipline.downstream-audit.md` before
  upgrading.** It carries the per-field delta tables, runnable greps and a
  triage recipe. The short version: if you meant the zeros, write them
  explicitly *before* you upgrade.

  The sharpest instances, for calibration:
  - `Settings(maxExamples: 7, seed: 42)` — the README's own example — left
    `maxRejections` at 0, and the first rejection ended the run as
    `otExhausted`. Any filtered or `assume`-using property reported exhaustion
    after about two examples, on a property that holds.
  - The symex suite's ten `const SymexSettings(...)` literals left
    `arithChecks` empty, so no arithmetic defect fork was emitted at all and
    `OverflowDefect`/`DivByZeroDefect`/`RangeDefect` were unreachable.
  - `BmcSettings(maxDepth: 5)` — the idiom `bmc.nim`'s own doc comment
    recommended — left `maxStates` at 0 and returned `bmcExhaustedBudget`
    before expanding a single state.

- **`0` now means unlimited on both `BmcSettings` caps**, matching the
  convention `ResourceBudget` already documents. It previously meant "stop
  immediately", which is the worst available reading of a value a caller might
  deliberately write.

- **An explicitly all-zero `IntegerBiasConfig` is honoured rather than
  rescued.** It was a sentinel for "use the library default"; it now means an
  unbiased uniform draw. Only affects callers who wrote the zeros on purpose.

### Deprecated

Warnings, not errors; all removed at the next major.

- `withSymexSettings` — write the `SymexSettings(...)` literal.
- `` `+` `` on `SymexSettings` and `ResourceBudget` — set the field on the base
  value. These had no production callers.
- `resolved()` — now the identity function.
- `orchestratorPolicy()` — write the `OrchestratorPolicy(...)` literal.
- `optimisedSymexSettings()` — byte-identical to `defaultSymexSettings()` since
  the Phase-2 endpoint; its doc comment claimed otherwise until now.

`defaultSettings()`, `defaultSymexSettings()`, `defaultResourceBudget()` and
`defaultIntegerBias` are deliberately **not** deprecated yet. Deprecating them
in the same release that already changes what every partial literal means would
be two migrations at once.

### Fixed

- **`examples/symex_loops.nim` had not compiled since CR-9(b)** moved the
  resource caps onto a `budget` sub-object, and **`examples/symex_oob.nim`
  compiled but failed at runtime** — Phase 15 made an out-of-bounds access a
  raise path, so `tIndexError` yields `sxRaised`/`raisedWitness`, not
  `sxSat`/`witness`. The README's own symex snippet had the same CR-9(b)
  breakage. Nothing compiled `examples/`, and compiling is not running.
- **`validateSymexSettings` is now called.** It was exported, unit-tested and
  invoked by nothing in `src/`. Its "arithChecks is empty" warning is exactly
  the defect above; it now runs at macro time on every `symexFind` and
  `assertCoveredBy`, at zero runtime cost.
- **Four registered-nowhere symex suites** (`tsymex_phase13_rlimit`,
  `_layer1_wire`, `_acceptunknown_guard`, `_unknown_roundtrip`) are registered
  in `nelli.nimble`, so they run in the sweep and in the `symex-mingw` corpus
  it derives.

### Added

- `scripts/sweep.sh` and `scripts/sweep-diff.sh` — a whole-suite parallel
  sweep and a baseline diff. There was previously no command that ran the
  whole suite: `psweep.sh` covers only `tsymex_*`, and `nimble test` is a
  serial loop that includes suites which hang on Linux. The sweep also reports
  registry drift; 92 test files on disk are registered in neither
  `nelli.nimble` nor any CI leg.
- `scripts/check-examples.sh`, plus an examples build step on the
  `symex-mingw` leg. Adding examples to `nimble test` would have bought zero
  CI coverage, because nothing in CI runs that task.

## [0.7.0] — 2026-08-29

### Fixed

- **`import nelli` no longer reaches Z3.** v0.6.0's Track-G C4 wiring made
  `fuzzmacro` auto-build a real concolic bridge for every caller, which forced
  `import ./symex` into core and pulled Z3 into the base import surface. That
  silently broke a contract `README.md` documents and `tests/tsmoke.nim`
  asserts — and `tsmoke` sat red for a whole release because no workflow ran
  it. Both the property and its CI pin are restored: a compile-only probe
  (`tests/tz3free_probe.nim`) now runs on both Windows fuzzer legs with every
  config source skipped and the nimblepath withheld, and `tsmoke` runs as a
  named step alongside it.

### Added

- **`nelli/concolic`** — the opt-in door for concolic-assisted fuzzing, and
  the only module in the fuzz stack that imports the walker.
  - `fuzzConcolic(strategy, property, settings)` — the documented default
    form. It names the strategy and property once and generates both uses, so
    the pair the campaign draws from and the pair the assist solves for cannot
    diverge.
  - `concolicAssist(strategy, property, stallRounds = 1, maxBranchAttempts = 8)`
    — builds the assist as a value, for composition.
  - `guardSolverUnavailable` — see *missing libz3* below.
- **`ConcolicAssist`** (in `nelli/fuzz`, Z3-free): a bridge plus the
  activation policy that fires it, as one value.
- **Graceful degradation when `libz3` cannot be loaded.** Previously a failed
  lazy load aborted the entire campaign — an optional feature killing the
  whole run. The assist now catches `SoftlinkError` (and only that; a solver
  that computes something *wrong* still raises), latches so a broken load is
  not retried every stall round, and reports the new `cfoSolverUnavailable`
  outcome while the campaign completes on ordinary mutation.
- **`ConcolicAssistError`** — raised at campaign start for a hand-built
  `ConcolicAssist` that names an activation policy but carries no bridge.

### Changed

- **BREAKING: `import nelli` no longer re-exports `nelli/symex`.** Concolic
  fuzzing needs `import nelli/concolic`; symbolic execution needs
  `import nelli/symex`. Forgetting the import is a compile error, never a
  silent no-op.
- **BREAKING: `GuidanceConfig.stallRounds` and
  `GuidanceConfig.concolicMaxBranchAttempts` are removed.** They were a fossil
  of auto-wiring: while core built a bridge for everyone, bridge presence
  carried no user intent, so a second knob had to. That made either-key
  omission a silent no-op. The policy now travels with the assist, and
  `stallRounds` defaults to the *active* value.
  - Migration: `fuzz(s, p, FuzzSettings(guidance: GuidanceConfig(stallRounds: 1)))`
    → `fuzzConcolic(s, p, FuzzSettings())`. The old spelling is a compile
    error naming the missing field, which is a better diagnostic than any
    runtime warning.
- **BREAKING: `fuzz`'s `concolicBridge` parameter is now `assist: ConcolicAssist`.**
  Affects direct `proc fuzz*[T]` callers only.
  - Migration: `concolicBridge = b` → `assist = ConcolicAssist(bridge: b, stallRounds: 1)`.
- **A non-nil bridge with `stallRounds <= 0` is now coerced active, not
  inert.** Assist present ⇒ assist active; "off" is spelled by passing no
  assist. This inverts the old "opt-in required" behavior *at the `fuzz` entry
  points only* — the raw `newOrchestrator` seam deliberately keeps
  `concolicBridge` and `OrchestratorPolicy.stallRounds` as independent knobs,
  where "bridge configured, `stallRounds` 0 ⇒ inert" remains the contract.
- `symexTarget` / `symexAssert` / `symexAssume` and the `assertCoveredBy`
  capture cluster moved to `nelli/engine/markers`, reachable from bare
  `import nelli`. **No migration needed** in either direction: they resolve
  under `import nelli` and are still re-exported by `nelli/symex`. This is
  what keeps marker-annotated production code compiling without a solver in
  its build.
- `docs/fuzz/INTERFACE.md` is now checked by `tests/tfuzzpackaging.nim`
  instead of being normative by convention. It had drifted.
- The package version is pinned across all three of its sites
  (`nelli.nimble`, `milpa.kdl`, `nelliVersion`), which had drifted to
  0.6.0 / 0.4.0 / 0.1.0.

## [0.6.0] — 2026-08-28

Reconstructed from the release commit (`1f50752`) because chapulin has not yet
migrated across it and 0.7.0 compounds it.

### Added

- RFC-fuzzer-nextgen: the isolated-executor track (process/fork workers, the
  centralized orchestrator, lifecycle and circuit breakers), the coverage and
  cmplog shared-memory transports, the scheduling track (Entropic power
  schedule, UCB1 operator bandit, havoc stacking, corpus culling,
  checkpointing), and the concolic-assist track.

### Changed

- **BREAKING: `FuzzSettings` was regrouped (ADR-0031).** The guided-fuzzing
  knobs moved from the flat settings object onto three nested config objects —
  `ExecutorConfig`, `GuidanceConfig`, `SchedulingConfig`. The core fields
  (`maxIterations`, `database`, `persistKey`, …) stay flat.
