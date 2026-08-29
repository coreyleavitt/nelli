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

## [0.7.0] — unreleased

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
