# Extracting symex as `nim-symex`

When a second non-PBT consumer surfaces, the symex package becomes a
candidate for extraction into its own library. This document
records the concrete steps, the boundary leaks the
[boundary report](#boundary-report) identifies, and the resolution
for each.

## Trigger condition

Two of the following:

- A non-PBT consumer adopts symex (e.g. a static analyser, a
  verification CLI, a coverage-guided fuzzer that doesn't want
  nelli's engine).
- The nelli maintainers want to ship symex on its own release
  cadence.
- The substrate (`nim-z3`) version nelli needs lags or leads
  what symex needs.

Single-criterion extraction is premature. The `symex/` package is
small enough that carrying it inside nelli costs nothing today.

## Module-boundary state (as of Phase 9)

Run `nim r scripts/symex_boundary_report.nim` to refresh. Current
totals:

| Category | Count |
|---|---|
| in-package (`smt/*` + `symex.nim`) | 15 |
| nelli-shared (extraction targets) | 3 |
| substrate (`z3`) | 2 |
| nim-stdlib | 19 |

The three nelli-shared imports are the entire surface to be
re-routed for extraction.

## The three extraction targets

### 1. `choice` (`nelli/choice`)

**Why symex needs it**: `renderAsChoices[T](w: T): seq[ChoiceNode]`
linearises a witness into the regression-seed format. Used by
`saveSymexWitness` / `loadSymexWitnesses`.

**Resolution**: `ChoiceNode` is a generic, self-contained type for
"recorded primitive draw". It belongs to nelli's PBT engine
conceptually, but the type itself has no PBT dependencies.

**Recommended path**: extract `ChoiceNode` + the constructors
(`integerChoice`, `booleanChoice`, `stringChoice`, …) into a tiny
shared package — e.g. `nim-choice-ir` — that both `nelli` and
`nim-symex` depend on. Effort: half a day; the file is ~400 lines
and has no transitive nelli deps.

**Alternative**: define a local `SymexChoice` type in `nim-symex`,
with an adapter on nelli's side that converts. Decoupled but
duplicates the type definition. Choose if `nim-choice-ir` would be
the only shared library and that overhead isn't justified.

### 2. `db` (`nelli/db`)

**Why symex needs it**: `saveSymexWitness` / `loadSymexWitnesses`
use the example DB's `save` / `loadPrimary` operations with a
Z3-version-tagged testId.

**Resolution**: the DB is more deeply PBT-shaped than `choice` —
it deals with `Settings.testId`, secondary entries with Pareto
scores, etc. Symex only needs primary `save` / `loadPrimary` and
`removeMany`.

**Recommended path**: in `nim-symex`, declare a
`SymexWitnessStore` protocol (closure-based, like the existing
`ExampleDatabase`):

```nim
type SymexWitnessStore* = object
  saveImpl*:  proc(key: string, choices: seq[SymexChoice])
  loadImpl*:  proc(key: string): seq[seq[SymexChoice]]
```

Adapter on nelli's side wraps `ExampleDatabase` to satisfy
this protocol. Effort: a few hours.

### 3. `engine/types` (`nelli/engine/types`)

**Why symex needs it**: `SymexFinding` and `SymexFindingStatus`
live there so `Report[T].symexFindings` can carry them.

**Resolution**: this is the wrong direction of dependency. `engine`
imports `symex` thematically — nelli's engine integrates with
symex, not the other way around.

**Recommended path**: move `SymexFinding` to `nim-symex/types`.
Nelli's `engine/types` imports `nim-symex/types` to embed the
field in `Report[T]`. The current "string-typed `targetDesc` to
avoid a smt/types dep" workaround disappears — `nim-symex/types`
can hold the typed `SymexTarget` directly.

This is the cleanest extraction win: the workaround was already
a smell.

Effort: one PR. Trivial mechanically; the constraint is just
ordering the dependency the right way.

## Checklist

1. **Extract `nim-choice-ir`** (or commit to the `SymexChoice`
   alternative). Verify nelli tests pass against the extracted
   `choice` import. Tag `nim-choice-ir` v0.1.
2. **Create the `nim-symex` repo** with:
   - `src/symex/` containing the current contents of
     `src/nelli/smt/**` and `src/nelli/symex.nim` (renaming
     `nelli/symex.nim` → `symex.nim`).
   - `src/symex/types.nim` containing the moved `SymexFinding`.
   - A `nimble` file pinning `nim-z3` and `nim-choice-ir` (or
     the SymexChoice equivalent).
3. **Reverse the `engine/types` ↔ `SymexFinding` dependency**:
   - Delete `SymexFinding` from `nelli/engine/types.nim`.
   - Import `nim-symex/types` into `nelli/engine/types.nim`.
   - Re-export so existing callers still see `SymexFinding`
     through `nelli/engine`.
4. **Replace `db` import** with the `SymexWitnessStore` protocol +
   nelli-side adapter.
5. **Rename test files** in nelli:
   - `tests/tsymex_*.nim` → these stay in nelli (they test the
     nelli-side integration).
   - Mirror the core fragment tests inside `nim-symex/tests/`.
6. **Update `docs/symex/`** in nelli to reference
   `nim-symex` as the upstream; keep the integration story local.
7. **Tag `nim-symex` v0.1**. Pin to it in nelli's
   `nelli.nimble`.

## What does *not* need to change

- The IR types (`IRType`, `IRStmt`, `IRExpr`, etc.) — already
  self-contained in `smt/types.nim`.
- The walker, parser, abstraction layer, runtime — entirely
  in-package.
- The Z3 substrate — `nim-z3` is already a separate library,
  pinned by both nelli and the (future) `nim-symex`.
- The `{.symexOpaque.}` pragma — declared in symex.nim, ports
  verbatim.
- Public API of `assertCoveredBy`, `symexFind`, marker procs —
  the surface is already the right shape for extraction.

## Boundary report

The companion script
[`scripts/symex_boundary_report.nim`](../../scripts/symex_boundary_report.nim)
produces the live import inventory. Re-run it after any change to
symex's imports to confirm the boundary stays minimal. The CI
target should fail loud if `nelli-shared` grows beyond the
three current targets without a corresponding update to this
checklist.

## References

- [README.md](README.md) — public surface
- [SYMEX_PLAN.md § Phase 9](../SYMEX_PLAN.md) — the phase that
  produced this checklist
- [Ousterhout, *A Philosophy of Software Design*, Ch. 4 — Deep Modules](https://web.stanford.edu/~ouster/cgi-bin/aposd.php)
  — the principle behind extracting a small, deep interface
