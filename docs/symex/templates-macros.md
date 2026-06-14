# Templates and macros under symex (Cluster L)

> Status: confirmed and regression-guarded (Phase 15, cycles L1–L3).
> This document records *why* proptest's symbolic executor needs no
> template- or macro-specific handling, and where the trust boundary lies.

## The semchecker expands before symex sees anything

Nim's semantic-checking pass expands **all** templates and applies **all**
macros while elaborating the typed AST. Every proptest symex entry point —
`symexFind`, `symexForAll`, `assertCoveredBy` — obtains the SUT body via
`fn.getImpl`, which yields the *elaborated* `nnkProcDef`. By the time any
`macro` body (including proptest's own) runs, every template expansion has
already been reduced and every macro transformation applied along the call
graph.

Consequently `parseProc` opens with `procDef.expectKind nnkProcDef` and never
encounters an `nnkTemplateDef`, `nnkMacroDef`, or an unresolved
`nnkCall`-to-macro node. This is not a design choice — it is a property of how
Nim's macro system works.

## Trust boundary — trust the semchecker, regression-test it

Open question 1 (closed, architect bake-in): **we trust the semchecker and
encode the trust boundary as an executable regression surface.** Second-guessing
elaboration inside the walker would mean reimplementing a subset of Nim's
elaboration rules — fragile and incorrect under language evolution.

`tests/tsymex_phase15_l1_boundary.nim` is that regression surface. It defines a
SUT three ways and symexes each end-to-end:

1. **template-defined** — a `template` that expands to a `proc` definition;
2. **macro-emitted** — a `macro` that `quote do:`-emits a `proc`;
3. **`{.dirty.}` template-defined** — a non-gensym template (injects identifiers
   into the caller scope, which can produce different AST residuals than a
   vanilla template).

Each must produce a sound `SymexResult` (here `sxSat` for a reachable target).
If a future Nim version changes elaboration order or leaks a new node kind
through `getImpl`, one of these turns RED — making the breakage visible before
it can silently corrupt analysis.

**Reconciliation note (vs the RFC's L1):** the RFC specified an internal
structural assertion calling `parseProc(fn.getImpl)` and scanning the IR tree.
We verify **behaviorally** instead — symexing each SUT to a sound verdict. This
is the stronger end-to-end proof (it exercises the entire parse→walk→solve
pipeline, not just the parser's entry shape) and does not depend on the internal
`parseProc` being exported.

## Source-location behaviour

The `nnkProcDef` from `getImpl` carries the source location of the **expanded
proc declaration site**: for a template-defined proc, the template
*instantiation* site (not the template definition file); for a macro-emitted
proc, the macro emission site. Diagnostics therefore point at the user's call
site, not at template/macro internals.

## Confirmed non-scope

- **Dynamically-named SUTs.** `symexFind(fn, …)` requires `fn` to be a
  resolvable proc symbol at the call site. A SUT whose *name* is computed by a
  macro that proptest's own macro never sees cannot be symexed — there is no
  symbol to take `getImpl` of.
- **`quote`-block residuals the semchecker leaves unresolved** (e.g. spliced
  type-class constraints not concretised at the `getImpl` site): classified as a
  `SymexErrorInfo` (`seUnsupportedOp`) at walk time per invariant 3; the walker
  makes no attempt to resolve them.
- **`{.experimental: "…"}` pragma surfaces** (e.g. `strictFuncs`, `views`): any
  node kind they surface is classified `seUnsupportedOp` at parse time and is
  not a Cluster L regression.

## Cluster L is verification-only

No walker version bump, no new IR kinds, no new `SymVal` variants land in
Cluster L. If a cycle discovers a residual node the walker cannot handle, it
either extends `parseStmt`/`parseExpr` narrowly (preferred) or emits a
classified `isUnsupported` with a `SymexErrorInfo` — never a bare `sxUnknown`.
