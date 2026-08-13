# Templates and macros under symex (Cluster L)

> Status: confirmed and regression-guarded (Phase 15, cycles L1–L3).
> This document records *why* nelli's symbolic executor needs no
> template- or macro-specific handling, and where the trust boundary lies.

## The semchecker expands before symex sees anything

Nim's semantic-checking pass expands **all** templates and applies **all**
macros while elaborating the typed AST. Every nelli symex entry point —
`symexFind`, `symexForAll`, `assertCoveredBy` — obtains the SUT body via
`fn.getImpl`, which yields the *elaborated* `nnkProcDef`. By the time any
`macro` body (including nelli's own) runs, every template expansion has
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
  macro that nelli's own macro never sees cannot be symexed — there is no
  symbol to take `getImpl` of.
- **`quote`-block residuals the semchecker leaves unresolved** (e.g. spliced
  type-class constraints not concretised at the `getImpl` site): classified as a
  `SymexErrorInfo` (`seUnsupportedOp`) at walk time per invariant 3; the walker
  makes no attempt to resolve them.
- **`{.experimental: "…"}` pragma surfaces** (e.g. `strictFuncs`, `views`): any
  node kind they surface is classified `seUnsupportedOp` at parse time and is
  not a Cluster L regression.

## `untyped` template parameters (L2)

`untyped` template parameters defer typechecking until expansion, but by
`getImpl` time the semchecker has produced a fully-typed body. Verified
(`tests/tsymex_phase15_l2_untyped_template.nim`):

- An `untyped`-param template expanding to supported nodes symexes to a sound
  verdict (`sxSat`).
- A template whose expansion *constrains* the path (`if n != 5: return`) is
  **faithfully walked** — the early return is honored, so a downstream
  contradiction (`n == 6`) is correctly `sxUnsat`. Were the expansion dropped,
  the contradiction would look reachable. This proves untyped-template bodies are
  symexed, not skipped.

### Known limitation — `isUnsupported` statements are skipped, not halted

Discovered during L2: when the parser classifies a *statement* as
`isUnsupported` (`mkUnsupported(reason)` — e.g. `try`/`except`, not modelled
until Cluster E), the walker currently handles it with `of isUnsupported:
discard` and continues the path **without** marking it uncertain. Consequences:

- **Sound** when the skipped construct has no effect on the target's
  reachability (e.g. a no-op `try: discard except: discard` — the verdict is
  unchanged and correct).
- **Conservative-incompleteness risk** if a skipped unsupported statement *did*
  have a target-relevant effect: the verdict could be wrong rather than
  `sxUnknown`. This is a **pre-existing** behaviour (not introduced by Phase 15),
  and the window shrinks as later clusters model these constructs (E: exceptions,
  R: ref/heap, etc.). The reason string lives on the internal `RawResult`; the
  public `SymexResult` exposes only `status` (no `errors` surface).
- **Future work (not L2):** per invariant 3, hitting an `isUnsupported` node
  should mark the path `sxUnknown`. Changing it requires care — existing tests
  may rely on the current skip for no-op unsupported constructs — so it is
  tracked here rather than forced into a verification cycle.

## `getAst` / `quote do` macros (L3)

Verified (`tests/tsymex_phase15_l3_quote_do.nim`):

- A `quote do` macro that emits a SUT calling a symex-known stdlib op (`s.len`)
  is **walker-identical** to a hand-written twin — both reach `sxSat` on the same
  target. The macro-construction layer adds nothing the walker can observe.
- A `quote do` macro emitting a call to a **user-defined generic** proc
  (`doubleOrd[T: Ordinal]`) symexes soundly: the parser monomorphizes the generic
  before walking, so the inlined concrete body is analysed and the reachable
  target is found (`sxSat`).

### Minor finding — expression-`if` (`nnkIfExpr`) is unsupported

A generic body written as an expression-`if` (`if a: x elif b: y else: z`,
`nnkIfExpr`) is rejected by `parseExpr` with a **compile-time** error (not a
runtime verdict). This is a general expression-parsing limitation (statement-`if`
is supported; expression-`if` is not), surfaced here because inlined proc bodies
can contain it. Use statement form in symex-targeted SUTs.

## Cluster L is verification-only

No walker version bump, no new IR kinds, no new `SymVal` variants land in
Cluster L. If a cycle discovers a residual node the walker cannot handle, it
either extends `parseStmt`/`parseExpr` narrowly (preferred) or emits a
classified `isUnsupported` with a `SymexErrorInfo` — never a bare `sxUnknown`.
