# Closures and procs-as-values in the symex walker

> **Skeleton (authored at C0-ADR, 2026-06-15).** This is the reference doc
> for proptest's symbolic execution of closures and proc-valued data. The
> top-level structure is authored here; later Cluster-C cycles fill in each
> section as the corresponding machinery lands (see the per-section "filled in
> at" notes). The normative design rationale lives in
> [ADR-0009](ADR-0009-closure-encoding.md); this doc is the operational
> reference that explains *how the engine behaves* for SUT authors and
> contributors.

## Overview

Before Cluster C, any lambda, `proc(...) = ...` value, or call through a
proc-valued variable is classified `isUnsupported` at parse time
(`dsl_parser.nim` `parseExpr` fall-through). Cluster C brings well-formed
closures — those whose captured locals have symex-representable types — into
the analyzed fragment.

A closure is encoded as the pair `(funcSym, envRecord)`, a new `SymVal`
variant `svClosure`:

- **`funcSym`** is a Z3 uninterpreted function symbol declared once per
  syntactic lambda site, keyed by `(symBodyHash(lambdaBody), declOrderIndex)`
  (formatting-stable, not `file:line:col`).
- **`envRecord`** is an `svTuple` of the captured free-variable values,
  snapshotted at the point the lambda expression is evaluated.

Application is **lazy**: the lambda body is descended into where the closure
is *called* (`iekClosureCall`), not where it is constructed, and the body's
return value is related to `funcSym(env, args)` by a **ground, per-call-site**
implication. See ADR-0009 for the full encoding, the rejected alternatives,
and — load-bearingly — why the closure-call axiom must be ground (the G4
uninterpreted-function-over-BV hang lesson).

## Encoding

> See cycle **C2a** for implementation notes (closure construction:
> `iekLambda` → `svClosure` with environment snapshot; per-site `funcSym`
> memoization in `WalkerStatics.closureSyms`). C0-ADR records the design in
> [ADR-0009 § D1–D5](ADR-0009-closure-encoding.md); the operational walk-through
> is appended here when C2a lands.

Key points (from ADR-0009, expanded at C2a):

- The environment is a **Nim-side `svTuple`**, not a Z3 record sort; its
  leaves are flattened to individual Z3 arguments for `funcSym` (the engine
  has no Z3 aggregate sort).
- `funcSym`'s Z3 signature is `(flattened-env-leaf-sorts…, param-sorts…) ->
  ret`, with domain sorts derived at walk time by `sortOfTuple`.
- Application uses the raw `Z3_mk_app` / `Z3_mk_func_decl` FFI (the
  phantom-typed wrapper cannot express runtime-known sorts).

## Capture restrictions

> See cycle **C2a** for implementation notes. Captured locals must have
> symex-representable types; a `var T` capture (by-reference mutation through
> the closure) emits `ceUnsupportedCapture` and degrades the path to
> `sxUnknown` rather than silently mis-modelling aliased mutation.

## Closure-call dispatch and the multi-return-path axiom

> See cycle **C2b** for implementation notes. The walker descends the lambda
> body **once** per `iekClosureCall` per path, collecting one `(pc_i, v_i)`
> per body sub-path, and asserts a **GROUND** implication per sub-path:
> `implies(path.pc and pc_i, funcSym(env, args) == v_i)`, with `env`/`args`
> the concrete terms of *this* call occurrence. The call result is the
> `ite`-merge of the sub-path values. **No universal (`∀`) axiom is ever
> emitted** — that would re-introduce the G4 uninterpreted-fn-over-BV / MBQI
> hang (ADR-0009 § D6). This section documents the descent + axiom mechanics
> in full when C2b lands.

## Top-level procs as values

> See cycle **C3** for implementation notes. A module-scope proc used in
> expression position (an `nnkSym` whose type is `nnkProcTy`) is encoded with
> a **unit-sort (empty) `envRecord`**, so it shares the `(funcSym, envRecord)`
> pair encoding and the closure-call dispatch path without a special case.

## DSL higher-order functions (`map` / `fold` / `filter`)

> See cycle **C4** for implementation notes. `map`/`fold`/`filter` over
> `seq[T]` mix two strategies under `SymexSettings.inlinePolicy` (default
> `ipHybrid`): bounded **inline** unrolling for concrete short sequences
> (≤ `seqInlineThreshold`, default 8 — net-new setting), and an
> **axiomatize** path for symbolic lengths. The `filter` axiomatize branch is
> **deferred to Phase 16** (no Z3 `seqFilter` HOF in nim-z3); C4 emits
> `ceUnsupportedHof` there. Inline unrolling keeps constraints quantifier-free.

## Equality semantics

> See cycle **C5** for implementation notes. Two `svClosure` values are equal
> under **nominal-for-site + structural-for-env** (ADR-0009 § D7):
>
> - Different `(siteHash, declOrder)` → unequal (Nim-side integer-pair
>   comparison; never touches Z3).
> - Same site → equal iff their `envRecord` `svTuple`s are Z3-equal
>   (`svTupleEq`, net-new structural tuple equality added in C5).
>
> Full mechanics + the `bEq`/`bNe` walker arms documented when C5 lands.

## Generics interaction

> See cycle **C6** for implementation notes. `iekLambda` is emitted
> **post-monomorphization** (ADR-0009 § D8), so `lambdaParams` carry concrete
> types and the same lambda site at `T=int` vs `T=string` yields distinct
> `funcSym` entries and distinct canonicalize keys (no cache collision). This
> section records the closure-×-generics composition behaviour verified by the
> C6 regression smoke.

## Known divergences from Nim runtime

> See cycle **C5** for implementation notes. Notably: symex models **same-site
> environment equality structurally** (a sound field-by-field `svTuple`
> equality), whereas Nim's runtime `==` on closures compares proc-and-
> environment *pointers* and is effectively undefined for the
> environment-equality question — two distinct allocations of the same
> captured values are not pointer-equal at runtime but *are* equal under the
> symex model. The symex model is deliberately more precise here; this section
> enumerates the divergences in full when C5 lands.
