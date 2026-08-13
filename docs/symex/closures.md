# Closures and procs-as-values in the symex walker

> **Skeleton (authored at C0-ADR, 2026-06-15).** This is the reference doc
> for nelli's symbolic execution of closures and proc-valued data. The
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
  syntactic lambda site, keyed by `(siteHash, declOrder)`. **Site-keying
  reality (C1):** a *nameless* lambda (`nnkLambda` / expression-position
  `nnkProcDef`) has **no symbol** for `std/macros.symBodyHash` to hash, so the
  RFC's `symBodyHash(lambdaBody)` does **not** apply; C1 uses the ADR-0008 D2
  **`lineInfo`** fallback — `siteHash = hash("file:line:col")` of the lambda
  node — with `declOrder` from a per-parse `lambdaCounter`. A *top-level* proc
  used as a value (C3) **does** have a symbol, so it reuses `symBodyHash` with
  the same `lineInfo` fallback and `declOrder = 0`. The practical consequence
  (see *Equality semantics* and *Known divergences*): lambda-site identity is
  POSITION-based for nameless lambdas — two lambdas at different source
  positions are different sites even if textually identical, and a lambda at a
  *fixed* position keys stably across runs (a comment inside the body does not
  move its declaration `line:col`).
- **`envRecord`** is an `svTuple` of the captured free-variable values,
  snapshotted at the point the lambda expression is evaluated.

Application is **lazy**: the lambda body is descended into where the closure
is *called* (`iekClosureCall`), not where it is constructed, and the body's
return value is related to `funcSym(env, args)` by a **ground, per-call-site**
implication. See ADR-0009 for the full encoding, the rejected alternatives,
and — load-bearingly — why the closure-call axiom must be ground (the G4
uninterpreted-function-over-BV hang lesson).

## Encoding

**Implemented at C2a** (`runtime.nim` `buildClosure`, dispatched from
`lower(iekLambda)`). Constructing a closure does three things and adds **no Z3
assertion** (no body descent at construction):

1. **Environment snapshot.** Each captured free-variable name (computed at
   parse time by the C1 scope-stack diff) is looked up in the *current* env and
   its `SymVal` collected, in capture order, into an `svTuple` `closureEnv`. A
   capture absent from the env is dropped (the `funcSym` domain follows the
   snapshot). An empty capture list yields a **zero-field `svTuple`** unit-env
   (the C3 top-level-proc case).
2. **Per-site `funcSym`.** Get-or-create the uninterpreted func-decl over
   runtime-known sorts via raw `Z3_mk_func_decl` (+ `incRefFD`). Memoized in
   the `currentClosureSyms` threadvar keyed by
   `((siteHash, declOrder), envSortId, paramsSortTupleId)` — so the SAME site
   at two monomorphizations (distinct env-leaf / param sorts, D8) gets distinct
   funcSyms — and mirrored onto the `WalkerStatics.closureSyms` field after the
   walk. `lower` runs in the pure env→SymVal evaluator with no `WalkCtx` in
   scope, hence the threadvar (the same pattern G4 uses for `currentDistinctSorts`).
3. **Assemble** `svClosure{closureSite, closureEnv, closureRawFD}`.

Key points (from ADR-0009):

- The environment is a **Nim-side `svTuple`**, not a Z3 record sort; its
  leaves are flattened to individual Z3 arguments for `funcSym` (the engine
  has no Z3 aggregate sort).
- `funcSym`'s Z3 signature is `(flattened-env-leaf-sorts…, param-sorts…) ->
  ret`, with domain sorts derived at walk time by `sortOfTuple`.
- Application uses the raw `Z3_mk_app` / `Z3_mk_func_decl` FFI (the
  phantom-typed wrapper cannot express runtime-known sorts).
- `svClosure` carries the *site key* + *env* + *funcSym*, **not** the lambda
  body IR; `buildClosure` separately stashes the body + signature into the
  `currentClosureBodies` site→body map for the call to descend (C2b).

## Capture restrictions

**Implemented at C1/C2a.** Captured locals are enumerated by a parse-time
scope-stack diff: the lambda body's `nnkSym` references whose `symKind ∈
{nskParam, nskLet, nskVar, nskForVar}` (runtime VALUE bindings — top-level
procs/types/consts are excluded by `symKind`), minus the lambda's own params
and body-local definitions. Captured locals must have symex-representable
types. A `var T` capture (by-reference mutation through the closure) emits
`ceUnsupportedCapture` (sevError) and degrades the path to `sxUnknown` rather
than silently mis-modelling aliased mutation (Invariant 3). Because the
environment is snapshotted **by value** at construction, symex models a closure
as capturing the *values* present when the lambda expression is evaluated.

**`ref T` / `ptr T` captures — SUPPORTED since R13.** Once the Cluster-R logical
heap exists, a closure may capture an `svRef`/`svPtr` free variable: the env
snapshot collects the captured ref's `svRef` SymVal (the SAME `Ref_T` address
const the outer scope holds — `SymVal` is a value type, so the copy shares the
underlying Z3 const), the closure `funcSym` domain flattens that const like any
other leaf, and CALLING the closure derefs the captured ref through `path.heaps`
exactly as any other `svRef` deref does (the heap threads in via R1b's
call-frame mechanism). So a closure that captures a `ref int` local and, when
called, observes a heap write committed before the closure was constructed is
modelled soundly. R13 lifts the prior `ceUnsupportedCapture` restriction for
ref/ptr captures (in practice the classification was only ever *declared* — the
construction path always snapshotted whatever SymVal was in the env, and the R9
`svRef`/`svPtr` arms on `rawAnyAstOf`/`flattenLeafAsts`/`sortOfTuple` already
made the flatten/apply sound). `extractFromSymVal` for a captured `svRef`/`svPtr`
field follows it through the heap to recover the `pointsTo` pointee in the
witness.

## Closure-call dispatch and the multi-return-path axiom

**Implemented at C2b** (`runtime.nim` `lowerClosureCall` → `applyClosureGround`,
dispatched from `lower(iekClosureCall)`). For each `iekClosureCall`:

1. **Resolve** `ccCallee` to an `svClosure` in the current env — a
   C2a-constructed lambda **or** a proc-valued *parameter* (same dispatch, no
   special case). An unresolved callee → `ceClosureUnknownCallee` / sxUnknown
   (Invariant 3).
2. **Apply** the per-site `funcSym` at the **GROUND** `(env, args)` of *this*
   occurrence via raw `Z3_mk_app` over the flattened env-leaf asts ++ flattened
   call-arg asts (`flattenLeafAsts`, the ast-side mirror of `sortOfTuple`). The
   wrapped application IS the call's result `SymVal`.
3. **Descend** the lambda body **once** (reached via the `currentClosureBodies`
   site→body map; `lower` reaches the live walk through the `currentWalkCtxPtr`
   threadvar), harvesting one `(pc_i, v_i)` per return sub-path from both the
   explicit-`return` channel and the implicit-`result`/fall-through channel.
4. **Assert** a **GROUND** implication per sub-path:
   `implies(and(branch_conds_i), funcSym(env, args) == v_i)` into
   `currentClosureCallAxioms` (drained into every `trySolve`). With multiple
   sub-paths these implications collectively pin the result (one per arm,
   vacuously true off its branch).

**No universal (`∀`) axiom is ever emitted** — `funcSym` is applied at the
ground occurrence and equated to a value, the same decidable QF_UFBV shape as
G4's eject-pin; a `∀env,args` axiom would re-introduce the G4
uninterpreted-fn-over-BV / MBQI hang (ADR-0009 § D6). A per-frame
`closureInlineCount` budget (vs `SymexSettings.maxClosureInlineCount`, default
64) bounds nested descent; overflow → `ceInlineBudgetExceeded` / sxUnknown.

## Top-level procs as values

**Implemented at C3.** A module-scope proc used in expression (value) position
— `let g = double`, or `double` passed as a proc-valued argument — is detected
in the bare-`nnkSym` value branch of `parseExpr` (`symKind == nskProc` with a
resolvable `nnkProcDef` `getImpl`) and encoded as an `iekLambda` with
`lambdaCaptures = @[]`: a **unit-env closure** (zero-field `svTuple` env). It
reuses the C2a `buildClosure` construction and C2b `lowerClosureCall` dispatch
wholesale — no new walker semantics. The value-vs-callee distinction is
**structural, not heuristic**: a proc in callee position (`double(n)`) is
parsed structurally as a normal call and never reaches this branch; a call
through a proc-valued local (`g(n)`) is C2b's `iekClosureCall`; a proc-valued
*param* is `nskParam` (≠ `nskProc`). The proc-as-value call gives the SAME
witness and verdict as a direct call (the encoding is semantically
transparent). Unlike a nameless lambda, a top-level proc **has** a symbol, so
its site key uses `symBodyHash` (with the lineInfo fallback), `declOrder = 0`.

## DSL higher-order functions (`map` / `fold` / `filter`)

**Implemented at C4.** A parser `hofDispatch` block intercepts
`filter`/`map`/`fold` **guarded on origin** (`calleeSym.owner.strVal ==
"sequtils"`) → `iekHofCall`; a same-named non-sequtils proc owns to its own
module and falls through to a normal call (no hijack). `map`/`filter` over
`seq[T]` mix two strategies under `SymexSettings.inlinePolicy` (default
`ipHybrid`):

- **Inline** (concrete length ≤ `seqInlineThreshold`, default 8 — net-new
  setting): unroll `0..<N` and apply the closure per element via
  `applyClosureGround` (the C2b ground funcSym-app + body-descent + GROUND
  axiom, reused once per element); map = per-element store, filter = compacted
  keep-mask. Quantifier-free, bounded by N.
- **Axiomatize** (symbolic length): map → `mapArray` (Z3 `Z3_mk_map`, a
  *decidable pointwise* array-map — NOT a universal-∀ — so it terminates;
  capture-free int→int only); **filter → `ceUnsupportedHof` (sxUnknown)**,
  deferred to **Phase 16** (no Z3 `seqFilter` HOF in nim-z3).

`std/sequtils` `foldl`/`foldr` are **templates** the typed macro expands to a
`for…items` loop before the parser runs, so the realised closure HOFs are
`map`/`filter` (real `{.closure.}` procs).

## Equality semantics

**Implemented at C5** (`runtime.nim` `closureEq` / `svTupleEq` / `svLeafEq`,
dispatched from the `bEq`/`bNe` arm of `lower(iekBinop)` when **both** operands
resolve to `svClosure`). Two `svClosure` values are equal under
**nominal-for-site + structural-for-env** (ADR-0009 § D7):

- **Different site.** If `(c1.siteHash, c1.declOrder) != (c2.siteHash,
  c2.declOrder)` — a pure **Nim-side integer-pair** comparison, no Z3 involved
  — the closures are **always unequal**: `==` → `mkBool(false)`, `!=` →
  `mkBool(true)`. Two closures from different syntactic lambda sites are
  unequal regardless of their environments, and the common different-site case
  stays entirely off the solver.
- **Same site.** If the site pairs are equal, the closures are equal iff their
  captured environments are equal: `c1.closureEnv == c2.closureEnv` via the
  **net-new `svTupleEq`** — a field-by-field Z3 conjunction of leaf equalities
  over the two `svTuple` environments. (There was no `svTuple` `==` arm in the
  engine before C5.) `svTupleEq` recurses through nested tuples and
  concrete-length arrays, dispatches each leaf through `svLeafEq` (int/bool/
  BV/float/string; `svDistinct` ejects to its base and recurses), and treats a
  **zero-field unit-env** (top-level proc, C3) as vacuously equal
  (`mkBool(true)`). `!=` negates the conjunction.

**Site keying caveat (C1 reality).** Because a nameless lambda's `siteHash`
is `lineInfo`-based (see *Encoding*), "same site" means *same source position*,
not "textually identical lambda" — two textually identical lambdas at different
positions are *different* sites (correctly: they are different lambda sites).
The same lambda at a fixed position keys stably, so two closures derived from
one site (e.g. one bound then aliased, or constructed twice from one syntactic
lambda) take the structural-env branch.

## Generics interaction

Closures compose with Cluster G's generic instantiation machinery because
`iekLambda` is emitted **post-monomorphization** (ADR-0009 § D8): by the time
the parser reaches a lambda, the enclosing generic has already been
monomorphized by the Cluster-G path (the ADR-0008 D2 instantiation key,
`instKeyFor` / `gatherTypeSubst` / `monomorphize`), so `lambdaParams` carry
**concrete** types. The same lambda site at `T=int` vs `T=string` therefore
yields distinct `funcSym` entries (the `ClosureSymKey` includes the flattened
env-leaf and param **sort fingerprints**, `Z3_get_sort_id`) and distinct
canonicalize keys — no cross-instantiation cache collision (the same
distinct-key discipline ADR-0008 establishes for generic `ProcSig`s).

The headline composition is a **generic higher-order proc with a closure
argument**:

```nim
proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))
proc sut(n: int): int = applyTwice(proc(x: int): int = x + 1, n)
```

Here Cluster G's `classifyProcTy` must survive `monomorphize` substitution
(`T → int`): the monomorphized `proc(x: int): int` formal arrives as a
synthesized `nnkProcTy` carrying no resolved type, so `classifyType` matches it
**structurally before** `getTypeInst` (→ the `__closure` placeholder), and the
closure CALL `f(f(v))` is detected early in `parseExpr`
(`earlyClosureCallDetect`). The proc-valued parameter `f` is then resolved as
an `svClosure` (NOT `ceClosureUnknownCallee`) by the same C2b dispatch that
handles a locally-bound lambda — there is no separate path. `applyTwice`
applies `f` twice: `(n+1)+1 == n+2`; gated at 42, symex witnesses `n == 40`.

**Why the two clusters' state does not collide.** The Cluster-G instantiation
cache (`WalkCtx.instantiationCache` / `ctx.procs` keyed by `instKeyFor`) and the
Cluster-C closure state (`currentClosureSyms`, `currentClosureBodies`,
`WalkerStatics.closureSyms`) live in **disjoint scopes** — the former keys on the
generic proc's instantiation, the latter on the lambda's `(siteHash, declOrder)`
+ sort fingerprints. The C6 regression smoke
(`tests/tsymex_phase15_C6_smoke.nim`) exercises the `applyTwice[T]` composition
alongside the full C1–C5 surface and the Cluster-G sample suite; it found **no
state-threading regression** (no production change beyond the walker version
bump). See also ADR-0008 (instantiation keying) and ADR-0009 (closure encoding).

## Known divergences from Nim runtime

**Documented at C5.** The known divergences between the symex model and Nim
runtime behaviour for closures:

- **Closure equality.** Nim's runtime `==` on closure values is **undefined**
  for the environment-equality question: it compares proc-and-environment
  *pointers* (and a bare `proc ==` may be rejected), so two distinct
  allocations of the same captured values are *not* pointer-equal at runtime.
  The symex model is deliberately **more precise**: under nominal-for-site +
  structural-for-env (D7) two same-site closures with structurally-equal
  captured environments compare **equal**. SUT authors should not expect symex
  closure `==` to mirror a runtime `==`; the symex semantics are the *defined*
  ones (and are sound for correctness reasoning). Different-site closures are
  always unequal under both models.
- **Multi-return-path application (C2b).** A closure call is modelled by a
  ground per-sub-path axiom relating `funcSym(env, args)` to each body return
  value; this is an exact model of the body's value, not a runtime call. The
  `funcSym` is left **opaque** in the symbolic-length HOF `map` axiom path
  (C4) — a sound over-approximation.
- **By-value capture.** The environment is snapshotted by value at
  construction; a `var T` capture (by-reference local mutation through the
  closure) is classified `ceUnsupportedCapture` rather than modelled (Invariant
  3). A `ref T` / `ptr T` capture, however, IS modelled since R13: the captured
  ref's address const is snapshotted by value, but the heap CELL it points at is
  shared mutable state — a write through the captured ref (or through any alias)
  is observed on subsequent derefs via the logical heap.

These divergences are the closure-specific rows of the engine's
known-divergences ledger; see also [determinism.md](determinism.md).
