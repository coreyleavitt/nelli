# ADR-0009 — Closure encoding for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-15 |
| **Deciders** | proptest maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [RFC-phase15-language-fragments.md § Cluster C](RFC-phase15-language-fragments.md), [RFC-phase15-reconciliation.md § F-C](RFC-phase15-reconciliation.md), [ADR-0008](ADR-0008-generic-instantiation.md) (generic instantiation — closures inherit its post-monomorphization timing and `symBodyHash` keying), [closures.md](closures.md) (reference doc) |

> **HEADLINE INVARIANT (read first).** The closure-call axiom that relates
> `funcSym(env, args)` to the body's return value(s) MUST be **ground**
> (asserted per call site, with the concrete `env` and `args` of that
> occurrence) — NEVER universally quantified (`∀env, args. …`). This is the
> single most load-bearing decision in this ADR. Cluster G's G4 cycle proved
> empirically that a Z3 **uninterpreted function over bit-vectors with a
> quantified axiom HANGS** (180s MBQI loop → `unknown`), and that **even a
> ground *reverse* application** of such a function (`inject(base) == dConst`)
> hangs. The decidable fragment is **QF_UFBV** — uninterpreted functions
> applied at *ground* argument tuples, with all relating constraints asserted
> as ground implications. The closure-call axiom is in exactly the same
> hazard class as G4's distinct-sort bijectivity, so it inherits exactly G4's
> mitigation: ground, per-occurrence, never `forall`. See **Decision D6**.

## Context

Before Cluster C, any system-under-test (SUT) containing a lambda
expression, a `proc(...) = ...` value binding, or a call through a
proc-valued variable is classified `isUnsupported` at parse time. The Nim
front-end never recognises a `nnkLambda` / expression-position `nnkProcDef`;
it falls through `parseExpr` to
`error("symex: unsupported expression kind … in …")`
(`dsl_parser.nim:1144`), and the Phase-14 B67 diagnostic surfaces a
`{.warning.}` for nested unsupported constructs. Closures are therefore a
genuine net-new fragment, not a hardening pass over existing machinery
(contrast Cluster G, where generics already symex'd end-to-end via
parse-time monomorphization).

First-class procs require a new symbolic-value variant because a closure is
not reducible to any existing `SVKind`. It is neither a scalar (`svInt`,
`svBV*`, `svBool`, `svFloat*`), nor a structured aggregate of scalars
(`svTuple`, `svArray`, `svSeq`), nor an opaque uninterpreted reference
(`svUninterpRef`, `svDistinct`). A closure carries **two** pieces of state
that must both participate in equality and in application: a *code identity*
(which lambda body it runs) and a *captured environment* (the values of the
free variables snapshotted at construction time). A scalar cannot encode
this pair; a plain tuple cannot encode the code identity in a way the solver
can *apply*.

**Prior art.** Symbolic-execution engines that model procedure-valued data
— KLEE, CBMC, angr — uniformly treat the callee body **lazily**: the body
is not inlined where the function value is *constructed*, but descended into
where it is *applied*, at which point the concrete (or path-constrained)
arguments are known. The function value itself is carried as a first-order
name (a pointer, a symbol). proptest adopts the same lazy-body discipline,
realised in Z3 as an uninterpreted function symbol per lambda site, with the
body's behaviour asserted as a constraint at each application.

The central question this ADR answers is therefore: **what is the symbolic
representation of a closure value, how is its identity keyed, and how is its
application modelled in Z3 without re-introducing the quantified-axiom hang
that G4 discovered?**

## Decisions

### D1. A closure is the pair `(funcSym, envRecord)`, kind `svClosure`

A closure value is encoded as an ordered pair:

- **`funcSym`** — a Z3 uninterpreted function symbol identifying *which*
  lambda body this value runs. Declared once per syntactic lambda site
  (D3). Its Z3 signature is `(envRecord_sort, params…) -> ret`.
- **`envRecord`** — the captured environment: the values the lambda's free
  variables hold on the path where the lambda expression is evaluated,
  snapshotted at *construction* time. Concretely an `svTuple` (D2).

Together this pair is a new `SymVal` variant, **`svClosure`**, introduced as
a stub in C1 (no walker descent) and wired up in C2a (construction) / C2b
(application). The `svClosure` carries:

- `closureSite: (siteHash: int64, declOrder: int)` — the lambda-site key (D3),
- `closureEnv: SymVal` — the `svTuple` environment record,
- (the per-site `funcSym` declaration itself lives in
  `WalkerStatics.closureSyms`, keyed by site + sorts — see Consequences).

Top-level procs with no captures (C3) use a **distinguished unit-sort
envRecord** (an empty `svTuple`) so they fit the same pair encoding without a
special case in the walker.

### D2. `envRecord` is a `svTuple` (Nim-side aggregate), NOT a Z3 tuple sort

The captured environment is an `svTuple` — proptest's existing aggregate
`SymVal` whose fields are a `seq[SymVal]` plus parallel `fieldNames`
(`runtime.nim:170-172`). **This is a Nim-side structure, not a Z3 tuple/
datatype sort.** proptest models every aggregate (tuples, arrays, the
discriminated parts of variants) as a Nim-side tree of leaf `SymVal`s whose
*leaves* are Z3 ASTs; there is no Z3 tuple/record/datatype sort anywhere in
the current engine. Equality, field projection, and ite-merge over
aggregates are all open-coded field-by-field over the Nim-side seq.

The consequence for closures: the RFC's literal phrasing — `funcSym`'s
domain is "the Z3 datatype sort of the environment tuple" — does **not**
match the engine as built. There is no single Z3 sort that *is* the
environment. C2b therefore takes the environment apart and passes the
captured leaves **as flattened individual Z3 arguments** to `funcSym`: the
domain is the concatenation of the per-leaf Z3 sorts (derived at walk time
by the `sortOfTuple` helper, D5), not a one-element "record sort". This is
the correct and minimal reconciliation; building a real
`Z3_mk_tuple_sort`-based record sort purely to satisfy the literal signature
would add an aggregate-sort abstraction the rest of the engine does not have
and does not need. (`Z3_mk_tuple_sort` *does* exist in `ffi.nim:781` should a
future cluster want it; Cluster C deliberately does not use it.)

### D3. Lambda-site keying: `(symBodyHash(lambdaBody), declOrderIndex)`

The lambda-site key is the integer pair
`(symBodyHash(lambdaBody), declOrderIndex)` — **NOT** `"file:line:col"`.

- `symBodyHash` hashes the *semantic* AST of the lambda body, so the key is
  **formatting-stable**: re-indenting, re-wrapping, or commenting the source
  does not change it. This is the same `symBodyHash` approach Cluster G uses
  for generic-instantiation keying (`dsl_parser.nim:1890`).
- `declOrderIndex` is the monotone integer index of the lambda declaration
  within its enclosing scope. It disambiguates two lambdas with *identical
  bodies* (e.g. two `proc(x: int): int = x + 1` in the same proc), which
  would otherwise collide on body hash alone.

The `closureSite` field on `svClosure` carries the
`(siteHash: int64, declOrder: int)` pair. String-based `lambdaSite` keys are
not introduced at all (the RFC's v1 `"file:line:col"` framing is rejected —
see Rejected Alternatives A).

**Reconciliation caveat (verify in C1).** G1a applies `symBodyHash` to a
proc *symbol* (`calleeSym`, an `nnkSym`) and carries a `lineInfo` fallback
for the empty-hash case. A lambda in expression position presents as an
`nnkLambda` / `nnkProcDef` *node*, and its body is a statement node — not
necessarily a symbol `symBodyHash` accepts directly. C1 must confirm the
exact node `symBodyHash` is applied to (the proc-def symbol if one exists,
else a structural hash of the body AST) and carry the same `lineInfo`-style
fallback ADR-0008 D2 specifies. The *decision* (formatting-stable body hash +
order index) stands; the *node plumbing* is a C1 implementation detail.

### D4. Application path: raw `Z3_mk_app`, not the phantom-typed wrapper

Closure application cannot use the phantom-typed
`Z3FuncDecl[ArgsTup, Ret]` wrapper. That wrapper fixes its domain/range
sorts as *compile-time* type parameters, but a closure's domain sorts are
known only at **walk time** (they depend on the captured-leaf types and the
monomorphized parameter types of *this* instantiation). The application path
therefore goes through the **raw FFI**:
`Z3_mk_app(ctx.raw, fd.raw, nArgs, argsPtr)` (`ffi.nim:836`), with the
func-decl built via `Z3_mk_func_decl` (`ffi.nim:842`). The result is a
`Z3AnyAst` cast to the appropriate typed wrapper via `wrap[T]` keyed on the
known return `IRType`.

This is exactly the raw-FFI discipline G4 already established for distinct
inject/eject functions ("phantom `Z3FuncDecl` unusable — runtime-known
sorts"; "`Z3_mk_app` args + func-decl domains must be HEAP seqs; intermediate
app results must be `wrap`-ped"). Closures reuse that proven pattern. C1
ships a proof-of-concept fixture validating `Z3_mk_app` over
runtime-constructed sorts before C2b wires it into the full closure-call
descent (Feas-H2 / H10).

### D5. `sortOfTuple` derives the domain sort at walk time

A helper `sortOfTuple(sv: SymVal): RawZ3Sort` derives the Z3 domain
sort(s) from the components of an `svTuple` at walk time. Because the
environment is flattened (D2), this yields the *sequence* of per-leaf sorts
that, concatenated with the parameter sorts, forms `funcSym`'s domain. The
helper is added in C1 alongside the `svClosure` stub and consumed by the
C2b application path.

### D6. Multi-return-path axiom — **GROUND, per call site** (the G4 lesson)

When the walker sees an `iekClosureCall`, it descends **once** into the
lambda's IR body — with the captured `envRecord` leaves bound in a fresh
environment and the concrete call arguments bound to the parameters — and
collects the body's return behaviour. A lambda body may have multiple return
paths (branches): the descent yields a `seq[WalkResult]`, one
`(pc_i, v_i)` per sub-path.

For **each** sub-path the walker asserts a **ground** implication:

```
implies(path.pc and pc_i, funcSym(env, args) == v_i)
```

where `env` and `args` are the **concrete (path-constrained) Z3 terms of
this specific call occurrence** — not bound variables. The overall result of
the call is an `ite`-merge of the sub-path return values under their
sub-path conditions. There is **no `forall`** anywhere in this construction.

This is non-negotiable, and it is the reason this ADR leads with the
headline invariant:

- G4 proved a Z3 **uninterpreted function over BV with a universal axiom**
  (`∀x. eject(inject(x)) == x`) **HANGS** — a 180s MBQI loop that returns
  `unknown` even with triggers.
- G4 further proved that **even a ground but *reverse* application**
  (`inject(baseSym) == dConst`, applying the fn to a symbolic argument to
  pin a value) **also hangs**. The runtime documents this verbatim at
  `runtime.nim:2440-2444`: the `inject_T(eject_T(a) op eject_T(b))` chain
  "HANGS (uninterpreted-fn-over-BV / MBQI; the G4 finding)".
- The **only** decidable model G4 found is a **ground per-occurrence pin**
  in QF_UFBV (`eject(dConst) == baseSym`, the function applied to a *ground*
  term, equated to a value).

`funcSym(env, args) == v_i` is structurally the same kind of constraint as
G4's decidable pin: the uninterpreted function applied at the **ground**
`(env, args)` of *this* occurrence, equated to a value. Asserting it under
`implies(path.pc and pc_i, …)` keeps it ground, keeps the query in QF_UFBV,
and prevents cross-path axiom accumulation from over-constraining the solver.

**Drift correction.** The RFC round-2 decision text (CRIT C4) already reads
ground/per-call-site ("for each sub-path `(pc_i, v_i)` assert
`implies(path.pc and pc_i, funcSym(env, args) == v_i)`"), and that is
correct. This ADR pins it explicitly so C2b is implemented that way and so
that no later phrasing ("the axioms relating `funcSym` to the body") is
read as licence for a universal `∀env, args` axiom. **If any cycle proposes
a universal closure axiom, it must be rejected at review:** it will hang
exactly as G4's did. (Should a non-decidable need ever arise, the correct
fallback is the G4 fallback: skip the relating constraint and emit a
classified hint, degrading to `sxUnknown`, never a quantified axiom.)

### D7. Closure equality: nominal-for-site + structural-for-env

Two `svClosure` values are equal under **nominal-for-site +
structural-for-env** semantics (closing the RFC's Open Question 6):

- If `(c1.siteHash, c1.declOrder) != (c2.siteHash, c2.declOrder)`
  — a **Nim-side integer-pair** comparison, no Z3 involved — the closures are
  unequal: emit `mkBool(false)`.
- If the site pairs are equal, the closures are equal iff their environments
  are equal: emit `c1.closureEnv == c2.closureEnv`, i.e. **structural Z3
  equality of the two `svTuple` environments** (a field-by-field conjunction
  of leaf equalities — there is no `svTuple` `==` arm in the engine today, so
  C5 adds the structural tuple-equality helper the RFC calls `svTupleEq`;
  it is net-new).

This matches Nim's runtime proc-value semantics: a proc pointer's identity
distinguishes different lambda sites, while the captured environment
distinguishes two closures from the same site. The integer-pair short-circuit
keeps the common (different-site) case entirely off the solver.

**Nim-runtime divergence.** Nim's own `==` on closure values is *not* a
defined structural comparison — comparing two closures at runtime compares
proc-and-environment *pointers*, and is effectively undefined for the
environment-equality question (two distinct allocations of the same captured
values are not pointer-equal). The symex model is therefore *more precise*
than Nim runtime for same-site environment equality: it asserts a sound
structural equality where Nim would compare allocation identity. This
divergence is documented in `closures.md § Known divergences` (C5) so users
are not surprised when symex finds a same-site environment equality that a
naive runtime `==` would not.

### D8. Monomorphization timing: `iekLambda` emitted post-monomorphization

`iekLambda` nodes are emitted **after** monomorphization — exactly as
ADR-0008 D1 establishes for generic call bodies. The parser emits an
`iekLambda` only once the containing generic proc has been instantiated at
concrete types, so `lambdaParams` always carry **concrete** `IRType` values,
never type-variable placeholders.

Consequence: the *same* lambda site instantiated at `T = int` and
`T = string` produces **two distinct** `iekLambda` nodes — different
`lambdaParams`, different flattened parameter sorts, and therefore distinct
`funcSym` entries in `WalkerStatics.closureSyms`. This mirrors G's
per-instantiation `ProcSig` and guarantees no cache collision between
instantiations (the canonicalize key includes the concrete `params=[…]`).

## Rejected alternatives

### A. `"file:line:col"` string key for the lambda site

Rejected. A source position is **formatting-sensitive**: re-indenting or
re-wrapping the source moves the column/line and breaks nominal closure
equality and the construction-cache key, for a lambda that is semantically
unchanged (Des-H6). `symBodyHash` of the body hashes the *semantic* AST and
is stable across whitespace/comment edits; `declOrderIndex` disambiguates
identical bodies. This is the same reasoning ADR-0008 D2 applies to generic
instantiation keys.

### B. Inlining the lambda body at the construction site

Rejected. Inlining the body where the closure is *constructed* (rather than
where it is *applied*) has two fatal problems: (1) at construction there is
no concrete call target — the walker would have to descend without arguments,
producing an unconstrained body walk; and (2) it duplicates the body into
*every* path that merely constructs the closure (even paths that never call
it), causing path explosion. The lazy-body discipline (descend at
application, once per `iekClosureCall` per path) is the standard KLEE/CBMC/
angr approach and is what D6 specifies.

### C. Phantom-typed `Z3FuncDecl[ArgsTup, Ret]` wrapper for application

Rejected. The wrapper's domain/range sorts are compile-time type parameters,
but closure domain sorts are runtime-known (they depend on the captured-leaf
and monomorphized-parameter types of the specific instantiation). The wrapper
cannot be instantiated at walk time. The raw `Z3_mk_func_decl` /
`Z3_mk_app` FFI path (D4) is the same one G4 already uses for distinct
inject/eject and is the only viable surface here.

### D. A real Z3 tuple/record sort for `envRecord` (`Z3_mk_tuple_sort`)

Rejected for Cluster C. The engine has **no** Z3 aggregate sort anywhere —
every tuple/array/variant aggregate is a Nim-side tree of leaf `SymVal`s
(D2). Introducing a real Z3 record sort solely to make `funcSym`'s domain a
single "record sort" would add an aggregate-sort abstraction that the rest of
the engine neither has nor needs, and would require re-expressing existing
`svTuple` equality/projection against it. Flattening the environment to its
leaf Z3 arguments (D2) reuses the existing model and is strictly simpler.
`Z3_mk_tuple_sort` remains available (`ffi.nim:781`) for a future cluster
that genuinely needs a first-class record sort.

### E. Universally-quantified closure-call axiom (`∀env, args. …`)

Rejected — see D6. A universal axiom over the uninterpreted `funcSym` is in
exactly the hazard class G4 proved hangs (uninterpreted fn over BV +
quantifier → 180s MBQI → `unknown`). The ground per-occurrence implication
is the decidable model. This alternative is called out explicitly because the
RFC's lazy-body narration ("the solver reasons over `funcSym` via the axioms
the walker asserts") could be *mis-read* as licensing a universal axiom; it
must not be.

## Consequences

### Intended

- The closure fragment becomes fully analyzable: a well-formed closure (one
  whose captured locals have symex-representable types) is descended into at
  application and modelled soundly, where it was `isUnsupported` before.
- The `(funcSym, envRecord)` encoding unifies lambdas and top-level procs
  (the latter via a unit-sort empty environment, C3) under one walker path.
- Closure equality is sound and cheap: the different-site case is an
  integer-pair comparison that never touches Z3.
- Because the closure-call axiom is **ground** (D6), the closure fragment
  stays in QF_UFBV and does not re-introduce the G4 hang.

### Net-new symbols / structures (added across C1–C5)

- `svClosure` added to `SVKind` (`runtime.nim`), with the exhaustiveness
  ripple across `walk` / `extractFromSymVal` / `allocateSym` / `tyOf` /
  `symValHash` / `iteSV` / `canonicalize` (stubs in C1, filled C2a/C2b/C5).
- `iekLambda` and `iekClosureCall` added to `IRExprKind` (`types.nim`), with
  the `iek`/`is`/`it` prefix-convention comment block (M2).
- `closureSyms` field on `WalkerStatics` (per-walker memo of per-site
  `funcSym` decls, keyed by `((siteHash, declOrder), envSortId,
  paramsSortTupleId)`). **Currently only referenced in a comment**
  (`runtime.nim:2985`); the field itself is net-new in C2a.
- `closureInlineCount` field on `CallFrameCtx` (per-frame inline budget for
  C4 HOFs). **Currently only referenced in a comment**
  (`runtime.nim:3013`); the field itself is net-new in C2a.
- `sortOfTuple(sv: SymVal): RawZ3Sort` helper added to `runtime.nim` (C1).
- `svTupleEq` structural tuple-equality helper (C5) — net-new; the engine
  has no `svTuple` `==` arm today.
- C4 settings: `seqInlineThreshold` (default 8) is **net-new** in
  `SymexSettings` (NOT present today). `inlinePolicy: InlinePolicy`
  **already exists** (`types.nim:731`, default `ipHybrid`); C4 consumes it
  and must NOT redefine it. (`maxClosureInlineCount = 64` from the settings
  family is likewise net-new if C4 wants a hard inline cap; reconcile the
  exact name against `seqInlineThreshold` at C4.)
- The `ce*` error kinds C1/C4 emit — `ceNotImplemented`,
  `ceUnsupportedCapture`, `ceUnsupportedHof` — **already exist** in
  `SymexErrorKind` (`types.nim:611`, added during Z3a). Reuse; do NOT re-add.

### Accepted as cost

- The flattened-environment encoding (D2) means `funcSym`'s arity grows with
  the number of captured leaves; deeply-capturing closures produce
  wide func decls. This is bounded by the capture-list size and is not a
  solver-theory hazard (the application is ground).
- The same-site structural environment equality (D7) is *more precise* than
  Nim runtime `==` on closures; this is documented as a deliberate divergence,
  not a bug.

### Deferred (out of scope for Cluster C)

| Topic | Future home |
|---|---|
| Closure iterators (`iterator foo(): T {.closure.}`) | Phase 16; C1 emits `ceNotImplemented` with a detail string |
| `{.closure.}` vs `{.nimcall.}` calling-convention surfaces | Cluster C assumes `{.closure.}`; nimcall proc values go through the C3 unit-env path |
| `func` purity / effect-tracking | Phase 16; symex treats `func` identically to `proc` within this cluster |
| Symbolic `filter` over `seq[T]` (axiomatize branch) | Phase 16; C4 emits `ceUnsupportedHof` (no Z3 `seqFilter` HOF in nim-z3 today) |
| `var T` capture | C2a emits `ceUnsupportedCapture` |

## Validation

ADR-0009 is validated by the Cluster C test suite:

- **C1 DoD** — `iekLambda` / `iekClosureCall` IR round-trips through
  `canonicalize`; two-instantiation (`T=int`/`T=string`) keys are distinct
  (D8); the `Z3_mk_app` PoC fixture accepts a runtime-constructed func decl
  over `sortOfTuple`-derived sorts (D4/D5); closure iterators emit
  `ceNotImplemented`, not a crash.
- **C2a DoD** — an `iekLambda` capturing a local produces an `svClosure`
  whose `closureEnv` holds the correct captured `SymVal`s (D1/D2);
  `closureSyms` memoizes one `funcSym` per `(site, sorts)`.
- **C2b DoD** — a **two-branch** lambda body produces **both** ground axiom
  arms under their sub-path conditions (D6); no `forall` is emitted; the call
  result is the `ite`-merge. **No hang** under the bounded runner — the
  load-bearing G4-lesson check.
- **C5 DoD** — different-site closures compare unequal via the integer-pair
  short-circuit; same-site closures compare via `svTupleEq` structural
  environment equality (D7); the Nim-runtime divergence is documented.
- **C6 DoD** — Cluster-C regression smoke vs Cluster G; walker version bumped
  `"8" → "9"`.
