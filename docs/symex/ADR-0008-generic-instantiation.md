# ADR-0008 — Generic instantiation policy for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-06 |
| **Deciders** | proptest maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [RFC-phase15-language-fragments.md § Cluster G](RFC-phase15-language-fragments.md), [ADR-0001](ADR-0001-integer-semantics.md) (integer semantics), [ADR-0002](ADR-0002-dsl-factoring.md) (DSL factoring), [ADR-0003](ADR-0003-variant-soundness.md) (variant soundness), [ADR-0004](ADR-0004-frontier-pruning.md) (frontier pruning) |

## Context

Nim's semchecker performs full per-call-site monomorphization before
proptest's macro ever sees the typed AST. Every call to `proc foo[T](x:
T): T` at a given `T` already has a fully concrete body: the semchecker
has substituted the type parameter, checked constraints, and resolved
overloads. The symex walker receives this post-monomorphization AST.

The central question is: should the symex engine model generics
symbolically (treating `T` as a Z3 type variable), or should it replicate
the per-call-site monomorphization that the semchecker already performed?

This ADR records the decision, the rationale, the instantiation-key
schema, the cache structure, the `distinct T` encoding, the concept
policy, the cap, and the rejected alternatives.

## Decisions

### D1. Per-call-site monomorphization, no symbolic generic walking

The symex walker performs **per-call-site monomorphization** matching
Nim's own compilation model. For each `isGenericCall` IR node the
walker encounters, it:

1. Reads the `gcTypeArgs` tuple from the IR node (populated by the parser
   from the semchecker's typed AST at macro-expansion time).
2. Looks up the cached `ProcSig` under the instantiation key.
3. If not cached, parses the callee's `getImpl` body under the type
   substitution from `gatherTypeSubst`, registers the monomorphized
   `ProcSig`, and delegates to the existing `isCall` walk path.

The parsed body at each instantiation is the **exact code the program
runs** — the same code the Nim compiler emits for that call site. This
makes the approach sound by construction: the symex models what
actually executes.

### D2. Instantiation-key schema

Keys in `ParseCtx.procs: Table[string, ProcSig]` follow two coexisting
forms:

- **Generic procs**: `name#typeargs` (e.g. `"foo#int"`, `"foo#int;string"`)
- **Non-generic procs**: `name` (e.g. `"bar"`)

`name` is derived from `symBodyHash(calleeSym)` (Nim's `std/macros`
`symBodyHash`). This hash is stable across compilations for the same
body and is **module-disambiguating**: two procs with the same source
name in different modules produce different hashes because `symBodyHash`
encodes the full module path and body identity, not just the surface
spelling.

**Fallback when `symBodyHash` returns 0 or is unavailable**: use
`getImpl.lineInfo.filename & ":" & calleeSym.strVal`. This encodes the
defining module's file path plus the proc name, which is unambiguous
for any two source procs as long as no file has two procs with the same
name (which is a Nim compile error anyway). The fallback is explicitly
**not** `repr(calleeSym.getImpl).hash` — `repr` is structurally
ambiguous across modules (two identical-body procs in different modules
produce identical `repr` strings) and does not survive across
recompilations (Feas-H5).

Type-arg tuple encoding for multi-param generics: sorted by formal
param name, joined by `";"`. Sorting ensures canonical key identity
regardless of syntactic argument order at the call site (see D6).

Static-param values included as `";static=" & $val` (see G7).

### D3. Instantiation cache

```
ParseCtx.instCache: Table[string, ProcSig]
ParseCtx.instCountPerProc: Table[string, int]
```

- `instCache` is **per-walker** (lives on `ParseCtx`, which is created
  once per `runSymex` call and not shared across concurrent walkers).
- Two call sites instantiating the same generic proc at the same type
  tuple share **one `ProcSig`** — the body is parsed exactly once.
- The `when defined(proptest_testing): cacheHitsFor(ctx, key): int`
  test accessor enables DoD assertions.
- The parse-time `instCache` is distinct from the verdict cache (the
  DB layer keyed by SUT hash + settings). They operate at different
  levels of the stack and must not be confused.

### D4. `distinct T` as a fresh uninterpreted Z3 sort

When a user writes `type Meters = distinct float`, the semantic intent
is a type-level wall between `Meters` and `float`. The symex engine
honors this wall:

- `distinct T` maps to a new **uninterpreted Z3 sort** allocated via
  `mkUninterpretedSort(ty.distinctName)` from `sort.nim`.
- The phantom-typed `Z3UninterpretedVal[T]` API is **not** used here
  because `T` is a runtime-known type name, not a compile-time type
  parameter.
- Two uninterpreted functions are declared per distinct type:
  `inject_T: Base → Distinct` and `eject_T: Distinct → Base`.
- **Bijectivity axioms** are asserted at sort-allocation time, but
  **only for base types in the decidable fragment** `{int, BV, bool}`.
  For base types in `{FP, String}`, bijectivity is skipped and a
  `geDistinctBijectivitySkipped` error (severity: `sevHint`) is emitted.
  Rationale: universally-quantified axioms over FP or string sorts push
  Z3 into the incomplete quantified fragment, producing `UNKNOWN` rather
  than `SAT`/`UNSAT`. The hint informs users that the distinct sort is
  modeled without the round-trip guarantee.
- **Bijectivity axioms are asserted at most once per `(sortName,
  runSymex)`**. The cache key is the sort name (equal to the distinct
  type name) together with the walker identity. A SUT using `Meters` in
  both caller and callee allocates exactly one `distinctSorts` entry.
- **Distinct sort cache** lives on `WalkerStatics.distinctSorts:
  Table[string, Z3Sort[stUninterpreted]]` (per-walker, shared across
  all call frames). It does **not** live on `WalkCtx` directly or on
  any per-frame structure.
- **Nested distinct chains** (`type KiloMeters = distinct Meters`) are
  supported: ejection recurses through the chain; bijectivity is asserted
  at each level (where the base is in the decidable fragment).

Witness extraction for `distinct`-typed SUT params goes through
ejection: `eject_T(witness)` is called, then the base-type extractor
is applied. This is not a conservative approximation — it is the correct
model. A symex that aliased `Meters` to `float` would prove false
equalities and miss real type-boundary bugs.

### D5. Concept policy: stdlib table vs user trust

| Concept source | Policy |
|---|---|
| Stdlib (`SomeNumber`, `SomeInteger`, `SomeFloat`, etc.) | Validated against a compile-time membership table in the walker (`ProcSig.conceptConstraints`). Non-conformance → `geConceptViolation`. |
| User-defined concepts | Trust the Nim semchecker. The semchecker verified the constraint at the call site before proptest's macro saw the typed AST. `geConceptViolation` fires only for test-injected invariant violations, not real Nim source. |

Rationale: re-validating user concepts at walker time would require the
walker to execute arbitrary constraint bodies symbolically — a
bootstrapping problem. The semchecker is the authoritative enforcer.

### D6. Multi-param instantiation key is order-independent

The type-arg tuple in the instantiation key is produced by collecting
the `gatherTypeSubst` output (a `Table[string, NimNode]` mapping formal
param name to bound type) and then **sorting by param name** before
joining. This ensures two call sites with the same bound types but
different syntactic argument order produce the same cache key and
share the same `ProcSig`.

### D7. Instantiation cap

`SymexSettings.maxInstantiationsPerProc: int = 64`

- `0` means unlimited (matching the `maxFrontierSize = 0` convention
  in `SymexSettings`).
- When the cap is exceeded, `ensureProcRegistered` registers a sentinel
  `ProcSig` with `isCapped = true`.
- The walker arm for a capped `ProcSig` appends
  `SymexErrorInfo{kind: geInstantiationCapped, procSym, observedCount}`
  to `w.errors` and sets `w.sawUnknown = true`.
- 64 is sufficient for all known generic-heavy PBT patterns (e.g., a
  numeric proc instantiated at all stdlib numeric types yields at most
  ~12 concrete types).

## Rejected alternatives

### Alt 1 — Symbolic generic walking (type-variable theory in Z3)

Model `proc foo[T](x: T): T` directly in Z3 by introducing a
type-variable sort `SortT` and declaring `foo_symbolic: SortT → SortT`.

**Rejected.** Z3 has no type-variable theory. Encoding parametric
polymorphism as an uninterpreted-function family indexed by a synthetic
sort is neither sound nor necessary:

- **Unsound**: the walker cannot express Z3 constraints over an unknown
  sort's operations. `foo_symbolic(x) + foo_symbolic(y)` has no meaning
  when `SortT` is uninterpreted. Any constraint encoding would have to
  case-split on all possible `T` — which is per-call-site
  monomorphization under a different name, with more machinery.
- **Unnecessary**: Nim's semchecker already monomorphized every call site
  before proptest's macro saw the AST. Per-call-site monomorphization at
  the IR layer matches Nim's own compilation model and requires no Z3
  theory extension.

The nonexistent type-variable theory would also make the walker
untestable: every test would need a mock "type universe" that doesn't
exist in Z3's sort system.

### Alt 2 — `repr.hash` as the instantiation-key base

Use `repr(calleeSym.getImpl).hash.toHex` as the stable identifier.

**Rejected.** `repr` is structurally ambiguous across modules: two
identical-body procs in different modules produce identical `repr`
output. This causes module-collision bugs (Feas-H5). `symBodyHash`
from `std/macros` encodes the full module path and is the correct
tool. The `lineInfo` fallback preserves module disambiguation without
depending on `symBodyHash`'s availability.

### Alt 3 — Cache distinct sorts per call frame

Store `distinctSorts` on `WalkCtx`/`CallFrameCtx` rather than
`WalkerStatics`.

**Rejected.** A distinct type like `Meters` appearing in both a caller
and a callee must map to the **same Z3 sort** — otherwise Z3 sees two
unrelated uninterpreted sorts with the same name and may produce
inconsistent constraints. Per-frame storage breaks this invariant.
`WalkerStatics` (shared across all call frames within one `runSymex`
invocation) is the correct lifetime.

## Consequences

### Intended

- Every symex result for a generic SUT reflects the exact monomorphized
  body the Nim compiler would execute — soundness matches D1.
- The `ProcSig` cache amortizes the parse cost for hot generic procs
  (identity, `max`, `min`, arithmetic ops) across all call sites.
- `distinct T` is correctly modeled as a type wall — real type-boundary
  bugs (e.g., passing `float` where `Meters` is required) appear as
  symex contradictions, not silently-passing equalities.
- The concept policy offloads constraint-validation to the semchecker
  for the common (user-defined) case, keeping the walker simple.

### Accepted as cost

- Per-call-site monomorphization may parse the same callee body multiple
  times for different instantiations. The `instCache` amortizes re-use,
  but new instantiations still incur a parse cost.
- Bijectivity axioms are absent for `distinct`-over-FP/String; callers
  in those domains receive a `geDistinctBijectivitySkipped` hint and
  must verify manually that the ejection model is adequate for their
  use case.
- `maxInstantiationsPerProc = 64` means sufficiently generic procs
  (e.g., a proc instantiated at every user-defined type) hit the cap
  and produce `sxUnknown`. Users can raise the cap in `SymexSettings`.

### Deferred

- **Variance annotations**: Nim has no variance annotations; this
  decision is trivially not needed.
- **`concept` with effect tracking**: concept bodies with effect
  constraints are trusted to the semchecker (D5); effect-aware
  re-validation is out of scope for Phase 15.
- **Generic parameter constraints requiring SMT-solvable type-arithmetic**
  (e.g., `T: static[int] where T mod 2 == 0`): the semchecker enforces
  these; the walker treats the resolved value as a literal.

## Validation

ADR-0008 is validated by the Cluster G test suite:

- **G1a DoD**: `isGenericCall` IR round-trip; stubs compile without
  panic; ADR-0008 authored.
- **G1a DoD (Feas-H5)**: two modules each defining `proc id[T](x: T):
  T = x` produce **two distinct cache entries** under the
  `lineInfo`-fallback key path (module-collision avoidance confirmed).
- **G1c DoD**: `cacheHitsFor` accessor confirms a single `ProcSig`
  shared across two call sites; `maxInstantiationsPerProc = 0` is
  unlimited.
- **G4 DoD**: `Meters` sort identity ≠ `float64` sort identity;
  bijectivity axioms present for `int`/`bool`/BV base; hint emitted
  for `float`/`string` base; distinct sort cache on `WalkerStatics`
  with exactly one entry for `Meters` across caller + callee.
- **G8 DoD**: swapped-argument-order calls (`foo[T=int, U=string]` and
  `foo[U=string, T=int]`) produce the same cache key.
