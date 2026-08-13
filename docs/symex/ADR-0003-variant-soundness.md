# ADR-0003 — Variant-soundness completeness for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-03 |
| **Deciders** | nelli maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [RFC-completeness.md](RFC-completeness.md) Cluster A, [PHASE11_PLAN.md](PHASE11_PLAN.md), [ADR-0001](ADR-0001-integer-semantics.md) |

## Context

Phase 11 shipped first-class variant soundness for the common case:
**single-`nnkRecCase`** objects with **enum discriminators**, **explicit
`of` arms**, and **static-tag reassignment**. Six features were deferred
to "consumer demand": multi-recCase, `else:` arms, non-enum
discriminators, symbolic-RHS reassignment, composite arm-field types
under reassignment, and Z3Int promotion of the discriminator under
`isOptimised`. RFC-completeness.md (Phase 14) closes those six.

This ADR records the semantic decisions for Cluster A's six items. A
companion ADR (ADR-0004) covers frontier pruning, which is sequenced
inside Cluster A but is its own concern.

## Decisions

### D1. Multi-`nnkRecCase` as a separate IR kind `itMultiVariant`

The single-recCase case (Phase 11's `itVariant`) stays unchanged.
Multi-recCase objects are represented by a new IR kind:

```nim
of itMultiVariant:
  mvObjectName*:      string
  mvPlainFieldNames*: seq[string]
  mvPlainFieldTypes*: seq[IRType]
  mvAxes*:            seq[VariantAxis]

VariantAxis* = object
  discName*: string
  discTy*:   IRType
  arms*:     seq[VariantArm]
```

`itMultiVariant` requires `mvAxes.len >= 2`. A single-axis object MUST
be represented as `itVariant` — the parser invariant. A single-axis
`itMultiVariant` is malformed IR; the constructor asserts. The canonical
encodings are intentionally disjoint (single-axis: `;disc=…`; multi-axis:
`;discs=[axis(…);axis(…)]`) so the cache key correctly separates them.

**Why a separate kind, not a structural extension of `itVariant`**:
Ousterhout's deep-modules principle. A `seq[VariantCase]` field folded
into `itVariant` would force every dispatch site (allocateSym,
isVariantField, isVariantReassign, extractFromSymVal, emitTyAndReader,
canonicalize) to write `if axes.len == 1` checks for the common case.
Separation keeps the existing single-axis path untouched and isolates
multi-axis complexity in its own dispatch branches.

### D2. `else:` arm encoding via Z3 conjunction-of-negations

`VariantArm` gains a single `isElse: bool` field. The walker's
arm-membership constraint for an `else:` arm is:

```
AND_k(disc != other_arm_k.tagOrdinal)
```

where `other_arm_k` ranges over the non-else arms on the same axis. The
constraint is computed **at walker time**, never materialized as a
`tagSet: seq[int]` in the IR. This works uniformly for enum
discriminators (finite complement, would have been representable as a
seq but isn't, for symmetry) and for non-enum discriminators (infinite
complement — `int` with two explicit `of` values has `2^64 - 2`
non-matching ordinals, which cannot be a seq).

The redundant `tags: seq[int]` field considered in earlier drafts is
**not** added. `arm.tagOrdinal` (the single explicit ordinal) suffices
for non-else arms; the else arm's constraint is derived from
other arms' tagOrdinals.

### D3. Non-enum discriminator type whitelist

Accepted ordinal types for discriminators:

- `enum`s (Phase 11 baseline)
- `int8` / `int16` / `int32` / `int64`
- `uint8` / `uint16` / `uint32` / `uint64`
- `char`
- `bool`
- `range[T]` where T is any of the above (including enum-backed range
  like `range[Color.Red..Color.Blue]`)

Rejected at parse time:

- `float` (not ordinal)
- `string` (not ordinal)
- object types (not ordinal)

The walker's existing arm-membership reasoning generalizes from enum's
`low(E)..high(E)` to any ordinal type's natural range. The lazy
conjunction-of-negations encoding for `else:` arms (D2) means this
generalization adds no new walker complexity for the `else:` case.

### D4. Symbolic-RHS discriminator reassignment via path-condition fork

For `obj.kind = someVar` where `someVar` is a symbolic value, the walker
emits **one path per explicit arm of the discriminator's `case`
statement**, plus one path for the `else:` arm if present. The fork is
bounded by the SUT's syntax, not by the discriminator type's range —
critical for non-enum discriminators (D3) where the type range may be
unbounded.

Each forked path adds a path-condition constraint:

- Non-else arms: `pc += [vrsRhs == arm.tagOrdinal]`
- Else arm: `pc += [AND_k(vrsRhs != other_arm_k.tagOrdinal)]`

**Critical invariant**: the fork does NOT call the zero-init path. The
zero-init in static-tag `isVariantReassign` exists because the new arm's
fields have never been allocated. For symbolic-RHS reassignment, the
existing `vArmFields` SymVal allocations from `allocateSym` are
preserved across the fork; only the path constraint changes. The walker
reads the same `vArmFields[arm_k]` SymVals on all forks, and the path
condition resolves them.

For `itMultiVariant` reassignment, the walker identifies the target
axis by matching the LHS field name against each
`VariantAxis.discName`. The fork operates on the target axis only;
other axes' `vDisc` and `vArmFields` are shallow-copied unchanged.

### D5. Composite arm-field types under static-tag reassignment

The static-tag `isVariantReassign` path (Phase 11) currently zero-inits
primitives only and raises `ValueError` for composite arm-field types
(tuples, seqs, Tables, HashSets, nested variants). Phase 14 replaces
this with full type-driven default construction, reusing
`allocateSym`'s existing per-type SymVal construction.

**Inherited scope limitations from `allocateSym`**:

- `itTable`: only `Table[string, int]` supported. Other key/value types
  remain unsupported (sub-deferral; not closed in this RFC).
- `itSet`: only `HashSet[int64]` supported. Same.

For an arm field with one of these unsupported shapes, static-tag
reassignment continues to raise `ValueError`. Broader Table/HashSet
expansion is a separate RFC.

For nested variants in arm fields, `allocateSym`'s recursion handles
construction correctly. Nim's type system prevents direct self-recursion
in objects (only via `ref`), so cycles are bounded.

### D6. Z3Int discriminator promotion mandatory under `isOptimised`

Under `isOptimised`, the variant discriminator `vDisc` is promoted from
`svBV{8,16}` to `svInt`. The arm-membership disjunction
(`disc == tag_0 OR disc == tag_1 OR ...`) is emitted using Z3Int
equalities instead of BV equalities. Soundness is preserved because the
disjunction is the only constraint binding the discriminator value —
no implicit BV-range constraint is relied upon.

Three sites in `runtime.nim` are updated to dispatch on `svInt`:

- `allocateSym` arm-disjunction emission
- `walk(isVariantField)`'s `discEq` inner proc
- `walk(isVariantReassign)` (and A4b's symbolic variant)

`extractFromSymVal` and `emitTyAndReader`'s `itInt` reader path already
handle `svInt` correctly.

**Mandatory under `isOptimised`** — no settings field. `isExact`
remains the established escape hatch for users who want pure BV
encoding for variant discriminators.

### D7. `var T` parameter semantics: initial value is the witness

The witness for a `var T` parameter is the **initial value** that
caused the target to be reached. Walker-internal mutation tracking
proceeds normally via the existing `let`/`assign` machinery. The
witness extraction path consults `WalkCtx.initialEnv` (already
populated at `runSymex` start; `trySolve` already uses it via the
existing conditional at `runtime.nim:1319`).

Caller-side identity is not relevant for symex: `symexFind` reports
"this initial value drives the SUT to T," and the test runtime calls
the SUT with a fresh mutable binding. The SUT mutates that binding;
the test observes whatever Nim's runtime produces. The witness is
about the inputs that REACHED the target, not the post-mutation state.

This is a **soundness-preserving acceptance** of a previously-rejected
SUT pattern. No new walker logic is added; the parser is fixed to set
`IRParam.isVar = true` for top-level SUT params (it currently only
does so for callee params), and `symexFindAllWitnesses` /
`assertCoveredBy` / `forAllWithSymexSeeds` are updated to handle the
`var T` parameter type at their respective layers.

## Consequences

### Soundness

- D1–D6 are conservative extensions of Phase 11's already-proven
  variant soundness. No existing single-axis SUT is affected
  (separate IR kind).
- D7 is a soundness-preserving acceptance — adds no new walker
  semantics, just permits a previously-rejected parser input.

### Cache invalidation

The walker version bumps `"3" → "4"` at the end of Cluster A. All
cached witnesses and verdicts rotate once. SUTs using the new patterns
(D1–D7) could not have had cached entries under `"3"` (parser
rejected them or walker dispatched to `default(T)` stubs), so the
rotation is necessary and sufficient.

### Out of scope

- Cross-module private callees (#138 / Phase 3 limit)
- Float / string / object discriminator types (D3 whitelist boundary)
- `var T` + generic procs (Nim macro-binding limit; documented
  workaround)
- Table/HashSet shapes beyond `[string, int]` / `[int64]` (D5
  inherited scope)
- Parallel symex (separate optimization track)

## Alternatives considered

### A1. Fold multi-recCase into `itVariant` via `seq[VariantCase]`

Rejected. Every dispatch site would need a `if axes.len == 1` check
for the common case. The cost of the single-axis path being
"protected by a generic loop" outweighs the surface saved.

### A2. Materialize else-arm complements as `seq[int]`

Rejected. Works for enum discriminators (finite complement) but
catastrophic for non-enum discriminators (`int` complement has 2^64
ordinals). The lazy conjunction-of-negations encoding works uniformly
and avoids the seq-materialization edge case.

### A3. Z3Int discriminator opt-in via `Settings.symexDiscPromotion: bool`

Rejected. `isOptimised` already promises "aggressive abstraction
optimisations." A separate toggle for the variant discriminator
specifically adds shallow surface area for no use case the existing
`isExact` escape hatch doesn't already cover.

### A4. Treat `var T` as a separate semantic mode requiring caller-side identity

Rejected. The semantic gap claimed in v1 ("no witness-reconstruction
identity for var T") was wrong. The witness is the initial value;
caller-side identity is not relevant. D7 is the correct, minimal
acceptance.
