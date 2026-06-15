# ADR-0010 — Logical-heap model for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-15 |
| **Deciders** | proptest maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [SYMEX_PLAN.md § ADR-0010](../SYMEX_PLAN.md), proptest Phase 15 Cluster H (authored at **H1**) and Cluster R (implements it: R1–R12), [ADR-0007 (exception flow)](ADR-0007-exception-flow.md), [witness-format-v3.md](witness-format-v3.md) (R11b), [nim-z3 array & uninterpreted-sort theory](https://github.com/coreyleavitt/nim-z3) |

> Authored in Phase 15 cycle **H1**, ahead of Cluster R (which implements it).
> H1 lands ONLY the structural prerequisite — the three `Path` heap-state fields
> (`heaps`, `heapDepth`, `allocCounters`), the `deepCopyHeapState` helper, the
> `forkPath` fork-deep-copy contract, and the fork-site registry — so that
> Cluster E (E3/E5/E7, which reference `path.heaps` to thread heap state through
> `try`/`finally` and inter-procedural exception propagation) can compile. **No
> heap SEMANTICS land in H1.** Symbolic allocation, dereference, ref-equality,
> nil-fork, alias propagation, and witness serialisation are all Cluster R. This
> ADR records the DESIGN that R will implement; H1 ships only the scaffolding.

## Context

Nim's `ref T` / `ptr T` introduce a level of indirection that the symex engine,
through Phase 14, deliberately did not model: `dsl_typebridge.nim` unwraps `ref`/
`ptr` to their pointee type and "aliasing is a follow-up" (the follow-up is
Cluster R). To model `ref object` SUTs soundly the engine must answer three
questions that the value-only model never had to:

1. **Identity / aliasing.** Two `ref Foo` values `p` and `q` may or may not point
   to the same object. A SUT that branches on `p == q` (reference equality) or
   mutates `p.x` and then reads `q.x` is observing identity, not value. The engine
   must be able to produce witnesses that distinguish `p` and `q` *and* witnesses
   in which they alias.

2. **Freshness.** `new(Foo)` returns an address that has never been observed on
   the current path. A model that lets the solver pick an arbitrary address would
   admit unsound witnesses in which a freshly-allocated object aliases a
   pre-existing one.

3. **Nil.** `nil` is a distinguished reference value; `p.x` on a `nil` `p` is a
   `NilAccessDefect`. The engine must fork on nil-ness and (under the relevant
   target) solve the nil-deref branch.

A further structural constraint comes from the path-sensitive walker: heap state
is **per-path**. When the walker forks at an `if`/`case`/`while`/call site, each
child path must own an independent copy of the heap so that a mutation on one
branch never bleeds into a sibling or the parent. This is the same isolation the
walker already gives `pc` and `env` (both copied by value at every fork), and it
is the property H1's `deepCopyHeapState` + `forkPath` contract establishes.

The engine already owns *path satisfiability* (it walks one SUT at a time and
calls Z3 per feasible path). That capability is what makes a **precise,
path-sensitive heap model** affordable here — and precision is the whole point of
symex for PBT: a witness must be a concrete, replayable counter-example, not a
may-alias summary.

## Decision

### Logical-heap representation

The heap is modelled as a **family of Z3 arrays, one per pointee type**:

> `Z3Array[Ref_T, T]` — where `Ref_T` is an **uninterpreted sort** representing
> abstract addresses for objects of type `T`, and the array maps each live
> address to the current symbolic value of the object at that address.

Per-type arrays (rather than one monolithic heap) give cross-type ref comparisons
a **Z3 sort error at construction time**: `ref Foo` and `ref Bar` inhabit
different `Ref_T` sorts, so `(p: ref Foo) == (q: ref Bar)` cannot even be built,
which is exactly Nim's static typing. The uninterpreted address sort means the
solver never reasons about concrete pointer arithmetic — only about *equality and
distinctness of abstract addresses*, which is all that identity semantics require.

### Per-`Path` snapshot

Heap state is snapshotted on `Path` via three fields (landed in H1):

```nim
heaps:         Table[string, Z3AnyAst]   # keyed by Z3 sort name; the per-type
                                         # heap array (erased), one entry per Ref_T
heapDepth:     int                       # current heap-descent depth (bounded)
allocCounters: Table[string, int]        # keyed by type-ID string; per-type
                                         # fresh-address counter
```

- `heaps` is keyed by **sort name** and holds the erased `Z3Array[Ref_T, T]` for
  each pointee type touched on the path.
- `allocCounters` is keyed by **type-ID string** and holds the per-type fresh-ref
  counter that drives freshness (below).
- `heapDepth` bounds recursive `ref object` field expansion during witness
  serialisation.

Each field is **deep-copied at every fork site** (the H1 contract) so paths never
share mutable heap state. In Nim a `Table` assignment is a value copy, so
`deepCopyHeapState` (which does exactly `result.heaps = src.heaps` /
`result.allocCounters = src.allocCounters`) yields fork isolation; `heapDepth` is
an `int` and copies by value with the rest of the construction.

### Freshness

`new(T)` must return an address not previously observed on **any** path prefix.
This is maintained by `path.allocCounters[typeId]`: each `new` increments the
counter and asserts the resulting address is **distinct from all prior addresses**
for that type on the current path. Because the counter rides on `Path` and is
deep-copied at forks, two sibling branches that each allocate get *independent*
fresh addresses, and an allocation is never confused with a pre-existing object.

### Nil

`nil` is modelled as a **dedicated, globally-named sort-level constant** per
pointee type:

> `Z3_mk_const(ctx, nilSym_T, Ref_T)`

This `nil` constant is **never returned by the freshness mechanism**, so a fresh
allocation is always distinct from `nil`, and a `nil`-fork (`if p == nil`) is a
genuine two-way branch the walker can solve.

## Options considered and rejected

### Option A — Region-based analysis (Hind/Reps style)

Track which heap *regions* a pointer may alias, rather than tracking individual
allocations.

**Rejected.** Region-based techniques produce **may-alias sets**, not definite
value models. A symex engine that already owns path-sat can produce precise,
path-sensitive heap models; degrading to region summaries would lose the very
precision that makes symex useful for PBT witnesses (a may-alias set is not a
replayable counter-example).

### Option B — Andersen-style points-to analysis

Whole-program, flow-insensitive points-to over-approximation.

**Rejected.** Same precision argument as Option A; additionally, Andersen requires
a **whole-program view** the proptest engine does not have — it walks one SUT at a
time, with callees resolved on demand.

### Option C — Steensgaard-style unification

Linear-time alias analysis that **merges all aliasing pointers into one
equivalence class**.

**Rejected.** Merging alias classes prevents the engine from distinguishing `p`
and `q` when both *can* point to the same object — exactly the distinction needed
for ref-aliasing PBT witnesses. The engine must be able to emit one witness in
which they alias and another in which they do not.

### Option D (representation) — One monolithic heap array

A single `Z3Array[Addr, Value]` over a universal address/value sort.

**Rejected (in favour of per-type arrays).** A universal heap loses Nim's static
ref-type distinction, admitting `ref Foo == ref Bar` and forcing a tagged-union
value sort. Per-type arrays keep cross-type comparisons as construction-time sort
errors and keep each array's value sort concrete.

## Consequences

### Intended

- **Cross-type `ref` comparisons become Z3 sort errors at construction time**,
  preventing false aliasing between `ref Foo` and `ref Bar`.
- **Precise, path-sensitive aliasing.** The engine can emit both aliasing and
  non-aliasing witnesses for the same `p`/`q`, and freshness guarantees `new`
  never aliases a pre-existing object.
- **Bounded allocation cycles.** `maxHeapDepth` (a Cluster R `SymexSettings`
  field) caps the recursion depth of `ref object` field expansion during witness
  serialisation (R9/R12). When the bound is reached the field renders as
  `{truncated: true}`.
- **`path.heaps` is deep-copied at every fork site** (the H1 fork-site registry in
  `runtime.nim`, enforced through `forkPath`/`deepCopyHeapState`), so heap state
  is path-isolated exactly like `pc` and `env`.

### Accepted as cost

- Per-type arrays mean a SUT touching many distinct pointee types carries several
  heap arrays per path; this is the price of keeping cross-type comparisons
  ill-typed and value sorts concrete.
- The uninterpreted address sort cannot model pointer arithmetic or `cast`-based
  address inspection; such SUTs are outside the DSL scope (consistent with
  ADR-0005's `cast` exclusion).

### Deferred / what lands when

- **H1 (this cycle) lands ONLY the field scaffolding:** the three `Path` fields
  (empty/zero on every path), `deepCopyHeapState`, the `forkPath` deep-copy
  contract, and the fork-site registry. The walker neither reads nor writes the
  fields in H1 — they are inert until Cluster R. No walker version bump, no
  rendering version bump (H1 introduces no walker-semantic change).
- **Cluster R fills the model:** symbolic allocation + freshness (alloc),
  dereference + field read/write, `nil`-fork, ref-equality / alias propagation,
  inter-procedural heap threading, and witness serialisation. These are the cycles
  that make the fields live.

## Implementation notes

- **`Path` field schema:** `heaps: Table[string, Z3AnyAst]` keyed by sort name;
  `heapDepth: int`; `allocCounters: Table[string, int]` keyed by type-ID string.
  (`Z3AnyAst` is the codebase's type-erased Z3-AST handle, produced via
  `toAnyAst`; it carries `raw` + `ctx`. Confirmed the real erased-AST type in
  `runtime.nim` — the same handle already used for `seqDataRaw`/`tabDataRaw`/
  `setMembersRaw`/`uninterpAst`.)
- **Fork deep-copy contract:** every child `Path` is built through the `forkPath`
  template, which routes the three fields through `deepCopyHeapState`. The fresh
  ROOT path in `runSymex` is the only raw `Path(` construction and correctly gets
  empty-default heap fields. See the fork-site registry comment block above `walk`
  in `runtime.nim` (introduced H1; maintained through R; the R-cluster walker
  comment block supersedes it).
- **R1b preview (inter-procedural threading).** Call-descent passes the caller's
  `path.heaps` into callee descent (the H1 `forkPath(p, …)` at the call-descent
  site already carries it, inert); callee-exit heaps merge back out at the
  return-merge site (H1 forks that survivor from the returned callee path `cp`).
  `allocCounters` merge uses **`max(caller, callee)`** per type (finding C5 / R1b
  spec) so freshness is preserved across the call boundary.

## Heap witness invariants (Des-H7 / finding H21)

The following non-negotiable invariants govern the `heapSnapshot` section of the
witness format authored in R11b (`witness-format-v3.md`). They are recorded here
so R11b's author has a concrete contract and so E-cluster reviewers can
cross-reference:

1. `heapSnapshot` is emitted in a witness **only when** the witness includes at
   least one `svRef` or `svPtr` parameter.
2. **Alias groups are deduplicated:** the lexicographically-first parameter name
   among an alias group holds the `pointsTo` field; all other members carry
   `aliasRef: <primary_name>` and no `pointsTo`.
3. `nil` refs render as `{value: "nil", pointsTo: null}` with no `aliasGroup`
   entry.
4. `pointsTo` for a `ref object` value is recursively expanded using the same
   field-path format as non-ref tuple witnesses, **bounded by `maxHeapDepth`**.
   When `maxHeapDepth` is reached the field renders as `{truncated: true}`.

These invariants are cross-referenced by R11b (witness authoring) and R12 (final
serialisation DoD).

## Validation

ADR-0010 is validated structurally at **H1** and semantically across **Cluster R**:

- **H1 (scaffolding):** `tphase15_H1_path_heap_fields.nim` asserts (1) `Path`
  carries `heaps`/`heapDepth`/`allocCounters` and (2) the fork-site deep-copy
  contract gives isolation — mutating a forked child's `heaps["x"]` does not
  mutate the parent's. The full pre-R regression confirms the inert fields cause
  no behaviour change for Phase-14 SUTs.
- **Cluster R (semantics):** alloc/freshness, deref, nil-fork, ref-equality,
  alias propagation, inter-procedural threading, and witness serialisation each
  carry their own DoD tests against this model.
