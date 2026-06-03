# RFC — Symex completeness pass (Phase 11 + 12 + 13 deferrals)

> Closes the open deferrals carried by Phases 11, 12, and 13 in a
> single sweep. The standing trigger for these items was "a real
> consumer surfaces the pattern"; the standing direction for this
> RFC is **"we're building a complete library, not a single
> consumer's tool"** — so trigger conditions are waived.
>
> **Revision history**
> - **v1** — initial draft, phase-of-origin clustering, 22 cycles, 4
>   open questions for architect.
> - **v2** — round 1 architect review (4 lenses, 62 findings)
>   baked in. Major changes:
>   - `itMultiVariant` as separate IR kind (not folded into
>     `itVariant`).
>   - A1, A4 split into IR-extension sub-cycles + walker
>     sub-cycles.
>   - Walker version bump `"3"→"4"` moved to the LAST cycle of
>     Cluster A (was A1; rationale: parser `error()`s prevent
>     `"3"`-era caches from containing entries for new patterns,
>     so the single bump at the end is necessary and sufficient).
>   - C3 (`maxFrontierSize` enforcement) moved to land BEFORE A4
>     (large-disc-range fork explosion in A4 requires the prune).
>   - C3 semantics corrected: frontier-pruned walks yield
>     `sxUnknown` (cached under `:unk`), NOT `sxUnsat`. Adds a
>     third UNKNOWN sub-case to document.
>   - A2: drop redundant `tags: seq[int]` field. Else-arm
>     constraint is `AND(disc != tag_i)`, never materialized as a
>     seq.
>   - C1: `SymexResult.fromCache: bool` added; `abstractions=@[]`
>     and `callStats=@[]` on cache hit documented.
>   - C4 catches a specific Z3-derived exception type, NOT
>     `CatchableError` (would silently swallow `ValueError`
>     walker-logic bugs).
>   - B1: `constraintDigest: string` (plain field, not `proc():
>     string`); standard strategies auto-populate at construction.
>   - B2: `forcePhases: set[PhaseId]` (generalized; was
>     `symexAuditAlways: bool`).
>   - B5: `sfReplayMiss` (renamed from `sfNotReached`) restricted
>     to `assertCoveredBy` — `symexSeedPhase` has no target
>     provenance to compute it.
>   - B7: parse-time diagnostic in `dsl_parser.nim` (not IR
>     scan); honestly framed as "partial close" of Phase 12 #3
>     (improves observability; walker semantics unchanged).
>   - C4: structured `errors: seq[SymexErrorInfo]` field (not
>     flat `errorAnnotation: string`).
>   - D7 `var T` moved INTO scope as new cycle A7 — initial value
>     IS the witness; the "no caller-side identity" objection was
>     wrong. Generic procs stay excluded with workaround docs.
>   - ADR-0003 (variant semantic decisions) and ADR-0004
>     (frontier pruning policy) added as PRE-CYCLE work.
>   - All four "open questions" closed.
>   - Cycle count: 30 (was 22). Test file projection: ~70 (was 88).
> - **v3 (current)** — round 2 architect review (4 lenses, 44
>   findings) partial bake-in. Five CRITICAL findings fully applied;
>   remaining HIGH/MEDIUM/LOW summarized as a backlog in the new
>   "v3 round-2 backlog" section near the end of the doc — to be
>   addressed during the relevant cycle's TDD slice or in a focused
>   final-smoothing pass before TDD begins. Critical changes:
>   - **C4 catches `Z3Error`** (the abstract base class in
>     `_deps/z3/src/z3/error.nim:43` with 12 typed subclasses
>     including `Z3MemoryError`/`Z3InternalError`/`Z3OperationError`),
>     NOT a fictitious "Z3Exception". `Z3Error extends CatchableError`
>     so walker `ValueError`/`AssertionDefect` still propagate.
>   - **A7 premise corrected**: parser does NOT currently `error()`
>     on `var T`. `classifyType` silently unwraps `nnkVarTy` already.
>     A7's actual work: audit `parseProc` and set `isVar = true`
>     for top-level SUT params; verify `trySolve`'s `initialEnv`
>     path (which already exists at runtime.nim:1319-1322).
>   - **A7 split into A7a (parser/symex acceptance) + A7b
>     (downstream propagation)**: `symexFindAllWitnesses` has its
>     own var-T guard at `symex.nim:1062`; `forAllWithSymexSeeds`'s
>     `prop: proc(x: T)` is type-incompatible with `proc(x: var T)`;
>     `assertCoveredBy` emits `let wit; testFn(wit[0])` which is a
>     rvalue-passed-as-`var` compile error. A7b addresses all three.
>   - **A1a `emitTyAndReader` stub** explicitly returns
>     `default(ObjectName)` (Phase-5 fallback pattern) until A1d
>     implements the nested-case witness construction.
>   - **A1d round-trip invariant**: `renderAsChoices(multiDiscWitness)`
>     MUST produce a choice sequence whose order matches
>     `emitTyAndReader`'s nested-case reading order. Verified via an
>     explicit round-trip test (witness → replay → property called
>     with same field values).

## Why now

Phases 11 (variant soundness), 12 (input-source seeding), and 13
(verdict caching) each shipped with deferrals where the
maintainer judged: *the work is correctly scoped but the trigger
to land it is real consumer pressure*. With completeness as the
goal rather than utility-per-consumer, those deferrals become
items in a closure plan, not items waiting on signal.

## Pre-cycle work (architectural decisions)

Two ADRs land before any TDD slice runs:

- **ADR-0003: Variant-soundness semantic decisions.** Documents:
  - Multi-recCase as a separate IR kind (`itMultiVariant`) rather
    than `itVariant` extension. Rationale: single-recCase is the
    overwhelming common case; keeping it on its own code path
    avoids `if axes.len == 1` everywhere.
  - Else-arm encoding: `AND(disc != tag_i)` Z3 conjunction
    computed at walker time. Never materialized as a tag-set seq.
    Works for finite (enum) and unbounded (`int`) discriminator
    types uniformly.
  - Non-enum discriminator whitelist: enum, `int8..int64`,
    `uint8..uint64`, `range[T]` (T = any ordinal — including
    enum-backed ranges), `char`, `bool`. Everything else stays
    parser `error()`.
  - Symbolic-RHS reassignment fork semantics: walker emits one
    path-constraint `disc == arm_k_ord` per arm; does NOT call
    the zero-init path (that's static-tag-only behavior). For
    multi-axis (`itMultiVariant`) reassignment, the target axis
    is identified by matching LHS field name against each
    `VariantAxis.discName`.
  - `var T` parameter semantic: witness is the INITIAL value;
    mutations are walker-internal symbolic operations that the
    test runtime handles. No identity tracking needed.

- **ADR-0004: Frontier pruning policy.** Policy:
  **highest-uncertainty-first pruning** when
  `frontier.len > settings.maxFrontierSize`. Matches the
  walker's existing "uncertain paths converge to UNKNOWN" model.
  Pruning sets `sawUnknown = true` on the pruned-frontier walk;
  the walk's final result is therefore `sxUnknown`, cached under
  `:unk` (NOT `sxUnsat`).

## Inventory — what's in scope

Four clusters; ordering constraints documented at the cluster
and inter-cluster level.

### Cluster A — Variant soundness completeness (Phase 11 + var T)

| ID | Item | Phase 11 deferral | Cycle(s) |
|---|---|---|---|
| A1 | Multi-`nnkRecCase` per object via `itMultiVariant` | #1 | A1a–A1d (IR + parser + walker + witness emitter) |
| A2 | `else:` arms in variants | #2 | A2 |
| A3 | Non-enum discriminator types | #3 | A3 |
| A4 | Symbolic-RHS discriminator reassignment | #7 | A4a (IR + canonicalize) + A4b (walker fork) |
| A5 | Composite arm-field types under reassignment | #8 | A5 |
| A6 | Z3Int promotion of variant discriminator under `isOptimised` | #12 | A6 |
| A7 | `var T` parameters (NEW — moved from Cluster D) | Phase 12 #5 | A7 |

**Inter-cluster ordering**: C3 (frontier pruning) MUST merge
before A4 (non-enum-disc symbolic RHS reassignment can produce
unbounded fork explosion that C3 prunes).

**Within-cluster ordering**: A1 → A2 → A3 → C3 → A4 → A5 → A6 →
A7. Walker version bump `symexWalkerVersion = "3" → "4"` lands in
**A7's GREEN** (final cycle of Cluster A). Pre-bump caches under
`"3"` cannot contain entries for any A1–A7 SUT (parser
`error()`s prevent them), so the single bump at the end is both
necessary and sufficient.

### Cluster B — Input-source seeding completeness (Phase 12)

| ID | Item | Phase 12 deferral | Cycle(s) |
|---|---|---|---|
| B1 | `Strategy[T].constraintDigest: string` (auto-populated for standard strategies) | #1 | B1 |
| B2 | `Settings.forcePhases: set[PhaseId]` | #4 | B2 |
| B3 | `tables`/`sets` trace-equivalence under collision (pin + tighten docs) | #11 | B3 |
| B4 | Named-field tuple strategies in multi-arg `symexForAll` | #12 | B4 |
| B5 | `symexCapture` armed per-seed inside `assertCoveredBy`; `sfReplayMiss` finding kind | #13 | B5 |
| B6+7 | Label-by-name `excludeTargets` + parser-time diagnostic for `isUnsupported` markers | label-by-name + #3 (partial) | B67 |

**Coordination with Cluster A**: B1's `constraintDigest` field
on `Strategy[T]` participates in any cache key derived through a
strategy. Auto-population for standard strategies (`integers`,
`lists`, `sampledFrom`, `booleans`, etc.) means B1's landing
causes a one-time cache rotation for entries derived through
those strategies. Recommended sequencing: B1 lands together with
Cluster A's walker bump (i.e., in the same release wave) so the
user sees ONE rotation event, not two.

### Cluster C — Verdict caching completeness (Phase 13 follow-ups)

| ID | Item | Phase 13 follow-up | Cycle(s) |
|---|---|---|---|
| C1 | Verdict-cache cascade for `symexFind` / `assertCoveredBy` | "What this opens" #1 | C1 |
| C2 | Layer 1's `dbErrors` accumulator wired into `Report.dbErrors` | RFC cycle-3 design note | C2 |
| C3 | `maxFrontierSize` enforcement (frontier-pruned → sxUnknown) | round-1 HIGH-2 | C3 |
| C4 | Z3 internal-error policy (catch specific Z3 exception type → sfUnknown) | "What this opens" #2 | C4 |

**Inter-cluster ordering**: C3 → A4 (above). C1, C2, C4 are
independent of Cluster A and can land in any order before or
after.

### Cluster D — Close-out + explicit non-scope

| ID | Item | Where covered | Why excluded |
|---|---|---|---|
| D1 | Phase 3 deferral #138 — cross-module private helpers | (user-held session) | User-led session. |
| D2 | Shape A (#124–#132) — constraint-guided generation | Separate plan | Different architecture. |
| D3 | Phase 12 toolchain workarounds #14, #15 | RFC PHASE12_PLAN.md | Nim 2.2 bugs; close on toolchain fix. |
| D4 | Phase 12 deferral #2, #10 (cross-module callees in scan) | overlap with D1 | Same `getImpl` limit. |
| D5 | Phase 11 already-closed items | PHASE11_PLAN.md ✅ rows | Already shipped. |
| D6 | Phase 11 #6 multi-arm-collision | N/A by Nim syntax | Compiler prevents. |
| D7 | Generic-proc SUTs (Phase 12 #6) | Documented workaround pattern | Nim macro-binding limit — no type at expansion time. Users wrap with concrete-typed shim. |
| D8 | Phase 12 `derandomize` × symex seeds (#8) | Cycle 19 test | Already pinned. |
| D9 | Phase 12 cold-cache latency (#7) | Partially closed by Phase 13 | Fundamental to running Z3. |
| D10 | Per-tactic Z3 versioning | determinism.md | Already rejected pre-Phase-13. |

**Generic-proc workaround pattern** (D7, documented in cycle
30): users with `proc fn[T](x: T) = …` SUTs write a concrete
shim `proc fnInt(x: int) = fn(x)` and pass `fnInt` to
`symexForAll`/`symexFind`. The library cannot avoid this because
Nim macros have no concrete type at expansion time for a generic
proc reference.

## Semantic decisions, settled

ADR-0003 and ADR-0004 record these formally. Summary:

1. **`itMultiVariant` is a separate IR kind** from `itVariant`.
   Single-recCase objects keep using `itVariant` unchanged.
2. **Else-arm constraint is `AND(disc != tag_i)`**. Never
   materialize the complement as a seq — catastrophic for `int`
   discriminators. Walker computes lazily.
3. **Non-enum disc whitelist**: enum, int*, uint*, `range[T]`
   for any ordinal T, char, bool. Reject `float`, `string`, and
   object types at parse time.
4. **Symbolic-RHS reassignment**: walker forks on
   `disc == arm_k_ord`; preserves existing `vArmFields`
   SymVal allocations; does NOT call zero-init. For
   `itMultiVariant`, target axis is identified by LHS
   `discName` match.
5. **`var T` semantics**: initial value is the witness;
   walker-internal mutation tracking proceeds normally.
6. **Frontier pruning policy**: highest-uncertainty-first;
   pruned walk produces `sxUnknown` (third UNKNOWN sub-case,
   alongside Z3-rlimit-exhausted and walker-unwind-exhausted).
7. **B1 digest is auto-populated for standard strategies**. Yes
   this rotates the cache once on landing — that's a complete-
   library concern, the user explicitly waived consumer concerns.
8. **A6 is mandatory under `isOptimised`**. `isExact` remains
   available for users who want pure BV encoding.
9. **C4 catches a Z3-specific exception type**, not
   `CatchableError`. Walker-logic `ValueError` and
   `AssertionDefect` from walker bugs propagate as today.
10. **C4 is mandatory silent catch**. `sfUnknown` with
    structured `errors: seq[SymexErrorInfo]` lets consumers
    treat any UNKNOWN as fatal at the Report-policy level.

## Design — by cluster

### Cluster A — Variant soundness completeness

#### A1 (4 cycles): `itMultiVariant` IR kind for multi-`nnkRecCase` objects

**A1a — IR extension.** Add new `IRTypeKind.itMultiVariant`
with:

```nim
of itMultiVariant:
  mvObjectName*:     string
  mvPlainFieldNames*: seq[string]
  mvPlainFieldTypes*: seq[IRType]
  mvAxes*:            seq[VariantAxis]

VariantAxis* = object
  discName*: string
  discTy*:   IRType
  arms*:     seq[VariantArm]
```

Stubs added in every case dispatch:
- `types.nim`: render helpers, `mkMultiVariant` constructor.
- `dsl_parser.nim`: `emitIRType` recursive case (stub: emit one
  axis).
- `canonicalize.nim`: emit `";discs=[axis(d1:ty;[arms…]);axis(d2:ty;[arms…])]"`
  format.
- `runtime.nim`: `allocateSym`, `walk(isVariantField)`,
  `walk(isVariantReassign)`, `extractFromSymVal`. Stubs raise
  `defect` until A1c.
- `symex.nim`: `emitTyAndReader` stub branch — **returns
  `(objTyId, newCall(ident"default", objTyId))`** until A1d
  implements the nested-case construction. This is the same
  Phase-5 variant-fallback pattern used at symex.nim:498. The
  stub compiles cleanly; the A1d RED test will fail because
  `default(T)` doesn't reflect the actual witness, distinguishing
  "missing stub" from "stub present but not yet implementing
  nested-case."
- **Also stub** (omitted from v2's site list):
  `IRType` render helpers (`tyOf`, `IRType.==`, `IRType.$`) in
  `types.nim`; `collectSetLitMembers` and `collectTableLitKeys`
  in `runtime.nim`. `renderAsChoices`'s `of object:` branch is
  generic via Nim's `fields(w)` iterator and does NOT require a
  case branch — but A1d MUST verify the iteration order
  produced by `fields(w)` on multi-disc objects matches the order
  `emitTyAndReader`'s nested case emits.

RED: a test compiles a hand-built `itMultiVariant` IR through
canonicalize and asserts the key differs from a flat
single-axis `itVariant` with the same flattened arms.

GREEN: stubs land; compilation passes; canonicalize emits the
new format.

**A1b — Parser.** Extend `dsl_parser.nim` to detect multiple
`nnkRecCase` children in one object body. Emit `itMultiVariant`
with one `VariantAxis` per recCase. Single-recCase objects still
produce `itVariant`. RED: SUT with two `case kind:` blocks
compiles past the parser (previously erroring). GREEN: parser
constructs the IR correctly.

**A1c — Walker.** Extend `allocateSym`, `walk(isVariantField)`,
`walk(isVariantReassign)`, `extractFromSymVal` to handle
`itMultiVariant`. Each axis allocates its own `discInner` and
emits its own arm-ordinal disjunction. Field-access disambiguates
by axis via `vDiscName` membership. The product space is the
conjunction of per-axis disjunctions.

RED: SUT with two `case kind:` discriminators reaches a target
gated on one of the inner axes; symex finds witness with both
discriminators populated correctly.

**A1d — Witness emitter.** Extend `emitTyAndReader` to emit
nested case statements for `itMultiVariant`: outer `case disc1`,
inner `case disc2` per arm.

**Critical invariant**: `renderAsChoices(multiDiscWitness)` MUST
produce a choice sequence whose order matches the order in which
`emitTyAndReader`'s nested-case Nim code READS field values.
`renderAsChoices` on `T is object` uses Nim's `fields(w)`
iterator (symex.nim:115-122), which for multi-disc objects
iterates disc1, then per-disc1-arm: (disc2 + arm-of-disc2
fields). The `emitTyAndReader` nested-case construction must
match this exact order. A mismatch produces silent witness
corruption only detected by `sfReplayMiss` (Cluster B, lands
later) — not acceptable.

RED tests:
1. Witness round-trips through Nim's runtime (compile-time check
   that emitted code is well-formed).
2. **Explicit round-trip through `symexSeedPhase`**: render a
   constructed multi-disc witness via `renderAsChoices`; replay
   through the strategy; verify the replayed property receives
   field values matching the original. Catches order
   mismatches at A1d time, not at B5 time.

#### A2 — `else:` arms in variants

Add `isElse: bool` to `VariantArm` (not `tags: seq[int]` —
redundant; the walker computes the complement constraint
lazily). Parser recognizes `else:` in `nnkRecCase`, emits an
arm with `isElse = true` and `tagOrdinal = -1` (sentinel).
Walker's arm-membership constraint:

- For non-else arm: `disc == arm.tagOrdinal`.
- For else arm: `AND_over_other_arms(disc != other.tagOrdinal)`.

Canonicalize encodes `isElse` flag in the arm's serialization to
prevent same-arm-set collisions. **This canonical-encoding change
is part of A1's `mvAxes` format from the start** (forward-
compatible: single-axis variants get `isElse=false` for all
existing arms, no semantic change to their disjunction).

#### A3 — Non-enum discriminator types

Relax parser assertion. Walker uses the discriminator type's
ordinal range to derive the legal-tag set when needed.

For arms with explicit `of N:` values, the constraint is just
`disc == N` (the standard arm-membership). For `else:` arms
under non-enum disc, the constraint is the conjunction of
inequalities (no enumeration of the complement; works equally
for `case kind: int; else:` and `case kind: SomeEnum; else:`).

RED: SUT with `case kind: int; of 1: …; of 2: …; else: …`
compiles past the parser and produces a correct witness.

#### C3 (moved to land before A4) — `maxFrontierSize` enforcement

See Cluster C below for the implementation. Lands before A4 in
the slice ordering.

#### A4 (2 cycles): Symbolic-RHS discriminator reassignment

**A4a — IR extension.** Add new statement kind:

```nim
of isVariantReassignSymbolic:
  vrsObjName*: string
  vrsDiscName*: string   ## which axis (for itMultiVariant);
                          ## ignored for single-axis
  vrsRhs*: IRExpr        ## the symbolic RHS expression
```

Stubs in every case dispatch + canonicalize encoding (distinct
from `isVariantReassign`'s static-tag encoding).

**A4b — Walker fork.** `walk(isVariantReassignSymbolic)` emits
one path per arm-ordinal-disjunct of the discriminator's type:
each path is constrained `vrsRhs == arm_k_ord`. The existing
`vArmFields` SymVals are PRESERVED across the fork (no zero-init
— that's the static-tag path's job). For `itMultiVariant`, only
the named axis's `vDisc` is updated; other axes' state is
preserved.

C3 enforcement keeps the fork bounded.

RED: SUT with `obj.kind = someVar` compiles; walker explores
each arm reachable from `someVar`'s range; target reached on one
arm produces a witness with `someVar` bound to that arm's
ordinal.

#### A5 — Composite arm-field types under reassignment

Replace the "primitives-only zero-init" with full type-driven
construction in `walk(isVariantReassign)` for static-tag
reassignment. Reuses `allocateSym`'s existing per-type SymVal
construction.

**Scope note**: `allocateSym` currently raises for
`Table[K≠string]` and `HashSet[T≠int64]`. A5's "reuse that path"
inherits this scope: arm fields of these types still raise. This
is documented as a sub-deferral (not closing
`itTable`/`itSet` expansion in this RFC).

#### A6 — Z3Int promotion of variant discriminator (mandatory under `isOptimised`)

Three sites updated:
- `allocateSym` arm-disjunction emission: dispatch on
  `discInner.kind`, add `svInt` case (`disc.zi == mkZ3IntLit(ord)`).
- `walk(isVariantField)` `discEq`: same dispatch.
- `walk(isVariantReassign)` (and A4b's symbolic variant): same.

Plus verify `extractFromSymVal` and the `itInt` reader handle
the promoted `svInt` discriminator correctly (audit confirms
they do).

Mandatory under `isOptimised`. No setting field — `isExact` is
the established escape hatch for users who want pure BV.

Estimate: **Medium** (was Light in v1; round-1 feasibility
review surfaced the three crash sites).

#### A7 — `var T` parameter support (split into A7a + A7b)

**Correction from v2**: the parser does NOT currently `error()`
on `var T`. `classifyType` in `dsl_typebridge.nim:48-49` silently
unwraps `nnkVarTy` already. `parseProc` in `dsl_parser.nim`
accepts the param but does NOT set `isVar = true` for top-level
SUT params (`parseCalleeImpl` does it correctly; `parseProc`
omits it). The witness is the INITIAL value, which already works
correctly via the `initialEnv` path at `runtime.nim:1319-1322`
when `initialEnv.len > 0` (which is always true for non-empty
SUT param lists).

But A7's downstream story has THREE additional sites that v2
missed:
1. `symexFindAllWitnesses` (Layer 1) has its own `var T` guard at
   `symex.nim:1062` — separate from `parseProc`. Must be removed.
2. `forAllWithSymexSeeds` (Layer 2) takes `prop: proc(x: T)`. For
   `var T` SUTs, this is type-incompatible — Nim requires
   `proc(x: var T)` for the property.
3. `assertCoveredBy` (Phase 7) emits `let wit = …; testFn(wit[0])`
   at `symex.nim:720-723`. For `var T` SUTs, `wit[0]` is an
   rvalue passed as `var T` — compile error.

Split into two cycles:

**A7a — Parser + symexFind acceptance.** Fix `parseProc` to set
`isVar = true` for top-level SUT params. Verify witness extraction
through `symexFind` for a `var T` SUT produces the initial value.
Add tests confirming `initialEnv` is consulted, not `path.env`.

**A7b — Downstream propagation.** Remove the
`symexFindAllWitnesses` `var T` guard. Extend
`forAllWithSymexSeeds` and `symexForAll` to accept
`proc(x: var T)` properties (either through a separate generic
overload or by detecting at macro time and emitting a `var`
local). Change `assertCoveredBy`'s emission to use `var wit` (or
per-param `var` copies) so var-params can be passed by reference
during the test-runtime call.

**Walker version bump lands in A7b's GREEN** (final cycle of
Cluster A).

RED tests:
- A7a: SUT `proc f(x: var int) = x = x + 1; if x == 42: symexTarget("hit")`
  via `symexFind` produces witness `x = 41`.
- A7b: same SUT via `symexForAll(integers(), f, db)` produces a
  Report with the seeded witness; `assertCoveredBy(f, tLabel("hit"))`
  compiles and passes.

### Cluster B — Input-source seeding completeness

#### B1 — `Strategy[T].constraintDigest: string`

Add the field to `Strategy[T]` as a plain `string`. Populate at
construction:

```nim
proc integers*(lo, hi: int, …): Strategy[int] =
  result.constraintDigest = "integers:lo=" & $lo & ";hi=" & $hi
  result.run = …

proc lists*[T](elem: Strategy[T], minLen = 0, maxLen = 100): Strategy[seq[T]] =
  result.constraintDigest = "lists:el=" & elem.constraintDigest &
                             ";min=" & $minLen & ";max=" & $maxLen
  …
```

All standard strategies updated (`integers`, `lists`, `tables`,
`sets`, `sampledFrom`, `booleans`, `floats`, `strings`,
`tuples`, `map`, etc.). The digest cascades through composing
strategies (e.g., `lists(integers(0, 100))` produces
`"lists:el=integers:lo=0;hi=100;min=0;max=100"`).

`newStrategy` (the escape hatch for custom strategies) leaves
the field empty by default; custom-strategy authors populate it
when their strategy is used in a cache-keyed context. The
silent-clamp caveat shrinks to "custom strategies that don't
populate digest."

Cache key derivation in `proptest/smt/canonicalize.nim` includes
`strategy.constraintDigest` when a strategy is in the call site
(via `symexFindAllWitnesses` / `forAllWithSymexSeeds` / etc.).
Empty digest contributes empty string — preserves backward
behavior for custom strategies.

**One-time cache rotation on landing**: every cached entry
derived through a standard strategy is invalidated. Per the
user's explicit "complete library, not single consumer"
direction, this is acceptable. B1 should land in the same
release wave as Cluster A's walker bump for a single user-
visible rotation event.

#### B2 — `Settings.forcePhases: set[PhaseId]`

```nim
type
  PhaseId* = enum
    phDbReuse, phExplicit, phSymexSeed, phRandom, phTargeted,
    phShrink, phExplain, phFinalize

  Settings* = object
    # … existing fields …
    forcePhases*: set[PhaseId]
      ## Phases that run unconditionally, overriding skip
      ## conditions (e.g. dbReuse short-circuit).
```

`symexSeedPhase` checks `phSymexSeed in state.spec.settings.forcePhases`
in addition to the existing `rawFalsification.isSome` self-gate.
When forced, the phase runs even after a prior phase falsified;
its findings are appended to `Report.symexFindings` (not
overwriting the existing `rawFalsification`).

Default: empty set (no behavior change).

#### B3 — `tables`/`sets` trace-equivalence

Phase 12 cycle 6 already sorts iteration. The remaining gap is
*collision*: two distinct keys hashing to the same bucket
producing the same iteration order with different reachable
values. The fix is to render under semantic equality:
sorted-unique elements only. Mostly tested already; this cycle
adds an explicit pin and tightens the docs.

#### B4 — Named-field tuple strategies in multi-arg `symexForAll`

Macro extension: when `s.getTypeInst()[1]` is `nnkTupleTy` (named
fields), walk the field names and match against `fn`'s formal
params. Emit wrapper `proc(t: tuple[a: T1, b: T2]) = fn(t.a, t.b)`.

Existing `error()` at symex.nim:419-423 removed.

#### B5 — `symexCapture` per-seed in `assertCoveredBy`; `sfReplayMiss`

The original B5 design called for `symexCapture` armed in
`symexSeedPhase`. Round-1 review surfaced: `symexSeedPhase`
receives raw choice sequences with no attached target metadata,
so `sfReplayMiss` cannot be reliably computed at that layer.

Revised scope: B5 wraps `symexCapture` per-replay inside
`assertCoveredBy`'s existing capture loop (where target
provenance IS available). New `SymexFindingStatus.sfReplayMiss`
records "this seed claimed to reach the target but the live
replay didn't hit the marker." Useful for diagnosing
strategy-mismatch issues in regression tests.

Per-replay scoping: `symexCaptureBegin/End` called inside the
per-seed loop, not wrapping it.

`symexSeedPhase` is unchanged. Documented as an honest scope
restriction — `symexSeedPhase`'s seed-layer capture is a future
RFC if a consumer needs it.

#### B67 — Label-by-name `excludeTargets` + parse-time `isUnsupported` diagnostic (merged)

Two small items; one cycle.

**Label-by-name filter**: when `excludeTargets` contains
`tLabel("name")`, filter ONLY that label name (current behavior
filters all labels by kind). Implementation: extend the macro
that already walks `excludeTargets` to track per-target label
names.

**`isUnsupported` diagnostic**: in `dsl_parser.nim`, when a
sub-AST is classified as `isUnsupported`, scan the **unparsed
Nim sub-AST** for `symexTarget(...)` / `symexAssert(...)` calls
and emit a `{.hint.}` listing each one found. This is a
parse-time diagnostic (the IR scan can't see past
`isUnsupported`; round 1 caught this).

**Honest framing**: this improves observability of Phase 12
deferral #3 (markers in branches after unsupported nodes
invisible). It does NOT close #3 — the walker semantics are
unchanged, the markers are still invisible to the analysis.
PHASE12_PLAN.md updated to "**PARTIAL — observability improved
by B67; semantic closure deferred to Phase 3 fragment
expansion**."

### Cluster C — Verdict caching completeness

#### C1 — Verdict-cache cascade for `symexFind` / `assertCoveredBy`

Extend `symexFind`'s macro emission to mirror Layer 1's cycle-7
cascade: SAT cache → verdict cache → cold `runSymex`. The result
shape requires care:

```nim
type SymexResult*[T] = object
  status*:        SymexStatusKind
  witness*:       T
  abstractions*:  AbstractionLog   ## empty when fromCache = true
  callStats*:     CallStats        ## empty when fromCache = true
  fromCache*:     bool             ## NEW — true iff served from cache
```

On verdict-cache hit: `status = sxUnsat` or `sxUnknown`, witness
default, `abstractions = @[]`, `callStats = @[]`, `fromCache =
true`. The empty fields are documented and consistent: a cached
verdict carries no abstraction log because the log is an
artifact of THIS run's exploration, not the original.

`assertCoveredBy` calls `symexFind` so it inherits the cache for
free. Documented in `determinism.md` as "Phase 13 cache
extension; previously cold `assertCoveredBy` calls now serve
from cache after first warm-up."

#### C2 — Layer 1's `dbErrors` accumulator wired into `Report.dbErrors`

Add `engineSymexDbErrors*: seq[string]` threadvar in
`engine/types.nim` (same pattern as `symexFindings`). Layer 1's
`symexFindAllWitnesses` macro emits a drain into this threadvar
at the end of its runtime block. `finalizePhase` consumes the
threadvar and appends entries to `Report.dbErrors`.

**Concurrent sink note**: `engineSymexDbErrors` and the existing
`symexFindings` are separate accumulators. B5's per-replay
`symexCapture` in `assertCoveredBy` does not interact with
either (it has its own context).

#### C3 — `maxFrontierSize` enforcement (lands BEFORE A4)

Walker tracks `currentFrontier.len` after each `walk` call. When
the frontier exceeds `settings.maxFrontierSize`, the
**highest-uncertainty paths are pruned** (ADR-0004 policy).
Pruned paths' `sawUnknown = true` flag propagates to the final
result.

Effect on cached verdicts: frontier-pruned walks produce
`sxUnknown` (NOT `sxUnsat`). Cached under `:unk`. This is the
**third UNKNOWN sub-case**, distinct from:
- Z3-rlimit-exhausted (Phase 13)
- Walker-loop-unwind exhausted (Phase 11 baseline)
- **Frontier-pruned (Phase 14, new)**

All three set `sawUnknown = true`; all three cache under `:unk`;
the distinction is documented in `determinism.md`'s UNKNOWN
semantics section but does not affect cache key participation.

**`maxFrontierSize` already participates in the cache key**
(canonicalize.nim:339). C3 makes that participation
behaviorally meaningful (previously the field was inert).

#### C4 — Z3 internal-error policy (mandatory silent catch with structured errors)

Wrap `runSymex`'s top level in `try/except` catching `Z3Error`
— the abstract base class defined in
`_deps/z3/src/z3/error.nim:43`. The 12 typed subclasses
(dispatched by `raiseZ3Error`) include `Z3MemoryError`,
`Z3InternalError`, `Z3OperationError`, `Z3InvalidUsageError`,
`Z3SortMismatchError`, `Z3IndexOutOfBoundsError`,
`Z3InvalidArgError`, `Z3ParseError`, `Z3InvalidPatternError`,
`Z3FileError`, `Z3RefcountError`, `Z3UnknownError`. Catching the
base captures all 12.

`Z3Error extends CatchableError`, which means walker
`ValueError` and `AssertionDefect` continue to propagate as
today — they are real walker bugs and must surface during
development.

On catch: return `RawResult(status: sxUnknown, errors:
@[SymexErrorInfo(...)], witness: default)`. The `errors` field is
new on `RawResult` (see below).

`ValueError` and `AssertionDefect` from walker logic are NOT
caught. They propagate as today — they are real bugs and must
surface during development.

Structured error info on `SymexFinding`:

```nim
SymexErrorInfo* = object
  source*:   string                 ## e.g. "z3:internal", "z3:oom"
  message*:  string
  severity*: SymexErrorSeverity     ## sevHint | sevWarning | sevError

SymexErrorSeverity* = enum
  sevHint, sevWarning, sevError

SymexFinding* = object
  # … existing fields …
  errors*: seq[SymexErrorInfo]      ## empty when clean
```

`recordSymexFinding(f)` fires unconditionally on the
exception-catch path (same `outside the if/else tree` invariant
Phase 13 established).

**Mandatory** — no settings field. Consumers treat any
`sfUnknown` with non-empty `errors` as fatal at their own report
policy.

## v3 round-2 backlog (non-critical findings to address during TDD)

Round 2 surfaced 14 HIGH, 18 MEDIUM, and 7 LOW findings beyond
the 5 CRITICAL items now baked in. Rather than re-rewriting the
RFC for each, they are catalogued here. Each is owned by its
relevant cycle's TDD slice — the implementer addresses the
backlog item when entering that cycle's plan.

**HIGH (14)**:
- **File path corrections**: A3 and A1b live in
  `dsl_typebridge.nim` (lines 158 and 193), NOT `dsl_parser.nim`.
  RFC text says "parser" but the discriminator type check and
  multi-recCase check are in the typebridge. Implementer must use
  the typebridge file for these cycles.
- **A1a stub list expansion**: include `IRType` render helpers
  (`tyOf`, `==`, `$`), `collectSetLitMembers` and
  `collectTableLitKeys` in `runtime.nim`.
- **A4a stub list expansion**: same — `collectSetLitMembers` and
  `collectTableLitKeys` need `of isVariantReassignSymbolic:
  discard` stubs.
- **B2 `PhaseId` definition site**: enum doesn't exist yet;
  must be defined in `engine/types.nim` with values mirroring
  `Phase[T].name` strings. Add a `phaseName(p: PhaseId): string`
  converter to keep them in sync.
- **B5 case-status audit step**: add an explicit "grep
  `case.*status` exhaustive dispatches and add `of sfReplayMiss:`
  branches" sub-step to B5's RED phase. Sites identified:
  `saveSymexVerdictImpl` at symex.nim:267 (return early — not
  cacheable), plus any others surfaced by grep. Same pattern as
  Phase 12 cycle 5's `sfNotApplicable` audit.
- **B67 diagnostic level**: emit `{.warning.}` not `{.hint.}`.
  Hints are styled informationally and often suppressed; the
  user placed `symexTarget` explicitly and wants symex to cover
  it — warning is the right urgency.
- **C1 `SymexResult.fromCache` placement**: `SymexResult[T]` is
  a discriminated union (`case status*: SymexStatusKind`).
  `fromCache: bool` must be added as a **base (pre-discriminator)
  field** to be accessible across all status branches.
- **C3 enforcement site**: `walkBlock` inline, after each
  `walk(s, result, w)` call — NOT a `WalkCtx.currentFrontier`
  field. The frontier is the `paths: seq[Path]` argument flowing
  through `walkBlock`'s loop at `runtime.nim:1421-1426`.
- **C3 sort policy** (binary `uncertain` flag): "highest-
  uncertainty-first" concretely means: sort certain paths before
  uncertain; stable sort within each tier; truncate to
  `maxFrontierSize`; mark all pruned paths' contribution via
  `w.sawUnknown = true`. `maxFrontierSize = 0` = unlimited (no
  prune).
- **Report.symexErrors placement**: add
  `Report.symexErrors: seq[SymexErrorInfo]` for walker-level Z3
  errors that occur BEFORE any per-target finding is generated.
  `SymexFinding.errors` is per-target; `Report.symexErrors` is
  walker-level. Add `engineSymexErrors` threadvar in
  `engine/types.nim` (same pattern as `engineSymexDbErrors` from
  C2); drain in `finalizePhase`.
- **`RawResult.errors` plumbing**: `RawResult` in `smt/types.nim`
  gains `errors: seq[SymexErrorInfo]` field. `SymexErrorInfo`
  lives in `smt/types.nim` (NOT `engine/types.nim`) to avoid an
  `smt/` → `engine/` import. The translation from
  `RawResult.errors` to `SymexFinding.errors` happens at the
  macro-emitted runtime layer in `symex.nim`.
- **B1 digest composition for combinators**: specify the digest
  string for each composing strategy explicitly. Recommended:
  - `map(s, f)` → `"map:" & s.constraintDigest` (opaque
    transform — closure not captured; documented as silent-clamp
    on the transform)
  - `flatMap(s, f)` → `""` (indeterminate; silent-clamp
    documented)
  - `filter(s, pred)` → `"filter:" & s.constraintDigest`
  - `oneOf(ss)` → `"oneOf:[" & ss.mapIt(it.constraintDigest).join(",") & "]"`
  - `frequency(ws)` → `"frequency:[" & ws.mapIt($it[0] & ":" & it[1].constraintDigest).join(",") & "]"`
  - `recursive(...)` → `""` (closure-based; documented)
  - Unconstrained leaves (`booleans()`, `bytes()`) → name as
    sentinel: `"booleans"`, `"bytes"`
- **`var T` `assertCoveredBy` emission**: change `let wit` to
  `var wit` (or per-param `var` copies) so var-params can be
  passed by reference. Covered by A7b but listed here for
  visibility.
- **B5 `sfReplayMiss` detection mechanism per target kind**:
  - `tLabel`: `symexCapture` per-replay (current B5 mechanism)
  - `tAssertionViolation` / `tIndexError` / `tFieldDefect`:
    boolean flags (existing `assertCoveredBy` machinery), no
    `symexCapture` needed.

**MEDIUM (18)** — sequencing, scope, doc gaps:
- B2 `forcePhases` for non-skippable phases (`phShrink`,
  `phExplain`): no-op vs error when forced without falsification.
- A6 + A7 commit atomicity for shared-DB CI scenarios (single
  commit or coordinated).
- Phase 12 deferral #1 reframed PARTIAL (custom strategies
  unchanged), matching #3's treatment.
- A1+A2, A1+A3, A1+A2+A3 maximal-soup composition tests added.
- A3+A5 (non-enum disc + composite arm field) interaction test
  added.
- C1 + `assertCoveredBy` cached `sfUnsat` vacuous-pass contract
  documented.
- Cycle 24 docs sweep enumerates A6 as a behavioral change for
  existing `isOptimised` + variant users.
- UNSAT-monotonicity property w.r.t. `maxFrontierSize`
  documented in determinism.md.
- `SymexErrorSource` as enum (`sesZ3 | sesWalker | sesUnknown`)
  not raw string.
- `SymexErrorSeverity` dropped (C4 only produces `sevError`) OR
  documented as reserved.
- `allPhases* = {phDbReuse, ...}` constant added.
- `newStrategyWithDigest*` constructor as custom-strategy escape
  hatch; document mutation hazard on field.
- `sfReplayMiss` doc comment cross-references `sfNotApplicable`.
- B2 enum sync with `Phase[T].name`; converter proc.
- ADR-0003 split into ADR-0003 (IR shape) + ADR-0005 (variant
  semantic decisions A2/A3/A4/A7).
- A4b else-arm under symbolic-RHS: conjunction-of-inequalities
  form (distinct from non-else arm equality form).
- Release strategy (one PR or two for Cluster A + B + C; affects
  user-visible rotation event count).
- C3 transient peak allocation bounded by SUT's arm count, not
  by `maxFrontierSize` (post-fork prune, not pre-fork guard).

**LOW (7)**: naming polish, doc clarifications, `discoveredBy`
reuse for var T, generic-strategies-vs-generic-SUTs clarification,
SYMEX_PLAN.md row format, test file naming `tsymex_phase14_*`,
`SymexErrorInfo.source` enumeration if kept as string.

---

## Slice plan — 30 cycles

### Pre-cycle ADRs (2)

- **ADR-0003**: write `docs/symex/ADR-0003-variant-soundness.md`.
- **ADR-0004**: write `docs/symex/ADR-0004-frontier-pruning.md`.

These land first (no code). Each is ~1h.

### Cluster A — variant completeness (9 cycles)

1. **A1a** — IR `itMultiVariant` extension + stubs in every dispatch site. Heavy.
2. **A1b** — Parser detects + emits multi-recCase. Light.
3. **A1c** — Walker handles `itMultiVariant` (allocateSym, isVariantField, isVariantReassign, extractFromSymVal). Heavy.
4. **A1d** — Witness emitter (nested case for multi-disc objects). Medium.
5. **A2** — `else:` arms (parser + walker constraint). Medium.
6. **A3** — Non-enum discriminator types (parser relax + walker generalize). Medium.
7. **C3** — Frontier pruning (lands here in Cluster A's ordering — pre-A4 dependency). Heavy.
8. **A4a** — IR `isVariantReassignSymbolic` + stubs. Light.
9. **A4b** — Walker fork for symbolic RHS. Heavy.
10. **A5** — Composite arm-field zero-init via full SymVal construction. Light.
11. **A6** — Z3Int discriminator promotion: three crash sites updated. Medium (was Light in v1).
12. **A7** — `var T` parameter support + walker version bump `"3" → "4"`. Medium.

### Cluster B — input-source completeness (6 cycles)

13. **B1** — `Strategy[T].constraintDigest` field + populate for all standard strategies. Heavy (touches every standard strategy constructor + cache key derivation).
14. **B2** — `Settings.forcePhases: set[PhaseId]` + symexSeedPhase honors it. Light.
15. **B3** — `tables`/`sets` trace-equivalence under collision: pin + doc. Light.
16. **B4** — Named-field tuple strategies in multi-arg `symexForAll`. Heavy (macro work).
17. **B5** — `symexCapture` per-seed in `assertCoveredBy` + `sfReplayMiss` status. Medium.
18. **B67** — Label-by-name `excludeTargets` + parse-time `isUnsupported` diagnostic. Light.

### Cluster C — verdict caching completeness (3 cycles, since C3 moved)

19. **C1** — verdict-cache cascade for `symexFind` / `assertCoveredBy`; `SymexResult.fromCache` field. Heavy.
20. **C2** — `engineSymexDbErrors` threadvar drain in `finalizePhase`. Light.
21. **C4** — Z3 internal-error policy (specific exception catch) + `errors: seq[SymexErrorInfo]` field. Medium.

### Composition + negative-boundary tests (2 cycles)

22. **A1+A4+A5 composition test** — multi-recCase object with composite arm field reassigned via symbolic RHS; each axis resolves independently; composite field constructed correctly. Heavy.
23. **A3 negative-boundary tests** — `case kind: float`, `case kind: SomeObject`, etc. still produce macro-time `error()` with clean diagnostic. Light.

### Close-out (7 cycles)

24. **Docs sweep — determinism.md**: Verdict-caching section UNKNOWN semantics updated with third sub-case (frontier-pruned); strategy-constraint-cache section closed (B1 closes it for standard strategies; custom strategies retain documented opt-in caveat); walker version history table entry `"3" → "4"` with A1–A7 rationale; ADR-0003 + ADR-0004 references; Phase 13→14 migration note (parser-erroring patterns can't have cached entries under `"3"`, so single bump at A7 is sufficient).
25. **Docs sweep — README.md**: supported Nim fragment updated; new "What this does NOT support" section enumerating remaining gaps (generic procs with workaround, cross-module privates, etc.); Phase 14 status; cache-hit example with `fromCache` field.
26. **Docs sweep — generic-proc workaround pattern**: new section in determinism.md (or a focused `docs/symex/generics.md`) showing the concrete-shim pattern.
27. **PHASE11_PLAN.md** — close-out: all 6 open deferrals marked CLOSED; reference Phase 14 RFC.
28. **PHASE12_PLAN.md** — close-out: #1, #4, #11, #12, #13 CLOSED; #3 PARTIAL (B67); #5 CLOSED (A7); #6 documented workaround.
29. **PHASE13 RFC** — `/docs/symex/RFC-unsat-caching.md` "What this opens" updated: all 4 items CLOSED.
30. **SYMEX_PLAN.md** — Phase 14 row; design-decision section; status block (test count update: ~70 files, ~250 tests).
31. **Memory + plan close-out**: `proptest-symex-shipped.md` updated; `MEMORY.md` index refreshed.
32. **Final regression sweep** + commit.

**Total: 30 cycles + 2 pre-cycle ADRs.** Estimated effort: 100–130h.

## Compatibility on upgrade

| Change | Impact |
|---|---|
| `symexWalkerVersion` `"3" → "4"` (A7 GREEN) | Rotates ALL cached witnesses and verdicts. Parser-erroring patterns under `"3"` cannot have entries, so this single bump is both necessary and sufficient for A-cluster semantic changes. One-time cold re-derivation. |
| `Strategy[T].constraintDigest` field (B1) | Rotates entries derived through standard strategies. Same wave as walker bump → one user-visible event total. |
| New `itMultiVariant` IR kind | Backward-compatible: single-recCase objects still use `itVariant` unchanged. |
| `Settings.forcePhases: set[PhaseId]` | Non-breaking; default empty preserves Phase 13 behavior. |
| `SymexFinding.errors: seq[SymexErrorInfo]` | Non-breaking; default empty seq. |
| `SymexResult.fromCache: bool` | Non-breaking; defaults to `false`. |
| `SymexFindingStatus.sfReplayMiss` | Non-breaking enum extension; existing case-status matches updated. |
| `A6` Z3Int discriminator promotion under `isOptimised` | Mandatory; covered by walker bump rotation. Users wanting pure BV use `isExact`. |
| `var T` parameter parser acceptance | SUTs that previously errored at macro time now compile and run. No behavior regression for existing callers. |
| `C4` mandatory silent catch | Z3 internal errors no longer propagate; they become `sfUnknown` with `errors` populated. Consumer workflows treating ANY `sfUnknown` as fatal preserve the abort-on-Z3-error behavior. Document this as a deliberate behavior change. |

## Open questions for `/architect`

**None.** Round 1 review closed all four open questions:
- Q1 (A1 IR shape) → `itMultiVariant` separate kind.
- Q2 (A3 disc whitelist) → enum + int* + uint* + range[T any
  ordinal] + char + bool.
- Q3 (B1 digest contract) → plain `string` field, auto-populated
  for standard strategies.
- Q4 (C3 pruning policy) → highest-uncertainty-first; pruned →
  sxUnknown.
- Q5 (A4 fork budget) → C3 enforcement, with A4 sequenced after.
- Q6 (ADR vs determinism for A2/A3/A4) → ADR-0003 covers A4's
  fork semantics (real architectural consequence) and the A1
  `itMultiVariant` design choice. ADR-0004 covers C3 frontier
  pruning policy. A2/A3 are determinism.md subsections
  (mechanical extensions).

## What this RFC explicitly closes

- **All open Phase 11 deferrals**: #1, #2, #3, #7, #8, #12.
- **Phase 12 deferrals**: #1 (silent-clamp for standard
  strategies), #4 (dbReuse override), #5 (`var T`), #11
  (`tables`/`sets` collision), #12 (named-field tuple), #13
  (capture in `assertCoveredBy`), label-by-name `excludeTargets`.
- **Phase 12 #3** (markers in unsupported branches) — PARTIAL
  closure via B67 observability improvement. Full closure
  requires Phase 3 fragment expansion (separate RFC).
- **All open Phase 13 follow-ups**: C1, C2, C3, C4.

## What this RFC explicitly does NOT close

- **Phase 12 deferral #6** (generic procs) — Nim macro-binding
  limit; documented wrapper pattern.
- **#138** (cross-module private helpers) — user-held session.
- **Shape A** (#124–#132) — separate architecture.
- **Nim 2.2 toolchain workarounds** (#14, #15) — close on
  toolchain fix.
- **Parallel symex** — separate optimization track.
- **`itTable[K≠string]` / `itSet[T≠int64]`** expansion — A5's
  composite-field work inherits the existing scope; broader
  container expansion is a separate RFC.

## Estimated effort

30 cycles + 2 ADRs. ~100–130h. Cluster A is ~50h. Cluster B is
~25h. Cluster C is ~20h. Composition/negative tests ~15h. Docs
+ close-out ~20h.

Largest single cycle: **A1c (walker handles `itMultiVariant`)**
— ~8h, touches `runtime.nim` in 4 places.

Cluster A can land as one PR (walker bump at A7's end). Cluster
B can land as another PR (B1 should coordinate timing with
Cluster A's release for single-rotation UX). Cluster C splits:
C3 inside Cluster A's PR (ordering dependency); C1+C2+C4 as a
separate PR.

This is the largest single RFC since Phase 11, exceeding Phase
13 in scope. The cluster organization keeps each cluster
independently testable and reviewable.
