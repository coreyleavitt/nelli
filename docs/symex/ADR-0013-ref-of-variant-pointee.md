# ADR-0013 — ref-of-variant pointee (field-split-per-arm heap)

> **STATUS: ACCEPTED — 2026-06-28.** Design ADR for RFC slice **A2** (ref-of-
> variant / complex-pointee deref). Authored from a codebase-mode `/architect`
> design pass (Explore map + design draft + control-loop adversarial soundness
> review). Sits on top of **ADR-0010** (logical heap) and reuses the value-variant
> machinery (`allocateSym(itVariant)` / the `isVariantField` walk arm).
> Citations are point-in-time at walker **v26**; re-verify each `/tdd` cycle.

## Context — the blocker

A `ref object` whose pointee is an object variant (`case kind: K of ...`) cannot
be deref'd today: field/discriminant access through the ref raises
`SymexRefVariantUnsupportedError` → `sxUnknown` + `heRefVariantUnsupported`
(guards in `runtime_heap.nim` `walkHeapArm`: the `isDeref` read arm and the
`isDerefWrite` arm both reject `stmt.dObjTy.kind in {itVariant, itMultiVariant}`).

**Root cause:** a variant has **no single Z3 sort.** `allocateSym(itVariant)`
yields a discriminator SymVal + per-arm field arrays, not one AST. ADR-0010's heap
is a per-type `Z3Array[Ref_T, <valueSort>]`, and `heapValueSort` (which reads the
Z3 sort of an `allocateSym` result) is **undefined for `itVariant`** — there is no
sort to use as the array's value type.

## Decision

**Adopt Option B — field-split-per-arm.** Model the variant pointee as several
**primitive-sorted** heap arrays — one for the discriminant, one per (arm, field),
and the existing shared array for plain fields. Each array's value sort is a
primitive (`Z3Int`/`BV`/`Z3Bool`/`Ref_T`), so `heapValueSort` is **never called
for the whole variant** and the "undefined sort" problem evaporates. Field access
asserts `disc == tag` before read/write — exactly the inline `isVariantField`
pattern, lifted to the heap.

**Option A — Z3 datatypes — is REJECTED.** nim-z3's typed `declareDatatype[T]`
needs a *static* Nim marker type at compile time, but SUT variant types are
*runtime-described* (`IRType`/`itVariant`). Using Z3 datatypes means dropping to
raw `Z3_mk_constructor`/`Z3_mk_datatype`/`Z3_query_constructor` FFI and
re-introducing the refcount/lifecycle hazards the binding exists to hide. High
burden, no modeling advantage over field-split for our purposes. (May revisit as a
future optimization; not now.)

## Design

### D1 — heap-key scheme

| Category | Key | Value sort |
|----------|-----|------------|
| Discriminant | `refPointeeTypeId(objTy) & "__@disc"` | primitive sort of `objTy.vDiscTy` (Bool/Int/BV — **not always Int**) |
| Arm field | `refPointeeTypeId(objTy) & "__@" & $arm.tagOrdinal & "__" & field` | the field's primitive sort |
| Plain/shared field | `refPointeeTypeId(objTy) & "__" & field` (== existing `fieldHeapKey`) | the field's primitive sort |

The **`@` prefix is the collision guard**: a Nim identifier cannot begin with `@`,
so `__@disc` / `__@<ordinal>__<field>` can never collide with a legitimate plain-
field key `__<field>`. Arm tags use the **ordinal** (`arm.tagOrdinal: int`, the
key already used by `vArmFields`/`vArmFieldNames`); an `else` arm is ordinal `-1`.
Plain fields keep the existing non-variant key verbatim, so a plain-field access
through a variant ref is indistinguishable from an object-field access through a
non-variant ref (and the R6 alias tests are unaffected).

### D2 — deref-READ protocol (`isDeref`, `p.field`)

Lift the `itVariant` half of the read guard (keep `itMultiVariant` raising until
the deferred multi-variant slice). Then branch by field category:

- **Discriminant read** (`stmt.dField == objTy.vDiscName`): materialise the disc
  heap (`__@disc`) lazily, `select` at the ref address, lift to a SymVal of
  `vDiscTy`, bind. **No fork** — mirrors the value-variant rule that disc access is
  a pure expression (`iekField`), never an `isVariantField` fork.
- **Plain field read**: identical to the existing R6 non-variant path. No fork.
- **Arm-specific field read**: mirror the `isVariantField` walk arm **exactly** so
  ref-variants and value-variants behave identically:
  1. scan `objTy.vArms` for arms declaring the field → `(tagOrdinal, fieldIx)`;
  2. materialise the disc heap, `select` the disc, build `discSV`;
  3. build `discEq(tag)` with the **same dispatch** as `isVariantField`
     (`svBV8/16/32/64`, `svInt`, `svBool`; any other disc sort → classified
     `heRefVariantUnsupportedDisc`, `sxUnknown` — never guess);
  4. `inArmCond = OR of matching-arm equalities` (else-arm = conjunction of
     negations of the non-else ordinals, mirroring the value path);
  5. **FieldDefect fork** on `not inArmCond` (D1a unconditional — same call shape
     as the value-variant arm);
  6. in-arm continuation asserts `inArmCond`; read each matching arm's field heap;
     bind via an **ite-chain** over the matching arms.

### D3 — deref-WRITE protocol (`isDerefWrite`, `p.field = v`)

Symmetric to D2 with `Z3_mk_store`:
- **Discriminant write**: `store(disc_heap, ref, v)`. No special invalidation — any
  later arm read selects the updated disc and forks correctly; `store` is a pure
  functional update, so other paths/aliases are unaffected per Z3 array theory.
  (Whether the SUT subset even permits post-construction disc assignment is moot —
  the model is correct if it occurs.)
- **Plain field write**: as R6 non-variant.
- **Arm field write**: scan arms, select disc, `inArmCond`, **FieldDefect fork** on
  `not inArmCond` (writing through an inactive arm is a FieldDefect — same as the
  value semantics), lower RHS, `store` into the matching arm's field heap. Disc heap
  carried unchanged. Aliasing is automatic: two refs to one address share every
  heap array, so `select(store(h,p,v),q)` with `p==q` yields `v`.

### D4 — soundness (Invariant 3 — no false positives)

1. **Inactive arm never read as active.** The in-arm continuation asserts
   `inArmCond` onto `pc`; a path whose disc is pinned to a different arm is UNSAT,
   so the ite result is never observed for the wrong arm.
2. **Disc consistency across aliasing.** The disc heap is one `Z3Array`; aliased
   refs select the same index; a `store` through one is observed by the other — the
   same property that makes R6 field-split heaps alias-observable.
3. **Off-arm access ⇒ FieldDefect**, never a silent wrong value (D1a fork).
4. **Distinct arm heaps never alias** (distinct key strings ⇒ distinct free
   arrays).
5. **Discriminant-range constraint — REQUIRED for EVERY ref-to-variant address,
   not only `new`.** *(Control-loop review addition — the design draft covered only
   `isNew`.)* A free `select(disc_heap, addr)` is unconstrained, so for an
   `enum`/`int`/`BV` discriminant Z3 may pick an ordinal matching **no** arm,
   producing an unsound witness (a pointee with an impossible `kind`). Arm-field
   reads self-constrain (they assert `disc == tag` for a *valid* ordinal), but
   reading the **discriminant itself** into a witness does not. Therefore the
   disc-range disjunction (`OR over legal arm ordinals`, mirroring
   `allocateSym(itVariant)` at the value level) **must be asserted once per address
   whose disc heap is first materialised — for `new`-allocated AND param/input
   refs alike.** For a **bool** discriminant the disjunction is tautologically true
   (a no-op), so Slice 1 / the r6 `tag: bool` test is unaffected; the constraint is
   load-bearing the moment an enum/int discriminant appears (Slice 2 must test it).
6. **Multi-tag arm fields (`of A, B: x`).** *(Edge note.)* A field shared by several
   tags must be modeled **consistently with the value-variant `isVariantField`
   treatment** (whether `vArmFields` shares one SymVal across the tags or splits per
   ordinal). Mirror whatever the value model does; do not introduce a divergence.
   Rare in practice; not a Slice 1 blocker.
7. **Degrade-not-guess cases** (each → classified `sevError`, `sxUnknown`):
   unsupported disc sort; `itMultiVariant` pointee (until the deferred slice);
   degenerate else-only variant (mirror the `isVariantField` guard).

### D5 — witness serialization

Extend `extractFromSymVal` (the `svRef`/`svPtr` arm) with an `itVariant` pointee
branch: evaluate the disc under the model, emit the discriminant leaf, then emit
**only the active arm's fields** (active arm = the arm whose ordinal equals the
evaluated disc), then plain fields. Recursive `ref` trees of variant nodes are
bounded at walk time by `maxHeapDepth`; the extraction-time recursion needs its own
small depth guard (Slice 2+ refinement).
**Implementation flag:** extraction needs the winning path's `heaps` table; this
likely wants a new `currentVariantHeaps` threadvar populated before
`extractWitness`, analogous to `currentHeapDerefVals`. (NB: [[symex-version-bump-cr2]]
governs the pin updates, not this threadvar — A0 just left the closure-axiom
threadvars noted, unrelated.) Slice 1 needs only a structural marker (the r6 test 5
checks `status == sxSat`, not witness shape), so full serialization can land in
Slice 2.

### D6 — multi-variant (`itMultiVariant`): DEFERRED

A2's first slices model **single-axis `itVariant`** only (covers the r6 test 5 and
the common case). Keep the existing `itMultiVariant` error guard. When taken up
(later slice): per-axis disc key `..."__@disc__" & ax.discName`, per-axis arm field
`..."__@" & ax.discName & "__" & $ord & "__" & field`, axis identified by the same
scan as the value `svMultiVariant` arm.

### D7 — no new budgets

Variant forks are ordinary path forks (≤ 2 per arm-field access: in-arm +
FieldDefect), bounded by existing `maxHeapDepth` / `maxFrontierSize`;
freshness is untouched; ite-chains are J-deep for a field in J arms (trivial for
Z3 / QF_AUFBV). No new budget parameters.

## Consequences

- `tests/tsymex_phase15_r6_refobj.nim` **test 5** flips from `sxUnknown +
  heRefVariantUnsupported` to a real verdict (`sxSat` for `variantRef`).
- **New modeled construct ⇒ cache-key change ⇒ `symexWalkerVersion` bump + both
  pins** (`tsymex_phase15_CR2_cachekey`, `tsymex_phase16_R16_1_arithcheck_foundation`)
  on each behaviour-changing slice. See [[symex-version-bump-cr2]]. A previously-
  cached `sxUnknown` for such a SUT is semantically stale and MUST be invalidated.
- Value- and ref-variant field access become behaviourally identical (same
  FieldDefect semantics) — a deliberate consistency win.

## Implementation path (`/tdd`)

1. **Slice 1 — discriminant read/write through a ref.** Lift the `itVariant` read
   & write guards (keep `itMultiVariant`); disc read (no fork) + disc write; assert
   the disc-range disjunction at first disc materialisation for **every** address
   (D4.5; no-op for bool); structural witness marker. RED: r6 test 5 → `sxSat`.
   **Bump v26→v27 + both pins.**
2. **Slice 2 — arm-field read + FieldDefect + full witness.** Matching-arm scan,
   discEq, FieldDefect fork, ite-chain bind; `extractFromSymVal` variant branch
   (`currentVariantHeaps`). **Add an enum/int-discriminant test** (exercises D4.5,
   which bool can't). RED: arm-field-read `sxSat` + wrong-arm `tFieldDefect`.
   **Bump v27→v28 + both pins** (unless folded with Slice 1 in one landed round).
3. **Slice 3 — arm-field write + aliasing.** Symmetric write path. RED:
   read-after-write `sxSat`, alias-through-two-refs `sxSat`, wrong-arm-write
   `tFieldDefect`. **Bump + both pins.**
4. **Slice 4 (separate, deferred) — `itMultiVariant`.** Per D6.

Each slice: full both-backend `dt-bounded` sweep; never restructure a SUT to pass —
escalate as a BLOCKER. Rejected-alternative and soundness rationale above is the
contract; re-verify line anchors per cycle (they drift).
