# Phase 11 — Variant soundness build plan

> Closes the variant-witness-reconstruction stub *and* the underlying
> walker soundness gap. Introduces `itVariant` as a first-class IR
> kind, `svVariant` as a first-class SymVal, and `tFieldDefect()` as
> a first-class symex target. Drops the flat-tuple lowering for
> variants entirely.

## Why we're doing this

The Phase 4 flat-tuple lowering of variants is a soundness compromise:
the walker can reason about every variant field regardless of the
discriminator's arm. In practice this hasn't bitten any SUT (real
Nim code gates field access by `kind`), and the runtime `FieldDefect`
catches any miss before incorrect output propagates. But it is
unsound, and the witness-emission stub (`default(Object)`) is a
user-facing correctness bug.

Phase 11 closes both: variants get proper sum-type representation,
the walker forks at each field access, and `tFieldDefect()` joins
`tIndexError()` as a memory-safety target kind.

## Architectural sketch

### IR

```nim
type
  VariantArm* = object
    tagOrdinal*: int          # enum constant's ordinal value
    tagName*:    string       # source name; used in case-dispatch emit
    fieldNames*: seq[string]
    fieldTypes*: seq[IRType]

  IRType* = ref object
    case kind*: IRTypeKind
    of itVariant:
      vDiscName*:   string    # discriminator field name (any name)
      vDiscTy*:     IRType    # must be itInt (the enum's int repr)
      vArms*:       seq[VariantArm]
      vObjectName*: string
    ...
```

### Walker runtime

```nim
type
  SymVal* = ref object
    case kind*: SVKind
    of svVariant:
      vDisc*:      SymVal                    # discriminator (svInt)
      vArmFields*: Table[int, seq[SymVal]]   # tag ordinal → per-arm fields
```

- **Allocation**: fresh `vDisc` constrained to `legal-tag-ordinals`;
  fresh symbolic SymVal per (arm, field).
- **`iekField`**: walks each arm — for arm tag `T`, the in-arm path
  conjoins `vDisc == T` and binds the field to `vArmFields[T][ix]`;
  the not-in-arm path conjoins `vDisc != T` and treats the access
  as a `FieldDefect`. Result is an ite-chain plus a fork to the
  field-defect path.
- **Discriminator access** (`obj.kind` when `kind` is the discName):
  returns `vDisc` directly, no fork.
- **Discriminator assignment** (`obj.kind = newTag`): the active arm
  changes; existing arm-field bindings are replaced with fresh
  symbols. Rare in real code; must be sound.

### New target

```nim
SymexTargetKind* = enum
  stkLabel, stkAssertionViolation, stkIndexError
  stkFieldDefect              # NEW

proc tFieldDefect*(): SymexTarget = SymexTarget(kind: stkFieldDefect)
```

### Witness emission (`emitTyAndReader`)

```nim
of itVariant:
  # Read discriminator → enum constant.
  let kindReader = primReader(ty.vDiscTy)
  # Case-dispatch over legal tag values; per arm, construct the
  # variant with the discriminator literal + the arm's fields.
  result = quote do:
    case `kindReader`
    of `tag1Ordinal`: ObjType(`discName`: tag1Const, f1: ..., f2: ...)
    of `tag2Ordinal`: ObjType(`discName`: tag2Const, fA: ...)
    ...
```

Replaces the `default(Object)` heuristic stub.

### Canonicalize

```nim
of itVariant:
  var armParts: seq[string]
  for arm in t.vArms:
    var fParts: seq[string]
    for i in 0 ..< arm.fieldNames.len:
      fParts.add arm.fieldNames[i] & "=" & canonicalize(arm.fieldTypes[i])
    armParts.add $arm.tagOrdinal & ":" & arm.tagName & ":[" & fParts.join(";") & "]"
  "Ty<Vr:" & t.vObjectName & ";disc=" & t.vDiscName & "=" &
    canonicalize(t.vDiscTy) & ";[" & armParts.join(",") & "]>"
```

Bumps `symexWalkerVersion` from `"1"` to `"2"` — old persisted
witnesses are invalidated by the walker change (they were already
defective for variants, so this is correct).

## Cycle plan

Each cycle is one RED → GREEN → REFACTOR. Cycles depend on the
previous unless marked "independent". Estimated effort per cycle in
parens. **No batching** — one test, one behavior, one cycle.

### 1. `itVariant` IR kind + canonicalize (≈1h)

- **RED**: a unit test in `tsymex_canonicalize.nim` constructs an
  `itVariant` IR by hand and checks the canonical string is
  distinct from `itTuple` for the same fields.
- **GREEN**: add `itVariant` kind + fields to `IRType`; add
  `canonicalize` arm; bump `symexWalkerVersion`.
- **Touches**: `smt/types.nim`, `smt/canonicalize.nim`,
  `tests/tsymex_canonicalize.nim`.
- **No-go signals**: existing canonicalize tests fail (means we
  changed itTuple by mistake).

### 2. typebridge emits itVariant for nnkRecCase (≈2h)

- **RED**: a Nim object with `nnkRecCase` runs through
  `classifyType` — assert the resulting IRType is `itVariant`
  with the right discName and arm count.
- **GREEN**: rewrite the `nnkRecCase` branch in
  `dsl_typebridge.nim` to populate `VariantArm` records instead
  of flattening. The flat-tuple path goes away.
- **Touches**: `smt/dsl_typebridge.nim`, `tests/tsymex_typebridge_variants.nim` (new).
- **No-go**: existing rectify-variants test fails. Expected (we're
  changing the IR shape); fix it later in cycle 11.

### 3. `svVariant` SymVal + param allocation (≈3h)

- **RED**: a symex SUT taking a variant param + reading
  `obj.kind` finds the right witness. Just discriminator access
  — no arm-field access yet.
- **GREEN**: add `svVariant` to the `SVKind` enum; add allocation
  in `allocateSym` for `itVariant`; teach the discriminator-only
  field path in `walk()`/`evalExpr()` to return `vDisc`.
- **Touches**: `smt/runtime.nim` (~10 svTuple dispatch sites
  pattern-match → add svVariant peer).
- **No-go**: any non-variant test fails (we broke a dispatch).

### 4. `iekField` on variant — in-arm binding via ite/fork (≈4h)

- **RED**: a SUT that reads a field-in-arm after `if obj.kind ==
  someArm` finds a witness with the right discriminator + field
  value.
- **GREEN**: in `evalExpr` for `iekField`, when receiver is
  `svVariant`, look up the field name across `vArms`; build the
  ite-chain `if vDisc == arm1 then vArmFields[arm1][ix] else if
  vDisc == arm2 then ...`; the path with `vDisc not in
  matching_arms` forks to an uncertain branch (will become
  field-defect target in cycle 5).
- **Touches**: `smt/runtime.nim`, `smt/dsl_parser.nim` (field
  name → arm lookup).
- **No-go**: rectify-variants test starts producing wrong
  witnesses.

### 5. `tFieldDefect` target (≈2h)

- **RED**: a SUT that *unconditionally* accesses an arm-specific
  field, called with the wrong discriminator — symex returns
  `sxSat` under `tFieldDefect()` with the matching witness.
- **GREEN**: add `stkFieldDefect` to `SymexTargetKind` + the
  constructor; extend the cycle-4 fork so the "not-in-any-arm"
  path is the satisfying branch under this target.
- **Touches**: `smt/types.nim`, `smt/runtime.nim`, `symex.nim`
  (target enum export).

### 6. Discriminator reassignment resets arm bindings (≈2h)

- **RED**: a SUT that does `obj.kind = newKind` and then reads a
  field in the new arm finds a coherent witness.
- **GREEN**: in the walker's assign path, when the target is
  `obj.kind` on an `svVariant`, replace `vArmFields[newTagOrdinal]`
  with fresh symbols and update `vDisc`.
- **Touches**: `smt/runtime.nim`.
- **Note**: uncommon in real code; correctness matters even if
  rarely exercised.

### 7. Witness emitter — case-dispatch construction (≈3h)

- **RED**: an existing rectify-variants test asserting the
  returned witness is the correct variant value (not
  `default(Object)`).
- **GREEN**: in `emitTyAndReader` (symex.nim:215), drop the
  `isLikelyVariant` heuristic and the `default(Object)` stub.
  For `itVariant`, generate a `case discReader of tag: ObjType(disc: tag, ...)`
  block per arm.
- **Touches**: `symex.nim`, `tests/tsymex_rectify_variants.nim`
  (gets stronger assertions).

### 8. `renderAsChoices` for variant witnesses (≈2h)

- **RED**: a unit test that `renderAsChoices(someVariantValue)`
  produces choices `[discriminator, …active-arm fields…]` in
  positional order.
- **GREEN**: extend the `when T is object` branch in
  `renderAsChoices` to detect variants at compile time (Nim's
  typetraits) and emit discriminator + arm-specific fields.
- **Touches**: `symex.nim`,
  `tests/tsymex_phase7_assertcovered.nim` (regression).

### 9. Abstraction — discriminator range refinement (≈2h)

- **RED**: a SUT where the abstraction layer's interval-bounded
  output for the discriminator is observable (e.g., a path
  condition like `obj.kind > 5` becomes UNSAT when no arm has
  ordinal > 5).
- **GREEN**: in `abstraction.nim`, for `svVariant` allocation,
  set the interval to `[min(vArms.tagOrdinal), max(vArms.tagOrdinal)]`.
  For full-enum coverage, leave as the enum's range.
- **Touches**: `smt/abstraction.nim`, `smt/runtime.nim`.

### 10. Nested variants (≈3h)

- **RED**: an object with a variant field whose arm contains
  another variant. SUT path requires the outer arm + an inner
  arm — symex finds the witness.
- **GREEN**: should "just work" if cycles 3-7 used proper
  recursion. If not, fix the bug.
- **Touches**: probably none — verify the recursion is right.

### 11. Migrate `tsymex_rectify_variants.nim` + add tFieldDefect tests (≈2h)

- Update the existing test to assert proper-witness construction
  (was asserting `default(Object)` was the stub).
- Add `tests/tsymex_phase11_fielddefect.nim` covering
  `tFieldDefect()` for nested + non-nested variants.
- Full symex suite green.

### 12. Bump `symexWalkerVersion` + docs (≈1h)

- `symexWalkerVersion = "2"` in `canonicalize.nim`.
- Update `README.md` fragment matrix: replace the variant-objects
  row with `itVariant` semantics + `tFieldDefect` target.
- Update `abstraction-internals.md`: add the discriminator-range
  refinement to the proof obligations.
- Update `determinism.md`: walker version bump entry.

### 13. SYMEX_PLAN.md status + memory (≈30m)

- Add Phase 11 row to SYMEX_PLAN.md status table with the new
  commit SHA.
- Update `proptest-symex-shipped.md` memory.

## Total estimate

~27 hours engineering, spread over 2-3 days of focused TDD.

## What this closes

- `proptest-symex-shipped.md` open follow-up: "Variant-object
  witness reconstruction (currently returns `default(Object)`)"
- Theoretical soundness gap: walker reasoning about variant
  field access outside the active arm

## What this does NOT close

- Object inheritance (`type Foo = object of Bar`) — separate
  feature, no overlap with variant soundness
- `case`-discriminator narrowing via flow-sensitive parser — Phase
  11 forks at every field access; a flow-sensitive parser could
  recognise `if obj.kind == X` as narrowing the field-access
  branches that follow. Real soundness gain is zero (the walker's
  fork produces the same witnesses); ergonomic gain is tighter
  paths in the frontier. Track as future work.
- `NilAccessDefect` / other defect target kinds — separate
  proposals; same scaffolding as `tFieldDefect`.

## Deferrals accumulated during the build

Items called out during a cycle and explicitly punted. Each is
guarded by either a macro-time error, a runtime error, or a
known soft-soundness note — none silently produces a wrong
witness. Triggers for picking each one back up are listed.

| # | Item | Cycle introduced | Guard | Trigger to address |
|---|---|---|---|---|
| 1 | Multiple `nnkRecCase` discriminators per object | 2 | parser macro-time `error()` | a real SUT with two recCases under one object surfaces |
| 2 | `else:` branches in `nnkRecCase` | 2 | parser macro-time `error()` | a real SUT uses `else` arm (uncommon — most code enumerates `of`) |
| 3 | Non-enum discriminator types | 2 | parser macro-time `error()` | Nim allows `case kind: int` but it's rare; revisit if seen |
| 4 | Wide-enum discriminators (uint16/32/64) | 3 | ✅ closed by `reachWide` test in `tsymex_phase11_walker.nim` (BigKind = 261-value enum classifies as uint16; symex finds high-ordinal witness) | — |
| 5 | Plain-fields shared allocation across arms | 4 | ✅ closed post-cycle-12: IR now carries `vPlainFieldNames`/`vPlainFieldTypes` separately; allocateSym allocates plain fields once; survives discriminator reassignment. Walker version `"2"` → `"3"`. `plainSurvivesReassign` test verifies. | — |
| 6 | Multi-arm-collision FieldDefect detection | 5 | ❌ **N/A** — Nim's variant syntax disallows duplicate field names across arms (`Error: attempt to redefine`). The walker's `isVariantField` ite-chain for multi-arm matches is structurally unreachable from user code. | — |
| 7 | Symbolic-RHS discriminator reassignment (`obj.kind = k` where `k` is a var) | 6 | parser macro-time `error()` | uncommon in idiomatic Nim; revisit on demand |
| 8 | Composite arm field types under reassignment (only primitives zero-init) | 6 | walker `ValueError` at runtime | a variant arm with a tuple/seq/Table field is reassigned via `obj.kind = X` |
| 9 | Multiple consecutive reassignments | 6 | ✅ closed by `threeReassigns` test (three back-to-back `x.kind = …` yield final disc = last) | — |
| 10 | Dead `lower(iekField on svVariant)` arm-field ite-chain (replaced by `isVariantField` A-normalisation) | 5 (refactor) | ✅ closed post-cycle-12: arm-field else branch in `lower(iekField on svVariant)` now `raise`s — clean fail-loud if any future caller bypasses the parser | — |
| 11 | Nested variants — full test coverage | 7 (defer to 10) | ✅ closed by cycle 10 (`deepCheck` test) | — |
| 12 | Discriminator Z3Int promotion (vs. log-only) | 9 | abstraction layer LOGS the interval; vDisc stays as svBV{8,16}. No soundness loss — disjunction in pc still constrains disc; just slower than svInt-with-range for arithmetic-over-disc patterns | a SUT that does heavy arithmetic on `ord(obj.kind)` shows perf issues, OR a consumer wants the abstraction layer to also tighten Z3 reasoning |

**Audit cadence**: revisit this list at the end of Phase 11 (cycle
13's memory + SYMEX_PLAN updates) and decide which to roll into a
"Phase 11.1 polish" cycle vs. file as standalone follow-up issues.

For deferrals that the build *surfaces but cannot solve here*
(future Phases), see § "What this does NOT close" above.

## Compatibility

Walker version bumps from `"1"` to `"2"`. Persisted witnesses from
Phase 10 cease to be visible — correct, because they were derived
under the old (unsound) variant model.

Source-level API: the only change is a new `tFieldDefect()` target
constructor. `symexFind` / `assertCoveredBy` / `saveSymexWitness` /
`loadSymexWitnesses` all keep their existing signatures.
