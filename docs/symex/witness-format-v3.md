# Symex witness format (v3 reference)

Status: authored at Phase 15 Cluster R cycle **R11b**; the **R12 heap-snapshot
witness format** is now SHIPPED. Reflects the witness format under **walker
version `"10"`** and **rendering version (`renderAsChoicesVersion`) `"3"`** (both
bumped at R12 — see [Rendering versions](#rendering-versions)). The per-param
heap-snapshot witness (`SymexResult.heapSnapshot`) landed at R12 (see
[the heap-snapshot witness](#the-heapsnapshot-witness-field-r12)); the in-tuple
ref/ptr rendering described below is its R1–R11 form and is unchanged.

This doc is the companion to [`determinism.md`](determinism.md): determinism
covers *when a witness is invalidated*; this doc covers *what a witness is and
how it renders*.

## TL;DR

A **witness** is the concrete counterexample the symbolic engine extracts from a
SAT Z3 model: a binding from each SUT param (and the result, for result-typed
targets) to a concrete Nim value that drives the SUT down the path to the
target. Internally it is a flat `RawWitness` — a bundle of `Table[string, V]`
maps keyed by a structural **path** string — that two cooperating halves
produce and consume:

- **Extraction** (`extractFromSymVal` / `extractLeaf`, `runtime.nim`): walks the
  param's `SymVal`, evaluates each leaf against the Z3 model, and writes
  concrete values into the flat tables under structural paths.
- **Rendering** (`emitTyAndReader`, `symex.nim`): a compile-time macro that
  emits, per param type, a Nim **type AST** plus a **reader expression** that
  pulls the leaves back out of the tables (by the SAME path strings) and
  reconstructs a real Nim value.

The path strings are the shared contract between the two halves. Extraction and
rendering must agree on every path, or a render-time `KeyError` results.

## The flat witness structure (`RawWitness`)

`RawWitness` (`runtime.nim`) is a record of per-kind tables, each keyed by a
structural path string:

| Table | Value type | Holds |
|---|---|---|
| `intVals`    | `int64`            | signed int leaves (`int`/`int8`/`int16`/`int32`/`int64`) — read via `readInt`/`readInt8`/… |
| `uintVals`   | `uint64`           | unsigned int leaves (`uint`/`uint8`/…) — read via `readUInt`/… |
| `boolVals`   | `bool`             | bool leaves |
| `float64Vals`| `float64`          | bit-exact `float`/`float64` leaves (F7) — read via `readFloat` |
| `float32Vals`| `float32`          | bit-exact `float32` leaves (F7) — read via `readFloat32` |
| `strVals`    | `string`           | string leaves (Cluster S, byte-faithful model) — read via `readString` |
| `seqLens`    | `int`              | per-`seq`/per-`array` element count at a path |
| `tabKeys`    | `seq[string]`      | per-`Table` chosen key list |
| `setMembers` | `seq[int64]`       | per-`HashSet[int]` chosen members |
| `paramOrder` | `seq[string]`      | the top-level param names, in declaration order |

The maps are deliberately **flat**: structure is encoded entirely in the path
key, never in nesting. A param named `p` of a nested type produces *many* leaf
entries under paths derived from `p` (see [paths](#the-path-grammar)).

### The path grammar

A path is built by the extractor/renderer as it descends a type, starting from
the param name and appending one suffix per structural step:

| Construct | Path suffix | Example |
|---|---|---|
| top-level param | the param name | `p` |
| tuple/object field (named) | `.<fieldName>` | `p.x` |
| tuple element (positional) | `.<index>` | `p.0` |
| array / seq element | `.<index>` | `xs.3` |
| variant discriminator | `.<discName>` | `v.kind` |
| variant plain (shared) field | `.<fieldName>` | `v.id` |
| variant arm-specific field | `.@<tagOrdinal>.<fieldName>` | `v.@1.payload` |
| multi-variant axis disc | `.<discName>` | `v.axis` |
| multi-variant arm field | `.<discName>.@<tagOrdinal>.<fieldName>` | `v.axis.@2.f` |

The extractor (`extractFromSymVal`) and the renderer (`emitTyAndReader`) both
construct these suffixes identically — that mutual agreement is the witness
format's core invariant.

## Per-kind witness rendering

Each entry below pairs **what the extractor writes** with **what the renderer
reads**, grounded in the real `extractLeaf`/`extractFromSymVal`/`emitTyAndReader`
arms.

### Primitive leaves (int, uint, bool, float64, float32)

- **Extract** (`extractLeaf`): evaluate the leaf SymVal against the model and
  write into the matching table. Signed bit-vectors (`svBV8/16/32/64`, `svInt`)
  go to `intVals`; unsigned to `uintVals`; a promoted variant discriminator is
  mirrored into BOTH `intVals` and `uintVals` (A6) so whichever reader the
  emitter picks resolves it. Floats are **bit-exact** (F7): NaN is detected via
  the `isNaN` FP predicate and emitted as Nim's single canonical NaN (ADR-0005,
  no payload distinctions); all other values (±Inf, ±0, normals, subnormals)
  round-trip losslessly through `evalFloat64Opt`/`evalFloat32Opt` with explicit
  `modelCompletion = true`.
- **Render** (`emitTyAndReader` `itBool`/`itInt`/`itFloat32`/`itFloat64`): emits
  `readInt(witId, path)` / `readBool` / `readFloat` / … — a direct table read.

### String witnesses

- **Extract**: byte-faithful (Cluster S — chars `≤ 0xFF` map to Nim bytes, NOT
  the RFC's codepoint model). Written to `strVals` at the path.
- **Render** (`itString`): `readString(witId, path)`.

### seq / array / tuple / object witnesses

- **array** (`itArray`): fixed `size`; each element renders at `path.<i>` for
  `i in 0 ..< size`. The element type's reader is emitted per index.
- **seq** (`itSeq`): the extractor writes the model length into `seqLens[path]`
  (clamped to `[0, 64]`) and extracts each element under `path.<i>`. The
  renderer reads the length via `readSeqLen` and rebuilds the seq. Specialised
  readers exist for `seq[int]` (`readSeqInt`), `seq[float]`/`seq[float32]`
  (F9b), and `seq[ref T]` (R3 — see [heap-snapshot](#refptr-heap-snapshot-witness)).
- **tuple / object** (`itTuple`): each field renders at `path.<fieldName>`
  (named) or `path.<index>` (positional). A nominal object reconstructs via
  `nnkObjConstr`; an anonymous tuple via `nnkTupleConstr`/`nnkTupleTy`.

### Table / HashSet witnesses

- **Table[string, int]** (`itTable`): chosen keys recorded in `tabKeys[path]`,
  values under per-key sub-paths; rebuilt via `readTableStrInt`.
- **HashSet[int]** (`itSet`): chosen members in `setMembers[path]`; rebuilt via
  `readSetInt`. Both deterministically sorted (renderAsChoices `"2"`) so the
  cache key is stable across Nim's undefined hash-iteration order.

### Variant / multi-variant witnesses

- **Extract** (`svVariant`/`svMultiVariant`): the discriminator value goes under
  `path.<discName>`; plain (shared) fields under direct sub-paths; arm-specific
  fields under `path.@<tagOrdinal>.<fieldName>`. Multi-variant prefixes the arm
  path with the axis disc name.
- **Render** (`itVariant`/`itMultiVariant`): a `case` on the discriminator
  reader rebuilds the object on the arm Z3 picked, reading plain fields at their
  shared path in every branch (matching Nim's shared-field memory layout) and
  arm fields at the `@tag` sub-paths.

### Distinct witnesses

- **Extract** (`svDistinct`, G4): ejects the BASE SymVal (`== eject_T(const)`)
  and extracts it at the SAME path.
- **Render** (`itDistinct`): reads the base value at `path`, then wraps it in the
  distinct converter `DistinctName(baseValue)`.

### Unsupported-as-witness kinds (classified, not silent)

Per **Invariant 3** (no silent fallbacks), a value that cannot be reconstructed
as a concrete witness is *classified*, not dropped:

- **closure** as a top-level SUT result (`svClosure`) → `ceNotImplemented`
  (sevError) in the finding's `errors`; a closure as a param TYPE renders a
  `nil` proc placeholder + a compile-time `{.warning.}`.
- **opaque exception ref** (`svUninterpRef`, E8) → `eeUninterpRefExtraction`
  (sevHint); no leaf.

## ref/ptr heap-snapshot witness

Cluster R (ADR-0010) models `ref T`/`ptr T` through a **logical heap**: a
per-pointee-type uninterpreted address sort `Ref_<typeId>` and a per-path
`Z3Array[Ref_T, T]`. A `ref`/`ptr` param is a `svRef`/`svPtr` carrying that
abstract address const, not a numeric pointer. The witness therefore cannot be
a raw address; it is a **heap cell** holding the value the param's deref took in
the model.

### How a `ref T` param renders (the `new(T); c[] = …` form)

This is the R1/R6 rendering, the concrete answer to "what does a ref witness
look like":

- **Extract** (`extractFromSymVal` `svRef`/`svPtr`): if the param was
  dereferenced (`p[]`), the heap-select value `select(heap, p)` — recorded under
  the param name in the `currentHeapDerefVals` hook at deref time — is extracted
  at the SAME path, exactly like a plain value leaf. If the param was NEVER
  dereferenced, the pointee renders as the type's **default** (zero/`false`/…)
  so the leaf exists and the reader never KeyErrors — sound, because an
  unobserved pointee can hold any value.
- **Render** (`emitTyAndReader` `itRef`): emits a **heap cell** that
  reconstructs `p[] == <model value>`:

  ```nim
  (var c = new(T); c[] = <pointeeReader>; c)
  ```

  i.e. `new`-allocate a `ref T`, store the extracted pointee value into it, and
  yield the ref. Replaying the SUT with this witness drives the same deref value.

### `ref object` field-accessed params (R6)

A `ref object` accessed only by field (`p.field`, the field-split heaps) records
no whole-object deref value. The extractor materialises a **default object
SymVal** and extracts its leaves PER FIELD (so the `itTuple` reader finds every
`path.<field>` leaf), and the param renders as a `new(T)`-cell whose object has
those default field values. The aliasing/observability the SUT exercised is a
*solver* property (same `Ref_T` index → same value); the rendered witness is a
sound replayable representative, not a full alias-group snapshot (that is R12).

### `ptr T` params (R8)

A `ptr T` cannot be safely heap-reconstructed without an owning cell (a raw
`ptr` to a GC'd `new` cell would dangle). The R8 rendering emits a `nil` ptr
placeholder + a compile-time `{.warning.}`, and the finding carries the
**`hePtrFamily`** hint (sevHint, non-halting) so a consumer can distinguish an
unmanaged-ptr witness from a managed-ref one. The deref VALUE itself is decided
in-solver (the `ptr` deref routes through the same heap as `ref`); only the
rendered witness value is deferred to R12.

### `seq[ref T]` (R3)

The element pointee values are observed only through the heap, so no per-element
leaf is extracted. The renderer builds a `seq[ref T]` of the model length, each
element a fresh `new(T)` default cell — sound (the pointees were constrained
in-solver, never individually rendered) and replayable (correct length). The
full per-element heap snapshot is R12.

### Recursive `ref object` fields (R9)

A self-referential field (`next: Node` of a linked list) classifies to a finite
named placeholder and renders as `nil` of its named `ref Obj` type — sound and
replayable; the full chain rendering is R12.

### Nil and the nil-access defect (R5)

`nil` is the per-sort distinguished const `nil_<typeId>`. `p == nil` is a ground
`Ref_T` equality. A deref of a possibly-nil ref forks: the nil sub-path is the
**NilAccessDefect** finding, surfaced under the `tNilAccess()` target with a
witness asserting `p == nil`. (A freshly `new`-allocated ref is provably non-nil
— the nil fork is short-circuited, never producing a spurious nil witness.)

## Rendering versions

Two maintainer-bumped version constants (`canonicalize.nim`) gate witness
determinism, independently of each other:

- **`symexWalkerVersion` = `"10"`** — how the WALKER reasons about the SUT
  (covers heap semantics). Cluster R bumped it `"9"→"10"` at **R12** (the FINAL
  Phase 15 bump — the full R1–R11b heap machinery is live).
- **`renderAsChoicesVersion` = `"3"`** — how a SAT witness is SERIALISED into the
  choice IR (`renderAsChoices`), distinct from how the walker reasons. The
  two-version split lets a witness-encoding bump avoid invalidating witnesses
  whose encoding didn't change. The heap-snapshot witness FORMAT extension at
  R12 bumped this **`"2"→"3"`**. (Version history table lives in
  [`determinism.md`](determinism.md#renderaschoicesversion-history).)

Both constants are single-sourced in `canonicalize.nim` (Invariant 6 / M12 — no
duplicate in `runtime.nim`).

## Determinism guarantees

The witness obeys the determinism contract in [`determinism.md`](determinism.md):

- **Reproducibility.** The same SUT + target + settings under the same
  `symexWalkerVersion`/`renderAsChoicesVersion` + Z3 version yields the same
  witness (Z3 `random_seed = 0`, fixed `rlimit`). A witness persisted under one
  version is correctly invalidated by a bump of either version.
- **Stable ordering.** Collection witnesses (`Table` keys, `HashSet` members)
  are deterministically sorted at render time, so the cache key for the same
  logical witness is stable across Nim's undefined hash-iteration order.
- **No silent gaps (Invariant 3).** Every leaf either resolves to a concrete
  value or its un-renderability is classified into the finding's `errors`
  (`feExtractionFailed`, `ceNotImplemented`, `eeUninterpRefExtraction`,
  `hePtrFamily`, …) — a witness is never silently truncated.
- **Heap soundness.** A ref/ptr witness is a sound *representative*: it
  reconstructs the deref VALUES the model committed to; properties decided purely
  in-solver (alias groups, distinctness, nil structure) are not yet rendered into
  the witness value (R12) but never produce an unsound replayable witness — a
  never-observed pointee renders as a default, never a wrong concrete value.

## The `heapSnapshot` witness field (R12)

R12 (the final R cycle) bumped `symexWalkerVersion` `"9"→"10"` and
`renderAsChoicesVersion` `"2"→"3"`, and added the **heap-snapshot witness** as a
distinct, structured field on the result — `SymexResult.heapSnapshot:
seq[HeapSnapshotEntry]` (`smt/types.nim`). It records, per ref/ptr SUT param,
what the logical heap committed to in the SAT model, ALONGSIDE the existing
in-tuple `ref T` rendering (the `(var c = new(T); c[] = …; c)` cell above — that
is unchanged and still drives replay).

### `HeapSnapshotEntry` schema

| Field | Type | Meaning |
|---|---|---|
| `name`     | `string`           | the param name (the `seq` preserves declaration order) |
| `sort`     | `string`           | the `Ref_<typeId>` address-sort name |
| `value`    | `string`           | `"nil"`, or the model rendering of the abstract address |
| `pointsTo` | `Option[string]`   | the modelled pointee value rendering; `none` for a nil ref or a non-primary alias member |
| `aliasRef` | `Option[string]`   | `some(primary)` when this param aliases an earlier param's address; `none` otherwise |

### How it is built (`buildHeapSnapshot`, `runtime.nim`)

After `extractWitness` populates every flat leaf, `buildHeapSnapshot` walks the
ref/ptr params (in declaration order) against the live Z3 model:

- **Address & nil.** Each param's abstract address (`refAst`/`ptrAst`) is
  evaluated under the model (`$m.eval(addr)`); that rendering is both the
  `value` and the **alias-group key**. Nil is detected by comparing it against
  the evaluated `nil_<typeId>` const → `value == "nil"`, `pointsTo == none`.
- **Alias groups.** Refs that bound to the SAME address render as the SAME
  cell. The **lexicographically-first** param name in an address group is the
  PRIMARY: it carries `pointsTo` (the pointee value, read back from the
  populated witness leaf via `pointeeRendering` — a primitive resolves to its
  stringified value; a composite `ref object` renders the `<object>` marker).
  Every other param in the group carries `aliasRef = <primary>` and no
  `pointsTo`.
- **Backward compat.** A SUT with NO ref/ptr params produces an EMPTY
  `heapSnapshot` (the key is ABSENT, not null). Every prior cluster's witness is
  unchanged — the field is purely additive.

The snapshot is threaded `RawWitness.heapSnapshot` → `RawResult.witness` →
(`readHeapSnapshot*`, since `RawWitness` is an unexported type) → the `symexFind`
macro's `SymexResult(... heapSnapshot: …)` on both the `sxSat` and `sxRaised`
branches.

### Still represented in-solver only (sound, not yet rendered into the snapshot)

The snapshot records the per-param address/pointee/alias facts the model
committed to. A few heap properties remain decided purely in-solver and are not
expanded into the snapshot value (always sound — never an unsound replayable
witness): per-element `seq[ref T]` pointee values (the seq renders default
cells of the correct length), recursive-ref chain expansion beyond the
heap-depth budget (a recursive field renders `nil`), and the `ptr T` in-tuple
witness VALUE (a `nil` placeholder + `hePtrFamily` hint — the `ptr` param still
gets a heap-snapshot ENTRY with its modelled `pointsTo`).
