## RFC-chapulin-hardening CR-2c — witness-reader codegen `error()` →
## whole-run forced-`sxUnknown` (Cluster 2 — Crash-totality).
##
## `emitTyAndReader` (`src/nelli/symex.nim`) is the POST-SOLVE
## witness-reader codegen macro — a THIRD, structurally-distinct
## macro-`error()` surface, separate from CR-2a (parser catch-all,
## `dsl_parser.nim`) and CR-2b (param-type classify catch-all,
## `dsl_typebridge.nim`). It hard-`error()`ed at MACRO-EXPANSION time on
## unmodeled witness shapes, aborting compilation of the whole test file:
##   * `seq[...]` with a non-scalar/non-ref element type ("seq witness
##     reader for ... not yet implemented").
##   * `Table[...]` other than `Table[string, int]`.
##   * `HashSet[...]` other than `HashSet[int]`.
##
## Mechanism (control-loop-resolved Option A): reuse CR-2b's live degrade
## pipeline rather than mint parallel machinery. `parseProc*`'s TOP-LEVEL
## SUT parameter-classification loop (`dsl_parser.nim` — the single choke
## point every witness-rendering entry macro, e.g. `symexFind`, shares)
## now runs each parameter's `classifyType` result through
## `demoteUnrenderableWitnessTy`, applying a SHARED renderability predicate
## (`isRenderableSeqElemTy`/`isRenderableTableTy`/`isRenderableSetElemTy`,
## `smt/types.nim` — the single source of truth also consulted by
## `emitTyAndReader`'s `itSeq`/`itTable`/`itSet` arms) to the
## element/key/value `IRType`. Deliberately NOT inside `classifyType`
## itself: that classifier is also used for purely-internal (non-witness)
## types (e.g. an in-body helper's `seq[byte]` return type), and gating it
## there was found to over-trigger — it broke unrelated internal seq/
## Table/HashSet usages that never reach a witness reader at all. An
## unrenderable TOP-LEVEL parameter shape classifies to an
## `itUninterp("__unsupported_witness:" & s)` placeholder INSTEAD of
## `itSeq`/`itTable`/`itSet` — so the run degrades at PARAMETER-ALLOCATION
## time, before the walker ever solves for a witness, and the three
## `emitTyAndReader` `error()` sites become unreachable for these
## TOP-LEVEL shapes (never reached: allocateSym has already forced
## `sxUnknown`).
##
## `allocateSym` (`smt/runtime.nim`) gains a matching `__unsupported_witness:`
## prefix branch raising CR-1c's generic `SymexClassifiedDegradeError`
## carrier with the NEW `feUnsupportedWitnessType` kind — distinct from
## CR-2b's `feUnsupportedParamType` (a different macro/site class per §0).
## No new exception type.
##
## Walker version: v45 -> v46 (compile-abort -> sxUnknown is a verdict
## change; see the pin-test comment for the "otherwise none" note this
## supersedes).

import std/[unittest, strutils, tables, sets]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# Object type used to build an unrenderable seq element shape.
# ---------------------------------------------------------------------------

type
  Widget = object
    a: int
    b: int

  ShapeKind = enum skWidgets, skCount

  # A variant object whose skWidgets arm carries an UNRENDERABLE field
  # (`seq[Widget]`). emitTyAndReader's itVariant arm recurses into every arm's
  # field types, so this compile-aborts today at the itSeq error() site.
  ShapeBad = object
    case kind: ShapeKind
    of skWidgets:
      widgets: seq[Widget]
    of skCount:
      count: int

  # Same shape but with a RENDERABLE arm field (`seq[int]`) — the recursion
  # must NOT over-demote this; it must stay resolvable.
  ShapeOk = object
    case kind: ShapeKind
    of skWidgets:
      nums: seq[int]
    of skCount:
      count: int

# ---------------------------------------------------------------------------
# SUTs — unsupported witness SIGNATURE shapes (RED repros / strong-form)
# ---------------------------------------------------------------------------

# SUT 1: seq[Widget] — a non-scalar/non-ref seq element hits emitTyAndReader's
# itSeq catch-all (`symex.nim`, "seq witness reader for ... not yet
# implemented"). Params are allocated before the body is walked, so this
# degrades the WHOLE RUN to sxUnknown regardless of the (trivially reachable)
# body target.
proc sutSeqObject(ws: seq[Widget], y: int) =
  if y == 42:
    symexTarget("seq_object_target")

# SUT 2: seq[seq[int]] — a nested seq is also not in the scalar/ref element
# set (elemTy.kind == itSeq is not itInt/itFloat32/itFloat64/itRef).
proc sutSeqSeqInt(ws: seq[seq[int]], y: int) =
  if y == 42:
    symexTarget("seq_seq_int_target")

# SUT 3: Table[string, string] — value type is not itInt(64, signed), hits
# emitTyAndReader's itTable catch-all ("only Table[string, int] supported").
proc sutTableStrStr(t: Table[string, string], y: int) =
  if y == 42:
    symexTarget("table_strstr_target")

# SUT 4: Table[int, int] — key type is not itString.
proc sutTableIntInt(t: Table[int, int], y: int) =
  if y == 42:
    symexTarget("table_intint_target")

# SUT 5: HashSet[string] — element type is not itInt(64, signed), hits
# emitTyAndReader's itSet catch-all ("only HashSet[int] supported").
proc sutHashSetString(s: HashSet[string], y: int) =
  if y == 42:
    symexTarget("hashset_string_target")

# ---------------------------------------------------------------------------
# SUTs — NESTED unsupported witness shapes (nested-aggregate completeness gap).
# The unrenderable seq/Table/HashSet is NESTED inside a tuple / array / variant,
# NOT a bare top-level param. emitTyAndReader recurses into these aggregates at
# macro-expansion (tuple fields, array elems, variant arm fields), so each
# compile-aborts TODAY (before the recursive-predicate fix) even though the
# top-level param kind is itTuple/itArray/itVariant, not itSeq/itTable/itSet.
# ---------------------------------------------------------------------------

# SUT N1: tuple nesting an unrenderable seq[Widget] field.
proc sutNestedTupleSeqObject(x: tuple[a: seq[Widget], n: int], y: int) =
  if y == 42:
    symexTarget("nested_tuple_seqobj_target")

# SUT N2: array of an unrenderable HashSet[string].
proc sutNestedArrayHashSetString(a: array[2, HashSet[string]], y: int) =
  if y == 42:
    symexTarget("nested_array_hashset_target")

# SUT N3: variant object whose one arm carries an unrenderable seq[Widget].
proc sutNestedVariantArm(s: ShapeBad, y: int) =
  if y == 42:
    symexTarget("nested_variant_arm_target")

# SUT N4: seq of a tuple that itself nests an unrenderable seq[Widget]
# (double nesting — proves the recursion goes all the way down).
proc sutNestedSeqTupleSeqObject(xs: seq[tuple[w: seq[Widget], n: int]], y: int) =
  if y == 42:
    symexTarget("nested_seq_tuple_target")

# ---------------------------------------------------------------------------
# SUTs — SUPPORTED witness shapes (regression guard: unaffected)
# ---------------------------------------------------------------------------

proc sutPlainSeqInt(xs: seq[int], y: int) =
  if xs.len > 0 and xs[0] == 7 and y == 7:
    symexTarget("plain_seq_int")

proc sutPlainTable(t: Table[string, int], y: int) =
  if y == 9:
    symexTarget("plain_table")

proc sutPlainHashSet(s: HashSet[int], y: int) =
  if y == 11:
    symexTarget("plain_hashset")

proc sutPlainScalar(x: int, b: bool) =
  if x == 13 and b:
    symexTarget("plain_scalar")

# RENDERABLE-NESTED regression guards: the recursion must NOT over-demote a
# nested aggregate whose leaves are all renderable — these must STAY resolvable
# (sxSat), proving the fix does not degrade previously-working nested shapes.

proc sutRenderNestedTupleSeqInt(x: tuple[a: seq[int], n: int], y: int) =
  if y == 21:
    symexTarget("render_nested_tuple_seqint")

proc sutRenderNestedArrayHashSetInt(a: array[2, HashSet[int]], y: int) =
  if y == 23:
    symexTarget("render_nested_array_hashset_int")

proc sutRenderNestedVariantArm(s: ShapeOk, y: int) =
  if y == 25:
    symexTarget("render_nested_variant_arm")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening CR-2c — witness-reader catch-all degrade":

  test "CR-2c-1: seq[Widget] compiles and degrades to whole-run sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutSeqObject, tLabel("seq_object_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2c-2: seq[seq[int]] compiles and degrades to whole-run sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutSeqSeqInt, tLabel("seq_seq_int_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2c-3: Table[string, string] compiles and degrades to whole-run sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutTableStrStr, tLabel("table_strstr_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2c-4: Table[int, int] compiles and degrades to whole-run sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutTableIntInt, tLabel("table_intint_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2c-5: HashSet[string] compiles and degrades to whole-run sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutHashSetString, tLabel("hashset_string_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex RFC-chapulin-hardening CR-2c — NESTED-aggregate degrade (completeness gap)":

  test "CR-2c-N1: tuple[a: seq[Widget], n: int] compiles and degrades to sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutNestedTupleSeqObject, tLabel("nested_tuple_seqobj_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2c-N2: array[2, HashSet[string]] compiles and degrades to sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutNestedArrayHashSetString, tLabel("nested_array_hashset_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2c-N3: MIGRATED (Round-6 Bug #2, walker v85) — an untouched variant-arm seq[Widget] field no longer whole-run-poisons; proves sxSat":
    ## Pre-v85: `ShapeBad`'s `widgets: seq[Widget]` arm field (elemTy itTuple,
    ## unbacked) hit `classifyObjectRecordFields`'s EAGER whole-type
    ## classification — `allocateSym` raised unconditionally the moment `s:
    ## ShapeBad` was merely ALLOCATED, regardless of `sutNestedVariantArm`
    ## never touching `widgets` at all — exactly Round-6 Bug #2 (see
    ## `docs/rfc/0001-chapulin-hardening.handoff.md`'s "FORK RESOLUTION" bullet
    ## and `tests/tsymex_r6_bug2_scopeddecline.nim`). The per-field SCOPED
    ## DECLINE fix classifies `widgets` to a kind-marked placeholder instead
    ## (`isUnsupportedFieldPlaceholder`, `types.nim`) — `allocateSym`
    ## allocates it fresh-opaque rather than raising, so the untouched field
    ## no longer poisons this proc's verdict. `y == 42` was ALWAYS trivially
    ## reachable independent of `widgets`; it now resolves to its REAL
    ## verdict (this is the SAME "crash/decline -> real verdict" migration
    ## class A1's "MIGRATED" pin and A3's symbolic-disc construction pin
    ## already establish elsewhere in this RFC). A DIRECT read of `widgets`
    ## still degrades classified — see `tsymex_r6_bug2_scopeddecline.nim`'s
    ## HONEST DEGRADE pins — this test's SUT simply never performs one.
    let r = symexFind(sutNestedVariantArm, tLabel("nested_variant_arm_target"))
    check r.status == sxSat
    check r.witness[1] == 42

  test "CR-2c-N4: seq[tuple[w: seq[Widget], n: int]] (double nesting) degrades to sxUnknown + feUnsupportedWitnessType":
    let r = symexFind(sutNestedSeqTupleSeqObject, tLabel("nested_seq_tuple_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex RFC-chapulin-hardening CR-2c — regression guard (supported shapes unaffected)":

  test "CR-2c-6: seq[int] still resolves sxSat with exact witness":
    let r = symexFind(sutPlainSeqInt, tLabel("plain_seq_int"))
    check r.status == sxSat
    check r.witness[0] == @[7]
    check r.witness[1] == 7

  test "CR-2c-7: Table[string, int] still resolves sxSat":
    let r = symexFind(sutPlainTable, tLabel("plain_table"))
    check r.status == sxSat
    check r.witness[1] == 9

  test "CR-2c-8: HashSet[int] still resolves sxSat":
    let r = symexFind(sutPlainHashSet, tLabel("plain_hashset"))
    check r.status == sxSat
    check r.witness[1] == 11

  test "CR-2c-9: plain scalars still resolve sxSat":
    let r = symexFind(sutPlainScalar, tLabel("plain_scalar"))
    check r.status == sxSat
    check r.witness[0] == 13
    check r.witness[1] == true

  test "CR-2c-10: RENDERABLE nested tuple[a: seq[int], n: int] NOT over-demoted — stays sxSat":
    ## Proves the recursion demotes ONLY when a leaf is genuinely unrenderable:
    ## every leaf here (seq[int], int) is renderable, so the whole param must
    ## keep its real itTuple classification and resolve normally.
    let r = symexFind(sutRenderNestedTupleSeqInt, tLabel("render_nested_tuple_seqint"))
    check r.status == sxSat
    check r.status != sxUnknown
    for e in r.errors:
      check e.kind != feUnsupportedWitnessType

  test "CR-2c-11: RENDERABLE nested array[2, HashSet[int]] NOT over-demoted — stays sxSat":
    let r = symexFind(sutRenderNestedArrayHashSetInt, tLabel("render_nested_array_hashset_int"))
    check r.status == sxSat
    check r.status != sxUnknown
    for e in r.errors:
      check e.kind != feUnsupportedWitnessType

  test "CR-2c-12: RENDERABLE nested variant (seq[int] arm) NOT over-demoted — stays sxSat":
    let r = symexFind(sutRenderNestedVariantArm, tLabel("render_nested_variant_arm"))
    check r.status == sxSat
    check r.status != sxUnknown
    for e in r.errors:
      check e.kind != feUnsupportedWitnessType

suite "symex RFC-chapulin-hardening CR-2c — walker version pin":

  test "walker version floor >= 46 (CR-2c introduced at 46)":
    ## CR-2c converts emitTyAndReader's three seq/Table/HashSet witness-shape
    ## compile-aborts to a classified whole-run sxUnknown degrade (reusing
    ## CR-2b's classify-time pipeline); bump 45->46 rotates any stale cache
    ## entries (there are none for the compile-abort case, but SUTs newly
    ## reachable through this path must not collide with any unrelated
    ## pre-46 cache key). The RFC's "otherwise none" note for CR-2c is
    ## superseded by the CR-2a/CR-2b precedent: converting a macro-error()
    ## compile-abort into a classified sxUnknown is always a verdict-surface
    ## change, and bumping is always cache-safe (worst case rotates cache;
    ## never wrong).
    check parseInt(symexWalkerVersion) >= 46
