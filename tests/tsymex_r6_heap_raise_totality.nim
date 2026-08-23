## N46-followup-2 (round-6 re-review, heap-raise totality slice) — closes the
## 13-site `runtime_heap.nim` LEDGERED-LIVE backlog N46 (v111,
## `tsymex_r6_n36_raise_class_audit.nim`) opened: a first-ever file-coverage
## widen of the raw-raise-in-lower CLASS audit found 13 unmarked
## `raise (ref Symex*)` sites in the heap-deref/ref-variant-field machinery,
## deliberately left unconverted pending dedicated scoping.
##
## Adjudication (see `symexWalkerVersion`'s own doc comment, `canonicalize.
## nim`, for the full per-site writeup):
##   - 7 CONVERTED to the in-band degrade idiom (`allocDegrade` +
##     `forkPathTainted`/a fresh `allocateSym` placeholder, matching the
##     established `seqElemAt`/`isUnsupported` idioms):
##       * `liftHeapValue`'s unsupported-pointee-kind `else` (a `string`/
##         `Table`/`HashSet`/`distinct` heap-select VALUE — the most ordinary
##         shape possible: any `ref object` field of one of these types).
##       * the `itMultiVariant` field-deref / field-write declines (an
##         INLINE `ref`/`ptr`-to-multi-axis-variant PARAMETER — the
##         classifier wraps such a pointee in `itRef`/`itPtr` UNCHANGED;
##         only the NAMED-alias and field-typed-ref classification paths
##         exempt variant pointees from heap routing, ADR-0022 sub-decision
##         #1 in `dsl_typebridge.nim` — confirmed by direct trace and by
##         `tests/tsymex_a2_refvariant_fields.nim`'s own existing, passing
##         SUTs, which all use exactly this inline-ref-param shape).
##       * four `refSV.kind`-not-`svRef`/`svPtr` mismatches (general
##         deref/deref-write + arm-field deref/deref-write) — converted by
##         the SAME mirrored idiom as their siblings above for consistency
##         and defense-in-depth, though this slice did not construct an
##         independent repro for these four specifically (the plausible
##         trigger — an `iteSV` merge landing a degraded/opaque SymVal kind
##         on a nominally ref-typed variable — routes through machinery this
##         slice did not have to modify further to make sound).
##   - 6 RECLASSIFIED `verified-unreachable` (left as raw raises, now marked
##     `# [raise-audited: verified-unreachable: ...]` per this audit's own
##     marker convention): the two "field declared by no arm of the variant"
##     sites (field names are parser-resolved against the SUT's own real
##     type before the scan runs — a Nim SUT with an undeclared field
##     reference does not compile), the two "else-only variant, no non-else
##     arm to negate against" sites (Nim's `case` syntax requires >= 1 `of`
##     branch before an optional `else`), and the two disc-kind `else` arms
##     in `discEq`/`discEqW` (`VariantAxis.vDiscTy` is always `itInt` by
##     construction and `liftHeapValue`'s `itInt` arm is width-exhaustive, so
##     a disc value read through `heapSelect` can only ever be
##     `svBV8`/`16`/`32`/`64`).
##
## THE CORE PROOF (RED/GREEN, task item 2): a raw raise unwinding through
## `walkHeapArm`/`walk`/`walkBlock` reaches `runSymexImpl`'s TOP-LEVEL
## catch-all — a WHOLE-RUN abort. That catch classifies the error
## correctly-LOOKING (a specific `SymexErrorKind`, never a crash) but
## aborts EVERY path in flight, not just the one that hit the hazard. When
## the hazard is reached on one branch BEFORE an unrelated, hazard-free
## SIBLING branch's target is ever explored, the sibling's true `sxSat`
## witness is never found at all — the walk reports `sxUnknown` for a
## program whose correct, honest verdict is `sxSat` (the N31/ADR-0023 SND-3
## silent-loss class). `heapMaskingOrdered` below is exactly this shape,
## stash-verified: pre-fix `sxUnknown` (wrong), post-fix `sxSat` (correct).
##
## Walker: v112 -> v113 (see `symexWalkerVersion`'s own doc comment for the
## full writeup). CR-2 `==` pin 112 -> 113
## (`tests/tsymex_phase15_CR2_cachekey.nim`).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Shapes
# =============================================================================

type
  HeapStrNode = ref object
    s: string
    n: int

  HKindA = enum hkaX, hkaY
  HKindB = enum hkbP, hkbQ

  HeapMultiVariantObj = object
    case kindA: HKindA
    of hkaX: a1: int
    of hkaY: a2: int
    case kindB: HKindB
    of hkbP: b1: int
    of hkbQ: b2: int

# =============================================================================
# Site: `liftHeapValue`'s unsupported-pointee-kind `else` (converted).
# Triggered by an ordinary `string` field read through a heap-deref'd ref.
# =============================================================================

proc heapStrFieldRead(p: HeapStrNode) =
  if p != nil:
    if p.s == "hello":
      symexTarget("heap_str_field_read")

proc heapGoodIntFieldRead(p: HeapStrNode) =
  ## Sound-path companion (no over-taint): the `n: int` field is fully
  ## backed -- verdict must be an ordinary sxSat, unaffected by this slice.
  if p != nil:
    if p.n == 777:
      symexTarget("heap_good_int_read_sat")

proc heapGoodIntFieldUnsat(p: HeapStrNode) =
  ## UNSAT companion for the same good field.
  if p != nil:
    if p.n == 1 and p.n == 2:
      symexTarget("heap_good_int_read_unsat")

## THE CORE PROOF: hazard branch (string-field deref) evaluated FIRST in
## program order; the winning target sits on the OTHER, hazard-free branch.
## Correct verdict is unambiguously sxSat (the `else` branch is an
## unconditional, unguarded target hit). Pre-fix: the raw raise on the
## `choose` branch unwound the WHOLE walk before the `else` branch's target
## was ever explored -- sxUnknown (wrong). Post-fix: the hazard branch
## degrades in-band and contributes no survivor, but does not touch the
## sibling branch at all -- sxSat (correct).
proc heapMaskingOrdered(p: HeapStrNode, choose: bool) =
  if choose:
    if p != nil:
      discard p.s
  else:
    symexTarget("heap_masking_ordered")

suite "N46-followup-2 -- liftHeapValue unsupported-pointee-kind (converted)":

  test "sanity: string field read alone is honest sxUnknown carrying heUnresolvedRef, never a crash":
    let r = symexFind(heapStrFieldRead, tLabel("heap_str_field_read"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == heUnresolvedRef: saw = true
    check saw
    check r.status != sxSat   ## a tainted path must never mint a bogus sat

  test "sound-path companion: an ordinary backed int field is sxSat (no over-taint)":
    let r = symexFind(heapGoodIntFieldRead, tLabel("heap_good_int_read_sat"))
    check r.status == sxSat
    check r.errors.len == 0

  test "sound-path companion: UNSAT for the same good field (no over-taint)":
    let r = symexFind(heapGoodIntFieldUnsat, tLabel("heap_good_int_read_unsat"))
    check r.status == sxUnsat

  test "REGRESSION (RED pre-fix / GREEN post-fix): hazard branch does not mask a sibling path's true sxSat":
    let r = symexFind(heapMaskingOrdered, tLabel("heap_masking_ordered"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# Site: `itMultiVariant` field-deref decline (converted). Triggered by an
# INLINE `ref`-to-multi-axis-variant parameter's field access.
#
# NOTE: witness rendering for a `ref`-to-multi-axis-variant PARAMETER has a
# pre-existing, UNRELATED crash in the witness reader (`readUInt8`: "key not
# found: p.kindA") that reproduces even with ZERO heap-deref/field-access
# involved (a bare `if p != nil: symexTarget(...)`) -- confirmed by isolated
# probe during this slice's investigation, out of scope for the raw-raise
# CLASS this file closes. Every test below therefore checks `.status`/
# `.errors` only, never `.witness`, and only exercises SUT shapes whose
# correct verdict is `sxUnknown` (never `sxSat`) so the crash is never
# triggered.
# =============================================================================

proc heapMultiVariantFieldRead(p: ref HeapMultiVariantObj) =
  if p != nil:
    if p.a1 == 5:
      symexTarget("heap_mv_field_read")

proc heapMultiVariantFieldWrite(p: ref HeapMultiVariantObj) =
  if p != nil:
    p.a1 = 5
    if p.a1 == 5:
      symexTarget("heap_mv_field_write")

suite "N46-followup-2 -- itMultiVariant field deref/write decline (converted)":

  test "field READ through an inline ref-to-multi-variant param -- honest sxUnknown carrying heRefVariantUnsupported":
    let r = symexFind(heapMultiVariantFieldRead, tLabel("heap_mv_field_read"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == heRefVariantUnsupported: saw = true
    check saw
    check r.status != sxSat

  test "field WRITE through an inline ref-to-multi-variant param -- honest sxUnknown carrying heRefVariantUnsupported, write dropped not crashed":
    let r = symexFind(heapMultiVariantFieldWrite, tLabel("heap_mv_field_write"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == heRefVariantUnsupported: saw = true
    check saw
    check r.status != sxSat

suite "N46-followup-2 -- walker version pin":

  test "walker version floor >= 113 (heap-raise totality: runtime_heap.nim's 13-site LEDGERED-LIVE backlog closed)":
    check parseInt(symexWalkerVersion) >= 113
