## N43 (round-6 review, Low, process) — predicate/allocator PARITY test.
##
## Nothing structurally enforces that the allocability PREDICATE
## (`unallocatableFieldIssue`, `smt/types.nim`) and the ALLOCATOR
## (`allocateSym`, `smt/runtime.nim`) agree on every `IRTypeKind` — and this
## drift has already bitten TWICE: N39 found `unallocatableFieldIssue` had a
## false NEGATIVE on a non-string-key `Table` (the predicate said
## "allocatable", `allocateSym` crashed); N40 found further walk-time
## `allocateSym` call sites reachable UNGUARDED by the predicate at all. Both
## were closed as one-off fixes with no standing regression net for the
## *class* of drift (predicate says X, allocator does Y). This file is that
## net: a representative matrix over every `IRTypeKind` both dispatch on,
## asserting the two sides AGREE, so a FUTURE edit to either one alone (a new
## `IRTypeKind` arm, a widened/narrowed predicate branch, a new `allocateSym`
## case) fails loudly here instead of waiting for a third empirical spot-check
## to find it.
##
## ----------------------------------------------------------------------------
## Two parts, two different levels of the stack
## ----------------------------------------------------------------------------
## PART 1 (PREDICATE MATRIX) calls `unallocatableFieldIssue` directly on
## `IRType` values built via `smt/types.nim`'s own constructors (`tTable`,
## `tSeq`, `tVariant`, …) — pure Nim, no Z3, no `symexFind`. This is the fast,
## exhaustive half: every `IRTypeKind` arm the predicate's own `case t.kind`
## dispatches on, including its recursive arms (`itDistinct`, `itTuple`,
## `itArray`, `itVariant`, `itMultiVariant`) fed both an all-good and a
## one-bad-field-nested-arbitrarily-deep shape.
##
## PART 2 (ALLOCATOR CONFIRMATION) routes representative matrix cells through
## an ACTUAL walk (`symexFind`), confirming `allocateSym`'s real dispatch
## agrees with what Part 1 predicted — not just that the predicate is
## internally consistent. This needs a genuinely UNGUARDED call site (one
## that does not itself pre-check `unallocatableFieldIssue` before calling
## `allocateSym` — testing a GUARDED site would only prove the predicate
## agrees with itself, not with the allocator):
##   - Variant literal/symbolic CONSTRUCTION (`lowerVariantLit` /
##     `isVariantConstructSym`, `runtime.nim`) is EXCLUDED for this reason —
##     both are N39-guarded: they call `unallocatableFieldIssue` themselves
##     BEFORE ever calling `allocateSym` for a bad arm field, so routing
##     through them would be circular.
##   - A heap-deref READ of a bad-shaped FIELD (`{.symexOpaque.}` call
##     returning a `ref` to an object with a bad field, `discard p.field`,
##     mirroring `tsymex_r6_n40_alloc_totality.nim`'s own family 2/3 —
##     PROVEN clean in this exact codebase by that file's N40-3/N40-4 pins)
##     reaches `heapValueSort` → `allocateSym` genuinely UNGUARDED. Used here
##     for `itTable`/`itSet`/`itUninterp`(ownership) — single-field-kind
##     shapes only. NOT used for a composite pointee (`itTuple`/`itArray`
##     nesting a bad field): `liftHeapValue`'s `case pointeeTy.kind`
##     (`runtime_heap.nim`) has no arm for those yet ("composite pointees...
##     land R3+" — the still-open N41 gap; using heap-deref there would test
##     THAT unrelated, already-tracked gap instead of this one).
##   - A LAMBDA param type (`buildClosure`/`paramSorts`, `runtime_closures.nim`,
##     mirroring `tsymex_r6_n40_alloc_totality.nim`'s own family 4/5) reaches
##     `allocateSym` genuinely unguarded too, and — unlike heap-deref — never
##     needs to LIFT a value back (only a static SORT, via `sortOfTuple`,
##     which recurses through `svTuple` fields), so it is safe for the
##     COMPOSITE-nesting cells heap-deref cannot cover.
##
## Every "bad" cell asserts `r.status == sxUnknown` and NEVER a crash/hang —
## the actual regression class N39/N40 closed. Every "good" cell asserts a
## clean `sxSat`/`sxUnsat` with ZERO errors — no over-degrade.
##
## `itSeq` is deliberately excluded from Part 2's allocator confirmation:
## `unallocatableFieldIssue`'s own doc comment states flagging it would be a
## FALSE POSITIVE (`allocateSym`'s `itSeq` arm self-guards via
## `isBackedSeqElemTy`/`seqUnsupportedFieldReason` and returns a forced-empty
## placeholder WITHOUT ever calling `allocDegrade`, backed or not) — Part 1
## pins the predicate's own "always none" contract for both backed and
## unbacked element types; the allocator side of that exact contract is
## already extensively pinned by the Bug #2/B7r2/N13 test suites
## (`tests/tsymex_r6_n13_reassign_seqarm.nim` et al.) — not re-duplicated
## here.
##
## `itDistinct`'s bad-base recursion is Part-1-only: `allocDistinctSym`
## (`runtime.nim` ~1615) calls `allocateSym(ty.distinctBase, ...)`
## unconditionally (confirmed by inspection) — the SAME unguarded recursion
## shape as `itTuple`/`itArray` — but a Nim `distinct` of a `Table`/`HashSet`
## base is exotic enough (no clean DSL-idiomatic construction) that this
## slice does not attempt a live SUT for it; Part 1's direct `IRType`
## construction already exercises the predicate's own `itDistinct` recursion
## exhaustively, and the allocator's matching recursion is a one-line, cited
## code fact rather than a live-tested one for this specific cell.
##
## Two of `itUninterp`'s three classified-marker prefixes
## (`__unsupported:`, `__unsupported_witness:`) are, BY CONSTRUCTION, never
## reachable through `allocateSym`'s own walk-time recursion at all —
## `__unsupported_witness:` is minted ONLY by `demoteUnrenderableWitnessTy`
## at the TOP-LEVEL PARAMETER boundary (CR-2c); `__unsupported:` similarly
## arises from `classifyType`'s param/return-type catch-all. Both are
## consumed by the OTHER documented caller of the SAME `unallocatableFieldIssue`
## predicate — `raiseParamAllocIssue`'s pre-walk parameter-entry boundary
## (`allocateSym`'s own doc comment: "it pre-checks every top-level param
## type with `unallocatableFieldIssue` and raises the classified error
## itself, by design, before this proc — or any walk state — ever exists").
## Part 2 confirms parity at THAT boundary for these two cells specifically
## (a companion suite below), rather than forcing them through a shape they
## cannot structurally reach.
##
## No engine code changes in this slice — test-only. Walker version:
## unchanged (`symexWalkerVersion` stays "108"; the floor pin below matches
## house convention).
import std/[unittest, strutils, tables, sets, options]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

proc errorKinds(r: SymexResult): seq[SymexErrorKind] =
  for e in r.errors: result.add e.kind

# =============================================================================
# PART 1 -- PREDICATE MATRIX: unallocatableFieldIssue(t) called directly on
# constructed IRType values. Covers every IRTypeKind arm both
# unallocatableFieldIssue and allocateSym dispatch on.
# =============================================================================

suite "symex N43 -- predicate matrix (unallocatableFieldIssue)":

  let badTable = tTable(tInt(64, signed = true), tInt(64, signed = true))
    ## bad KEY (non-string) -- the exact N40 false-negative shape.

  test "itBool: always allocatable":
    check unallocatableFieldIssue(tBool()).isNone

  test "itInt: always allocatable, any width/signedness":
    check unallocatableFieldIssue(tInt(64, signed = true)).isNone
    check unallocatableFieldIssue(tInt(8, signed = false)).isNone
    check unallocatableFieldIssue(tUInt(32)).isNone

  test "itString: always allocatable":
    check unallocatableFieldIssue(tString()).isNone

  test "itFloat32 / itFloat64: always allocatable":
    check unallocatableFieldIssue(tFloat32()).isNone
    check unallocatableFieldIssue(tFloat64()).isNone

  test "itRef / itPtr: always allocatable (structural stub, not a decline)":
    check unallocatableFieldIssue(tRef(tBool())).isNone
    check unallocatableFieldIssue(tPtr(tInt())).isNone

  test "itDistinct: recurses into the base -- good base allocatable, bad base not":
    check unallocatableFieldIssue(tDistinct("D", tBool())).isNone
    check unallocatableFieldIssue(tDistinct("D", badTable)).isSome

  test "itTuple: recurses into every field -- all-good allocatable, one bad field (nested arbitrarily) not":
    check unallocatableFieldIssue(tTuple(@[tBool(), tInt()])).isNone
    check unallocatableFieldIssue(tTuple(@[tBool(), badTable])).isSome
    # nested two levels deep -- unallocatableFieldIssue recurses through its
    # own itTuple arm, not just one level.
    check unallocatableFieldIssue(tTuple(@[tTuple(@[tInt(), badTable])])).isSome

  test "itArray: recurses into elemTy":
    check unallocatableFieldIssue(tArray(tBool(), 3)).isNone
    check unallocatableFieldIssue(tArray(badTable, 3)).isSome

  test "itSeq: deliberately EXCLUDED -- always allocatable per the predicate's own documented contract, backed or not (allocateSym's itSeq arm self-guards and never raises/degrades either way for this kind -- see the header note; the allocator-side half of this exact contract is pinned by the Bug #2/B7r2/N13 suites, not re-duplicated here)":
    check unallocatableFieldIssue(tSeq(tInt())).isNone                       ## backed elem
    check unallocatableFieldIssue(tSeq(tTuple(@[tString(), tString()]))).isNone  ## unbacked elem -- STILL none

  test "itTable: good key+val allocatable; bad key / bad val not":
    check unallocatableFieldIssue(tTable(tString(), tInt(64, signed = true))).isNone
    check unallocatableFieldIssue(badTable).isSome                                 ## bad key
    check unallocatableFieldIssue(tTable(tString(), tInt(32, signed = true))).isSome  ## bad val (width)

  test "itSet: good elem allocatable; bad elem not":
    check unallocatableFieldIssue(tSet(tInt(64, signed = true))).isNone
    check unallocatableFieldIssue(tSet(tInt(32, signed = true))).isSome

  test "itUninterp: the three classified marker prefixes are unallocatable; an unrecognized name is the Defect-class sentinel arm (predicate returns none -- allocateSym's own doc comment: unreachable from valid DSL surface)":
    check unallocatableFieldIssue(tUninterp("__ownership:WeakRef")).isSome
    check unallocatableFieldIssue(tUninterp("__unsupported:cstring")).isSome
    check unallocatableFieldIssue(tUninterp("__unsupported_witness:seq[Foo]")).isSome
    check unallocatableFieldIssue(tUninterp("__closure")).isNone

  test "itVariant: recurses into the discriminator, every plain field, and every arm's fields":
    let goodVariant = tVariant("V", "kind", tInt(),
      @[VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["x"],
                   fieldTypes: @[tBool()])])
    check unallocatableFieldIssue(goodVariant).isNone
    let badDiscVariant = tVariant("V", "kind", badTable, @[])
    check unallocatableFieldIssue(badDiscVariant).isSome
    let badPlainVariant = tVariant("V", "kind", tInt(), @[],
      plainFieldTypes = @[badTable])
    check unallocatableFieldIssue(badPlainVariant).isSome
    let badArmVariant = tVariant("V", "kind", tInt(),
      @[VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["t"],
                   fieldTypes: @[badTable])])
    check unallocatableFieldIssue(badArmVariant).isSome

  test "itMultiVariant: recurses into every axis's plain fields, disc, and arm fields":
    let goodArm = VariantArm(tagOrdinal: 0, tagName: "x", fieldNames: @[], fieldTypes: @[])
    let badArm = VariantArm(tagOrdinal: 0, tagName: "x", fieldNames: @["f"],
                            fieldTypes: @[badTable])
    let goodAxis = VariantAxis(discName: "a", discTy: tInt(), arms: @[goodArm], discTags: @[])
    let badArmAxis = VariantAxis(discName: "a", discTy: tInt(), arms: @[badArm], discTags: @[])
    let badDiscAxis = VariantAxis(discName: "b", discTy: badTable, arms: @[goodArm], discTags: @[])
    check unallocatableFieldIssue(mkMultiVariant("MV", @[goodAxis, goodAxis])).isNone
    check unallocatableFieldIssue(mkMultiVariant("MV", @[goodAxis, badArmAxis])).isSome
    check unallocatableFieldIssue(mkMultiVariant("MV", @[goodAxis, badDiscAxis])).isSome

# =============================================================================
# PART 2 -- ALLOCATOR CONFIRMATION: routing representative matrix cells
# through an actual symexFind walk via genuinely UNGUARDED allocateSym call
# sites (see header for why variant construction is excluded as circular).
# =============================================================================

type
  WeakRef[T] = distinct T
    ## Local ownership stand-in matching classifyType's head-text-match
    ## ("WeakRef"/"Atomic" -> __ownership:*) -- same convention as
    ## tests/tsymex_r6_n42_deref_taint.nim's own WeakRef stand-in. MUST be
    ## named exactly "WeakRef" (or "Atomic") -- classifyType matches on the
    ## generic HEAD's text, not structurally, so any other name falls
    ## through to the generic `__unsupported:` catch-all instead.

  N43BadHeap = object
    good:        int
    tableKeyBad: Table[int, string]
    tableValBad: Table[string, int32]
    setBad:      HashSet[int32]
    ownBad:      WeakRef[bool]

  N43Outer = object
    ## Two-hop indirection, mirroring tests/tsymex_r6_n42_deref_taint.nim's
    ## own N42Outer*/N42Bad* shapes exactly, and for the SAME reason its
    ## header documents: the OUTER pointee (`N43Outer`) is clean, so a
    ## TOP-LEVEL param of this type dodges CR-2c's whole-param
    ## witness-renderability demotion (which would otherwise short-circuit
    ## BEFORE any walk-time allocateSym call, testing the param boundary
    ## instead of allocateSym's own dispatch); the bad field is only reached
    ## on the SECOND hop, at WALK time, via `isDeref`.
    ##
    ## An EARLIER version of this suite reached `N43BadHeap` directly through
    ## a `{.symexOpaque.}` call (matching tsymex_r6_n40_alloc_totality.nim's
    ## OWN family-2 idiom) -- empirically WRONG for a "good field, no
    ## over-degrade" control: `stmt.opaque`'s own walk handler
    ## (runtime.nim ~8069-8083) unconditionally sets `w.sawUnknown = true`
    ## and taints EVERY surviving path for ANY opaque call, regardless of
    ## return type or field shape (that IS what `{.symexOpaque.}` means --
    ## "unknown side effects, never trust a target reached after this call").
    ## N40's own family-2/3 tests never needed a clean GOOD-field control
    ## through their opaque route for exactly this reason. The two-hop PARAM
    ## shape below has no such blanket taint, so it can carry a genuine
    ## no-over-degrade control alongside the bad-field cells.
    next: ref N43BadHeap
    m: int

proc n43HeapGoodBlock(p: ref N43Outer) =
  if p != nil:
    if p.next != nil:
      discard p.next.good
      symexTarget("n43_heap_good")

proc n43HeapTableKeyBlock(p: ref N43Outer) =
  if p != nil:
    if p.next != nil:
      discard p.next.tableKeyBad
      symexTarget("n43_heap_table_key")

proc n43HeapTableValBlock(p: ref N43Outer) =
  if p != nil:
    if p.next != nil:
      discard p.next.tableValBad
      symexTarget("n43_heap_table_val")

proc n43HeapSetBlock(p: ref N43Outer) =
  if p != nil:
    if p.next != nil:
      discard p.next.setBad
      symexTarget("n43_heap_set")

proc n43HeapOwnershipBlock(p: ref N43Outer) =
  if p != nil:
    if p.next != nil:
      discard p.next.ownBad
      symexTarget("n43_heap_ownership")

suite "symex N43 -- allocator confirmation via heap-deref (genuinely unguarded allocateSym reach)":

  test "N43-H0: an untouched sibling GOOD field stays sxSat, zero errors (no over-degrade from bad siblings on the same object)":
    let r = symexFind(n43HeapGoodBlock, tLabel("n43_heap_good"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.errors.len == 0

  test "N43-H1: Table bad-KEY field -- predicted unallocatable (Part 1), allocator confirms: sxUnknown, seUnsupportedTableKeyType, no crash":
    check unallocatableFieldIssue(tTable(tInt(64, true), tString())).isSome
    let r = symexFind(n43HeapTableKeyBlock, tLabel("n43_heap_table_key"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    check seUnsupportedTableKeyType in errorKinds(r)

  test "N43-H2: KNOWN-DISPARITY -- Table bad-VAL field of the WRONG WIDTH (Table[string, int32]) -- predicate says unallocatable/seUnsupportedTableValType, but allocateSym's itTable arm actually DISAGREES with the predicate":
    ## Real disparity found by this slice's own matrix, pinned per the N43
    ## mandate (report, do not fix engine code). `unallocatableFieldIssue`
    ## correctly flags `Table[string, int32]` (val kind is itInt, but width
    ## 32 != 64) as unallocatable with `seUnsupportedTableValType`. But
    ## `allocateSym`'s itTable arm (runtime.nim ~2210) dispatches on the val
    ## type by `case ty.tabValTy.kind` alone: `of itInt:` unconditionally
    ## `doAssert`s `width == 64 and signed` instead of falling through to the
    ## `else: allocDegrade(seUnsupportedTableValType, ...)` branch the way
    ## the predicate expects for ANY non-canonical itInt width -- so a
    ## non-int64 (or unsigned int64) table VALUE type never reaches the
    ## classified decline at all; it trips the bare `doAssert` instead, an
    ## AssertionDefect caught only by CR-1c's generic top-level catch-all
    ## (`weInternalWalkerFault` -- "the walker itself hit a bug"), not the
    ## specific `seUnsupportedTableValType` the predicate promises. Invariant
    ## 3 (never an uncaught crash) still holds -- this IS caught, still
    ## degrades to sxUnknown -- but the SPECIFIC classified kind the
    ## predicate/allocator contract promises is wrong. This is the narrower,
    ## VALUE-side sibling of the exact N40 false-negative class (there: bad
    ## KEY type silently crashed pre-N40; here: a bad-WIDTH VALUE type still
    ## crashes today, just now caught generically instead of raising
    ## uncaught). Left unfixed per this slice's test-only mandate; flagged in
    ## the slice's own return for follow-up.
    check unallocatableFieldIssue(tTable(tString(), tInt(32, true))).isSome
    let r = symexFind(n43HeapTableValBlock, tLabel("n43_heap_table_val"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    check weInternalWalkerFault in errorKinds(r)
    # Pins the DISPARITY itself: the predicate's promised kind never actually
    # appears. If this flips to `in` after a future fix, that fix should also
    # flip this assertion (and the KNOWN-DISPARITY note above) -- see the doc
    # comment.
    check seUnsupportedTableValType notin errorKinds(r)

  test "N43-H3: HashSet bad-elem field -- predicted unallocatable (Part 1), allocator confirms: sxUnknown, seUnsupportedSetCharInterop, no crash":
    check unallocatableFieldIssue(tSet(tInt(32, true))).isSome
    let r = symexFind(n43HeapSetBlock, tLabel("n43_heap_set"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    check seUnsupportedSetCharInterop in errorKinds(r)

  test "N43-H4: ownership-wrapped field -- predicted unallocatable (Part 1), allocator confirms: sxUnknown, heUnsupportedOwnership, no crash":
    check unallocatableFieldIssue(tUninterp("__ownership:WeakRef")).isSome
    let r = symexFind(n43HeapOwnershipBlock, tLabel("n43_heap_ownership"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    check heUnsupportedOwnership in errorKinds(r)

# -----------------------------------------------------------------------------
# Composite-nesting cells: routed via a LAMBDA param type (paramSorts /
# buildClosure, runtime_closures.nim) instead of heap-deref -- see header for
# why (liftHeapValue has no arm yet for a composite pointee, the still-open
# N41 gap; a closure never needs to lift a value back, only a static sort).
# -----------------------------------------------------------------------------

proc n43ClosureGoodBlock(n: int) =
  for i in 0 ..< 1:
    block:
      let f = proc(t: (int, bool)): int = n
      symexTarget("n43_closure_good")

proc n43ClosureNestedTupleBlock(n: int) =
  for i in 0 ..< 1:
    block:
      let f = proc(t: (int, Table[int, string])): int = n
      symexTarget("n43_closure_nested_tuple")

proc n43ClosureNestedArrayBlock(n: int) =
  for i in 0 ..< 1:
    block:
      let f = proc(t: array[2, Table[int, string]]): int = n
      symexTarget("n43_closure_nested_array")

suite "symex N43 -- allocator confirmation via lambda param sorts (composite-nesting recursion parity)":

  test "N43-C0: an ordinary, fully-backed lambda param is unaffected (no over-degrade)":
    let r = symexFind(n43ClosureGoodBlock, tLabel("n43_closure_good"))
    check r.status == sxSat

  test "N43-C1: tuple nesting a bad-key Table field, as a lambda param -- predicted unallocatable (Part 1's itTuple recursion), allocator confirms honest sxUnknown, no crash":
    check unallocatableFieldIssue(tTuple(@[tInt(), tTable(tInt(64, true), tString())])).isSome
    let r = symexFind(n43ClosureNestedTupleBlock, tLabel("n43_closure_nested_tuple"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

  test "N43-C2: array nesting a bad-key Table field, as a lambda param -- predicted unallocatable (Part 1's itArray recursion), allocator confirms honest sxUnknown, no crash":
    check unallocatableFieldIssue(tArray(tTable(tInt(64, true), tString()), 2)).isSome
    let r = symexFind(n43ClosureNestedArrayBlock, tLabel("n43_closure_nested_array"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

# -----------------------------------------------------------------------------
# Companion: the two itUninterp prefixes NOT reachable through allocateSym's
# own walk-time recursion at all (__unsupported:, __unsupported_witness:) --
# confirmed at the OTHER documented call site of the SAME predicate,
# raiseParamAllocIssue's pre-walk parameter-entry boundary (see header).
# -----------------------------------------------------------------------------

type
  N43WitnessObj = object
    a: int

proc n43ParamUnsupported(x: cstring, y: int) =
  if y == 42:
    symexTarget("n43_param_unsupported")

proc n43ParamUnsupportedWitness(xs: seq[N43WitnessObj], y: int) =
  if y == 42:
    symexTarget("n43_param_unsupported_witness")

suite "symex N43 -- companion: param-boundary confirmation for the two structurally-walk-unreachable itUninterp prefixes":

  test "N43-P1: an unresolved parameter type (__unsupported:) -- predicted unallocatable (Part 1), raiseParamAllocIssue confirms: whole-run sxUnknown, feUnsupportedParamType":
    check unallocatableFieldIssue(tUninterp("__unsupported:cstring")).isSome
    let r = symexFind(n43ParamUnsupported, tLabel("n43_param_unsupported"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    check feUnsupportedParamType in errorKinds(r)

  test "N43-P2: an unrenderable witness shape (__unsupported_witness:, a plain-object seq element) -- predicted unallocatable (Part 1), raiseParamAllocIssue confirms: whole-run sxUnknown, feUnsupportedWitnessType":
    let r = symexFind(n43ParamUnsupportedWitness, tLabel("n43_param_unsupported_witness"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    check feUnsupportedWitnessType in errorKinds(r)

suite "symex N43 -- walker version pin":

  test "walker version floor >= 108 (N43: test-only parity net, no verdict change)":
    check parseInt(symexWalkerVersion) >= 108
