## N40 (round-6 fix round 6) — `allocateSym` is TOTAL for classifiable input.
##
## Three successive slices (N36/N37/N39) tried to close the raw-raise-in-lower
## CLASS's last five sites (`allocateSym`'s `itUninterp` x3 / `itTable` /
## `itSet` classified-decline arms) by guarding individual CALLERS
## (`isVariantConstructSym`/`lowerVariantLit`, N39). Each slice's own
## spot-check found a FURTHER unguarded caller. N40 retires per-caller
## guarding: `allocateSym` itself never raises for classifiable input again
## (see its own doc-comment addendum, `runtime.nim`, and the new `allocDegrade`
## chokepoint's doc comment for the full design writeup) — every caller
## benefits automatically, with no per-site change required.
##
## This file pins the NEWLY-FOUND unguarded walk-time families the N40 spot
## check surfaced, plus the `unallocatableFieldIssue` FALSE NEGATIVE it closed
## (a non-string-key `Table[int, string]` — ordinary Nim syntax — was
## previously an UNTAGGED `ValueError` crash in `allocateSym`'s `itTable` arm,
## not even a classified carrier):
##
##   1. `runtime_heap.nim`'s heap-deref READ (`heapValueSort`, materialising a
##      field-split heap array's value sort) reaching an unallocatable field
##      type through a call-returned ref (top-level SUT PARAMS of this shape
##      are already safe via CR-2c's pre-existing witness-renderability
##      demotion — see the companion test below — so this family is reached
##      via a `{.symexOpaque.}` call, mirroring `freshRetSym`'s own Medium
##      adjudication). NOTE: a block-nested variant of this SUT (matching
##      N39's own `for i in 0 ..< 1: block:` wrapping idiom) was tried first
##      and empirically confirmed RED — but via an unrelated MISATTRIBUTED
##      `beBudgetExhausted` finding, not a clean crash/silent-loss repro (a
##      SEPARATE while-loop-unwind interaction with the opaque-call +
##      heap-materialisation combination, itself worth a future look); the
##      flat (non-block) SUT below reproduces the SAME core RED (see the
##      per-test doc comments) without that confound.
##   2. `runtime_heap.nim`'s heap-deref WRITE (`derefWriteProto`) — same
##      shape, write side.
##   3. `runtime_closures.nim`'s lambda PARAM sort allocation (`paramSorts`,
##      called from `buildClosure` at `iekLambda` construction time, before
##      the closure is ever called). FINDING (see the family 4/5 SUTs' own
##      comment below): `allocateSym` itself no longer raises here, but a
##      SEPARATE, PRE-EXISTING gap in `sortOfTuple`/`rawAnyAstOf` (no arm for
##      any compound `sv*` kind, valid or not) still crashes downstream —
##      caught by the top-level net (still `sxUnknown`, Invariant 3 intact),
##      but not with N40's own specific classified kind. Flagged, not fixed
##      (out of this slice's scope); pinned status-only.
##   4. `runtime_closures.nim`'s lambda RETURN sort allocation
##      (`buildClosure`'s own `retRep`) — same FINDING as #3.
##   5. The N39 predicate gap itself: a variant arm field of type
##      `Table[int, string]` (bad KEY, not bad VALUE) — `unallocatableFieldIssue`
##      did not flag this prior to N40, so N39's own `isVariantConstructSym`/
##      `lowerVariantLit` guards silently let it through to the (pre-N40) raw
##      `ValueError` crash.
##
## Companions: the pre-walk PARAMETER-entry boundary keeps its whole-run raise
## semantics unchanged (byte-identical kind/message to pre-N40); an ordinary
## fully-backed SUT is unaffected; one UNSAT companion proves no over-degrade.
##
## Walker version: v103 -> v104 (a genuine verdict-surface change — see the
## per-family notes below for which shapes were empirically RED pre-fix).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Family 1: N39 predicate gap -- Table[int, string] (bad KEY) variant arm field
# =============================================================================
# Mirrors tests/tsymex_r6_n39_variant_field_alloc.nim's own VBadTable shape
# exactly, substituting a bad-KEY Table for N39's bad-VALUE Table -- the
# precise false negative `unallocatableFieldIssue` carried since N39 (closed
# this slice, types.nim).

type
  VKind = enum vkGood, vkBad

  VBadTableKey = object
    ## `vkBad`'s field classifies to `itTable` with an unsupported KEY type
    ## (only `Table[string, V]` is backed by `allocateSym`) -- distinct from
    ## N39's own `VBadTable` (bad VALUE type).
    case kind: VKind
    of vkGood: x: int
    of vkBad: t: Table[int, string]

proc n40SymTableKeyBlock(b: byte) =
  let k = if b == 1'u8: vkGood else: vkBad
  for i in 0 ..< 1:
    block:
      let v = VBadTableKey(kind: k)
      if v.kind == vkGood:
        symexTarget("n40_sym_tablekey_block")

proc n40LitTableKeyBlock(a: int) =
  for i in 0 ..< 1:
    block:
      let v = VBadTableKey(kind: vkGood, x: a)
      if v.kind == vkGood and v.x == 42:
        symexTarget("n40_lit_tablekey_block")

# =============================================================================
# Family 2 + 3: heap deref READ / WRITE through an unallocatable field type,
# reached via a {.symexOpaque.} call-returned ref (freshRetSym's own Medium
# adjudication: a call whose declared return type carries an unallocatable
# shape).
# =============================================================================

type
  BadTableHeap = object
    t: Table[int, string]
    n: int

proc n40MkBadHeap(): ref BadTableHeap {.symexOpaque.} =
  discard

proc n40MkBadTable(): Table[int, string] {.symexOpaque.} =
  discard

proc n40HeapReadBlock() =
  let p = n40MkBadHeap()
  if p != nil:
    discard p.t
    symexTarget("n40_heap_read_block")

proc n40HeapWriteBlock() =
  let p = n40MkBadHeap()
  if p != nil:
    p.t = n40MkBadTable()
    symexTarget("n40_heap_write_block")

# =============================================================================
# Family 4 + 5: lambda with an unallocatable PARAM / RETURN type
# (runtime_closures.nim `paramSorts`/`buildClosure`).
#
# FINDING (flagged, NOT fixed -- a SEPARATE, PRE-EXISTING gap discovered by
# this slice's own spot-check, out of N40's scope): `paramSorts`/`buildClosure`
# flatten an allocated param/return SymVal to its Z3 sort(s) via
# `sortOfTuple`/`rawAnyAstOf` (`runtime.nim`), and `rawAnyAstOf` has NO arm for
# `svTable`/`svSet`/`svSeq`/`svVariant`/... at all -- it raises its OWN raw
# `ValueError` ("rawAnyAstOf: unsupported distinct base kind ...") for ANY
# compound-kind leaf, valid or not. This is INDEPENDENT of whether the Table
# shape itself is supported: a closure with a perfectly VALID
# `Table[string, int]` param would hit the IDENTICAL crash (confirmed by
# inspection -- `rawAnyAstOf`'s dispatch never inspects `tabKeyTy`/`tabValTy`
# at all). Pre-N40, `allocateSym`'s own raw raise for an UNSUPPORTED Table
# shape fired FIRST (before `sortOfTuple` was ever reached), so this deeper
# gap was masked. Post-N40, `allocateSym` no longer raises -- control reaches
# `sortOfTuple`, which then crashes on ITS OWN, DIFFERENT reason. The
# observable OUTCOME is unfortunately the SAME (`sxUnknown` via the
# `weInternalWalkerFault` top-level catch-all) both before and after this
# slice for a Table-typed closure param/return specifically -- Invariant 3
# still holds (never silently lost, never a crash escaping the process), but
# N40 does not itself unlock this family; a follow-up slice extending
# `rawAnyAstOf`/`sortOfTuple` to compound placeholder kinds (or declining
# earlier, in `buildClosure` itself, when a param/return type is not
# leaf-flattenable) is the natural next step, left for a future round.
# =============================================================================

proc n40ClosureParamBlock(n: int) =
  for i in 0 ..< 1:
    block:
      let f = proc(t: Table[int, string]): int = n
      symexTarget("n40_closure_param_block")

proc n40ClosureRetBlock(n: int) =
  for i in 0 ..< 1:
    block:
      let g = proc(x: int): Table[int, string] = n40MkBadTable()
      symexTarget("n40_closure_ret_block")

# =============================================================================
# Companion: pre-walk PARAMETER-entry boundary keeps whole-run raise
# semantics -- unaffected by allocateSym's own totality.
# =============================================================================

proc n40ParamBoundaryTable(t: Table[int, string], y: int) =
  if y == 42:
    symexTarget("n40_param_boundary_table")

# NOTE: a `WeakRef[T]`/`Atomic[T]` (`heUnsupportedOwnership`) param-boundary
# companion was attempted here and DROPPED: it hit a genuinely PRE-EXISTING,
# unrelated engine gap -- `emitTyAndReader` (`symex.nim`) has no witness-reader
# case for an `itUninterp("__ownership:...")` top-level param at all (only
# `__closure`/`__unsupported:*`/`__unsupported_witness:*` are handled there),
# so `symexFind` crashes with `ValueError: emitTyAndReader(itUninterp):
# opaque-ref witness reader lands with cluster E` before `raiseParamAllocIssue`
# (or, pre-N40, `allocateSym` itself) ever runs -- confirmed via a standalone
# probe, out of this slice's scope (a `symex.nim` witness-codegen gap, not an
# `allocateSym`/`unallocatableFieldIssue` one). `raiseParamAllocIssue`'s
# `heUnsupportedOwnership` dispatch arm is still exercised structurally by
# `tests/tsymex_phase15_R1a_ir.nim`'s own `ref`/`ptr` R1a coverage and by
# code review (it is a 3-line mechanical mirror of the pre-N40 `allocateSym`
# raise, byte-identical carrier/message).

# =============================================================================
# Companion: an ordinary, fully-backed SUT is unaffected (no over-degrade).
# =============================================================================

proc n40PlainSat(x: int) =
  if x == 777:
    symexTarget("n40_plain_sat")

proc n40PlainUnsat(x: int) =
  if x == 1 and x == 2:
    symexTarget("n40_plain_unsat")

suite "symex N40 -- family 1: Table[int,string] (bad KEY) variant arm field":

  test "N40-1: symbolic-disc construction reaching an unsupported-KEY Table arm field -- honest sxUnknown, never a false sxUnsat":
    let r = symexFind(n40SymTableKeyBlock, tLabel("n40_sym_tablekey_block"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedTableKeyType and
         "variant constructor field allocation unmodeled" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N40-2: variant LITERAL, unsupported-KEY Table field on the INACTIVE arm -- honest sxUnknown":
    let r = symexFind(n40LitTableKeyBlock, tLabel("n40_lit_tablekey_block"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedTableKeyType and
         "variant literal inactive-arm field" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

suite "symex N40 -- family 2/3: heap deref read/write through an unallocatable field":

  test "N40-3: heap-deref READ of an unsupported-KEY Table field (call-returned ref) -- honest sxUnknown carrying the SPECIFIC classified kind (seUnsupportedTableKeyType), not the generic weInternalWalkerFault catch-all":
    ## The stronger assertion matters: PRE-N40 this raw-raises from
    ## `heapValueSort` (`runtime_heap.nim`); even where the raise reaches the
    ## top-level `runSymexImpl` catch-all intact (rather than being silently
    ## lost under nesting), it lands as the BLUNT `weInternalWalkerFault`
    ## ("the walker itself hit a bug") -- never the SPECIFIC construct-gap
    ## kind this shape deserves. Checking `.kind` (not just `.status`) is what
    ## actually discriminates pre- from post-fix here.
    let r = symexFind(n40HeapReadBlock, tLabel("n40_heap_read_block"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == seUnsupportedTableKeyType: saw = true
    check saw

  test "N40-4: heap-deref WRITE of an unsupported-KEY Table field (call-returned ref) -- honest sxUnknown carrying the SPECIFIC classified kind":
    let r = symexFind(n40HeapWriteBlock, tLabel("n40_heap_write_block"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == seUnsupportedTableKeyType: saw = true
    check saw

suite "symex N40 -- family 4/5: lambda with an unallocatable param/return type":

  test "N40-5: lambda construction with an unsupported-KEY Table PARAM type -- still an honest sxUnknown (Invariant 3 holds); status-only per the FINDING documented above (sortOfTuple's own separate, pre-existing compound-kind gap masks the specific kind here)":
    let r = symexFind(n40ClosureParamBlock, tLabel("n40_closure_param_block"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

  test "N40-6: lambda construction with an unsupported-KEY Table RETURN type -- still an honest sxUnknown (Invariant 3 holds); status-only, same FINDING as N40-5":
    let r = symexFind(n40ClosureRetBlock, tLabel("n40_closure_ret_block"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

suite "symex N40 -- companion: param-boundary decline unchanged":

  test "N40-7: a top-level Table[int,string] SUT param still whole-run-degrades via CR-2c's pre-existing witness demotion (feUnsupportedWitnessType, ONE error, unaffected by allocateSym's own totality)":
    ## A top-level param's type-tree is ALREADY intercepted by CR-2c's
    ## `demoteUnrenderableWitnessTy` before it ever reaches `allocateSym` as a
    ## raw `itTable` -- this test proves that pre-existing path is unaffected
    ## by N40 (the run degrades cleanly via the param-entry boundary, not via
    ## allocateSym's own itTable arm at all for this shape).
    let r = symexFind(n40ParamBoundaryTable, tLabel("n40_param_boundary_table"))
    check r.status == sxUnknown
    check r.errors.len == 1
    check r.errors[0].kind == feUnsupportedWitnessType

suite "symex N40 -- companion: ordinary fully-backed SUTs are unaffected":

  test "N40-9: a plain, fully-backed SAT SUT is unaffected (no over-degrade)":
    let r = symexFind(n40PlainSat, tLabel("n40_plain_sat"))
    check r.status == sxSat

  test "N40-10: a plain, fully-backed UNSAT SUT is unaffected (no over-degrade)":
    let r = symexFind(n40PlainUnsat, tLabel("n40_plain_unsat"))
    check r.status == sxUnsat

suite "symex N40 -- walker version pin":

  test "walker version floor >= 104 (N40: allocateSym is total; classified allocation failures degrade in-band)":
    check parseInt(symexWalkerVersion) >= 104
