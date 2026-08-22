## N42 (round-6 fix round 7) -- the heap-deref READ arm (`isDeref`,
## `runtime_heap.nim`) taints its own path when the field/pointee-type
## allocation it just materialised degraded via `allocateSym`/`allocDegrade`
## (N40), instead of relying solely on the global `w.sawUnknown` sync --
## which ADR-0012 D2's own documented sxSat-wins-over-sawUnknown verdict
## precedence (`runSymexImpl`, ~line 10498) makes insufficient for a path
## whose OWN allocation just degraded.
##
## FIX: all three `mkHeapArrayVar` call sites inside `isDeref` (bare/plain
## field, variant disc-heap, variant arm-field) now call
## `drainPendingLowerEffects` immediately after materialising the heap
## array, folding any pending `allocateSym` degrade into `Path.uncertain`
## (SND-1) before the value is used. A SECOND, independent instance of the
## identical shape was found and fixed in `isDerefWrite`'s variant
## ARM-FIELD write sub-arm (its own `armHeap` materialisation happens AFTER
## the RHS's own drain-providing `lowerInExpr` call). COMPANION FIX:
## `liftHeapValue` gained an `itUninterp` arm (was an uncaught crash --
## `SymexRefUnresolvedError` -- immediately after `heapSelect`) so the taint
## fix has an observable effect for that kind instead of being permanently
## pre-empted by that crash. `itTable`/`itSet` are DELIBERATELY untouched
## this slice (N41's `rawAnyAstOf` gap stays open -- see the walker-version
## doc comment, `canonicalize.nim`, for the "shipping the taint fix without
## also touching N41 would have been fine; shipping ONLY the `liftHeapValue`
## crash-removal WITHOUT the taint fix would have REGRESSED soundness"
## finding this slice confirmed by isolated probe).
##
## EMPIRICAL NOTE (read before assuming these are ordinary RED/GREEN
## pairs): roughly a dozen SUT shapes were tried to reproduce an OBSERVABLE
## false `sxSat` from this gap -- none did. `{.symexOpaque.}` calls (the
## `isCall` `stmt.opaque` arm, `runtime.nim`) and `new T` (when `T` has an
## unclean-zero field, `isNew`'s own zero-write guard) already
## unconditionally taint their OWN call/allocation site for unrelated,
## pre-existing, correct reasons -- independent of this gap. A top-level ref
## PARAM whose pointee has the bad field is independently caught by CR-2c's
## witness-demotion (`itTable`/`itSet`: `feUnsupportedWitnessType`, whole-run,
## before the walk starts) or crashes `emitTyAndReader` at MACRO-EXPANSION
## time (`itUninterp`: `symex.nim:650`, "opaque-ref witness reader lands
## with cluster E" -- pre-dates this slice, out of scope, matches the
## N40 test file's own dropped param-boundary companion note). The
## WORKING probe shape below (two-hop ref indirection through a param) dodges
## both: the outer param's own pointee is clean, so CR-2c/emitTyAndReader
## never trip, and nothing taints until the SECOND hop's field-deref
## actually runs. Even THERE, though, the very next `lower()`-calling
## statement that consumes the dereffed value (`discard`'s own `isLet`
## binding, confirmed via direct runtime instrumentation -- temporarily
## added, verified, removed) happens to drain the still-pending degrade
## onto the SAME unforked path before any target is reached -- sound by
## COINCIDENCE (whatever statement happens to run next), not by
## construction. Instrumentation directly confirmed the underlying
## mechanism gap regardless: `loweringDidDegrade` flips `true` during
## `isDeref`'s heap-array materialisation and `child.uncertain` stays
## `false` immediately after, pre-fix, for every shape tried. This fix
## closes that window unconditionally -- defense-in-depth against a FUTURE
## change (an optimisation eliding the redundant `discard`, a new
## consuming-statement shape) turning the now-latent gap into a live one --
## the same "fix even though today's observable behaviour already degrades
## via some other, blunter mechanism" pattern N36-N40 each established.
## Every test below is therefore a REGRESSION/behaviour pin (same status +
## same specific error kind, no crash residue, no over-taint of sound
## sibling paths), stash-verified to be UNCHANGED by this slice's own fix
## for every case except the `itUninterp` one below (which DOES flip: crash
## -> clean classified decline, once `liftHeapValue` gains its arm --
## verified via stash the taint-only half is what keeps it sound rather
## than merely quiet).
##
## Walker: v104 -> v105 (see `symexWalkerVersion`'s own doc comment,
## `canonicalize.nim`, for the full writeup). CR-2 `==` pin 104 -> 105
## (`tests/tsymex_phase15_CR2_cachekey.nim`).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Shared shapes: a clean OUTER node (no bad fields of its own -- dodges
# CR-2c/emitTyAndReader at the param boundary) whose `next` field points to
# an INNER heap object carrying the degraded field. First touch of the
# degraded field happens at WALK time, via `isDeref`, not at parse/macro time.
# =============================================================================

type
  WeakRef[T] = distinct T
    ## Local stand-in matching `classifyType`'s "WeakRef"/"Atomic"
    ## head-text-match -> `__ownership:*` (dsl_typebridge.nim ~582-588).
    ## Mirrors the N40 test file's own dropped param-boundary companion note
    ## (`tests/tsymex_r6_n40_alloc_totality.nim` ~175-188): a BARE top-level
    ## `WeakRef[T]` param crashes `emitTyAndReader` at macro-expansion time,
    ## unrelated to this slice, out of scope -- hence the two-hop indirection.

  N42BadOwnHeap = object
    w: WeakRef[bool]
    n: int

  N42OuterOwn = object
    next: ref N42BadOwnHeap
    m: int

  N42BadTableHeap = object
    t: Table[int, string]
    n: int

  N42OuterTable = object
    next: ref N42BadTableHeap
    m: int

  N42GoodHeap = object
    x: int
    y: bool

  N42OuterGood = object
    next: ref N42GoodHeap
    m: int

proc n42OwnBefore(p: ref N42OuterOwn) =
  if p != nil:
    symexTarget("n42_own_before")

proc n42OwnAfter(p: ref N42OuterOwn) =
  if p != nil:
    if p.next != nil:
      discard p.next.w
      symexTarget("n42_own_after")

proc n42TableBefore(p: ref N42OuterTable) =
  if p != nil:
    symexTarget("n42_table_before")

proc n42TableAfter(p: ref N42OuterTable) =
  if p != nil:
    if p.next != nil:
      discard p.next.t
      symexTarget("n42_table_after")

# =============================================================================
# Sound-path companions (task item iii): a normal, fully-backed deref read
# (sxSat with a replaying witness), an UNSAT companion, and derefwrite/isNew
# shapes with a GOOD field -- verdicts must be completely unaffected by this
# slice (the drain is a documented no-op when nothing degraded).
# =============================================================================

proc n42GoodReadSat(p: ref N42OuterGood) =
  if p != nil:
    if p.next != nil:
      if p.next.x == 777:
        symexTarget("n42_good_read_sat")

proc n42GoodReadUnsat(p: ref N42OuterGood) =
  if p != nil:
    if p.next != nil:
      if p.next.x == 1 and p.next.x == 2:
        symexTarget("n42_good_read_unsat")

proc n42GoodDerefWrite(p: ref N42OuterGood) =
  if p != nil:
    if p.next != nil:
      p.next.x = 42
      if p.next.x == 42:
        symexTarget("n42_good_derefwrite")

proc n42IsNewGoodField() =
  ## `new` on a NAMED record type is not this codebase's supported
  ## construction idiom (named-object heap construction goes through P2b's
  ## constructor-call syntax instead, `Node(val: x, next: nil)`, a totally
  ## different mechanism than `isNew`) -- mirrors the established `new int`
  ## idiom (`tests/tsymex_phase15_r2_new.nim` etc) for a bare primitive
  ## pointee instead, exercising `isNew`'s own universal zero-write path
  ## directly and unaffected by anything this slice touches (isNew's own
  ## `mkHeapArrayVar` call, `runtime_heap.nim` ~818, is unreachable for an
  ## unsupported field type by construction -- `zeroIRExprForType` returning
  ## `nil` short-circuits BEFORE it, per that arm's own N42-era audit note).
  let p = new int
  if p != nil:
    if p[] == 0:  ## isNew's universal zero-write: a fresh int is 0
      symexTarget("n42_isnew_good_field")

# =============================================================================
# Nested-block first-touch deref (task item iv, ADR-0023 depth): the SAME
# `n42OwnAfter`/`n42TableAfter` shapes, but with the degrading deref
# wrapped inside an extra `block:` -- the same nesting idiom N39's own SUTs
# used (`for i in 0 ..< 1: block:`) to probe the raw-raise-in-lower CLASS's
# own historical "misattributed under nesting" hazard (N40's own doc
# comment, `canonicalize.nim`, calls this out by name for this exact family).
# =============================================================================

proc n42OwnAfterNested(p: ref N42OuterOwn) =
  if p != nil:
    if p.next != nil:
      for i in 0 ..< 1:
        block:
          discard p.next.w
          symexTarget("n42_own_after_nested")

proc n42TableAfterNested(p: ref N42OuterTable) =
  if p != nil:
    if p.next != nil:
      for i in 0 ..< 1:
        block:
          discard p.next.t
          symexTarget("n42_table_after_nested")

suite "symex N42 -- itUninterp (ownership) heap-deref read":

  test "N42-1: sanity -- target reachable before the ownership-field deref (untainted baseline)":
    let r = symexFind(n42OwnBefore, tLabel("n42_own_before"))
    check r.status == sxSat
    check r.errors.len == 0

  test "N42-2: heap-deref READ of an ownership-wrapped field -- honest sxUnknown carrying heUnsupportedOwnership, no crash residue, never a false sxSat":
    let r = symexFind(n42OwnAfter, tLabel("n42_own_after"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == heUnsupportedOwnership and "WeakRef" in e.msg:
        saw = true
    check saw

  test "N42-3: nested-block first-touch (ADR-0023 depth) -- same honest decline, not misattributed under nesting":
    let r = symexFind(n42OwnAfterNested, tLabel("n42_own_after_nested"))
    check r.status == sxUnknown
    var saw = false
    for e in r.errors:
      if e.kind == heUnsupportedOwnership: saw = true
    check saw

suite "symex N42 -- itTable heap-deref read (N41 crash stays masked-sound, taint-only decision)":

  test "N42-4: sanity -- target reachable before the table-field deref (untainted baseline)":
    let r = symexFind(n42TableBefore, tLabel("n42_table_before"))
    check r.status == sxSat
    check r.errors.len == 0

  test "N42-5: heap-deref READ of a non-string-key Table field -- still sxUnknown (N41's rawAnyAstOf gap is UNTOUCHED this slice, masked-sound via crash exactly as before)":
    let r = symexFind(n42TableAfter, tLabel("n42_table_after"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

  test "N42-6: nested-block first-touch (ADR-0023 depth) -- same masked-sound sxUnknown, not misattributed under nesting":
    let r = symexFind(n42TableAfterNested, tLabel("n42_table_after_nested"))
    check r.status == sxUnknown

suite "symex N42 -- sound-path companions (no over-taint, verdicts unchanged)":

  test "N42-7: an ordinary, fully-backed deref read is sxSat with a replaying witness (no over-taint)":
    let r = symexFind(n42GoodReadSat, tLabel("n42_good_read_sat"))
    check r.status == sxSat
    check r.errors.len == 0

  test "N42-8: an ordinary, fully-backed deref read UNSAT companion (no over-taint)":
    let r = symexFind(n42GoodReadUnsat, tLabel("n42_good_read_unsat"))
    check r.status == sxUnsat

  test "N42-9: derefwrite with a good field -- unaffected (verdict unchanged by this slice)":
    let r = symexFind(n42GoodDerefWrite, tLabel("n42_good_derefwrite"))
    check r.status == sxSat

  test "N42-10: isNew with a good field -- unaffected (verdict unchanged by this slice)":
    let r = symexFind(n42IsNewGoodField, tLabel("n42_isnew_good_field"))
    check r.status == sxSat

suite "symex N42 -- walker version pin":

  test "walker version floor >= 105 (N42: heap-deref-read arm taints its own path on allocation degrade)":
    check parseInt(symexWalkerVersion) >= 105
