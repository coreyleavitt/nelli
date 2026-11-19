## RFC-0016 review D3c-6: the sort-checked Z3 term builders.
##
## `checkedStore` / `checkedSelect` / `checkedIte` / `checkedEq` build a Z3
## term with the operand sorts checked against what the operation expects. A
## mismatch is a walker fault (`weInternalWalkerFault`): it taints the path
## and a fresh term of the right sort stands in, so a sort error is a decline
## and never a Z3 abort. They were defined in `runtime.nim`, which the heap
## algebra (`heap_model.nim`) could not import; they and the two readers of a
## SymVal's raw term (`rawAnyAstOf`, `allocDegrade`) live here, below both.
## `probeContext` (a scratch context for decl-kind probes) and
## `termWalkMaxDepth` (the depth a recursive walk of a Z3 term stops at)
## ride along: every consumer is a term-level walk.
##
## Imports: `z3`, `./types`, `./symval` only.
import z3
import ./types
import ./symval

proc sortFault*(ctx: Z3Context; op: string; want, got: RawZ3Sort): bool =
  ## RFC-0005 S8m. True, after recording the walker fault, when `got` is not
  ## `want`. Z3 hash-conses sorts, so pointer identity is sort equality (what
  ## `Z3_is_eq_sort` computes).
  if want == got: return false
  lowerDegrade(weInternalWalkerFault,
    "Z3 sort mismatch at " & op & ": expected " &
      $Z3_sort_to_string(ctx.raw, want) & ", got " &
      $Z3_sort_to_string(ctx.raw, got) & " -- the walker built an ill-sorted " &
      "term; a fresh term stands in and the path is tainted " &
      "(RFC-0005 S8m; weInternalWalkerFault)")
  true

proc sortOfRaw*(ctx: Z3Context; a: RawZ3Ast): RawZ3Sort =
  ctx.checkErr Z3_get_sort(ctx.raw, a)

proc freshOfSort*(ctx: Z3Context; s: RawZ3Sort): RawZ3Ast =
  ctx.checkErr Z3_mk_fresh_const(ctx.raw, "__sortFault", s)

# ---- [s8m-checked-builders-begin] -----------------------------------------
# The only raw `Z3_mk_store` / `Z3_mk_select` / `Z3_mk_ite` / `Z3_mk_eq` calls
# of the walker are the four below, each after its sort check. Every other
# site calls the `checked*` builder. `tsymex_rfc0005_s8m_exits_b`'s audit
# exempts exactly this region and fails when either marker is missing.

proc checkedStore*(ctx: Z3Context; arr, idx, val: RawZ3Ast): RawZ3Ast =
  ## RFC-0005 S8m. `Z3_mk_store` with the index and value sorts checked
  ## against the array's domain and range.
  let arrSort = sortOfRaw(ctx, arr)
  if sortFault(ctx, "array store index",
               ctx.checkErr Z3_get_array_sort_domain(ctx.raw, arrSort),
               sortOfRaw(ctx, idx)) or
     sortFault(ctx, "array store value",
               ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort),
               sortOfRaw(ctx, val)):
    return freshOfSort(ctx, arrSort)
  ctx.checkErr Z3_mk_store(ctx.raw, arr, idx, val)

proc checkedSelect*(ctx: Z3Context; arr, idx: RawZ3Ast): RawZ3Ast =
  ## RFC-0005 S8m. `Z3_mk_select` with the index sort checked against the
  ## array's domain.
  let arrSort = sortOfRaw(ctx, arr)
  if sortFault(ctx, "array select index",
               ctx.checkErr Z3_get_array_sort_domain(ctx.raw, arrSort),
               sortOfRaw(ctx, idx)):
    return freshOfSort(ctx, ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort))
  ctx.checkErr Z3_mk_select(ctx.raw, arr, idx)

proc boolSortFault(ctx: Z3Context; op: string; got: RawZ3Sort): bool =
  ## RFC-0016 CRH-07: `sortFault` against Bool that makes no AST unless the
  ## sort is wrong. A caller may pass a fresh, unreferenced term, which the
  ## next call that makes an AST (`Z3_mk_bool_sort` too) frees; only the
  ## getters run before the term is built over it.
  if Z3_get_sort_kind(ctx.raw, got) == Z3_BOOL_SORT: return false
  sortFault(ctx, op, ctx.checkErr Z3_mk_bool_sort(ctx.raw), got)

proc checkedIte*(ctx: Z3Context; c, t, e: RawZ3Ast): RawZ3Ast =
  ## RFC-0005 S8m. `Z3_mk_ite` with a Bool condition and two same-sort arms.
  ## Makes no AST before `Z3_mk_ite` on the well-sorted path (CRH-07).
  let tSort = sortOfRaw(ctx, t)
  if boolSortFault(ctx, "ite condition", sortOfRaw(ctx, c)) or
     sortFault(ctx, "ite else-arm", tSort, sortOfRaw(ctx, e)):
    return freshOfSort(ctx, tSort)
  ctx.checkErr Z3_mk_ite(ctx.raw, c, t, e)

proc checkedEq*(ctx: Z3Context; a, b: RawZ3Ast): RawZ3Ast =
  ## RFC-0005 S8m. `Z3_mk_eq` over two same-sort operands.
  if sortFault(ctx, "equality", sortOfRaw(ctx, a), sortOfRaw(ctx, b)):
    return freshOfSort(ctx, ctx.checkErr Z3_mk_bool_sort(ctx.raw))
  ctx.checkErr Z3_mk_eq(ctx.raw, a, b)

# ---- [s8m-checked-builders-end] -------------------------------------------

proc allocDegrade*(kind: SymexErrorKind, msg: string) =
  ## N40 (round-6 fix round 6, walker v104) — TOTALITY AT THE ALLOCATOR.
  ## Shared in-band degrade recorder for every classified-decline arm inside
  ## `allocateSym` (far below, and every OTHER caller that has no `Path`/
  ## `w: WalkCtx` in scope — `rawAnyAstOf` immediately below this proc,
  ## reached from `sortOfTuple`/`heapValueSort`, is one such caller;
  ## Round-6 N41): previously each of these arms `raise`d a dedicated
  ## `Symex*Error`/`SymexClassifiedDegradeError` carrier directly. Three
  ## successive slices (N36/N37/N39) tried to guard `allocateSym`'s
  ## individual raw-raise sites at each CALLER instead — every slice found a
  ## further unguarded caller (`isVariantConstructSym`, `lowerVariantLit`,
  ## then N40's own spot-check: `runtime_heap.nim`'s heap-deref-read/write
  ## paths, `runtime_closures.nim`'s lambda param/return allocation,
  ## `freshRetSym`'s call-return sites, `lowerHofCall`'s fold accumulator —
  ## an open-ended list `allocateSym` has ~70 call sites across this
  ## codebase). Per-caller guarding does not scale and is not auditable by
  ## construction (nothing stops a 71st caller from being added unguarded).
  ## This slice retires that strategy: `allocateSym` itself never raises for
  ## classifiable input again (see its own doc-comment addendum at its
  ## definition) — totality lives at the ONE place that can enforce it for
  ## every caller at once.
  ##
  ## LAYOUT (item 3, round-6 re-review): this proc used to sit far below —
  ## right above `allocateSym` — while a separate one-line forward
  ## declaration lived here (immediately after `syncAllocDegradeSawUnknown`'s
  ## own forward declaration) purely so `rawAnyAstOf` could call it before
  ## reaching the real definition. `allocDegrade`'s own body has no
  ## dependency on anything declared between here and `allocateSym`
  ## (`loweringDegradeErrors`/`loweringDidDegrade` are threadvars declared
  ## above this point; `syncAllocDegradeSawUnknown` is the SAME
  ## `WalkCtx`-circularity forward declaration immediately above) — so the
  ## fwd-decl/definition split was pure layout debt, not a real dependency
  ## cycle. Consolidated: this IS the definition now, living beside every
  ## other early-foundations `sync*` forward declaration it depends on; no
  ## second declaration of this proc exists anywhere else in the file.
  ##
  ## SINK CHOICE (the open design question this slice had to resolve): two
  ## existing in-band sinks precede this one, reached from two DIFFERENT
  ## calling contexts --
  ##   (a) `loweringDegradeErrors`/`loweringDidDegrade` (ADR-0023/SND-3) --
  ##       drained by `drainPendingLowerEffects` at every `lower()`/
  ##       `lowerBool()` call site inside `walk`, forking the SURVIVING
  ##       PATH's `uncertain = true` (SND-1's precise per-path taint) in
  ##       addition to `w.sawUnknown`. Correct for `allocateSym` callers
  ##       reached FROM INSIDE `lower()` (`lowerVariantLit`, `buildClosure`/
  ##       `paramSorts`, `lowerHofCall`'s fold-accumulator degrade, etc.) --
  ##       the NEXT `lower()` call at that same statement drains it.
  ##   (b) `w.walkDegradeErrors`/`w.sawUnknown` (+ `forkPathTainted`) --
  ##       written directly by WALK-level statement handlers
  ##       (`isVariantConstructSym`'s two budget checks) that have `w`/
  ##       `Path` in scope but never call `lower()` around the allocation
  ##       itself.
  ## `allocateSym` has NEITHER a `Path` NOR (in most callers) a `lower()`
  ## wrapper in scope -- it is a bare recursive allocator. Auditing every
  ## walk-time DIRECT caller (`isVariantConstructSym`'s per-fork field loop,
  ## `runtime_heap.nim`'s three sites, `freshRetSym`'s five call-return
  ## sites) confirmed NONE of them wrap the allocation in a `lower()` call
  ## that would drain sink (a) afterward -- sink (a) alone would leak the
  ## taint un-drained into whatever unrelated `lower()` call happens next
  ## (misattributed to the wrong statement/path) or, if none follows before
  ## the walk ends, LOST entirely -- exactly the silent-loss hazard this
  ## whole fix class exists to close. Sink (b) is unusable here for the
  ## opposite reason: `allocateSym` has no `w`/`Path` parameter and adding
  ## one would ripple through all ~70 call sites, defeating the point of
  ## fixing totality in ONE place.
  ##
  ## RESOLUTION: write BOTH effects directly, unconditionally, at the
  ## instant of degrade (this proc) --
  ##   1. `loweringDegradeErrors`/`loweringDidDegrade` still fire, so a
  ##      `lower()`-context caller keeps the PRECISE per-path SND-1 taint
  ##      it already had (no regression for `lowerVariantLit`'s own shape).
  ##   2. `currentWalkCtxPtr` (the threadvar every walk sets to `addr w` for
  ##      exactly this "no `w` in scope but a walk is active" situation --
  ##      the SAME idiom already used at `lowerHofCall`'s filter/map/fold
  ##      degrade sites, runtime.nim ~9348/9366/9387/9414) has
  ##      `.sawUnknown` set to `true` DIRECTLY, IMMEDIATELY, synchronously
  ##      -- not deferred to a later drain. This is "immediate-degrade-on-
  ##      alloc" semantics (sanctioned for non-`itSeq` kinds per this
  ##      slice's own design brief): the run is marked degraded the MOMENT
  ##      an unallocatable value is allocated, regardless of whether
  ##      anything ever reads it. This is NOT a new precision loss relative
  ##      to the pre-N40 status quo -- `isVariantConstructSym`'s own N39
  ##      guard and `lowerVariantLit`'s own N39 guard ALREADY degrade
  ##      unconditionally on allocation (never gated on a later read), so
  ##      this matches established, audited precedent rather than
  ##      introducing a new over-approximation.
  ## Effect (2) makes silent loss STRUCTURALLY IMPOSSIBLE: `currentWalkCtxPtr`
  ## is non-nil for the ENTIRE duration of every walk-time reachable code
  ## path (set immediately before `walk` begins, cleared only after
  ## `runSymexImpl` returns -- see its own threadvar doc comment), and the
  ## ONLY other `allocateSym`-calling context (the pre-walk param-entry
  ## boundary) no longer reaches these arms at all as of this slice (item 3
  ## of the design: a `unallocatableFieldIssue` pre-check RAISES directly,
  ## before `currentWalkCtxPtr` is even set -- see `raiseParamAllocIssue`
  ## below). So whichever of the two sinks actually applies, `w.sawUnknown`
  ## ends up `true` before the walk can report a verdict -- Invariant 3 is
  ## satisfied unconditionally, not contingent on a caller remembering to
  ## drain anything. Deliberately NOT a `raise`: unwinding from inside
  ## `allocateSym` (itself often called from deep inside `lower()`'s own
  ## recursion, or straight from a `walk`-level statement handler) is
  ## EXACTLY the C-backend goto-exception hazard ADR-0023/SND-3 exists to
  ## ban, and B7r2 additionally confirmed even a NON-top-level `try`/`except`
  ## around a walk-reachable recursive call silently ELIDES the exception on
  ## this toolchain -- ordinary control flow (no raise, no catch) is the
  ## only form proven safe.
  ## RFC-0005 S1: effect (2) below is now DERIVED rather than written — the
  ## `loweringDegradeErrors` entry `lowerDegrade` records is a drained
  ## `sevError`, and `runSymexImpl` derives `w.runTaint` from exactly those
  ## entries, so the immediate/global run mark this proc used to sync through
  ## `currentWalkCtxPtr` (`syncAllocDegradeSawUnknown`, retired) holds by
  ## construction the instant the error is recorded — still unconditional,
  ## still not contingent on any drain.
  lowerDegrade(kind, msg)

proc rawAnyAstOf*(sv: SymVal): RawZ3Ast =
  ## The raw ast of ANY base SymVal that may underlie a distinct type — used
  ## only to derive the base sort for the inject/eject func-decl signatures
  ## (works for FP/String bases too, where bijectivity is skipped).
  case sv.kind
  of svInt:     sv.zi.raw
  of svBool:    sv.bo.raw
  of svBV8:     sv.bv8.raw
  of svBV16:    sv.bv16.raw
  of svBV32:    sv.bv32.raw
  of svBV64:    sv.bv64.raw
  of svFloat32: sv.fp32.raw
  of svFloat64: sv.fp64.raw
  of svString:  sv.str.raw
  of svDistinct: sv.distinctAst.raw   ## nested distinct base
  of svRef:     sv.refAst.raw         ## Phase 15 R9: ref-typed heap field value
  of svPtr:     sv.ptrAst.raw         ## Phase 15 R9: ptr-typed heap field value
  of svBitSet:  sv.bsRaw.raw          ## RFC-0005 S8bq: one bit-vector
  of svTable, svSet, svSeq, svArray, svTuple, svVariant, svMultiVariant,
     svClosure, svUninterpRef:
    # Round-6 N41: `svTable`/`svSet` are COMPOUND values (a data `Z3Array`
    # plus a separate present `Z3Array` — see `allocateSym`'s `itTable`/
    # `itSet` arms — never a single scalar ast), so there is no sound
    # representative leaf here, REGARDLESS of whether the underlying
    # Table/Set shape itself is otherwise supported: this arm is reached for
    # a perfectly VALID `Table[string, int]`/`HashSet[int]` too, not just an
    # unsupported key/value/element shape (N40's `allocDegrade` calls inside
    # `allocateSym` classify THAT gap already — this is a DIFFERENT,
    # downstream one: sort-DERIVATION for a closure param/return leaf
    # (`sortOfTuple`) or a heap array's value sort (`heapValueSort`,
    # `runtime_heap.nim`) fundamentally cannot flatten a compound value to a
    # single leaf). Previously an untagged `raise newException(ValueError,
    # ...)` here crashed UNCAUGHT all the way to the top-level
    # `runSymexImpl` catch-all (`weInternalWalkerFault`, a WHOLE-RUN degrade
    # with no per-path precision) for both the lambda-param/return family
    # and the heap-deref family, masking the itTable/itSet family behind the
    # walker's generic "the walker itself hit a bug" carrier. `allocDegrade`
    # (N40's own chokepoint) reports the classified kind instead of
    # raising — per-path SND-1 taint when reached from inside `lower()`
    # (`sortOfTuple`'s closure-construction callers), immediate whole-walk
    # `sawUnknown` otherwise (see `allocDegrade`'s own doc comment) — and
    # `allocDegrade` never raises, so control returns here normally. The
    # BV64-zero fallback ast is the SAME "safe unconstrained filler" shape
    # `lowerClosureCall`'s own `ceClosureUnknownCallee` arm already returns
    # elsewhere in this file: its CONTENT is never trustworthy, only its
    # SORT needs to be well-formed enough for the caller's `Z3_get_sort`/
    # `Z3_mk_array_sort`/`Z3_mk_func_decl` to complete without a Z3-level
    # error — `allocDegrade` has already forced the verdict to `sxUnknown`
    # regardless of what happens with it downstream (Invariant 3).
    #
    # N47 (round-6 raise-class-audit category-d closure): the remaining
    # composite kinds `svSeq`/`svArray`/`svTuple`/`svVariant`/
    # `svMultiVariant`/`svClosure`/`svUninterpRef` were previously an
    # untagged bare `raise newException(ValueError, ...)` in this proc's
    # `else` arm, category-d "uncertain reachability" pending a dedicated
    # check. CONFIRMED live via a container probe: an ordinary
    # `type SeqId = distinct seq[int]` PARAMETER (no heap/ref involvement at
    # all) reaches `allocDistinctSym`'s composite-base branch (`runtime.nim`,
    # `baseIsDecidable` is false for `itSeq`), which calls
    # `rawAnyAstOf(baseRep)` on the `svSeq` base representative to derive its
    # Z3 sort for the (bijectivity-skipped) inject/eject func-decls — the
    # SAME "no single-leaf sort" shape `svTable`/`svSet` already handle
    # above, just reached from a *different* caller (`allocDistinctSym`
    # rather than `sortOfTuple`/`heapValueSort`). Folded into this arm rather
    # than kept as a separate raise: identical hazard, identical fix.
    allocDegrade(seUnsupportedCompoundSortLeaf,
      "closure/heap/distinct-base sort derivation reached a compound value (" &
      plainEnglishSymValKind(sv.kind) &
      ") with no single-leaf Z3 sort representation " &
      "(seUnsupportedCompoundSortLeaf)")
    keepRaw(mkBitVec[64](0'i64))   # RFC-0016 CRH-07: the temporary's raw dangled

proc probeContext*(): Z3Context =
  ## RFC-0005 S8bp. A fresh Z3 context for a per-thread kind probe's terms
  ## (`seqCapKinds`, `byteDomainKinds`, `intDivDeclKinds`,
  ## `heapChainKinds`, `theoryFreeSimple`; batch 7: S8bq's `uninitKinds`,
  ## S8ax's `storeDeclKind` / `iteDeclKind`, batch 4's `constArrayDeclKind`,
  ## and S8bu's `int2bvDeclKind` / `eqDeclKind` / `selectDeclKind`). A decl kind is the linked Z3's,
  ## the same in every context, so it is read where it changes nothing:
  ## built in the walk's context, a probe's terms (and `theoryFreeSimple`'s
  ## check) made a thread's first walk search differently from its later
  ## ones (`tsymex_rfc0005_s8bp_isolation`). Not made the thread's current
  ## context.
  let prev = currentContext()
  result = newContext()
  setCurrentContext(prev)

const termWalkMaxDepth* = 256
  ## RFC-0005 S8ct. The deepest term a recursive walk of a Z3 term takes. A term
  ## can be far deeper than the stack or Nim's call depth limit allow, and either
  ## ends the process. Each walk gives the answer that claims nothing past this.
  ## 256 levels is under the `nimFrameReserve` a solve keeps, at 1 or 2 frames a
  ## level.

proc lambdaOver*(ctx: Z3Context; iVar: Z3Int; body: Z3AnyAst): Z3AnyAst =
  ## RFC-0005 S8bc. `lambda iVar. body`, as `iekSeqSlice` builds its view
  ## (beta-reduced by Z3 at every select; no quantifier). Wrapped at once.
  var iApp = ctx.checkErr Z3_to_app(ctx.raw, iVar.raw)
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_lambda_const(ctx.raw, 1'u32,
    cast[ptr UncheckedArray[RawZ3App]](addr iApp), body.raw))
