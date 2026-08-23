# runtime_heap.nim — Cluster R include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_heap.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents (CR-7-deeper Stage 8+):
#   Cluster R heap helpers (moved from runtime.nim — only used within
#   this cluster or in runtime_heap.nim's own code):
#     refPointeeTypeId, allocRefSort — bodies (forward-decls remain in runtime.nim)
#     freshRef, assertFreshness, pcImpliesNonNil
#     heapValueSort, mkHeapArrayVar, liftHeapValue, heapSelect, fieldHeapKey
#     heapDepthExhausted, nilDerefFork
#   `walkHeapArm(stmt, paths, w)` — the `walk()` dispatch arm for
#   `isDeref`, `isNew`, `isDerefWrite` (Cluster R, Stage 7 / Stage 8, CR-7).
# `isIndex` is left inline in `walk()` because it handles multiple container
# theories and cannot be cleanly attributed to the heap cluster alone.
# `buildHeapSnapshot` stays in runtime.nim (called from extractWitness before
# the heap include point).
# Placement in runtime.nim: between `walkBlock` and `walk`'s body
# (after `walk`'s forward-decl and before `walk`'s body).

proc refPointeeTypeId*(pointeeTy: IRType): string =
  ## Phase 15 R1; flipped at Cluster H Step B (ADR-0022). A stable
  ## per-pointee-type identifier used to key the `Ref_T` sort + heap array +
  ## nil const (and, via `fieldHeapKey`, the per-field heap arrays — an
  ## object's ref sort and its field-array keys must agree, so the same
  ## preference applies uniformly to `refPointeeTypeId(objTy)` calls too).
  ##
  ## Prefer the pointee's `nominalId` (a canonical, symbol-unique nominal
  ## identity — Cluster H Step A) over the structural `$pointeeTy` rendering
  ## when the pointee is a named object (`itTuple` with a non-empty
  ## `nominalId`). Two `IRType`s for the SAME nominal object can carry
  ## DIFFERENT structural renderings — e.g. a bare ref's full-field pointee
  ## vs. a recursive field's empty-fielded placeholder (`namedRefPlaceholder`,
  ## built to break compile-time self-reference) — yet they denote the same
  ## Nim type and must key the SAME `Ref_T` sort. Keying on `nominalId`
  ## unifies them; keying on `$pointeeTy` (the pre-Step-B behaviour) would
  ## mint two distinct sorts and a Z3 sort mismatch on the first cross-use
  ## (degrading to `sxUnknown`). That unification becomes reachable once a
  ## bare named-ref parameter itself routes through `itRef` (Step C); Step B
  ## proves the mechanism keeps inline-ref sort naming consistent first.
  ## Anonymous tuples and non-object pointees have no `nominalId` and keep
  ## the structural rendering (unchanged behaviour).
  let base = if pointeeTy.kind == itTuple and pointeeTy.nominalId.len > 0:
               pointeeTy.nominalId
             else:
               $pointeeTy
  result = base
  for i in 0 ..< result.len:
    if result[i] notin {'a'..'z', 'A'..'Z', '0'..'9', '_'}:
      result[i] = '_'

proc allocRefSort*(ctx: Z3Context, pointeeTy: IRType): RawZ3Sort =
  ## Phase 15 R1 (ADR-0010). Return the per-walker `Ref_<typeId>` uninterpreted
  ## sort for `pointeeTy`, allocating + caching it (and its `nil_<typeId>` const)
  ## on first use. Idempotent per (typeId, run) via `currentRefSorts`.
  ##
  ## G4 footgun discipline: pin the fresh sort with a `Z3_inc_ref` over its
  ## `Z3_sort_to_ast` — otherwise the heavy heap/const allocation that follows
  ## lets Z3 garbage-collect the un-referenced sort, corrupting every array
  ## sort / const that names it (the G4 SIGSEGV: the sort read back as
  ## `Z3_UNKNOWN_SORT`). The ref is held for the whole run (never dec'd — the
  ## context is torn down at run end).
  let typeId = refPointeeTypeId(pointeeTy)
  if not currentRefSorts.hasKey(typeId):
    let sortName = "Ref_" & typeId
    let sort = mkUninterpretedSort(ctx, sortName)
    Z3_inc_ref(ctx.raw, Z3_sort_to_ast(ctx.raw, sort.raw))
    currentRefSorts[typeId] = sort.raw
    # The distinguished `nil_<typeId>` constant of this ref sort (ADR-0010 §Nil).
    let nilSym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
      ("nil_" & typeId).cstring)
    let nilRaw = ctx.checkErr Z3_mk_const(ctx.raw, nilSym, sort.raw)
    let nilConst = wrap[Z3AnyAst](ctx, nilRaw)
    currentNilConsts[typeId] = nilConst
    # CR-9 Stage 4: also populate WalkerStatics.refSorts/nilConsts when a walk
    # is active, so the live WalkerStatics is the authoritative source during
    # the walk and the post-walk mirror loop becomes redundant.
    syncRefSortEntry(typeId, sort.raw, nilConst)
  currentRefSorts[typeId]

proc freshRef*(ctx: Z3Context, refSort: RawZ3Sort, typeId: string,
               path: Path): Z3AnyAst =
  ## Phase 15 R2 (ADR-0010). Mint a FRESH `Ref_T`-sorted const for a `new T`
  ## allocation on `path`. Increment the per-path `allocCounters[typeId]` (R1b
  ## already threads + max-merges this across call boundaries, so the counter
  ## is monotone along a path and a post-call caller alloc can't collide with a
  ## callee one) and derive a const named `"ref_<typeId>_<n>"` (n = the NEW
  ## counter value) via the raw `Z3_mk_const` discipline (G4 — `allocateSym`
  ## has no typed phantom for a runtime-known uninterpreted sort). The caller
  ## (`walk(isNew)`) binds the result in the env and calls `assertFreshness`.
  let n = path.allocCounters.getOrDefault(typeId, 0) + 1
  path.allocCounters[typeId] = n
  let name = "ref_" & typeId & "_" & $n
  wrap[Z3AnyAst](ctx, rawConstOf(ctx, refSort, name))

proc assertFreshness*(ctx: Z3Context, path: Path, typeId: string,
                      newRef: Z3AnyAst, settings: SymexSettings) =
  ## Phase 15 R2 (ADR-0010). Constrain a freshly allocated `newRef` to be
  ## DISTINCT from `nil` and from every PRIOR live ref of this pointee type on
  ## `path` (the counter-based distinctness guarantee). All GROUND inequalities
  ## (`Z3_mk_eq` negated) — NEVER a universal-∀ over the uninterpreted ref sort
  ## (the G4 MBQI hang lesson). Prior live refs are read from
  ## `path.liveRefs[typeId]`; `newRef` is appended after.
  ##
  ## The `newRef != nil` pin is ALWAYS emitted (a single assertion — a fresh
  ## allocation is never nil). The pairwise `newRef != prior` inequalities are
  ## CAPPED: once `path.freshnessAssertCount` would exceed
  ## `settings.maxFreshnessAssertions` (0 = unlimited) the remaining
  ## inequalities are SKIPPED and a `heFreshnessCapExceeded` (sevHint) is
  ## emitted ONCE for this `new T`. This is a SOUND over-approximation — Z3 may
  ## then allow `newRef` to alias an un-asserted prior ref, which is
  ## conservative (more models), never a false UNSAT.
  template mkNeq(a, b: Z3AnyAst): Z3Bool =
    not wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_eq(ctx.raw, a.raw, b.raw))
  # 1. newRef != nil (always — not pairwise, not capped).
  if currentNilConsts.hasKey(typeId):
    path.pc.add mkNeq(newRef, currentNilConsts[typeId])
  # 2. newRef != every prior live ref of this sort on THIS path (capped).
  let priors = path.liveRefs.getOrDefault(typeId, @[])
  let cap = settings.budget.maxFreshnessAssertions
  var capHitThisAlloc = false
  for prior in priors:
    if cap > 0 and path.freshnessAssertCount >= cap:
      capHitThisAlloc = true
      break
    path.pc.add mkNeq(newRef, prior)
    inc path.freshnessAssertCount
  if capHitThisAlloc:
    let capHint = SymexErrorInfo(
      kind: heFreshnessCapExceeded, severity: sevHint,
      msg: "freshness-assertion cap (" & $cap & ") reached on this path for " &
           "ref type `" & typeId & "`: distinctness inequalities for further " &
           "`new T` allocations are skipped (sound over-approximation — Z3 may " &
           "allow aliasing beyond the cap, never a false UNSAT)")
    freshnessCapHints.add capHint          # threadvar: fallback for probe paths
    syncFreshnessCapHint(capHint)          # CR-9 Stage 5: also write to WalkCtx
  # 3. Record `newRef` as a live ref for subsequent allocations on this path —
  # BUT only if we haven't already hit the cap for this type. Once the cap is
  # hit, further refs are never asserted-distinct anyway (step 2 skips them),
  # so storing them is O(N) memory waste. Capping the list length here keeps
  # liveRefs[typeId] bounded at `cap` entries even when N allocations are made.
  # Soundness: the cap already approximates freshness (heFreshnessCapExceeded
  # hint documents this); not storing past-cap refs is consistent with that
  # documented over-approximation.
  let alreadyAtCap = cap > 0 and path.freshnessAssertCount >= cap
  if not alreadyAtCap:
    if path.liveRefs.hasKey(typeId):
      path.liveRefs[typeId].add newRef
    else:
      path.liveRefs[typeId] = @[newRef]

proc pcImpliesNonNil(ctx: Z3Context, pc: seq[Z3Bool],
                     refAst, nilConst: Z3AnyAst, typeId: string): bool =
  ## Phase 15 R5 (Cluster R, Depth-LOW-D4). The nil-fork SHORT-CIRCUIT. Shallow
  ## (single-level) AST pattern-match of the path condition `pc` for a constraint
  ## that ALREADY implies `refAst != nil` — so a nil sub-path would be UNSAT by
  ## construction and need not be forked. NO Z3 `check-sat` is issued (this is a
  ## pure structural scan; the soundness is by inspection of the asserted terms).
  ##
  ## Two patterns are recognised (both ground over the uninterpreted `Ref_T`):
  ##   1. `not(eq(refAst, nilConst))` — an explicit `p != nil`. This is ALSO the
  ##      exact term `assertFreshness` adds for a `new`-allocated ref (`newRef !=
  ##      nil`), so a freshly `new`-ed ref dereffed never forks a nil path.
  ##   2. `eq(refAst, ref_<typeId>_N)` — `p` is constrained equal to a fresh
  ##      `new`-allocated ref (provably non-nil via pattern 1 on that fresh ref).
  ##      The fresh-ref operand is recognised by its decl name `ref_<typeId>_`.
  ## Both operand orders are matched (`eq` is symmetric).
  for term in pc:
    if getAstKind(term) != akApp: continue
    let dn = declName(ctx, getAppDecl(term))
    if dn == "not" and getAppNumArgs(term) == 1:
      let inner = getAppArg(term, 0)
      if getAstKind(inner) == akApp and
         declName(ctx, getAppDecl(inner)) == "=" and getAppNumArgs(inner) == 2:
        let a = getAppArg(inner, 0)
        let b = getAppArg(inner, 1)
        if (astEqual(a, refAst) and astEqual(b, nilConst)) or
           (astEqual(b, refAst) and astEqual(a, nilConst)):
          return true   ## pattern 1: explicit `p != nil` (incl. freshness pin)
    elif dn == "=" and getAppNumArgs(term) == 2:
      let a = getAppArg(term, 0)
      let b = getAppArg(term, 1)
      # `eq(p, fresh)` where one side is `refAst` and the other is a fresh ref
      # const (`ref_<typeId>_N`, asserted non-nil at its own allocation).
      let freshPrefix = "ref_" & typeId & "_"
      if astEqual(a, refAst) and getAstKind(b) == akApp and
         declName(ctx, getAppDecl(b)).startsWith(freshPrefix):
        return true   ## pattern 2: alias to a fresh non-nil ref
      if astEqual(b, refAst) and getAstKind(a) == akApp and
         declName(ctx, getAppDecl(a)).startsWith(freshPrefix):
        return true
  false

# ---- Phase 15 R1: logical-heap array helpers (ADR-0010) ----------------------
# These build/read the per-path `Z3Array[Ref_T, T_sym]` heap. They follow
# `allocateSym` because `heapValueSort` allocates a throwaway pointee SymVal to
# read its value sort (the G4 `baseRep` sort-probe idiom). Moved here from
# runtime.nim in CR-7-deeper Stage 8+ (only called from runtime_heap.nim).

proc heapValueSort(ctx: Z3Context, pointeeTy: IRType): RawZ3Sort =
  ## Phase 15 R1. The Z3 value sort of the heap array `Z3Array[Ref_T, T_sym]`
  ## for pointee type `pointeeTy` — i.e. the sort of the SymVal a deref yields.
  ## A throwaway prototype is allocated (its init constraints are discarded —
  ## only the sort is read), mirroring G4's `baseRep` sort probe.
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(pointeeTy, "__heapValSort", scratchPC)
  ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(proto))

proc mkHeapArrayVar(ctx: Z3Context, refSort: RawZ3Sort,
                    pointeeTy: IRType, name: string): Z3AnyAst =
  ## Phase 15 R1 (ADR-0010). Build a FREE `Z3Array[Ref_T, T_sym]` variable —
  ## the initial heap for one pointee type on one path. The key sort `Ref_T`
  ## is a RUNTIME uninterpreted sort, so the typed `mkArrayVar[K, V]` (which
  ## needs static K/V) cannot express it; we go through raw FFI
  ## (`Z3_mk_array_sort` + `Z3_mk_const`) and erase to `Z3AnyAst`. The result
  ## is a GROUND free array — every `select` on it is decidable (QF_AUFLIA-ish);
  ## NO universal-∀ axiom is ever asserted over the uninterpreted sort (the G4
  ## hang lesson).
  let valSort = heapValueSort(ctx, pointeeTy)
  let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, valSort)
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

proc liftHeapValue(ctx: Z3Context, valRaw: RawZ3Ast, pointeeTy: IRType): SymVal =
  ## Phase 15 R1. Wrap the raw value-sorted ast produced by a heap `select`
  ## into the SymVal variant for `pointeeTy`, so the dereffed value flows back
  ## into the ordinary `lower`/`symEq`/binop machinery. R1 covers the primitive
  ## pointees the heap-select can yield directly (int/bool/float); composite
  ## pointees (`ref object`, `seq[ref T]`) land R3+.
  case pointeeTy.kind
  of itInt:
    case pointeeTy.width
    of 8:  liftBV(wrap[Z3BitVec[8]](ctx, valRaw),  pointeeTy.signed)
    of 16: liftBV(wrap[Z3BitVec[16]](ctx, valRaw), pointeeTy.signed)
    of 32: liftBV(wrap[Z3BitVec[32]](ctx, valRaw), pointeeTy.signed)
    of 64: liftBV(wrap[Z3BitVec[64]](ctx, valRaw), pointeeTy.signed)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always 8/16/32/64)]
        "liftHeapValue: unsupported int width " & $pointeeTy.width)
  of itBool:   ofBool(wrap[Z3Bool](ctx, valRaw))
  of itFloat32: SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, valRaw))
  of itFloat64: SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, valRaw))
  of itUninterp:
    # N42 SPOT-PROBE FINDING (temporary — see N42 slice commit for the
    # permanent version of this comment): `itUninterp` had NO arm here,
    # which crashed (uncaught `SymexRefUnresolvedError`) on ANY heap-deref
    # read of a field/pointee whose type degraded to the ownership/
    # unsupported-param/unsupported-witness placeholder family
    # (`allocateSym`'s `itUninterp` arm always allocates that placeholder's
    # VALUE as `svBool` — see its own doc comment — so lifting it back here
    # the same way `itBool` does is the correct, symmetric mirror). This
    # crash was ACCIDENTALLY masking the per-path-taint gap under probe
    # (top-level catch -> sxUnknown either way) — added to make that gap
    # empirically observable.
    ofBool(wrap[Z3Bool](ctx, valRaw))
  of itRef, itPtr:
    # Phase 15 R9 (ADR-0010). A REF-TYPED field (e.g. the recursive `next: Node`
    # of a linked list) — its R6 field-split heap is `Z3Array[Ref_Obj, Ref_T]`,
    # so a `select` yields a `Ref_T`-sorted ast which we lift back into an
    # `svRef`/`svPtr` carrying its pointee. The pointee is the (finite, named)
    # placeholder the field-classifier built (`classifyFieldType`), so a deeper
    # `n.next.next` resolves the ref through the ordinary heap machinery (its
    # `Ref_<name>` sort keys on `refPointeeTypeId(pointee)`). NO heap is read
    # here — the value IS the next address; the deeper deref reads the heap.
    let inner = if pointeeTy.kind == itRef: pointeeTy.refPointeeTy
                else: pointeeTy.ptrPointeeTy
    let valAny = wrap[Z3AnyAst](ctx, valRaw)
    if pointeeTy.kind == itRef:
      SymVal(kind: svRef, refAst: valAny, refPointee: inner)
    else:
      SymVal(kind: svPtr, ptrAst: valAny, ptrFamily: true, ptrPointee: inner)
  else:
    # N46-followup (round-6 re-review, walker v113): was `raise (ref
    # SymexRefUnresolvedError)`, LEDGERED-LIVE. CONFIRMED live by a
    # dedicated probe (a `ref`/`ptr`-to-`string` field deref, the most
    # ordinary shape imaginable): the raise unwinds through
    # `walkHeapArm`/`walk`/`walkBlock` all the way to `runSymexImpl`'s
    # top-level catch, aborting the WHOLE walk. When that catch fires AFTER
    # an unrelated sibling path already reached the target (or BEFORE a
    # later, hazard-free branch gets a chance to), the walk reports
    # `sxUnknown` for a program whose correct verdict is `sxSat` -- the
    # N31/ADR-0023 SND-3 silent-loss class, reproduced RED/GREEN by this
    # slice's own SUT probe (see `tests/tsymex_r6_heap_raise_totality.nim`).
    # In-band degrade instead: `allocDegrade` records the classified
    # `heUnresolvedRef` and marks the run degraded immediately/globally
    # (Invariant 3), then a FRESH placeholder SymVal of the SAME pointee
    # type keeps the Z3 API call chain type-sound (mirrors `seqElemAt`'s own
    # unsupported-elem-kind idiom, `runtime.nim`) -- its CONTENT is never
    # trustworthy, only its SORT needs to be well-formed. Every
    # `heapSelect`/`liftHeapValue` call site in this file drains the pending
    # degrade into the surviving path's own `uncertain` flag (SND-1)
    # immediately after the select, so a path whose OWN read just degraded
    # can never mint a bogus winning `sxSat`.
    allocDegrade(heUnresolvedRef,
      "deref of `ref/ptr " & $pointeeTy & "` (non-primitive pointee) " &
      "not yet modeled (Cluster R R1 covers primitive pointees; " &
      "composite pointees — ref object / seq[ref T] — land R3+)")
    var freshLiftPc: seq[Z3Bool]
    allocateSym(pointeeTy, "__liftHeapValueUnsupported", freshLiftPc)

proc heapSelect(ctx: Z3Context, heap: Z3AnyAst, refAst: Z3AnyAst,
                pointeeTy: IRType): SymVal =
  ## Phase 15 R1 (ADR-0010). The GROUND heap read `select(heap, p)` — a single
  ## `Z3_mk_select` over the free heap array at the abstract address `p`. The
  ## result is the value-sorted ast; lift it into a SymVal. This is the whole
  ## of R1's deref: a decidable array select, NO quantifier (the G4 lesson —
  ## a ∀ over the uninterpreted Ref_T sort would HANG Z3).
  let valRaw = ctx.checkErr Z3_mk_select(ctx.raw, heap.raw, refAst.raw)
  liftHeapValue(ctx, valRaw, pointeeTy)

proc fieldHeapKey*(objTy: IRType, field: string): string =
  ## Phase 15 R6 (ADR-0010). The field-split heap key for `(objTy, field)`. An
  ## object pointee cannot be a single Z3 array VALUE sort (there is no Z3 tuple
  ## sort — C0-ADR), so each field gets its OWN heap array `Z3Array[Ref_T,
  ## <fieldSort>]`, keyed by the object's `refPointeeTypeId` + the field NAME
  ## (unique across the flat inheritance layout — Nim forbids field shadowing).
  ## The `Ref_T` SORT still keys on the OBJECT (`refPointeeTypeId(objTy)`), so
  ## every field of one ref shares a single abstract address (aliasing observed).
  refPointeeTypeId(objTy) & "__" & field

proc heapDepthExhausted(p: Path, w: var WalkCtx): bool =
  ## Phase 15 R9. The SOLE heap-depth check site, shared by `of isDeref:` and
  ## `of isDerefWrite:`. INCREMENT `p.heapDepth` (per-path; threaded/deep-copied
  ## at every fork via H1), then test it against the effective limit. On
  ## exhaustion: mark the path uncertain, record a classified `heDepthExhausted`
  ## (sevError) into the run sink, signal `w.sawUnknown`, and return `true` so the
  ## caller HALTS this path (binds nothing, contributes no survivor → sxUnknown).
  ## Otherwise return `false` and the deref/store proceeds normally. Per-path: a
  ## shallower path's deref does not exhaust and continues.
  inc p.heapDepth
  let limit = effectiveHeapDepthLimit(w.settings)
  if limit > 0 and p.heapDepth >= limit:
    p.uncertain = true
    let depthErr = SymexErrorInfo(
      kind: heDepthExhausted, severity: sevError,
      msg: "heap depth budget of " & $limit & " exceeded")
    heapDepthErrors.add depthErr    # threadvar: kept for compatibility
    w.heapDepthErrors.add depthErr  # CR-9 Stage 5: LIVE WalkCtx field
    w.sawUnknown = true
    return true
  false

proc nilDerefFork(p: Path, refAst: Z3AnyAst, elemTy: IRType,
                  w: var WalkCtx): seq[Path] =
  ## Phase 15 R5 (Cluster R, ADR-0010). Fork a `p[]` deref (READ or WRITE) of a
  ## possibly-nil ref/ptr `p` into:
  ##   * a NIL sub-path — `p == nil` asserted — which is the NilAccessDefect
  ##     finding (conceptually `sxRaised("NilAccessDefect")`, a Nim `Defect`). It
  ##     is GATED on the `stkNilAccess` target: only under that target is the
  ##     defect witness (`p == nil`) solved and recorded; under any other target
  ##     the nil path terminates silently. The nil path is TERMINAL — it never
  ##     continues into the select/store.
  ##   * a NON-NIL continuation — `p != nil` asserted — RETURNED to the caller to
  ##     continue the ordinary deref (the R1 select / R4 store).
  ##
  ## SHORT-CIRCUIT (path-explosion guard): if `p.pc` already implies `p != nil`
  ## (an explicit `p != nil`, or `p` aliases a fresh `new`-allocated ref — see
  ## `pcImpliesNonNil`), the nil path is UNSAT by construction, so the fork is
  ## SKIPPED entirely and `p` is returned UNCHANGED (no redundant `p != nil`
  ## assertion, no nil sub-path). A freshly `new`-allocated ref dereffed thus
  ## never forks a nil path — essential now that every deref would otherwise fork.
  let ctx = w.z3
  let typeId = refPointeeTypeId(elemTy)
  # Materialise the sort + nilConst if a prior op hasn't (e.g. the very first
  # touch of this pointee type is a deref); allocRefSort writes to both
  # threadvar and WalkerStatics.nilConsts (via syncRefSortEntry).
  discard allocRefSort(ctx, elemTy)
  # CR-9 Stage 4: read nilConsts from live WalkerStatics (nilDerefFork always
  # runs inside a walk arm — currentWalkCtxPtr != nil guaranteed here).
  let nilConst =
    if currentWalkCtxPtr != nil:
      cast[ptr WalkCtx](currentWalkCtxPtr)[].statics.nilConsts[typeId]
    else:
      currentNilConsts[typeId]
  # SHORT-CIRCUIT: a pc-implied non-nil ⇒ no nil path, no extra constraint.
  if pcImpliesNonNil(ctx, p.pc, refAst, nilConst, typeId):
    return @[p]
  # `p == nil` (the defect) and `p != nil` (the continuation), ground over Ref_T.
  let eqNil = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_eq(ctx.raw, refAst.raw, nilConst.raw))
  # NIL sub-path — NilAccessDefect fork. Phase 16 D1a unconditional.
  discard forkDefect(p, eqNil, "NilAccessDefect", none(string), w)
  # NON-NIL continuation: assert `p != nil` and continue the deref normally.
  @[forkPath(p, p.pc & @[not eqNil], p.env)]

proc refVariantDiscRangeClause(objTy: IRType, discSV: SymVal): Option[Z3Bool] =
  ## ADR-0013 D4.5 (Slice 1). Build the disc-range disjunction for a
  ## ref-to-variant pointee, mirroring `allocateSym(itVariant)` logic.
  ## Asserts `OR(disc==arm0_ord, disc==arm1_ord, …)` so Z3 never picks an
  ## illegal discriminant ordinal. For a bool disc this is a tautology (no-op
  ## for Z3); for enum/int discs it is load-bearing (Slice 2 exercises it).
  ## Returns `none` for a degenerate variant with no arms (should not occur).
  proc discEq(tagOrd: int64): Z3Bool =
    case discSV.kind
    of svBV8:  discSV.bv8  == mkBitVec[8](tagOrd)
    of svBV16: discSV.bv16 == mkBitVec[16](tagOrd)
    of svBV32: discSV.bv32 == mkBitVec[32](tagOrd)
    of svBV64: discSV.bv64 == mkBitVec[64](tagOrd)
    of svInt:  discSV.zi   == mkZ3IntLit(tagOrd)
    of svBool: discSV.bo   == mkBool(tagOrd != 0)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (ref-to-variant discriminator is always BV/Z3Int/Bool-allocated)]
        "refVariantDiscRangeClause: disc must be BV/Z3Int/Bool (got " &
        $discSV.kind & ")")
  var armEqClauses: seq[Z3Bool]
  var hasElse = false
  for arm in objTy.vArms:
    if arm.isElse:
      hasElse = true
      continue
    armEqClauses.add discEq(int64(arm.tagOrdinal))
  if hasElse:
    for dt in objTy.vDiscTags:
      var inNonElse = false
      for arm in objTy.vArms:
        if (not arm.isElse) and arm.tagOrdinal == dt.ord:
          inNonElse = true; break
      if inNonElse: continue
      armEqClauses.add discEq(int64(dt.ord))
  if armEqClauses.len == 0:
    return none(Z3Bool)
  var clause = armEqClauses[0]
  for k in 1 ..< armEqClauses.len:
    clause = clause or armEqClauses[k]
  some(clause)

proc degradeHeapArmForPath(p: Path, elemTy: IRType, retName,
                            placeholderTag: string): Path =
  ## Round-6 mechanical-debt slice: the shared per-path FORK half of the
  ## `allocDegrade` + fresh `allocateSym` + env-rebind + `forkPathTainted`
  ## idiom `walkHeapArm`'s READ-side `refSV.kind`-mismatch/multi-variant-
  ## pointee decline arms repeat (deref read, arm-field read, ref-to-multi-
  ## variant field read — each independently converted off a raw raise at
  ## walker v113/v113). The caller has ALREADY recorded the degrade via
  ## `allocDegrade(kind, msg)` at whatever granularity its own site calls
  ## for (once, statement-scoped, before the per-path loop for a decline
  ## that depends only on the statement's static type; or per-path, inside
  ## the loop, for a decline that depends on a per-path `lower()` result) —
  ## this helper does NOT call `allocDegrade` itself, so moving callers onto
  ## it cannot change how many `loweringDegradeErrors` entries a run
  ## accumulates. `elemTy`/`retName` are the field/pointee's own result type
  ## and the statement's bound name (`stmt.dRetName`); `placeholderTag` is
  ## the site's own fresh-const base name (kept per-site, not unified, so
  ## each degrade class stays independently greppable in a witness dump).
  ## The throwaway `pcOut` sink mirrors every other `allocateSym`-degrade
  ## caller: any init-side constraint `allocateSym` would deposit is
  ## discarded because this value is never trusted once the run is
  ## degraded.
  var freshPc: seq[Z3Bool]
  let placeholder = allocateSym(elemTy, placeholderTag, freshPc)
  var newEnv = p.env
  newEnv[retName] = placeholder
  forkPathTainted(p, p.pc, newEnv)

proc degradeHeapArmForPath(p: Path): Path =
  ## WRITE-side sibling of the 4-arg overload above: a write statement has
  ## no `dRetName`/`dwRetName` to bind, so the shared shape degenerates to
  ## "taint this path and DROP the write" — the pre-write env/heap carries
  ## forward unchanged (mirrors `isUnsupported`'s own walk-arm idiom for an
  ## unmodeled statement). Same "caller already called `allocDegrade`"
  ## contract as the read-side overload.
  forkPathTainted(p, p.pc, p.env)

proc walkHeapArm(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path] =
  ## Stage 7 (CR-7) Cluster R extraction. Called from `walk`'s case arm for
  ## `isDeref`, `isNew`, `isDerefWrite`. `heapSelect`/`allocRefSort`/`freshRef`/
  ## `assertFreshness`/`nilDerefFork`/`buildHeapSnapshot` are already named procs
  ## and are NOT moved here — they are called from within the arm bodies.
  ## `isIndex` is left inline in `walk` because it handles multiple container
  ## theories (Table/seq/array/ref) and cannot be cleanly attributed to heap alone.
  ##
  ## Shared-symbol dependencies for Stage 8 include-ordering:
  ##   heapDepthExhausted, lowerLeafInExpr, nilDerefFork, allocRefSort,
  ##   heapSelect, mkHeapArrayVar, fieldHeapKey, refPointeeTypeId,
  ##   freshRef, assertFreshness, lowerInExpr, allocateSym, liftBV, intToBv,
  ##   forkPath, wrap, Z3_mk_store, rawAnyAstOf, ptrFamilyHints,
  ##   currentHeapDerefVals, SymexErrorInfo, hePtrFamily, sevHint,
  ##   SymexRefUnresolvedError, SymexRefVariantUnsupportedError,
  ##   refVariantDiscRangeClause
  case stmt.kind
  of isDeref:
    # Phase 15 R1 (ADR-0010). `p[]` — a GROUND heap read. For each path:
    #   1. resolve the ref/ptr SymVal `p` (its `Ref_T`-sorted abstract address);
    #   2. lazily materialise `path.heaps[typeId]` to a fresh free
    #      `Z3Array[Ref_T, T_sym]` if this is the first deref of this pointee
    #      type on this path (heap is PER-PATH; the sort is PER-WALKER);
    #   3. `select(heap, p)` → the value-sorted ast → lift into a SymVal;
    #   4. bind it to the fresh let-name `stmt.dRetName`.
    # The select is decidable (QF_AUFLIA-ish); NO quantifier is asserted (the
    # G4 hang lesson). Phase 15 R5: the deref FORKS a nil path first (the
    # NilAccessDefect) — `nilDerefFork` emits the nil finding (gated on the
    # stkNilAccess target) and returns the NON-NIL continuation(s) on which the
    # select proceeds; a freshly-allocated / `p != nil`-constrained ref is
    # short-circuited (no fork). heapDepth bounding lands R9.
    let ctx = w.z3
    # Phase 15 R6: a FIELD deref (`p.field`, `dField != ""`) keys the `Ref_T`
    # SORT + nil-fork on the OBJECT (`dObjTy`) — one ref → one address shared by
    # every field — and the per-field heap ARRAY on `fieldHeapKey(dObjTy, field)`
    # with VALUE sort = the field type (`dElemTy`). A bare `p[]` keeps the R1
    # path (sort + heap both keyed on the whole pointee `dElemTy`).
    let isField = stmt.dField.len > 0
    # ADR-0013 Slice 1: itMultiVariant still raises (deferred to Slice 4).
    # itVariant: discriminant and plain fields proceed; arm-specific fields
    # are deferred (Slices 2/3).
    if isField and stmt.dObjTy.kind == itMultiVariant:
      # N46-followup (round-6 re-review, walker v113): was `raise (ref
      # SymexRefVariantUnsupportedError)`, LEDGERED-LIVE. LIVE (confirmed via
      # probe): a multi-axis `case`-`case` object reached through an INLINE
      # `ref T`/`ptr T` parameter (the classifier wraps such a pointee in
      # `itRef`/`itPtr` unchanged — only the NAMED-alias and field-typed-ref
      # paths exempt variant pointees from heap routing, per
      # `dsl_typebridge.nim`'s ADR-0022 sub-decision #1) reaches this arm at
      # WALK time on an ordinary `p.field` access. A raw raise here unwinds
      # through `walkHeapArm`/`walk`/`walkBlock` to `runSymexImpl`'s
      # top-level catch — a WHOLE-RUN abort that can mask an unrelated
      # sibling path's already-found (or not-yet-explored) `sxSat` (the
      # N31/ADR-0023 SND-3 class; same mechanism proven RED/GREEN for the
      # sibling `liftHeapValue` conversion above). This decline happens
      # BEFORE the per-path loop even starts (it depends only on
      # `stmt.dObjTy.kind`, not on any one path), so every INCOMING path is
      # degraded uniformly here: `allocDegrade` records the classified
      # `heRefVariantUnsupported` and marks the run degraded
      # immediately/globally, then each path is forked TAINTED with
      # `stmt.dRetName` bound to a fresh placeholder of the field's own type
      # (`stmt.dElemTy`) — never trustworthy content, but a well-formed Z3
      # sort so downstream statements that reference the bound name (an
      # `if`/comparison consuming the "read" value) do not crash on a
      # missing env key.
      allocDegrade(heRefVariantUnsupported,
        "field `." & stmt.dField & "` through a ref/ptr to multi-variant `" &
        $stmt.dObjTy & "` is unsupported (Slice 4 deferred, ADR-0013 D6)")
      var survivors: seq[Path]
      for p in paths:
        if w.shouldStop: return survivors
        survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
          "__heapMultiVariantUnsupported")
      return survivors
    # For itVariant: classify the field — disc, plain, or arm-specific.
    let isVariantPointee = isField and stmt.dObjTy.kind == itVariant
    let isDiscDeref = isVariantPointee and stmt.dField == stmt.dObjTy.vDiscName
    let isArmField = isVariantPointee and not isDiscDeref and
                     stmt.dField notin stmt.dObjTy.vPlainFieldNames
    if isArmField:
      # ADR-0013 D2 (Slice 2): arm-specific field READ through a ref-to-variant.
      # Mirror the value-variant `isVariantField` walk arm EXACTLY, lifted to the
      # field-split heap (ADR-0013 D1 key scheme): materialise the disc heap,
      # build the matching-arm equalities, FieldDefect-fork the out-of-arm side
      # (D1a unconditional), and on the in-arm continuation bind `dRetName` to an
      # ite-chain over the matching arms' field-heap selects.
      let ctx = w.z3
      let objTy = stmt.dObjTy
      let baseId = refPointeeTypeId(objTy)
      let discHeapKey = baseId & "__@disc"
      # Scan arms declaring the field → (tagOrdinal, fieldIx, isElse, fieldTy).
      # Nim forbids field-name shadowing across arms, so a non-else field lands
      # in exactly ONE arm (the ite-chain is then trivial); the loop stays general
      # for the rare multi-tag / else-shared case (ADR-0013 D4.6, mirror value).
      type ArmHit = tuple[tagOrd: int; fieldIx: int; isElse: bool; fieldTy: IRType]
      var armHits: seq[ArmHit]
      for arm in objTy.vArms:
        let fi = arm.fieldNames.find(stmt.dField)
        if fi >= 0:
          armHits.add (arm.tagOrdinal, fi, arm.isElse, arm.fieldTypes[fi])
      if armHits.len == 0:
        # N46-followup (round-6 re-review): reclassified from LEDGERED-LIVE to
        # verified-unreachable. `isArmField`'s own gate (above) only reaches
        # here with a `stmt.dField` the PARSER already resolved against
        # `objTy`'s real arm/plain field names via the typed AST
        # (`dsl_typebridge.classifyObjectRecordFields`'s per-arm field scan,
        # `dsl_parser`'s dot-expr field lookup) — a `dField` naming no field
        # on ANY arm would mean the IR references a field the SUT's own Nim
        # type does not declare, which the Nim compiler itself rejects at
        # the SUT's own compile time (undeclared field access is a compile
        # error). Degenerate IR only, never reachable from a SUT that
        # compiles at all.
        raise (ref SymexRefVariantUnsupportedError)(  # [raise-audited: verified-unreachable: dField is parser-resolved against objTy's real field names before this arm-scan runs; a Nim SUT with an undeclared field reference does not compile, so armHits.len==0 is degenerate IR only]
          msg: "arm-specific field `." & stmt.dField & "` is declared by no arm " &
               "of variant `" & $objTy & "` (degenerate IR — should not occur)")
      var survivors: seq[Path]
      for p in paths:
        if w.shouldStop: return survivors
        if heapDepthExhausted(p, w): continue
        let refSV = lowerLeafInExpr(p, stmt.dPtr)
        let refAst = case refSV.kind
          of svRef: refSV.refAst
          of svPtr: refSV.ptrAst
          else:
            # N46-followup (round-6 re-review, walker v113): was `raise (ref
            # SymexRefUnresolvedError)`, LEDGERED-LIVE. Same live-hazard class
            # as `liftHeapValue`'s converted `else` arm above (a raw raise
            # here unwinds through `walkHeapArm`/`walk`/`walkBlock` to
            # `runSymexImpl`'s top-level catch, a WHOLE-RUN abort that can
            # mask a sibling path's `sxSat`) — `stmt.dPtr` resolving to a
            # non-`svRef`/`svPtr` SymVal is reachable whenever the pointee
            # variable's OWN value degraded upstream (e.g. an `iteSV` merge
            # across an unsupported/opaque branch, already-converted
            # elsewhere in this codebase to the SAME degrade idiom rather
            # than raising). In-band degrade: taint THIS path only, bind
            # `stmt.dRetName` to a fresh placeholder of the field's type so
            # no downstream statement key-faults, and move on — the OTHER
            # paths in `paths` are untouched.
            allocDegrade(heUnresolvedRef,
              "arm-field deref of non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind))
            survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
              "__armFieldReadUnresolvedRef")
            continue
        if refSV.kind == svPtr:
          let ptrHint = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
            msg: "witness involves unmanaged ptr")
          ptrFamilyHints.add ptrHint
          w.ptrFamilyHints.add ptrHint
        for cp0 in nilDerefFork(p, refAst, objTy, w):
          if w.shouldStop: return survivors
          # Materialise the disc heap (D1 `__@disc`, value sort = vDiscTy) and
          # `select` the disc; the disc-range disjunction (D4.5) is asserted
          # below — per ADDRESS, before the FieldDefect fork — so Z3 can never
          # pick an illegal ordinal on EITHER fork sibling.
          var discHeap: Z3AnyAst
          if cp0.heaps.hasKey(discHeapKey):
            discHeap = cp0.heaps[discHeapKey]
          else:
            let refSort = allocRefSort(ctx, objTy)
            discHeap = mkHeapArrayVar(ctx, refSort, objTy.vDiscTy,
                                      "heap_" & discHeapKey)
          # N42: drain any `allocateSym` degrade from the disc-heap value-sort
          # probe above into this path's own taint (SND-1) — see the main
          # (non-variant-field) `isDeref` arm's own N42 comment, above, for
          # the full rationale; the disc type is always a primitive ordinal
          # by variant-discriminant construction so this is a defensive no-op
          # in practice, kept for audit completeness (every `mkHeapArrayVar`
          # call site on this READ path gets the same treatment).
          let cpA = drainPendingLowerEffects(cp0)
          let discSV = heapSelect(ctx, discHeap, refAst, objTy.vDiscTy)
          # discEq dispatch — IDENTICAL to isVariantField / refVariantDiscRangeClause.
          proc discEq(tagOrd: int64): Z3Bool =
            case discSV.kind
            of svBV8:  discSV.bv8  == mkBitVec[8](tagOrd)
            of svBV16: discSV.bv16 == mkBitVec[16](tagOrd)
            of svBV32: discSV.bv32 == mkBitVec[32](tagOrd)
            of svBV64: discSV.bv64 == mkBitVec[64](tagOrd)
            of svInt:  discSV.zi   == mkZ3IntLit(tagOrd)
            of svBool: discSV.bo   == mkBool(tagOrd != 0)
            else:
              # N46-followup (round-6 re-review): reclassified from
              # LEDGERED-LIVE to verified-unreachable. `discSV` comes from
              # `heapSelect(ctx, discHeap, refAst, objTy.vDiscTy)` ->
              # `liftHeapValue(ctx, valRaw, objTy.vDiscTy)`; `vDiscTy` is
              # ALWAYS `itInt` by construction (`types.nim`'s `VariantAxis.
              # vDiscTy` doc: "must be itInt (the enum's int representation)"),
              # and `liftHeapValue`'s `itInt` arm is exhaustive over width
              # 8/16/32/64 (its own width-exhaustive audited sibling, marked
              # separately at this file's `liftHeapValue` definition),
              # yielding only `svBV8`/`svBV16`/`svBV32`/`svBV64`. `svInt`/
              # `svBool`/this `else` can never be
              # the kind of a disc value read through this call path.
              raise (ref SymexRefVariantUnsupportedError)(  # [raise-audited: verified-unreachable: vDiscTy is always itInt (types.nim invariant) and liftHeapValue's itInt arm is width-exhaustive, so heapSelect can only yield svBV8/16/32/64 for a disc value -- this else is dead]
                msg: "arm-field deref: unsupported discriminant sort " &
                     plainEnglishSymValKind(discSV.kind) & " for variant `" & $objTy & "` (degrade, " &
                     "never guess — ADR-0013 D2/D7)")
          # Matching-arm equalities. An else-arm matches the conjunction of the
          # negations of every non-else ordinal (mirrors the value path / D2).
          var armEqs: seq[Z3Bool]
          for hit in armHits:
            let armEq =
              if hit.isElse:
                var conj: Z3Bool
                var seeded = false
                for arm in objTy.vArms:
                  if arm.isElse: continue
                  let neg = not discEq(int64(arm.tagOrdinal))
                  if not seeded: (conj = neg; seeded = true)
                  else:          conj = conj and neg
                if not seeded:
                  # N46-followup (round-6 re-review): reclassified from
                  # LEDGERED-LIVE to verified-unreachable. Nim's `case`
                  # syntax requires at least one `of` branch before an
                  # optional `else` — an else-only case body (no `of` arms
                  # at all) is not constructible, so `objTy.vArms` always
                  # contains >= 1 non-`isElse` arm whenever ANY `isElse` arm
                  # exists. `seeded` can only stay false here for a
                  # degenerate IR that no compilable SUT can produce.
                  raise (ref SymexRefVariantUnsupportedError)(  # [raise-audited: verified-unreachable: Nim case syntax requires >=1 `of` branch before an optional `else`, so an else-only variant with zero non-else arms is not constructible from valid Nim -- degenerate IR only]
                    msg: "arm-field deref: else-only variant `" & $objTy &
                         "` has no non-else arm to negate against (degenerate)")
                conj
              else:
                discEq(int64(hit.tagOrd))
            armEqs.add armEq
          var inArmCond = armEqs[0]
          for k in 1 ..< armEqs.len:
            inArmCond = inArmCond or armEqs[k]
          # Disc-range clause (D4.5) — assert for THIS address onto a base pc
          # BEFORE the FieldDefect fork, so BOTH the defect path and the in-arm
          # continuation are constrained to a legal ordinal. Per ADDRESS, NOT
          # gated on first heap materialisation: idempotent for a repeat access,
          # load-bearing for a second distinct address that shares the per-type
          # disc heap (a field shared by all arms would otherwise FieldDefect on
          # an impossible ordinal; a second ref's disc would otherwise be free).
          var basePc = cpA.pc
          let rangeOpt = refVariantDiscRangeClause(objTy, discSV)
          if rangeOpt.isSome:
            basePc = basePc & @[rangeOpt.get]
          # FieldDefect fork — Phase 16 D1a unconditional (same call shape as the
          # value-variant `isVariantField` arm); forked off the ranged base.
          discard forkDefect(forkPath(cpA, basePc, cpA.env),
                             not inArmCond, "FieldDefect", none(string), w)
          if w.shouldStop: return survivors
          # In-arm continuation: assert inArmCond on the range-constrained base.
          var childPc = basePc & @[inArmCond]
          # Materialise each matching arm's field heap (D1 `__@<ord>__<field>`),
          # `select` the field value, and bind an ite-chain over the matching arms.
          var armHeaps: seq[(string, Z3AnyAst)]
          var armSelects: seq[(int, SymVal)]
          for hit in armHits:
            let armHeapKey = baseId & "__@" & $hit.tagOrd & "__" & stmt.dField
            var armHeap: Z3AnyAst
            if cpA.heaps.hasKey(armHeapKey):
              armHeap = cpA.heaps[armHeapKey]
            else:
              let refSort = allocRefSort(ctx, objTy)
              armHeap = mkHeapArrayVar(ctx, refSort, hit.fieldTy,
                                       "heap_" & armHeapKey)
            armHeaps.add (armHeapKey, armHeap)
            armSelects.add (hit.tagOrd, heapSelect(ctx, armHeap, refAst, hit.fieldTy))
          # N42: second drain — covers a degrade from any arm-field heap just
          # materialised above (each iteration can independently degrade via
          # `allocateSym`; `loweringDidDegrade` is idempotent to drain once
          # after the loop, since nothing resets it between iterations).
          let cpB = drainPendingLowerEffects(cpA)
          var bound = armSelects[armSelects.len - 1][1]
          for k in countdown(armSelects.len - 2, 0):
            bound = iteSV(discEq(int64(armSelects[k][0])), armSelects[k][1], bound)
          var newEnv = cpB.env
          newEnv[stmt.dRetName] = bound
          # ADR-0013 D5: witness markers. Record the observed disc (so the witness
          # disc reflects the model) and each matching arm's field value (so the
          # active arm's leaf renders the observed value, not a proto default).
          if stmt.dPtr.kind == iekVar:
            currentHeapDerefVals[stmt.dPtr.vname & "." & objTy.vDiscName] = discSV
          var child = forkPath(cpB, childPc, newEnv)
          child.heaps[discHeapKey] = discHeap
          for (hk, hh) in armHeaps:
            child.heaps[hk] = hh
          survivors.add child
      return survivors
    let sortTy = if isField: stmt.dObjTy else: stmt.dElemTy
    let typeId = refPointeeTypeId(sortTy)
    # ADR-0013 D1: disc field uses the __@disc heap key (@ prefix is collision
    # guard — Nim identifiers cannot start with @). Plain/non-variant fields
    # keep the existing fieldHeapKey unchanged.
    let heapKey =
      if isDiscDeref: refPointeeTypeId(stmt.dObjTy) & "__@disc"
      elif isField:   fieldHeapKey(stmt.dObjTy, stmt.dField)
      else:           typeId
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return survivors
      # Phase 15 R9: bound recursive heap traversal. INCREMENT this path's
      # heapDepth and HALT it (no survivor → sxUnknown) if it reaches the
      # effective budget BEFORE the select — a recursive `n.next.next…` walk can
      # never loop unboundedly. Per-path: a shallower path continues.
      if heapDepthExhausted(p, w): continue
      ## Drain-coverage audit: `stmt.dPtr` is always an env-resident var —
      ## the parser A-normalises so deref operands are named bindings (no
      ## complex expression as the ref/ptr operand). A violation here means
      ## the parser emitted a non-var deref operand and drains would be needed.
      let refSV = lowerLeafInExpr(p, stmt.dPtr)
      let refAst = case refSV.kind
        of svRef: refSV.refAst
        of svPtr: refSV.ptrAst
        else:
          # N46-followup (round-6 re-review, walker v113): was `raise (ref
          # SymexRefUnresolvedError)`, LEDGERED-LIVE. Same live-hazard class
          # as `liftHeapValue`'s converted `else` arm and the arm-field-read
          # sibling above: a raw raise here unwinds through
          # `walkHeapArm`/`walk`/`walkBlock` to `runSymexImpl`'s top-level
          # catch, a WHOLE-RUN abort that can mask a sibling path's `sxSat`
          # (the N31/ADR-0023 SND-3 class, proven RED/GREEN for the
          # `liftHeapValue` conversion above). In-band degrade: taint THIS
          # path only, bind `stmt.dRetName` to a fresh placeholder of the
          # field/pointee's own type so no downstream statement key-faults,
          # and move on to the next path.
          allocDegrade(heUnresolvedRef,
            "deref of non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind) &
            " (Cluster R R1 expects an svRef/svPtr at the deref site)")
          survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
            "__derefReadUnresolvedRef")
          continue
      # Phase 15 R8. An UNMANAGED `ptr T` deref routes through the SAME heap as
      # a `ref T` (the `of svPtr` arm above), but emits a non-halting
      # `hePtrFamily` hint so a consumer can distinguish unmanaged ptr from
      # managed ref in the finding. A `ref T` deref emits NOTHING.
      if refSV.kind == svPtr:
        let ptrHint = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
          msg: "witness involves unmanaged ptr")
        ptrFamilyHints.add ptrHint   # threadvar: fallback
        w.ptrFamilyHints.add ptrHint # CR-9 Stage 5: LIVE WalkCtx field
      # Phase 15 R5: fork the nil path (the defect) off; continue on non-nil.
      # The nil-fork keys on the OBJECT ref sort (`sortTy`) so a field access
      # through a possibly-nil object ref forks correctly (R5 composition).
      for cp0 in nilDerefFork(p, refAst, sortTy, w):
        if w.shouldStop: return survivors
        # N42 (round-6 fix round 7, walker v105). Materialising the per-path
        # heap array below calls `mkHeapArrayVar` -> `heapValueSort` ->
        # `allocateSym(stmt.dElemTy, ...)` (a THROWAWAY prototype allocation,
        # used only to read the value SORT) -- and `allocateSym` is TOTAL
        # since N40: an unallocatable `dElemTy` (an `itUninterp`/`itTable`/
        # `itSet` field whose real Nim type this walker can't back -- an
        # ownership wrapper, a non-string-key Table, a non-int64 HashSet)
        # does not raise, it calls `allocDegrade` and returns an inert
        # placeholder. `allocDegrade` sets `loweringDegradeErrors`/
        # `loweringDidDegrade` (sink (a), ADR-0023 SND-3) AND syncs
        # `w.sawUnknown` immediately/globally -- but NEITHER of those taints
        # THIS PATH. Every OTHER `allocateSym`-degrade caller reachable at
        # walk time either wraps the call in `lower()`/`lowerInExpr` (which
        # drains sink (a) into the calling path's `uncertain = true` --
        # `isDerefWrite`/`isNew`'s own zero-write proto allocation) or writes
        # `Path.uncertain`/`forkPathTainted` directly (`isVariantConstructSym`,
        # `isUnsupported`) -- this READ arm did neither: it called
        # `mkHeapArrayVar` then proceeded straight to `heapSelect` +
        # `forkPath` (implicit propagate, never introduces taint) with NO
        # drain in between. Per ADR-0012 D2's own documented precedence
        # (`runSymexImpl`, ~line 10498) a winning `sxSat` in `w.found` beats
        # `w.sawUnknown` -- correctly, for a path whose degrade happened
        # elsewhere -- so a path whose OWN allocation just degraded and is
        # NOT tainted can still reach `isTargetLabel`'s `else` (non-uncertain)
        # arm and mint a technically-winning `sxSat` witness over a value that
        # was never really backed. Empirically (this slice's own spot-check),
        # direct instrumentation confirmed `loweringDidDegrade` DOES flip
        # `true` here and DOES NOT propagate to `child.uncertain` -- every
        # black-box SUT shape tried happened to have the taint incidentally
        # swept up by whatever `lower()`-calling statement consumed the
        # dereffed value NEXT (a `discard`/`let` binding, an `if` condition)
        # landing correctly by COINCIDENCE, not by construction -- exactly
        # the "misattributed... or lost entirely" hazard `allocDegrade`'s own
        # doc comment warns sink (a) carries for any caller that never drains
        # it directly. Fix: drain right here, unconditionally, the SAME
        # "seed(implicit)/lower(implicit via mkHeapArrayVar)/drain" shape
        # `lowerInExpr` uses -- `drainPendingLowerEffects` is idempotent and a
        # safe no-op when nothing degraded (the common case), and correctly
        # forks `cp.uncertain = true` (SND-1) + syncs `w.sawUnknown` (already
        # true, redundant-safe) when it did. Placed AFTER the materialisation
        # block (fresh OR cached) so a cache-hit (no new `allocateSym` call,
        # per `cp.heaps.hasKey(heapKey)` below) still safely drains any
        # STILL-PENDING flag from an earlier, not-yet-drained degrade on this
        # same path (idempotent either way).
        var newEnv = cp0.env
        # Materialise the per-path heap (field-split array for a field deref) on
        # first use. The ref SORT keys on the OBJECT; the value sort on the field.
        var heap: Z3AnyAst
        if cp0.heaps.hasKey(heapKey):
          heap = cp0.heaps[heapKey]
        else:
          let refSort = allocRefSort(ctx, sortTy)
          heap = mkHeapArrayVar(ctx, refSort, stmt.dElemTy,
                                "heap_" & heapKey)
        let cp = drainPendingLowerEffects(cp0)   ## N42 per-path taint drain
        newEnv = cp.env
        let valSV = heapSelect(ctx, heap, refAst, stmt.dElemTy)
        # N46-followup (walker v113): a SECOND drain, immediately after the
        # select — `liftHeapValue` (called from inside `heapSelect`) can now
        # degrade in-band (its own `else` arm, converted this slice) for a
        # pointee kind it does not lift (string/table/set/distinct/…). The
        # drain above (`cp`, before this select) only covers `mkHeapArrayVar`/
        # `heapValueSort`'s OWN degrade; this one covers a degrade from the
        # select's VALUE lift, the same "second drain" shape already used
        # below for the arm-field select loop (N42).
        let cp2 = drainPendingLowerEffects(cp)
        newEnv[stmt.dRetName] = valSV
        # ADR-0013 D4.5: assert the disc-range disjunction on EVERY disc read
        # (per address — NOT gated on first heap materialisation, so a second
        # ref sharing the per-type disc heap is constrained too). For a bool disc
        # this is a tautology (no-op for Z3); for enum/int discs it prevents Z3
        # from picking an illegal ordinal. Build the child pc FIRST so forkPath
        # uses the constrained pc. Idempotent for a repeat read of one address.
        var childPc = cp2.pc
        if isDiscDeref:
          let rangeOpt = refVariantDiscRangeClause(stmt.dObjTy, valSV)
          if rangeOpt.isSome:
            childPc = childPc & @[rangeOpt.get]
        # ADR-0013 D5: Witness marker for disc field so the ref witness renders
        # a structural marker (`p.tag`). Full active-arm serialization is Slice 2.
        if isDiscDeref and stmt.dPtr.kind == iekVar:
          currentHeapDerefVals[stmt.dPtr.vname & "." &
                               stmt.dObjTy.vDiscName] = valSV
        # R1 witness hook: if the dereffed ptr is a bare PARAM ref, record the
        # heap value under the param name so the witness reader renders `p[]`.
        # Only for a BARE `p[]` — a field deref's scalar value must not clobber
        # the object-cell witness slot for `p` (the field-split heap has no
        # whole-object witness reader at R6; the full heap-snapshot witness lands
        # R11b/R12).
        if not isField and stmt.dPtr.kind == iekVar:
          currentHeapDerefVals[stmt.dPtr.vname] = valSV
        # Carry the (possibly freshly-materialised) heap forward on the surviving
        # path so a SECOND deref of the SAME ref reads the SAME array (a genuine
        # functional read — `p[] == 42 and p[] == 43` is unsat).
        var child = forkPath(cp2, childPc, newEnv)
        child.heaps[heapKey] = heap
        survivors.add child
    survivors
  of isNew:
    # Phase 15 R2 (ADR-0010). `new T` allocation semantics. Per surviving path:
    #   1. `freshRef` increments `path.allocCounters[typeId]` (per-path; R1b
    #      threads + max-merges it) and mints a fresh `Ref_T` const
    #      `ref_<typeId>_<n>` (n = the new counter value) via raw `Z3_mk_const`;
    #   2. `assertFreshness` asserts the GROUND distinctness inequalities into
    #      `path.pc` — `newRef != nil` (always) + `newRef != prior` for every
    #      prior live ref of this sort on this path (CAPPED by
    #      `settings.maxFreshnessAssertions` → `heFreshnessCapExceeded` sevHint,
    #      a sound over-approximation);
    #   3. the fresh ref is bound in the env under `stmt.nRetName` as an
    #      `svRef`/`svPtr` (so a later `p[]` deref / `p == q` compare resolves
    #      it through the ordinary ref machinery).
    # NO universal-∀ over the uninterpreted sort (the G4 hang lesson); all
    # inequalities are ground and decidable.
    let ctx = w.z3
    # `nRefTy` is the full `itRef`/`itPtr` type; the ref sort keys on the
    # POINTEE (matching `allocateSym(itRef)` and `isDeref`).
    let isPtr = stmt.nRefTy.kind == itPtr
    let pointee = if isPtr: stmt.nRefTy.ptrPointeeTy else: stmt.nRefTy.refPointeeTy
    let typeId = refPointeeTypeId(pointee)
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return survivors
      let refSort = allocRefSort(ctx, pointee)
      var child = forkPath(p, p.pc, p.env)
      let newRef = freshRef(ctx, refSort, typeId, child)
      assertFreshness(ctx, child, typeId, newRef, w.settings)
      var newEnv = child.env
      if isPtr:
        newEnv[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: newRef,
                                       ptrFamily: true, ptrPointee: pointee)
      else:
        newEnv[stmt.nRetName] = SymVal(kind: svRef, refAst: newRef,
                                       refPointee: pointee)
      child.env = newEnv
      # Cluster H Step C (ADR-0022): universal isNew zero-write. A fresh
      # field-split heap array is a FREE Z3 const (`mkHeapArrayVar`), so an
      # unwritten field `select` is UNCONSTRAINED — without this, `new Node`
      # then reading `p.next != nil` would be falsely SAT (Invariant-3
      # violation). Zero-write EVERY field of an OBJECT pointee (not just the
      # fields a `Node(...)` constructor happened to write — the P2b
      # construction arm's per-PRESENT-field `mkFieldDerefWrite`s then
      # overwrite the fields it actually set). A non-object pointee (a plain
      # `ref int`/`ref float`/… inline allocation) has no fields to split —
      # skip. A variant object pointee never reaches `isNew` (named ref
      # aliases whose pointee has `case` fields classify to `itVariant`, not
      # `itRef` — ADR-0022 sub-decision #1 — so `isNewCall` gates never fire
      # for them); this loop is therefore never reached with a variant pointee.
      if pointee.kind == itTuple:
        for i, fname in pointee.fieldNames:
          let fty = pointee.fields[i]
          let zeroExpr = zeroIRExprForType(fty)
          if zeroExpr == nil:
            # SND-1: no clean zero encoding for this field's type this cycle
            # (seq/table/set/array/variant/distinct/uninterp) — taint-and-
            # continue (mirrors the `isUnsupported` walk arm exactly) rather
            # than leaving the field's heap cell silently unconstrained.
            child.uncertain = true
            w.sawUnknown = true
            let zeroErr = SymexErrorInfo(kind: heNewFieldZeroUnsupported,
              severity: sevError,
              msg: "new " & $stmt.nRefTy & ": field `" & fname &
                   "` of type " & $fty.kind & " has no clean zero-value " &
                   "encoding — isNew zero-write skipped for this field " &
                   "(SND-1 taint)")
            newFieldZeroErrors.add zeroErr   # threadvar: fallback
            w.newFieldZeroErrors.add zeroErr # CR-9-style LIVE WalkCtx field
            continue
          let fieldKey = fieldHeapKey(pointee, fname)
          var fheap: Z3AnyAst
          if child.heaps.hasKey(fieldKey):
            fheap = child.heaps[fieldKey]
          else:
            fheap = mkHeapArrayVar(ctx, refSort, fty, "heap_" & fieldKey)
          var scratchPC: seq[Z3Bool]
          let proto = allocateSym(fty, "__isNewZeroProto", scratchPC)
          let (valSVRaw, childAfter) = lowerInExpr(child, zeroExpr, w, some(proto))
          var valSV = valSVRaw
          # Reconcile svInt↔BV sort mismatch (same idiom as isDerefWrite):
          # a literal int/bool zero may lower to svInt (Z3Int) while the
          # field-split heap's value sort is BV — coerce via int2bv.
          if valSV.kind == svInt:
            case proto.kind
            of svBV8:  valSV = liftBV(intToBv[8](valSV.zi, Z3BitVec[8]),  proto.signed)
            of svBV16: valSV = liftBV(intToBv[16](valSV.zi, Z3BitVec[16]), proto.signed)
            of svBV32: valSV = liftBV(intToBv[32](valSV.zi, Z3BitVec[32]), proto.signed)
            of svBV64: valSV = liftBV(intToBv[64](valSV.zi, Z3BitVec[64]), proto.signed)
            else: discard
          let storedRaw = ctx.checkErr Z3_mk_store(
            ctx.raw, fheap.raw, newRef.raw, rawAnyAstOf(valSV))
          child = childAfter
          child.heaps[fieldKey] = wrap[Z3AnyAst](ctx, storedRaw)
      survivors.add child
    survivors
  of isDerefWrite:
    # Phase 15 R4 (ADR-0010). `p[] = v` — a GROUND heap WRITE (store). Promotes
    # R3's no-op stub to the real `path.heaps[typeId] := store(heap, p, v)`. For
    # each surviving path:
    #   1. resolve the ref/ptr SymVal `p` (its `Ref_T`-sorted abstract address);
    #   2. lazily materialise `path.heaps[typeId]` to a fresh free heap array if
    #      this is the first heap touch of this pointee type on this path (PER-PATH
    #      heap; the sort is PER-WALKER) — same discipline as `isDeref`;
    #   3. lower the RHS `v` to the pointee-typed SymVal (a prototype from the
    #      pointee type coerces an int literal to the matching BV width / sort) and
    #      extract its raw value-sorted ast;
    #   4. `store(heap, p, v)` → a NEW heap array equal to the old one with `p`
    #      updated to `v`; REPLACE `child.heaps[typeId]` with it.
    # Subsequent `select` reads on this path see `v` (real read-after-write);
    # reads through an ALIASED ref (same refSym) also see it — Z3's array theory
    # gives `select(store(h, p, v), q) == v` when `p == q` is forced, automatically
    # (no fork). The store is GROUND (`Z3_mk_store`) — NO universal-∀ over the
    # uninterpreted Ref_T sort (the G4 MBQI hang lesson). The write is PER-PATH:
    # a branch that never executed it keeps the pre-write heap (isolation).
    # Phase 15 R5: a WRITE through a possibly-nil ref is ALSO a NilAccessDefect —
    # `nilDerefFork` emits the nil finding (gated on stkNilAccess) and returns the
    # non-nil continuation(s) on which the store proceeds (short-circuited for a
    # freshly-allocated / `p != nil`-constrained ref).
    let ctx = w.z3
    # Phase 15 R6: a FIELD write (`p.field = v`, `dwField != ""`) keys the
    # `Ref_T` SORT + nil-fork on the OBJECT (`dwObjTy`) and stores into the
    # per-field heap ARRAY `fieldHeapKey(dwObjTy, field)` (value sort = the field
    # type `dwElemTy`). Only that field's array changes — an aliased read of the
    # SAME field sees it (Z3 array theory), a read of a DIFFERENT field is
    # independent. A bare `p[] = v` keeps the R4 whole-pointee path.
    let isField = stmt.dwField.len > 0
    # ADR-0013 Slice 1: itMultiVariant still raises (Slice 4 deferred).
    # itVariant: discriminant and plain fields proceed; arm-specific writes
    # are deferred (Slices 2/3).
    if isField and stmt.dwObjTy.kind == itMultiVariant:
      # N46-followup (round-6 re-review, walker v113): was `raise (ref
      # SymexRefVariantUnsupportedError)`, LEDGERED-LIVE. Same live-hazard
      # class as the read-side `isDeref` sibling above (an INLINE ref-to-
      # multi-variant parameter reaches this arm on an ordinary `p.field =
      # v` write; a raw raise here is a WHOLE-RUN abort that can mask a
      # sibling path's `sxSat`). This decline is statement-scoped (depends
      # only on `stmt.dwObjTy.kind`, not on any one path), so every incoming
      # path is degraded uniformly: `allocDegrade` records the classified
      # `heRefVariantUnsupported` and marks the run degraded
      # immediately/globally, then each path is forked TAINTED with its
      # PRE-write env/heap unchanged — the write is simply DROPPED (mirrors
      # the `isUnsupported` walk arm's own "SND-1: an unmodeled statement
      # dropped its mutation" idiom, `runtime.nim`), never silently applied.
      allocDegrade(heRefVariantUnsupported,
        "field-write `." & stmt.dwField & " = …` through ref/ptr to " &
        "multi-variant `" & $stmt.dwObjTy & "`: unsupported (Slice 4, ADR-0013 D6)")
      var survivors: seq[Path]
      for p in paths:
        if w.shouldStop: return survivors
        survivors.add degradeHeapArmForPath(p)
      return survivors
    let isVariantPointeeW = isField and stmt.dwObjTy.kind == itVariant
    let isDiscWrite = isVariantPointeeW and stmt.dwField == stmt.dwObjTy.vDiscName
    let isArmFieldWrite = isVariantPointeeW and not isDiscWrite and
                          stmt.dwField notin stmt.dwObjTy.vPlainFieldNames
    if isArmFieldWrite:
      # ADR-0013 D3 (Slice 3): arm-specific field WRITE through a ref-to-variant.
      # Symmetric to D2 arm-field read: scan arms for the field, materialise the
      # disc heap, build inArmCond, FieldDefect-fork the out-of-arm side (D1a,
      # unconditional, per D4.5 on the ranged basePc BEFORE the fork), and on the
      # in-arm continuation store the lowered RHS into the matching arm's field heap.
      # Disc heap carried unchanged (D3). Aliasing is automatic: two refs p,q with
      # p==q share heap arrays, so select(store(h,p,v),q) == v via Z3 array theory.
      let objTy = stmt.dwObjTy
      let baseId = refPointeeTypeId(objTy)
      let discHeapKeyW = baseId & "__@disc"
      type ArmHitW = tuple[tagOrd: int; fieldIx: int; isElse: bool; fieldTy: IRType]
      var armHitsW: seq[ArmHitW]
      for arm in objTy.vArms:
        let fi = arm.fieldNames.find(stmt.dwField)
        if fi >= 0:
          armHitsW.add (arm.tagOrdinal, fi, arm.isElse, arm.fieldTypes[fi])
      if armHitsW.len == 0:
        # N46-followup (round-6 re-review): reclassified from LEDGERED-LIVE
        # to verified-unreachable. Same argument as the read-side sibling:
        # `stmt.dwField` is parser-resolved against `objTy`'s real field
        # names before this arm-scan runs; a SUT referencing an undeclared
        # field does not compile. Degenerate IR only.
        raise (ref SymexRefVariantUnsupportedError)(  # [raise-audited: verified-unreachable: dwField is parser-resolved against objTy's real field names before this arm-scan runs; a Nim SUT with an undeclared field reference does not compile, so armHitsW.len==0 is degenerate IR only]
          msg: "arm-specific field write `." & stmt.dwField & "` declared by no arm " &
               "of variant `" & $objTy & "` (degenerate IR — should not occur)")
      var survivors: seq[Path]
      for p in paths:
        if w.shouldStop: return survivors
        if heapDepthExhausted(p, w): continue
        let refSV = lowerLeafInExpr(p, stmt.dwPtr)
        let refAst = case refSV.kind
          of svRef: refSV.refAst
          of svPtr: refSV.ptrAst
          else:
            # N46-followup (round-6 re-review, walker v113): was `raise (ref
            # SymexRefUnresolvedError)`, LEDGERED-LIVE. Same live-hazard
            # class as the read-side sibling. A write has no `dRetName` to
            # bind, so the fix mirrors the `isMultiVariant` write-side
            # conversion above and `isUnsupported`'s own idiom exactly: taint
            # this path and DROP the write (the pre-write env/heap carries
            # forward unchanged) rather than raising.
            allocDegrade(heUnresolvedRef,
              "arm-field deref-write of non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind))
            survivors.add degradeHeapArmForPath(p)
            continue
        if refSV.kind == svPtr:
          let ptrHintAW = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
            msg: "witness involves unmanaged ptr")
          ptrFamilyHints.add ptrHintAW
          w.ptrFamilyHints.add ptrHintAW
        for cp in nilDerefFork(p, refAst, objTy, w):
          if w.shouldStop: return survivors
          # Materialise disc heap (D1 `__@disc`) from cp (PRE-lower) and select
          # the disc for THIS address. Matches D2 arm-field read structure:
          # disc work and FieldDefect fork happen BEFORE lowering the RHS so
          # the defect path uses the clean pre-lower path state.
          var discHeap: Z3AnyAst
          if cp.heaps.hasKey(discHeapKeyW):
            discHeap = cp.heaps[discHeapKeyW]
          else:
            let refSort = allocRefSort(ctx, objTy)
            discHeap = mkHeapArrayVar(ctx, refSort, objTy.vDiscTy,
                                      "heap_" & discHeapKeyW)
          # N42 audit: defensive drain, mirroring the read-side disc-heap
          # site — `objTy.vDiscTy` is always a primitive ordinal by
          # variant-discriminant construction, so this never actually
          # degrades in practice; kept for call-site-audit completeness.
          # The subsequent `lowerInExpr` (below, for the RHS) already
          # drains unconditionally, so this is redundant-safe, not a
          # behaviour change.
          let cpDW = drainPendingLowerEffects(cp)
          let discSV = heapSelect(ctx, discHeap, refAst, objTy.vDiscTy)
          # discEq dispatch — identical to the arm-field read path.
          proc discEqW(tagOrd: int64): Z3Bool =
            case discSV.kind
            of svBV8:  discSV.bv8  == mkBitVec[8](tagOrd)
            of svBV16: discSV.bv16 == mkBitVec[16](tagOrd)
            of svBV32: discSV.bv32 == mkBitVec[32](tagOrd)
            of svBV64: discSV.bv64 == mkBitVec[64](tagOrd)
            of svInt:  discSV.zi   == mkZ3IntLit(tagOrd)
            of svBool: discSV.bo   == mkBool(tagOrd != 0)
            else:
              # N46-followup (round-6 re-review): reclassified from
              # LEDGERED-LIVE to verified-unreachable — identical argument to
              # the read-side `discEq` sibling: `objTy.vDiscTy` is always
              # `itInt`, and `liftHeapValue`'s `itInt` arm is width-exhaustive,
              # so `discSV.kind` can only ever be `svBV8`/`16`/`32`/`64` here.
              raise (ref SymexRefVariantUnsupportedError)(  # [raise-audited: verified-unreachable: vDiscTy is always itInt (types.nim invariant) and liftHeapValue's itInt arm is width-exhaustive, so heapSelect can only yield svBV8/16/32/64 for a disc value -- this else is dead]
                msg: "arm-field deref-write: unsupported discriminant sort " &
                     plainEnglishSymValKind(discSV.kind) & " for variant `" & $objTy &
                     "` (degrade, never guess — ADR-0013 D3/D7)")
          # Matching-arm equalities (identical to arm-field read; else-arm mirrors
          # the value-variant treatment: conjunction of negations of non-else tags).
          var armEqsW: seq[Z3Bool]
          for hit in armHitsW:
            let armEq =
              if hit.isElse:
                var conj: Z3Bool
                var seeded = false
                for arm in objTy.vArms:
                  if arm.isElse: continue
                  let neg = not discEqW(int64(arm.tagOrdinal))
                  if not seeded: (conj = neg; seeded = true)
                  else:          conj = conj and neg
                if not seeded:
                  # N46-followup (round-6 re-review): reclassified from
                  # LEDGERED-LIVE to verified-unreachable — identical
                  # argument to the read-side sibling: Nim's `case` syntax
                  # requires >= 1 `of` branch before an optional `else`, so
                  # an else-only variant with zero non-else arms cannot be
                  # constructed from valid Nim.
                  raise (ref SymexRefVariantUnsupportedError)(  # [raise-audited: verified-unreachable: Nim case syntax requires >=1 `of` branch before an optional `else`, so an else-only variant with zero non-else arms is not constructible from valid Nim -- degenerate IR only]
                    msg: "arm-field deref-write: else-only variant `" & $objTy &
                         "` has no non-else arm to negate against (degenerate)")
                conj
              else:
                discEqW(int64(hit.tagOrd))
            armEqsW.add armEq
          var inArmCondW = armEqsW[0]
          for k in 1 ..< armEqsW.len:
            inArmCondW = inArmCondW or armEqsW[k]
          # D4.5 disc-range clause — per ADDRESS, onto basePc BEFORE forkDefect.
          # Idempotent for repeat writes to the same address; load-bearing for a
          # second distinct address whose disc would otherwise be unconstrained.
          var basePcW = cpDW.pc
          let rangeOptW = refVariantDiscRangeClause(objTy, discSV)
          if rangeOptW.isSome:
            basePcW = basePcW & @[rangeOptW.get]
          # FieldDefect fork — D1a unconditional, forked off the ranged base.
          # Uses the PRE-lower cp state (the defect is about the disc, not the
          # RHS, so the RHS lower is irrelevant here — matching D2 read path).
          discard forkDefect(forkPath(cpDW, basePcW, cpDW.env),
                             not inArmCondW, "FieldDefect", none(string), w)
          if w.shouldStop: return survivors
          # In-arm continuation: build the child path, THEN lower the RHS on it.
          # Disc heap is carried unchanged (D3: the disc is not mutated by an
          # arm-field write — only the arm's data heap changes).
          var childPcW = basePcW & @[inArmCondW]
          var cpChild = forkPath(cpDW, childPcW, cpDW.env)
          cpChild.heaps[discHeapKeyW] = discHeap
          # Lower RHS on the in-arm path (proto from the field type) — BV coercion
          # mirrors the plain-field write path (svInt↔BV reconciliation).
          var scratchPC: seq[Z3Bool]
          let proto = allocateSym(stmt.dwElemTy, "__armWriteProto", scratchPC)
          let (valSVRaw, cpInArm) = lowerInExpr(cpChild, stmt.dwValue, w, some(proto))
          var valSV = valSVRaw
          if valSV.kind == svInt:
            case proto.kind
            of svBV8:  valSV = liftBV(intToBv[8](valSV.zi, Z3BitVec[8]),  proto.signed)
            of svBV16: valSV = liftBV(intToBv[16](valSV.zi, Z3BitVec[16]), proto.signed)
            of svBV32: valSV = liftBV(intToBv[32](valSV.zi, Z3BitVec[32]), proto.signed)
            of svBV64: valSV = liftBV(intToBv[64](valSV.zi, Z3BitVec[64]), proto.signed)
            else: discard
          # Store RHS into each matching arm's field heap.
          for hit in armHitsW:
            let armHeapKey = baseId & "__@" & $hit.tagOrd & "__" & stmt.dwField
            var armHeap: Z3AnyAst
            if cpInArm.heaps.hasKey(armHeapKey):
              armHeap = cpInArm.heaps[armHeapKey]
            else:
              let refSort = allocRefSort(ctx, objTy)
              armHeap = mkHeapArrayVar(ctx, refSort, hit.fieldTy,
                                       "heap_" & armHeapKey)
            let storedRaw = ctx.checkErr Z3_mk_store(
              ctx.raw, armHeap.raw, refAst.raw, rawAnyAstOf(valSV))
            cpInArm.heaps[armHeapKey] = wrap[Z3AnyAst](ctx, storedRaw)
          # N42 audit (round-6 fix round 7): unlike the plain-field write path
          # (below, in this same proc) and the disc-heap materialisation
          # above, THIS loop's `mkHeapArrayVar` calls happen AFTER the RHS's
          # own `lowerInExpr` (which produced `cpInArm` and already drained
          # sink (a) once) -- so a degrade from an ARM's OWN field type here
          # (a different, possibly-unsupported per-arm shape than the RHS's
          # own `stmt.dwElemTy` proto) would otherwise sit undrained past
          # `survivors.add` below. Same fix as the read-side arm-field path.
          let cpInArmDrained = drainPendingLowerEffects(cpInArm)
          survivors.add cpInArmDrained
      return survivors
    let sortTy = if isField: stmt.dwObjTy else: stmt.dwElemTy
    let typeId = refPointeeTypeId(sortTy)
    # ADR-0013 D1: disc write uses __@disc heap key; plain/non-variant use fieldHeapKey.
    let heapKey =
      if isDiscWrite: refPointeeTypeId(stmt.dwObjTy) & "__@disc"
      elif isField:   fieldHeapKey(stmt.dwObjTy, stmt.dwField)
      else:           typeId
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return survivors
      # Phase 15 R9: a deref-WRITE also bounds heap depth (same per-path counter
      # and effective budget as the read). HALT this path before the store if it
      # reaches the budget.
      if heapDepthExhausted(p, w): continue
      ## Drain-coverage audit: `stmt.dwPtr` is always an env-resident var —
      ## the parser A-normalises so deref-write operands are named bindings.
      ## A violation here means the parser emitted a non-var write-ptr and
      ## drains would be needed before the lower call.
      let refSV = lowerLeafInExpr(p, stmt.dwPtr)
      let refAst = case refSV.kind
        of svRef: refSV.refAst
        of svPtr: refSV.ptrAst
        else:
          # N46-followup (round-6 re-review, walker v113): was `raise (ref
          # SymexRefUnresolvedError)`, LEDGERED-LIVE. Same live-hazard class
          # as every sibling `refSV.kind` mismatch converted above: a raw
          # raise here is a WHOLE-RUN abort that can mask a sibling path's
          # `sxSat`. A write has no `dwRetName` to bind — taint this path and
          # DROP the write (pre-write env/heap unchanged), mirroring
          # `isUnsupported`'s own idiom.
          allocDegrade(heUnresolvedRef,
            "deref-write through non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind) &
            " (Cluster R R4 expects an svRef/svPtr at the write site)")
          survivors.add degradeHeapArmForPath(p)
          continue
      # Phase 15 R8. A write THROUGH an unmanaged `ptr T` also flags hePtrFamily
      # (same heap store as ref; sevHint, non-halting).
      if refSV.kind == svPtr:
        let ptrHintW = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
          msg: "witness involves unmanaged ptr")
        ptrFamilyHints.add ptrHintW   # threadvar: fallback
        w.ptrFamilyHints.add ptrHintW # CR-9 Stage 5: LIVE WalkCtx field
      for cp in nilDerefFork(p, refAst, sortTy, w):
        if w.shouldStop: return survivors
        # Materialise the per-path heap (field-split array for a field write) on
        # first use, exactly as `isDeref` does, so a write before any read still
        # has an array to store into and a later read of the same ref/field reads
        # this stored array. Ref SORT keys on the OBJECT; value sort on the field.
        var heap: Z3AnyAst
        if cp.heaps.hasKey(heapKey):
          heap = cp.heaps[heapKey]
        else:
          let refSort = allocRefSort(ctx, sortTy)
          heap = mkHeapArrayVar(ctx, refSort, stmt.dwElemTy, "heap_" & heapKey)
        # Lower the RHS with a pointee-typed prototype so an int literal coerces to
        # the matching BV width / sort the heap array expects (the seq/table store
        # idiom). The raw value-sorted ast feeds `Z3_mk_store` directly.
        # CR-9 Stage 2: build proto (pure allocation, no threadvar side-effects)
        # BEFORE calling lowerInExpr so the wrapper's reset does not interfere.
        var scratchPC: seq[Z3Bool]
        let proto = allocateSym(stmt.dwElemTy, "__derefWriteProto", scratchPC)
        ## Encapsulate seed→reset→lower→drain via wrapper.
        let (valSVRaw, cp) = lowerInExpr(cp, stmt.dwValue, w, some(proto))
        var valSV = valSVRaw
        # Reconcile svInt↔BV sort mismatch: float→int64 returns svInt (Z3Int)
        # but the heap array value sort is BV64.  Coerce via int2bv here rather
        # than in the heap-read path; equality-only goals are safe (no ordering
        # goal — the F5 int2bv/bv2int pathology does not apply here).
        if valSV.kind == svInt:
          case proto.kind
          of svBV8:  valSV = liftBV(intToBv[8](valSV.zi, Z3BitVec[8]),  proto.signed)
          of svBV16: valSV = liftBV(intToBv[16](valSV.zi, Z3BitVec[16]), proto.signed)
          of svBV32: valSV = liftBV(intToBv[32](valSV.zi, Z3BitVec[32]), proto.signed)
          of svBV64: valSV = liftBV(intToBv[64](valSV.zi, Z3BitVec[64]), proto.signed)
          else: discard  ## proto is not a BV — no BV coercion needed
        let storedRaw = ctx.checkErr Z3_mk_store(
          ctx.raw, heap.raw, refAst.raw, rawAnyAstOf(valSV))
        let storedHeap = wrap[Z3AnyAst](ctx, storedRaw)
        # REPLACE the per-path heap binding with the stored array on the surviving
        # path (PER-PATH — an unforked branch never sees this update).
        var child = forkPath(cp, cp.pc, cp.env)
        child.heaps[heapKey] = storedHeap
        survivors.add child
    survivors
  else:
    raise newException(ValueError,  # [raise-audited: category-c: documented single-caller dispatch invariant (walk's own case restricts stmt.kind to isDeref/isNew/isDerefWrite before ever calling walkHeapArm)]
      "walkHeapArm: unexpected stmt.kind=" & $stmt.kind &
      " (not isDeref/isNew/isDerefWrite)")
