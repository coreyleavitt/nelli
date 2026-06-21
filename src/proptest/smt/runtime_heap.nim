# runtime_heap.nim — Cluster R include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_heap.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents: `walkHeapArm(stmt, paths, w)` — the `walk()` dispatch arm for
# `isDeref`, `isNew`, `isDerefWrite` (Cluster R, Stage 7 / Stage 8, CR-7).
# Named helpers (`heapSelect`, `allocRefSort`, `freshRef`, `assertFreshness`,
# `nilDerefFork`, `buildHeapSnapshot`) are already defined in runtime.nim
# and are NOT moved here. `isIndex` is left inline in `walk()` because it
# handles multiple container theories and cannot be cleanly attributed to
# the heap cluster alone.
# Placement in runtime.nim: between `walk`'s forward-decl and `walk`'s body
# (after `walkBlock`, before `walk`'s body).

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
  ##   SymexRefUnresolvedError, SymexRefVariantUnsupportedError
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
    # A field access through a ref/ptr to a VARIANT object is out of scope —
    # there is no flat positional layout to split a heap on (Feas-MED-4 / M17).
    if isField and stmt.dObjTy.kind in {itVariant, itMultiVariant}:
      raise (ref SymexRefVariantUnsupportedError)(
        msg: "field `." & stmt.dField & "` through a ref/ptr to variant object `" &
             $stmt.dObjTy & "` is unsupported (Cluster R R6: the field-split heap " &
             "has no flat layout to split a variant on)")
    let sortTy = if isField: stmt.dObjTy else: stmt.dElemTy
    let typeId = refPointeeTypeId(sortTy)
    let heapKey = if isField: fieldHeapKey(stmt.dObjTy, stmt.dField) else: typeId
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
          raise (ref SymexRefUnresolvedError)(
            msg: "deref of non-ref/ptr SymVal kind=" & $refSV.kind &
                 " (Cluster R R1 expects an svRef/svPtr at the deref site)")
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
      for cp in nilDerefFork(p, refAst, sortTy, w):
        if w.shouldStop: return survivors
        var newEnv = cp.env
        # Materialise the per-path heap (field-split array for a field deref) on
        # first use. The ref SORT keys on the OBJECT; the value sort on the field.
        var heap: Z3AnyAst
        if cp.heaps.hasKey(heapKey):
          heap = cp.heaps[heapKey]
        else:
          let refSort = allocRefSort(ctx, sortTy)
          heap = mkHeapArrayVar(ctx, refSort, stmt.dElemTy,
                                "heap_" & heapKey)
        let valSV = heapSelect(ctx, heap, refAst, stmt.dElemTy)
        newEnv[stmt.dRetName] = valSV
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
        var child = forkPath(cp, cp.pc, newEnv, cp.uncertain)
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
      var child = forkPath(p, p.pc, p.env, p.uncertain)
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
    if isField and stmt.dwObjTy.kind in {itVariant, itMultiVariant}:
      raise (ref SymexRefVariantUnsupportedError)(
        msg: "field-write `." & stmt.dwField & " = …` through a ref/ptr to " &
             "variant object `" & $stmt.dwObjTy & "` is unsupported (Cluster R R6)")
    let sortTy = if isField: stmt.dwObjTy else: stmt.dwElemTy
    let typeId = refPointeeTypeId(sortTy)
    let heapKey = if isField: fieldHeapKey(stmt.dwObjTy, stmt.dwField) else: typeId
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
          raise (ref SymexRefUnresolvedError)(
            msg: "deref-write through non-ref/ptr SymVal kind=" & $refSV.kind &
                 " (Cluster R R4 expects an svRef/svPtr at the write site)")
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
        var child = forkPath(cp, cp.pc, cp.env, cp.uncertain)
        child.heaps[heapKey] = storedHeap
        survivors.add child
    survivors
  else:
    raise newException(ValueError,
      "walkHeapArm: unexpected stmt.kind=" & $stmt.kind &
      " (not isDeref/isNew/isDerefWrite)")
