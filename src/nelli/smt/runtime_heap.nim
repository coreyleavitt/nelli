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

proc sanitizeTypeId(base: string): string =
  ## The heap/sort-name spelling of a type id: every character outside
  ## `[A-Za-z0-9_]` becomes `_` (split out of `refPointeeTypeId` at RFC-0005
  ## S8bh, whose `fieldHeapKey` spells a declaring type's id the same way).
  result = base
  for i in 0 ..< result.len:
    if result[i] notin {'a'..'z', 'A'..'Z', '0'..'9', '_'}:
      result[i] = '_'

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
  ##
  ## RFC-0005 S8j: a variant pointee keys on its `vNominalId` the same way.
  ## An inline `ref Obj` field's pointee is the empty-fielded placeholder
  ## tuple, keyed on `nominalId(Obj)`; when `Obj` is a case object, every
  ## other position (the nil in `h.v != nil`, the pointee of `h.v.kind`)
  ## carries the full variant. Keyed structurally, the two were distinct
  ## sorts for one Nim type: a Z3 sort error, or a false `sxUnsat`.
  ## RFC-0005 S8l: a multi-variant keys on its `mvNominalId` for the same
  ## reason (an inline `ref MV` field was that sort error).
  ## RFC-0005 S8bh (item 3): a type of an inheritance hierarchy keys on the
  ## hierarchy's ROOT (`inheritChain[0]`): every ref of the hierarchy is an
  ## address of one sort, as in Nim, where `Base(d)` is `d`'s own address.
  let base = if pointeeTy.kind == itTuple and pointeeTy.inheritChain.len > 0:
               pointeeTy.inheritChain[0]
             elif pointeeTy.kind == itVariant and
                  pointeeTy.vInheritChain.len > 0:
               pointeeTy.vInheritChain[0]   # RFC-0005 S8bn (item 8)
             elif pointeeTy.kind == itTuple and pointeeTy.nominalId.len > 0:
               pointeeTy.nominalId
             elif pointeeTy.kind == itVariant and pointeeTy.vNominalId.len > 0:
               pointeeTy.vNominalId
             elif pointeeTy.kind == itMultiVariant and pointeeTy.mvNominalId.len > 0:
               pointeeTy.mvNominalId   # RFC-0005 S8l
             else:
               $pointeeTy
  result = sanitizeTypeId(base)

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

proc ptrPreKey*(typeId: string): string =
  ## RFC-0005 S8bh. The `liveRefs` key of the objects of type `typeId` a
  ## pointer of unknown origin addresses: each predates every allocation.
  "@ptrpre:" & typeId

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
    not wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, b.raw))
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
  # RFC-0005 S8bh. And from every object a pointer of unknown origin has
  # addressed on this path (`ptrTargets`): each predates the walk. Not
  # capped: a ptr target's object is one per field family it reaches.
  for prior in path.liveRefs.getOrDefault(ptrPreKey(typeId), @[]):
    path.pc.add mkNeq(newRef, prior)
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

# ---- RFC-0005 S8ap: compound-sort heap cells ---------------------------------
# A heap array's value is one Z3 sort, and a seq / Table / HashSet value is
# not one term: it is a seq's data array and length, a table's data array,
# presence array and size, a set's member array and size (`allocateSym`'s
# `itSeq`/`itTable`/`itSet` arms). Before S8ap a field (or bare pointee) of
# such a type had no heap at all: `heapValueSort`'s `rawAnyAstOf` declined
# (`seUnsupportedCompoundSortLeaf`) and `liftHeapValue` havocked the read
# (`heUnsupportedPointeeRead`). It is now held LEAF-SPLIT: one heap array per
# leaf, all indexed by the same `Ref_T` address, under the field's key plus a
# per-leaf suffix (`heapLeafSuffixes`; leaf 0 keeps the key itself, so
# `heapKeyShapes[key]` still names the field's whole type). Each leaf array is
# an ordinary heap entry, so everything the scalar heap does per key --
# per-path copies (`forkPath`), the `ite` joins of a branch and a return
# merge, `heapMetaExtends`' key comparison -- applies leaf by leaf with no
# change. Aliasing is the scalar heap's: two equal addresses select the same
# cell of every leaf. A `string` is one Z3 term and keeps a single heap; it
# was already writable, and `liftHeapValue` lifts it now.
#
# Well-formedness. A free INPUT cell must be a value Nim can hold: a length or
# size in `[0, 1024]` (the bound every free seq/table/set gets, `allocateSym`),
# a string of bytes (ADR-0006), a table's and a set's size at least the
# number of distinct keys present (`ContainerCardRegistry`, whose extractors
# render exactly that content). `heapCellWfConds` asserts these of the input
# cell `select(heap_<leaf>, p)` at every read of a compound or string cell
# (`isDeref`, an arm-field read, a discriminator write's same-branch carry):
# the input heap holds the program's inputs, so a fact about every input cell
# is a fact of the program, for ANY address -- including one a write on this
# path has since overwritten, where the fact is merely unused. A written value
# needs none: the program built it. A cell no path reads is unconstrained,
# and cannot affect the path; the witness renderer (`renderHeapCompound`)
# renders such a cell as any well-formed value.

# RFC-0005 S8bc: `distinctGround`, `heapUnitTy`, `heapTreeTy`,
# `heapCompoundTy`, `heapPartLabel` and `heapParts` moved to `types.nim`:
# `isBackedSeqElemTy` (a seq whose element is a tree value is held
# leaf-split, one array per leaf) and the heap's cell model are one
# predicate, and the type bridge needs it at classify time.

proc heapStandInTy(ty: IRType): bool =
  ## RFC-0005 S8ar. A value no cell holds, by a stated, scoped decline: a
  ## by-value case object, a `distinct` over a composite base, and a tuple,
  ## object or array with a part that is not a cell value (`heapCompoundTy`'s
  ## docstring). Every read of such a cell is `liftHeapValue`'s
  ## `heUnsupportedPointeeRead` (a fresh symbol) and every store
  ## `heapCellStore`'s, so the cell's array holds no value of the type and
  ## its sort is a stand-in (`heapValueSort`: Bool). Before S8ar the sort
  ## derivation also recorded `seUnsupportedCompoundSortLeaf` for the same
  ## access, and a store built an ill-sorted term.
  ty != nil and not heapCompoundTy(ty) and
    ty.kind in {itVariant, itMultiVariant, itDistinct, itTuple, itArray}

proc heapWfTy(ty: IRType): bool =
  ## RFC-0005 S8ap. A heap value whose input cells carry a well-formedness
  ## fact (`heapCellWfConds`): the compound kinds and `string`.
  heapCompoundTy(ty) or (ty != nil and ty.kind == itString)

proc svPartsOf(sv: SymVal; ty: IRType): seq[SymVal] =
  ## RFC-0005 S8at. The parts of a tree value, in `heapParts` order.
  ## Precondition: `svFitsHeapTy(sv, ty)` (or `sv` a prototype of `ty`).
  case ty.kind
  of itTuple: result = sv.fields
  of itArray: result = sv.arrElems
  of itVariant:
    result.add sv.vDisc[]
    result.add sv.vPlainFields
    for arm in ty.vArms: result.add sv.vArmFields[arm.tagOrdinal]
  of itMultiVariant:
    result.add sv.mvPlainFields
    for xi, ax in ty.mvAxes:
      result.add sv.mvAxes[xi].disc[]
      for arm in ax.arms: result.add sv.mvAxes[xi].armFields[arm.tagOrdinal]
  else: discard

proc svWithParts(proto: SymVal; ty: IRType; parts: seq[SymVal]): SymVal =
  ## RFC-0005 S8at. `proto` with its parts replaced by `parts`
  ## (`svPartsOf`'s inverse). A discriminator is re-boxed: `vDisc` is a
  ## `ref`, shared with `proto` otherwise.
  result = proto
  var k = 0
  proc next(): SymVal =
    result = parts[k]
    inc k
  case ty.kind
  of itTuple:
    for i in 0 ..< result.fields.len: result.fields[i] = next()
  of itArray:
    for i in 0 ..< result.arrElems.len: result.arrElems[i] = next()
  of itVariant:
    let d = new(SymVal)
    d[] = next()
    result.vDisc = d
    for i in 0 ..< result.vPlainFields.len: result.vPlainFields[i] = next()
    for arm in ty.vArms:
      var fs = newSeq[SymVal](arm.fieldTypes.len)
      for j in 0 ..< fs.len: fs[j] = next()
      result.vArmFields[arm.tagOrdinal] = fs
  of itMultiVariant:
    for i in 0 ..< result.mvPlainFields.len: result.mvPlainFields[i] = next()
    for xi, ax in ty.mvAxes:
      let d = new(SymVal)
      d[] = next()
      result.mvAxes[xi].disc = d
      for arm in ax.arms:
        var fs = newSeq[SymVal](arm.fieldTypes.len)
        for j in 0 ..< fs.len: fs[j] = next()
        result.mvAxes[xi].armFields[arm.tagOrdinal] = fs
  else: discard

proc heapLeafSuffixes(ty: IRType): seq[string] =
  ## RFC-0005 S8ap. The key suffix of each leaf heap of a value of type `ty`,
  ## in `svLeafAsts` order. `@` cannot begin a Nim identifier, so no field
  ## key collides with a leaf key (and `renderCell`'s field scan skips them:
  ## a suffix holding `__` is never a field).
  ##
  ## RFC-0005 S8ar: a tuple / object / array part `x` holds its leaves under
  ## `__@.x` followed by the part's own suffixes, at every depth -- so no
  ## two paths share a key (`o.inner.x` is `__@.inner__@.x`, `o.x` is
  ## `__@.x`). A `distinct` has its (scalar) base's one leaf.
  if not heapCompoundTy(ty): return @[""]
  case ty.kind
  of itSeq:
    # RFC-0005 S8bc: a tree element's further leaves (`seqDataMore`), one
    # per leaf of the element after its first.
    var r = @["", "__@len"]
    if seqBackedTy(ty) and isTreeSeqElemTy(ty.seqElemTy):
      for i in 1 ..< heapLeafSuffixes(ty.seqElemTy).len: r.add "__@d" & $i
    r
  of itTable:
    # RFC-0005 S8at: a container value's further leaves (`tabDataMore`).
    var r = @["", "__@present", "__@len"]
    if isTableContainerValTy(ty.tabValTy):
      for i in 1 ..< heapLeafSuffixes(ty.tabValTy).len: r.add "__@v" & $i
    r
  of itSet:   @["", "__@len"]
  of itDistinct: heapLeafSuffixes(distinctGround(ty))   ## RFC-0005 S8at
  else:
    var r: seq[string]
    for part in heapParts(ty):
      for sub in heapLeafSuffixes(part.ty):
        r.add "__@." & part.label & sub
    r

proc heapStoreValue(valSV: SymVal; proto: SymVal; ty: IRType): SymVal

proc heapLeafRaw(sv: SymVal; ty: IRType): RawZ3Ast =
  ## RFC-0005 S8ar. The term a scalar part `sv` of type `ty` stores: an
  ## `int` part held as a Z3 Int (a promoted value) is the heap's bitvector
  ## of its width (`isDerefWrite`'s own svInt -> BV coercion).
  ##
  ## RFC-0005 batch 3: a signed `int` part of an Int-sorted heap
  ## (`intHeapCell`, S8as; every signed `int` since S8ax) is held as an
  ## Int, the sort `liftHeapValue` reads it back as and `heapValueSort`
  ## gives its leaf heap (from this term), as `heapStoreValue` stores a
  ## scalar cell. Before, S8ar's tree leaves stored the bit-vector while
  ## the read wrapped it as an Int: an ill-sorted term at the first
  ## comparison (`Sorts (_ BitVec 64) and Int are incompatible`).
  if ty.kind == itInt and intHeapCell(ty):
    return heapStoreValue(sv, sv, ty).zi.raw
  if ty.kind == itInt and sv.kind == svInt:
    case ty.width
    of 8:  return intToBv[8](sv.zi, Z3BitVec[8]).raw
    of 16: return intToBv[16](sv.zi, Z3BitVec[16]).raw
    of 32: return intToBv[32](sv.zi, Z3BitVec[32]).raw
    else:  return intToBv[64](sv.zi, Z3BitVec[64]).raw
  rawAnyAstOf(sv)

proc svLeafAsts(sv: SymVal; ty: IRType = nil): seq[RawZ3Ast] =
  ## RFC-0005 S8ap. The leaf terms of a compound value, in
  ## `heapLeafSuffixes` order. Precondition: `sv.kind` is the compound kind.
  ## RFC-0005 S8ar: a tree value's parts in order (`ty` names the parts'
  ## types; a part that is a scalar stores `heapLeafRaw`). Precondition for
  ## a tree: `svFitsHeapTy(sv, ty)`.
  if ty != nil and heapTreeTy(ty):
    if ty.kind == itDistinct:
      let g = distinctGround(ty)
      if heapCompoundTy(g): return svLeafAsts(ejectBase(sv), g)  ## RFC-0005 S8at
      return @[heapLeafRaw(ejectBase(sv), g)]
    let parts = heapParts(ty)
    let psvs = svPartsOf(sv, ty)   ## RFC-0005 S8at
    for i, part in parts:
      let psv = psvs[i]
      if heapCompoundTy(part.ty): result.add svLeafAsts(psv, part.ty)
      else: result.add heapLeafRaw(psv, part.ty)
    return
  case sv.kind
  of svSeq:
    # RFC-0005 S8bc: and a tree element's further data arrays.
    var r = @[sv.seqDataRaw.raw, sv.seqLen.raw] # [placeholder-audited]
    for m in sv.seqDataMore: r.add m.raw
    r
  of svTable:
    var r = @[sv.tabDataRaw.raw, sv.tabPresentRaw.raw, sv.tabSize.raw]
    for m in sv.tabDataMore: r.add m.raw   ## RFC-0005 S8at
    r
  of svSet:   @[sv.setMembersRaw.raw, sv.setSize.raw]
  else:       @[rawAnyAstOf(sv)]

proc heapLeafTerm(sv: SymVal; ty: IRType; pinForm = false): Z3AnyAst =
  ## RFC-0005 S8bc. `heapLeafRaw`, as an owning handle: an `int` part held as
  ## a Z3 Int is converted to the heap's bitvector, a term nothing else
  ## holds, so its raw handle is not valid past the call that made it.
  ##
  ## RFC-0005 batch 4: a signed `int` part (`intHeapCell`, S8ax) is held as
  ## an Int, as `heapLeafRaw` stores it and `svWithLeaves` reads it back
  ## (`liftHeapValue`). S8bc's tree seq data arrays were built from these
  ## terms at the bit-vector sort while every read lifted the select as an
  ## Int: an ill-sorted term at the first comparison, the defect batch 3
  ## fixed in `heapLeafRaw`.
  if pinForm and sv.kind in {svBV8, svBV16, svBV32, svBV64}:
    # RFC-0016 K10b: the value's own bit-vector, not its Int projection
    # (`ubv_to_int` under a sign `ite`): an equality on the projection made
    # every query the second walk's pins joined a mixed-theory one.
    return wrap[Z3AnyAst](requireCurrentContext(), rawAnyAstOf(sv))
  if ty.kind == itInt and intHeapCell(ty):
    return toAnyAst(heapStoreValue(sv, sv, ty).zi)
  if ty.kind == itInt and sv.kind == svInt:
    case ty.width
    of 8:  return toAnyAst(intToBv[8](sv.zi, Z3BitVec[8]))
    of 16: return toAnyAst(intToBv[16](sv.zi, Z3BitVec[16]))
    of 32: return toAnyAst(intToBv[32](sv.zi, Z3BitVec[32]))
    else:  return toAnyAst(intToBv[64](sv.zi, Z3BitVec[64]))
  wrap[Z3AnyAst](requireCurrentContext(), rawAnyAstOf(sv))

proc svLeafTerms(sv: SymVal; ty: IRType; pinForm = false): seq[Z3AnyAst] =
  ## RFC-0005 S8bc. `svLeafAsts`, as owning handles (`heapLeafTerm`). A seq
  ## element store writes a value's leaves into the seq's data arrays across
  ## several Z3 calls. Precondition for a tree: `svFitsHeapTy(sv, ty)`.
  if ty != nil and heapTreeTy(ty):
    if ty.kind == itDistinct:
      let g = distinctGround(ty)
      if heapCompoundTy(g): return svLeafTerms(ejectBase(sv), g, pinForm)
      return @[heapLeafTerm(ejectBase(sv), g, pinForm)]
    let psvs = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      if heapCompoundTy(part.ty): result.add svLeafTerms(psvs[i], part.ty, pinForm)
      else: result.add heapLeafTerm(psvs[i], part.ty, pinForm)
    return
  # A container's leaves are the value's own fields, alive while `sv` is.
  let ctx = requireCurrentContext()
  for raw in svLeafAsts(sv, ty): result.add wrap[Z3AnyAst](ctx, raw)

proc svFitsHeapTy(sv: SymVal; ty: IRType): bool =
  ## RFC-0005 S8ar. `sv` has the shape a cell of `ty` stores: a tree value
  ## part by part, a compound value of its kind (not a placeholder seq), a
  ## scalar of its kind (an `int` as a bitvector or a promoted Z3 Int). A
  ## value some upstream degrade produced may not.
  if ty == nil: return false
  case ty.kind
  of itDistinct: svFitsHeapTy(ejectBase(sv), distinctGround(ty))
  of itTuple:
    if sv.kind != svTuple or sv.fields.len != ty.fields.len: return false
    for i, f in ty.fields:
      if not svFitsHeapTy(sv.fields[i], f): return false
    true
  of itArray:
    if sv.kind != svArray or sv.arrElems.len != ty.size: return false
    for e in sv.arrElems:
      if not svFitsHeapTy(e, ty.elemTy): return false
    true
  of itVariant:
    # RFC-0005 S8at. Every arm's slot, of its arity.
    if sv.kind != svVariant or sv.vDisc == nil or
       sv.vPlainFields.len != ty.vPlainFieldTypes.len:
      return false
    for arm in ty.vArms:
      if not sv.vArmFields.hasKey(arm.tagOrdinal) or
         sv.vArmFields[arm.tagOrdinal].len != arm.fieldTypes.len:
        return false
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      if not svFitsHeapTy(ps[i], part.ty): return false
    true
  of itMultiVariant:
    if sv.kind != svMultiVariant or sv.mvAxes.len != ty.mvAxes.len or
       sv.mvPlainFields.len != ty.mvPlainFieldTypes.len:
      return false
    for xi, ax in ty.mvAxes:
      if sv.mvAxes[xi].disc == nil: return false
      for arm in ax.arms:
        if not sv.mvAxes[xi].armFields.hasKey(arm.tagOrdinal) or
           sv.mvAxes[xi].armFields[arm.tagOrdinal].len != arm.fieldTypes.len:
          return false
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      if not svFitsHeapTy(ps[i], part.ty): return false
    true
  of itSeq:
    # RFC-0005 S8bc: a placeholder seq type holds a placeholder value, a
    # backed one a backed value with one data array per element leaf.
    if sv.kind != svSeq: return false
    if not seqBackedTy(ty): return sv.isUnsupportedFieldPlaceholder # [placeholder-audited]
    if sv.isUnsupportedFieldPlaceholder: return false # [placeholder-audited]
    let want = if isTreeSeqElemTy(ty.seqElemTy):
                 heapLeafSuffixes(ty.seqElemTy).len else: 1
    1 + sv.seqDataMore.len == want
  of itTable: sv.kind == svTable
  of itSet: sv.kind == svSet
  of itInt:
    case sv.kind
    of svInt: true
    of svBV8: ty.width == 8
    of svBV16: ty.width == 16
    of svBV32: ty.width == 32
    of svBV64: ty.width == 64
    else: false
  of itBool: sv.kind == svBool
  of itFloat32: sv.kind == svFloat32
  of itFloat64: sv.kind == svFloat64
  of itString: sv.kind == svString
  of itRef: sv.kind == svRef
  of itPtr: sv.kind == svPtr
  else: false

proc liftHeapValue(ctx: Z3Context, valRaw: RawZ3Ast, pointeeTy: IRType): SymVal

proc svWithLeaves(ctx: Z3Context; proto: SymVal; leaves: seq[Z3AnyAst];
                  ty: IRType = nil): SymVal =
  ## RFC-0005 S8ap. `proto` (a value of the cell's type) with its leaf terms
  ## replaced by `leaves`. The inverse of `svLeafAsts`. The leaves are
  ## OWNING handles: a raw term Z3 has not been asked to keep is only valid
  ## until the next API call, so no caller holds raw leaves across calls.
  ##
  ## RFC-0005 S8ar: a tree value (`ty`) is rebuilt part by part, a scalar
  ## part lifted from its leaf (`liftHeapValue`; a `distinct` is its base
  ## re-boxed, `reboxDistinct`: the distinct constant is opaque, the base is
  ## the value).
  if ty != nil and heapTreeTy(ty):
    if ty.kind == itDistinct:
      let g = distinctGround(ty)
      if heapCompoundTy(g):   ## RFC-0005 S8at: the base's leaves, re-boxed
        return reboxDistinct(ty, svWithLeaves(ctx, ejectBase(proto), leaves, g))
      return liftHeapValue(ctx, leaves[0].raw, ty)
    var pos = 0
    let pprotos = svPartsOf(proto, ty)   ## RFC-0005 S8at
    var rebuilt: seq[SymVal]
    for i, part in heapParts(ty):
      let n = heapLeafSuffixes(part.ty).len
      let sub = leaves[pos ..< pos + n]
      pos += n
      rebuilt.add(
        if heapCompoundTy(part.ty): svWithLeaves(ctx, pprotos[i], sub, part.ty)
        else: liftHeapValue(ctx, sub[0].raw, part.ty))
    return svWithParts(proto, ty, rebuilt)
  result = proto
  case proto.kind
  of svSeq:
    result.seqDataRaw = leaves[0] # [placeholder-audited]
    result.seqLen = wrap[Z3Int](ctx, leaves[1].raw) # [placeholder-audited]
    result.seqDataMore = leaves[2 .. ^1]   ## RFC-0005 S8bc
  of svTable:
    result.tabDataRaw = leaves[0]
    result.tabPresentRaw = leaves[1]
    result.tabSize = wrap[Z3Int](ctx, leaves[2].raw)
    result.tabDataMore = leaves[3 .. ^1]   ## RFC-0005 S8at
  of svSet:
    result.setMembersRaw = leaves[0]
    result.setSize = wrap[Z3Int](ctx, leaves[1].raw)
  else: discard

proc heapValueSort(ctx: Z3Context, proto: SymVal, pointeeTy: IRType,
                   leaf = 0): RawZ3Sort =
  ## Phase 15 R1. The Z3 value sort of the heap array `Z3Array[Ref_T, T_sym]`
  ## for pointee type `pointeeTy` — i.e. the sort of the SymVal a deref yields.
  ## A throwaway prototype is allocated (its init constraints are discarded —
  ## only the sort is read), mirroring G4's `baseRep` sort probe.
  ## RFC-0005 S8ap: for a compound pointee, the sort of leaf `leaf`
  ## (`heapLeafSuffixes`). The prototype is now the CALLER's
  ## (`mkHeapArrayVar`), which keeps it alive until the array sort is built:
  ## the returned sort is a borrowed handle, and the sort of a table's or a
  ## set's leaf array is referenced by nothing else, so destroying the
  ## prototype here freed it before `Z3_mk_array_sort` read it (Z3: "invalid
  ## array sort definition, parameter is not a sort"). A scalar's sort is
  ## interned and never showed this.
  if intHeapCell(pointeeTy):   # RFC-0005 S8as: Int-sorted `int` heap
    return ctx.checkErr Z3_mk_int_sort(ctx.raw)
  if heapCompoundTy(pointeeTy):
    return ctx.checkErr Z3_get_sort(ctx.raw, svLeafAsts(proto, pointeeTy)[leaf])
  if heapStandInTy(pointeeTy):   ## RFC-0005 S8ar
    return ctx.checkErr Z3_mk_bool_sort(ctx.raw)
  ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(proto))

proc heapStoreValue(valSV: SymVal; proto: SymVal; ty: IRType): SymVal =
  ## RFC-0005 S8as. `valSV` in the heap's value sort for pointee/field type
  ## `ty`: an Int for an `intHeapCell` (a BV operand through `bv2int`,
  ## signed), otherwise `proto`'s bit-vector width for an svInt operand
  ## (the `int2bv` coercion every store site carried inline).
  if intHeapCell(ty):
    if valSV.kind in {svBV8, svBV16, svBV32, svBV64}:
      # RFC-0005 S8ax: through `toSvIntPreserving`, which records the
      # conversion (`intOfBV`), so a read meeting the same bit-vector again
      # meets it unconverted.
      var iv = toSvIntPreserving(valSV)
      iv.ziWidth = ty.width
      iv.ziSigned = true
      return iv
    return valSV
  result = valSV
  if valSV.kind == svInt:
    case proto.kind
    of svBV8:  result = liftBV(intToBv[8](valSV.zi, Z3BitVec[8]),  proto.signed)
    of svBV16: result = liftBV(intToBv[16](valSV.zi, Z3BitVec[16]), proto.signed)
    of svBV32: result = liftBV(intToBv[32](valSV.zi, Z3BitVec[32]), proto.signed)
    of svBV64: result = liftBV(intToBv[64](valSV.zi, Z3BitVec[64]), proto.signed)
    else: discard

proc mkHeapArrayVar(ctx: Z3Context, refSort: RawZ3Sort,
                    pointeeTy: IRType, name: string,
                    variantTy: IRType = nil, leaf = 0): Z3AnyAst =
  ## Phase 15 R1 (ADR-0010). Build a FREE `Z3Array[Ref_T, T_sym]` variable —
  ## the initial heap for one pointee type on one path. The key sort `Ref_T`
  ## is a RUNTIME uninterpreted sort, so the typed `mkArrayVar[K, V]` (which
  ## needs static K/V) cannot express it; we go through raw FFI
  ## (`Z3_mk_array_sort` + `Z3_mk_const`) and erase to `Z3AnyAst`. The result
  ## is a GROUND free array — every `select` on it is decidable (QF_AUFLIA-ish);
  ## NO universal-∀ axiom is ever asserted over the uninterpreted sort (the G4
  ## hang lesson).
  ##
  ## RFC-0005 S8h: records the heap's value type -- and `variantTy`, the
  ## variant object, for a discriminator or branch-field heap -- in
  ## `heapKeyShapes` under the key (`name` less its `heap_` prefix), for
  ## `buildHeapSnapshot`, which renders the witness from the input constant
  ## this builds.
  ##
  ## RFC-0005 S8ap: `leaf` selects one leaf heap of a compound value
  ## (`heapLeafSuffixes`); only leaf 0, whose key is the field's own, records
  ## a shape.
  var key = if name.startsWith("heap_"): name["heap_".len .. ^1] else: name
  # RFC-0005 S8ar: a tree value's leaf 0 is not at the cell's own key
  # (`__@.<part>`); its shape is recorded under the cell's key.
  let suffix0 = heapLeafSuffixes(pointeeTy)[0]
  if leaf == 0 and suffix0.len > 0 and key.endsWith(suffix0):
    key.setLen(key.len - suffix0.len)
  # RFC-0005 S8ax: a havocked heap's constant (`heapInputName`, `@ep<n>`) is
  # not an input heap: the witness renders the input one.
  if leaf == 0 and "@ep" notin key and (not heapKeyShapes.hasKey(key) or
     (variantTy != nil and heapKeyShapes[key].variantTy == nil)):
    heapKeyShapes[key] = HeapKeyShape(valTy: pointeeTy, variantTy: variantTy)
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(pointeeTy, "__heapValSort", scratchPC)
  let valSort = heapValueSort(ctx, proto, pointeeTy, leaf)
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
    if intHeapCell(pointeeTy):   # RFC-0005 S8as: an Int-sorted `int` heap
      return SymVal(kind: svInt, zi: wrap[Z3Int](ctx, valRaw),
                    ziWidth: pointeeTy.width, ziSigned: true)
    case pointeeTy.width
    of 8:  liftBV(wrap[Z3BitVec[8]](ctx, valRaw),  pointeeTy.signed)
    of 16: liftBV(wrap[Z3BitVec[16]](ctx, valRaw), pointeeTy.signed)
    of 32: liftBV(wrap[Z3BitVec[32]](ctx, valRaw), pointeeTy.signed)
    of 64: liftBV(wrap[Z3BitVec[64]](ctx, valRaw), pointeeTy.signed)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always 8/16/32/64)]
        "liftHeapValue: unsupported int width " & $pointeeTy.width)
  of itBool:   ofBool(wrap[Z3Bool](ctx, valRaw))
  of itString:
    # RFC-0005 S8ap. A `string` field is one Z3 string term: its heap was
    # already written (`p.name = "ab"` stored it), and a read is the select
    # itself. Before S8ap the read fell to the `else` arm below and was
    # havocked (`heUnsupportedPointeeRead`). The input cell's byte-range fact
    # is asserted by the read site (`heapCellWfConds`).
    SymVal(kind: svString, str: wrap[Z3String](ctx, valRaw))
  of itFloat32: SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, valRaw))
  of itFloat64: SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, valRaw))
  of itDistinct:
    # RFC-0005 S8ar. A `distinct` cell holds its base's leaves
    # (`heapCompoundTy`), so a scalar base's term is the base value; the
    # distinct constant is opaque and fresh (`reboxDistinct`). Before S8ar a
    # distinct field was havocked (the `else` arm below), as one over a
    # composite base still is (it has no distinct sort to re-box into).
    if heapCompoundTy(pointeeTy):
      reboxDistinct(pointeeTy, liftHeapValue(ctx, valRaw, pointeeTy.distinctBase))
    else:
      degradeAlloc(pointeeTy, heUnsupportedPointeeRead,
        "deref of `ref/ptr " & $pointeeTy & "` (a distinct over a " &
        "composite base) not modeled", "__liftHeapValueUnsupported")
  of itBitSet:   ## RFC-0005 S8bq: a builtin set field is one bit-vector
    bitSetSV(wrap[Z3AnyAst](ctx, valRaw), pointeeTy.bsElemTy)
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
    # kind (`heUnresolvedRef` until S4) and marks the run degraded immediately/globally
    # (Invariant 3), then a FRESH placeholder SymVal of the SAME pointee
    # type keeps the Z3 API call chain type-sound (mirrors `seqElemAt`'s own
    # unsupported-elem-kind idiom, `runtime.nim`) -- its CONTENT is never
    # trustworthy, only its SORT needs to be well-formed. Every
    # `heapSelect`/`liftHeapValue` call site in this file drains the pending
    # degrade into the surviving path's own `uncertain` flag (SND-1)
    # immediately after the select, so a path whose OWN read just degraded
    # can never mint a bogus winning `sxSat`.
    #
    # RFC-0005 S4 (walker v142): this arm is the `allocDegrade` funnel's one
    # FRESH-SYMBOL site, so it records its own kind,
    # `heUnsupportedPointeeRead` (`classOf` = `dcFreshSymbol`: the run keeps
    # `sxUnsat` available, the path is a replay candidate) -- split off
    # `heUnresolvedRef`, whose other sites substitute rather than havoc (see
    # `classOf`'s row for it). That class is licensed ONLY by §2.1's
    # introduction invariant -- the substituted symbol carries NO constraint
    # at introduction -- which the pre-S4 spelling violated:
    # `allocateSym(pointeeTy, "__liftHeapValueUnsupported", ...)` named every
    # occurrence identically, so two reads of two DIFFERENT cells (`a.s`,
    # `b.s`) were the SAME Z3 constant -- an equality reality does not
    # impose, i.e. an under-approximation that proved `a.s != b.s`
    # unreachable (a false `sxUnsat` once the class stopped being ⊤; pinned
    # RED in `tests/tsymex_rfc0005_s4_alloc.nim`). `degradeAlloc` pairs the
    # record with a `freshDegradeName`-uniquified allocation and discards
    # `allocateSym`'s init-side `pcOut` (the byte-faithful char-range /
    # length-ceiling well-formedness facts) -- so each read is a fresh,
    # wholly unconstrained symbol of the pointee's own type.
    #
    # RFC-0005 S8ar: the message states the scope. A by-value case object is
    # not a cell value (`heapCompoundTy`: its fields depend on its
    # discriminator, and the arm-keyed layout a REF case object has does not
    # nest); neither is a tuple or array holding a part that is not one. The
    # pre-S8ar text ("composite pointees land R3+") predated every compound
    # cell.
    let why =
      if pointeeTy.kind in {itVariant, itMultiVariant}:
        "a by-value case object is not a heap cell value: its fields " &
          "depend on its discriminator"
      elif pointeeTy.kind in {itTuple, itArray}:
        "a part of it is not a heap cell value"
      else:
        "not a heap cell value"
    degradeAlloc(pointeeTy, heUnsupportedPointeeRead,
      "deref of `ref/ptr " & $pointeeTy & "` not modeled: " & why &
      " (RFC-0005 S8ar, scoped to this read)",
      "__liftHeapValueUnsupported")

var storeDeclKind {.threadvar.}: int
  ## RFC-0005 S8ax. The `Z3_decl_kind` ordinal of an array store, read off a
  ## probe term (as `seqCapKinds` does); 0 until first read.

proc storedAt(ctx: Z3Context; arr, idx: RawZ3Ast): Option[RawZ3Ast] =
  ## RFC-0005 S8ax. The value `arr` holds at `idx` when `arr` is a store at
  ## that same term (`store(h, idx, v)`), or `none`.
  if storeDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let probe = mkArrayVar[Z3Int, Z3Int](pc, "__s8ax_store_probe")
    let st = checkedStore(pc, probe.raw, mkInt(pc, 0).raw,
                          mkInt(pc, 0).raw)
    storeDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, st)))) + 1
  if Z3_get_ast_kind(ctx.raw, arr) != Z3_APP_AST: return none(RawZ3Ast)
  let app = Z3_to_app(ctx.raw, arr)
  if ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1 !=
     storeDeclKind or Z3_get_app_num_args(ctx.raw, app) != 3:
    return none(RawZ3Ast)
  if cast[pointer](Z3_get_app_arg(ctx.raw, app, 1)) != cast[pointer](idx):
    return none(RawZ3Ast)
  some(Z3_get_app_arg(ctx.raw, app, 2))

var selectDeclKind {.threadvar.}: int
  ## RFC-0005 S8bu. The `Z3_decl_kind` ordinal (+ 1) of an array `select`,
  ## read off a probe term as `storeDeclKind` is.

proc peelSelect(ctx: Z3Context; t: RawZ3Ast): RawZ3Ast =
  ## RFC-0005 S8bu. `t` with each `select(store(a, i, v), i)` (the same
  ## index term) read as `v`: a cell's value read back after it was stored.
  if storeDeclKind == 0:
    discard storedAt(ctx, t, t)   # reads `storeDeclKind`
  if selectDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let probe = mkArrayVar[Z3Int, Z3Int](pc, "__s8bu_select_probe")
    let sel = checkedSelect(pc, probe.raw, mkInt(pc, 0).raw)
    selectDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, sel)))) + 1
  result = t
  for _ in 0 ..< 100_000:
    if Z3_get_ast_kind(ctx.raw, result) != Z3_APP_AST: return
    let app = Z3_to_app(ctx.raw, result)
    if ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1 !=
       selectDeclKind or Z3_get_app_num_args(ctx.raw, app) != 2:
      return
    let v = storedAt(ctx, Z3_get_app_arg(ctx.raw, app, 0),
                     Z3_get_app_arg(ctx.raw, app, 1))
    if v.isNone: return
    result = v.get

var constArrayDeclKind {.threadvar.}: int
  ## RFC-0005 batch 4. The `Z3_decl_kind` ordinal (+ 1) of a constant array
  ## (`(as const ...)`), read off a probe term as `storeDeclKind` is.

proc constFalseStoreKeys(ctx: Z3Context; arr: RawZ3Ast): Option[seq[RawZ3Ast]] =
  ## RFC-0005 batch 4. The index terms of `arr` when it is a chain of
  ## `store`s over the constant-false array (`store(...store(K false, k1,
  ## v1)..., kn, vn)`, a table's presence array built from the empty table),
  ## or `none`. A term `x` with `select(arr, x)` true is then one of
  ## `k1..kn`: any other reads the base, false. A theorem of the array
  ## theory, so asserting it prunes no model.
  if storeDeclKind == 0:
    discard storedAt(ctx, arr, arr)   # reads `storeDeclKind`
  if constArrayDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let s = pc.checkErr Z3_get_sort(pc.raw, mkInt(pc, 0).raw)
    let probe = pc.checkErr Z3_mk_const_array(pc.raw, s, mkBool(pc, false).raw)
    constArrayDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, probe)))) + 1
  var keys: seq[RawZ3Ast]
  var a = arr
  while true:
    if Z3_get_ast_kind(ctx.raw, a) != Z3_APP_AST: return none(seq[RawZ3Ast])
    let app = Z3_to_app(ctx.raw, a)
    let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1
    if k == storeDeclKind and Z3_get_app_num_args(ctx.raw, app) == 3:
      keys.add Z3_get_app_arg(ctx.raw, app, 1)
      a = Z3_get_app_arg(ctx.raw, app, 0)
    elif k == constArrayDeclKind and Z3_get_app_num_args(ctx.raw, app) == 1:
      if Z3_get_bool_value(ctx.raw, Z3_get_app_arg(ctx.raw, app, 0)) != Z3_L_FALSE:
        return none(seq[RawZ3Ast])
      return some(keys)
    else:
      return none(seq[RawZ3Ast])

var iteDeclKind {.threadvar.}: int
  ## RFC-0005 S8ax. The `Z3_decl_kind` ordinal of an `ite`, read off a probe
  ## term as `storeDeclKind` is; 0 until first read.

var intCellFactSeen {.threadvar.}: HashSet[uint]
  ## RFC-0005 S8ax. The `select(base, idx)` terms `intCellRangeFacts` has
  ## bounded this run, by address (each fact holds its term, so the address
  ## is not reused while it is listed). Reset by `resetSymexRunState`.

proc intCellRangeFacts(ctx: Z3Context; arr, idx: RawZ3Ast; ty: IRType) =
  ## RFC-0005 S8ax. An Int-sorted heap (`intHeapCell`) holds, at every
  ## address, a value of its Nim type, but nothing in the Int sort says so:
  ## an input cell read unchanged was any integer, so `b.n + 1`'s overflow
  ## raise was SAT with `b.n` below `low(int)`, and extracting that model's
  ## witness raised out of the walk, which ended it with nothing recorded (a
  ## false `sxUnsat` on the target the walk never reached). Each heap
  ## constant `arr` reads through -- the input heap, or the fresh one an
  ## opaque call havocs, under any `store` and `ite` the walk built over it
  ## -- gets its type's bounds at `idx` (`globalEntryFacts`): true of every
  ## real heap at every address, so asserting it anywhere prunes no real
  ## execution.
  if storeDeclKind == 0 or iteDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let a = mkArrayVar[Z3Int, Z3Int](pc, "__s8ax_chain_probe_a")
    let b = mkArrayVar[Z3Int, Z3Int](pc, "__s8ax_chain_probe_b")
    let st = checkedStore(pc, a.raw, mkInt(pc, 0).raw, mkInt(pc, 0).raw)
    storeDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, st)))) + 1
    let it = checkedIte(pc, mkBoolVar(pc, "__s8ax_chain_probe_c").raw,
                        a.raw, b.raw)
    iteDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, it)))) + 1
  var lo, hi: int64
  if ty.hasRange:
    lo = ty.rangeLo
    hi = ty.rangeHi
  elif ty.width in [8, 16, 32]:
    lo = -(1'i64 shl (ty.width - 1))
    hi = (1'i64 shl (ty.width - 1)) - 1
  else:
    lo = low(int64)
    hi = high(int64)
  var todo = @[arr]
  while todo.len > 0:
    let a = todo.pop()
    if Z3_get_ast_kind(ctx.raw, a) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, a)
    let n = Z3_get_app_num_args(ctx.raw, app)
    if n == 0:
      let sel = checkedSelect(ctx, a, idx)
      let key = cast[uint](cast[pointer](sel))
      if key notin intCellFactSeen:
        intCellFactSeen.incl key
        let v = wrap[Z3Int](ctx, sel)
        globalEntryFacts.add(v >= mkZ3IntLit(lo))
        globalEntryFacts.add(v <= mkZ3IntLit(hi))
      continue
    let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1
    if k == storeDeclKind and n == 3:
      todo.add Z3_get_app_arg(ctx.raw, app, 0)
    elif k == iteDeclKind and n == 3:
      todo.add Z3_get_app_arg(ctx.raw, app, 1)
      todo.add Z3_get_app_arg(ctx.raw, app, 2)

proc heapSelect(ctx: Z3Context, heap: Z3AnyAst, refAst: Z3AnyAst,
                pointeeTy: IRType): SymVal =
  ## Phase 15 R1 (ADR-0010). The GROUND heap read `select(heap, p)` — a single
  ## `Z3_mk_select` over the free heap array at the abstract address `p`. The
  ## result is the value-sorted ast; lift it into a SymVal. This is the whole
  ## of R1's deref: a decidable array select, NO quantifier (the G4 lesson —
  ## a ∀ over the uninterpreted Ref_T sort would HANG Z3).
  # RFC-0005 S8ax: a read at the address the heap's last store wrote is
  # that store's value, read off the term (`select(store(h, a, v), a)` is
  # `v`), so a value stored and read back is the same term: the bit-vector
  # an Int-sorted heap stored then meets its source unconverted
  # (`intOfBV`).
  let hit = storedAt(ctx, heap.raw, refAst.raw)
  if hit.isNone and intHeapCell(pointeeTy):
    intCellRangeFacts(ctx, heap.raw, refAst.raw, pointeeTy)   # RFC-0005 S8ax
  let valRaw = if hit.isSome: hit.get
               else: checkedSelect(ctx, heap.raw, refAst.raw)
  liftHeapValue(ctx, valRaw, pointeeTy)

type HeapCell = seq[tuple[key: string; arr: Z3AnyAst]]
  ## RFC-0005 S8ap. The leaf heaps of one cell's value: one entry for a
  ## scalar, one per `heapLeafSuffixes` entry for a compound value.

proc heapCellArrays(ctx: Z3Context; p: Path; key: string; refSort: RawZ3Sort;
                    valTy: IRType; variantTy: IRType = nil): HeapCell =
  ## RFC-0005 S8ap. The heaps of `key` on path `p` -- each leaf's current
  ## array, or its free input constant `heap_<leafKey>` when the path has
  ## not touched it yet. Reads `p`, never writes it: the caller stores the
  ## arrays on the path it continues with.
  for i, suffix in heapLeafSuffixes(valTy):
    let k = key & suffix
    if p.heaps.hasKey(k):
      result.add (k, p.heaps[k])
    else:
      result.add (k, mkHeapArrayVar(ctx, refSort, valTy, heapInputName(p, k),
                                    (if i == 0: variantTy else: nil), i))

proc heapCellSelect(ctx: Z3Context; cell: HeapCell; refAst: Z3AnyAst;
                    valTy: IRType): SymVal =
  ## RFC-0005 S8ap. The value at `refAst`: `heapSelect` for a scalar; for a
  ## compound value, a prototype of `valTy` whose leaves are the selects of
  ## each leaf heap (the prototype's own constants, and its init facts, are
  ## discarded -- only its kind and element types are kept).
  if not heapCompoundTy(valTy):
    return heapSelect(ctx, cell[0].arr, refAst, valTy)
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(valTy, "__heapCellProto", scratchPC)
  var leaves: seq[Z3AnyAst]
  for c in cell:
    leaves.add wrap[Z3AnyAst](ctx, checkedSelect(ctx, c.arr.raw, refAst.raw))
  svWithLeaves(ctx, proto, leaves, valTy)

proc svCellWf(sv: SymVal; ty: IRType; nested: bool; bounded = true): seq[Z3Bool] =
  ## RFC-0005 S8ap (was `heapCellWfConds`' body); S8ar: recursive over a
  ## tree value's parts. The facts a free value of `ty` has (`allocateSym`'s
  ## init facts): a string of bytes, a length or size in `[0, 1024]`, a
  ## table's and a set's size tied to its keys (`ContainerCardRegistry`),
  ## and -- for a NESTED scalar part, which no read site sees -- its declared
  ## range (`rangeCondsIfNeeded`; a cell's own scalar range is the read
  ## site's).
  ##
  ## RFC-0005 S8bc: `bounded = false` drops the `1024` upper bounds, keeping
  ## the rest. A seq ELEMENT's facts are asserted at every read of it, and an
  ## element the body stored may hold a longer seq (`newSeq(n)`), so the
  ## input bound would be a false fact there (a false unsat).
  case sv.kind
  of svString:
    @[matches(sv.str, star(range(mkString("\x00"), mkString("\xff"))))]
  of svSeq:
    if bounded: @[sv.seqLen >= mkInt(0), sv.seqLen <= mkInt(1024)] # [placeholder-audited]
    else: @[sv.seqLen >= mkInt(0)] # [placeholder-audited]
  of svTable:
    registerTableBase(sv.tabPresentRaw, sv.tabSize, ty.tabKeyTy)
    registerTabTreeBase(sv)   ## RFC-0005 S8at
    if bounded: @[sv.tabSize >= mkInt(0), sv.tabSize <= mkInt(1024)]
    else: @[sv.tabSize >= mkInt(0)]
  of svSet:
    registerSetBase(sv.setMembersRaw, sv.setSize, ty.setElemTy)
    if bounded:
      @[sv.setSize >= mkInt(0),
        sv.setSize <= mkInt(min(1024'i64, cellDomainSize(ty.setElemTy)))]
    else:
      @[sv.setSize >= mkInt(0), sv.setSize <= mkInt(cellDomainSize(ty.setElemTy))]
  of svTuple:
    var r: seq[Z3Bool]
    for i, f in sv.fields: r.add svCellWf(f, ty.fields[i], true, bounded)
    r
  of svArray:
    var r: seq[Z3Bool]
    for e in sv.arrElems: r.add svCellWf(e, ty.elemTy, true, bounded)
    r
  of svDistinct:
    svCellWf(ejectBase(sv), distinctGround(ty), nested, bounded)
  of svVariant, svMultiVariant:
    # RFC-0005 S8at. Each part's facts, and each discriminator in its
    # legal domain (`allocateSym`'s clause: an `else` arm's ordinals
    # included, its sentinel not).
    var r: seq[Z3Bool]
    if not heapTreeTy(ty) or not svFitsHeapTy(sv, ty): return r
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty): r.add svCellWf(ps[i], part.ty, true, bounded)
    proc domainClause(d: SymVal; ordSet: seq[int]) =
      if ordSet.len == 0: return
      var clause = variantDiscEq(d, int64(ordSet[0]))
      for k in 1 ..< ordSet.len:
        clause = clause or variantDiscEq(d, int64(ordSet[k]))
      r.add clause
    if sv.kind == svVariant:
      domainClause(sv.vDisc[], discriminatorDomain(ty)[2])
    else:
      for xi, ax in ty.mvAxes:
        domainClause(sv.mvAxes[xi].disc[], axisDiscriminatorDomain(ax)[2])
    r
  else:
    if nested: rangeCondsIfNeeded(sv, ty) else: @[]

proc heapCellWfConds(ctx: Z3Context; key: string; refSort: RawZ3Sort;
                     valTy: IRType; refAst: Z3AnyAst): seq[Z3Bool] =
  ## RFC-0005 S8ap. The well-formedness of the INPUT cell at `refAst` (see
  ## the section comment above): the facts `allocateSym` gives a free value
  ## of `valTy`, stated of `select(heap_<leaf>, refAst)` for every leaf. A
  ## table's and a set's cell is also registered with the
  ## `ContainerCardRegistry`, which ties its size to the keys present at
  ## every check and is what `extractTableEntries`/`extractSetMembers`
  ## render. Empty for any other type (a scalar's range facts are the read
  ## site's `rangeCondsIfNeeded`, unchanged).
  if not heapWfTy(valTy): return @[]
  var input: HeapCell
  for i, suffix in heapLeafSuffixes(valTy):
    input.add (key & suffix,
               mkHeapArrayVar(ctx, refSort, valTy, "heap_" & key & suffix, nil, i))
  let sv = heapCellSelect(ctx, input, refAst, valTy)
  svCellWf(sv, valTy, false)

proc heapCellStore(ctx: Z3Context; cell: HeapCell; refAst: Z3AnyAst;
                   valSV: SymVal; valTy: IRType): HeapCell =
  ## RFC-0005 S8ap. `cell` with `valSV` stored at `refAst`, leaf by leaf. A
  ## scalar keeps the pre-S8ap single store (`rawAnyAstOf`, whose own decline
  ## is unchanged). A compound value whose kind does not match `valTy` (a
  ## value some upstream degrade produced: a placeholder seq, a `seq[byte]`
  ## held as a string) has no leaves to store: it is recorded as
  ## `seUnsupportedCompoundSortLeaf` through `allocDegrade` (drained onto the
  ## path by the caller, as the scalar store's decline is) and each leaf
  ## stores a fresh term of its sort.
  if heapStandInTy(valTy):
    # RFC-0005 S8ar: a by-value case object, a distinct over a composite
    # base, or an aggregate with a part that is neither, is not a cell value
    # (`heapStandInTy`; a read of it is `liftHeapValue`'s stated decline).
    # The scalar store below built an ill-sorted term for a distinct
    # (`weInternalWalkerFault`) and `seUnsupportedCompoundSortLeaf` for the
    # others. Declined the same way as the read, and the cell holds a fresh
    # term of its sort.
    let what =
      case valTy.kind
      of itDistinct: "a distinct over a composite base"
      of itTuple, itArray: "a part of it is not a heap cell value"
      else: "a by-value case object"
    allocDegrade(heUnsupportedPointeeRead,
      "heap store into a `" & $valTy & "` cell (" & what & ") not modeled")
    let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, cell[0].arr.raw)
    let fresh = freshOfSort(ctx,
      ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort))
    return @[(cell[0].key, wrap[Z3AnyAst](ctx,
      checkedStore(ctx, cell[0].arr.raw, refAst.raw, fresh)))]
  if not heapCompoundTy(valTy):
    # RFC-0005 batch 3: an `int` value in its heap's sort (`heapLeafRaw`:
    # an Int for an Int-sorted heap, else the bit-vector of its width), as
    # a tree value's leaves are; S8at's whole store of a ref case object
    # passed a constructor's bit-vector part into an Int-sorted field heap.
    let raw = if valTy != nil: heapLeafRaw(valSV, valTy)
              else: rawAnyAstOf(valSV)
    return @[(cell[0].key, wrap[Z3AnyAst](ctx,
      checkedStore(ctx, cell[0].arr.raw, refAst.raw, raw)))]
  # RFC-0005 S8ar: the shape check is recursive (`svFitsHeapTy`), for a
  # tree value's parts.
  let fits = svFitsHeapTy(valSV, valTy)
  var leaves: seq[Z3AnyAst]
  if fits:
    for raw in svLeafAsts(valSV, valTy): leaves.add wrap[Z3AnyAst](ctx, raw)
  else:
    allocDegrade(seUnsupportedCompoundSortLeaf,
      "heap store of a " & plainEnglishSymValKind(valSV.kind) & " into a `" &
      $valTy & "` cell: the value has no leaves of that type " &
      "(seUnsupportedCompoundSortLeaf)")
    for c in cell:
      let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, c.arr.raw)
      leaves.add wrap[Z3AnyAst](ctx, freshOfSort(ctx,
        ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort)))
  for i, c in cell:
    result.add (c.key, wrap[Z3AnyAst](ctx,
      checkedStore(ctx, c.arr.raw, refAst.raw, leaves[i].raw)))

proc heapCellIte(ctx: Z3Context; cond: Z3Bool; t, e: SymVal;
                 ty: IRType): SymVal =
  ## RFC-0005 S8ap. `if cond: t else: e` for two values of a cell of type
  ## `ty`. `iteSV` havocs a seq / Table / HashSet / string merge
  ## (`feUnsupportedOpHavoc`: its operands are not one term); two cells of
  ## one heap type have the same leaf sorts, so the merge is an `ite` per
  ## leaf. Used where a heap read selects among several arms' cells (an arm
  ## field shared by several tags, a discriminator write's carry).
  if t.kind == svString and e.kind == svString:
    return SymVal(kind: svString, str: wrap[Z3String](ctx,
      checkedIte(ctx, cond.raw, t.str.raw, e.str.raw)))
  if not heapCompoundTy(ty) or not svFitsHeapTy(t, ty) or not svFitsHeapTy(e, ty):
    return iteSV(cond, t, e)
  let tl = svLeafAsts(t, ty)
  let el = svLeafAsts(e, ty)
  var leaves: seq[Z3AnyAst]
  for i in 0 ..< tl.len:
    leaves.add wrap[Z3AnyAst](ctx, checkedIte(ctx, cond.raw, tl[i], el[i]))
  svWithLeaves(ctx, t, leaves, ty)

proc heapCellZero(ty: IRType): SymVal =
  ## RFC-0005 S8ap. Nim's zero of a compound cell (`new`, an object
  ## constructor's omitted field): the empty seq / Table / HashSet,
  ## `defaultZero`'s constant.
  defaultZero(ty, "__heapCellZero")

proc fieldHeapKey*(objTy: IRType, field: string): string =
  ## Phase 15 R6 (ADR-0010). The field-split heap key for `(objTy, field)`. An
  ## object pointee cannot be a single Z3 array VALUE sort (there is no Z3 tuple
  ## sort — C0-ADR), so each field gets its OWN heap array `Z3Array[Ref_T,
  ## <fieldSort>]`, keyed by the object's `refPointeeTypeId` + the field NAME
  ## (unique across the flat inheritance layout — Nim forbids field shadowing).
  ## The `Ref_T` SORT still keys on the OBJECT (`refPointeeTypeId(objTy)`), so
  ## every field of one ref shares a single abstract address (aliasing observed).
  ##
  ## RFC-0005 S8bh (item 3): a field of an inheritance hierarchy keys on the
  ## type that DECLARES it (`ownedFieldIds`), not on the static type it is
  ## read through: `d.x` (static `Derived`) and `b.x` (static `Base`) are one
  ## heap, and siblings' same-named fields are two. A field the type does
  ## not list (a tag level, `@lvl<j>`, or a type without `of`) keeps the
  ## `refPointeeTypeId` key -- the hierarchy's root for a tag level.
  if objTy != nil and objTy.kind == itTuple:
    let i = objTy.ownedFieldNames.find(field)
    if i >= 0 and i < objTy.ownedFieldIds.len:
      return sanitizeTypeId(objTy.ownedFieldIds[i]) & "__" & field
  # RFC-0005 S8bn (item 8): a case-object hierarchy's plain field likewise.
  if objTy != nil and objTy.kind == itVariant:
    let i = objTy.vOwnedFieldNames.find(field)
    if i >= 0 and i < objTy.vOwnedFieldIds.len:
      return sanitizeTypeId(objTy.vOwnedFieldIds[i]) & "__" & field
  refPointeeTypeId(objTy) & "__" & field

proc inheritTagKey*(objTy: IRType, level: int): string =
  ## RFC-0005 S8bh (item 3). The run-type tag heap of depth `level` of
  ## `objTy`'s hierarchy: `<root>__@lvl<level>`. An object of a type of depth
  ## `m` (its `inheritChain.len - 1`) stores `inheritTagCode` of its
  ## ancestor at each depth `1..m` and the sentinel 0 at depth `m + 1`
  ## (`isNew`). A down-conversion to a type `D` of depth `k` from a static
  ## type of depth `s` reads depths `s + 1 .. k` and compares them with `D`'s
  ## chain: depths `<= s` agree by static typing, and an object of depth
  ## `m < k` fails at depth `m + 1` (the sentinel), with no closed-world list
  ## of the hierarchy's types. A parameter's levels are free: its dynamic
  ## type is any subtype of its static one.
  fieldHeapKey(objTy, "@lvl" & $level)

proc variantDiscHeapKey(objTy: IRType): string =
  ## ADR-0013 D1. The discriminator heap of a ref-to-variant: `<id>__@disc`.
  ## RFC-0005 S8l: an axis view of a multi-variant (`mvAxisView`) keys its
  ## discriminator by name, `<id>__@disc__<discName>` -- one heap per axis.
  ## Its arm and plain field heaps need no such suffix: Nim forbids two
  ## fields of one object sharing a name, so `__@<ord>__<field>` and
  ## `__<field>` are already unique across axes.
  result = refPointeeTypeId(objTy) & "__@disc"
  if objTy.vIsAxisView: result.add "__" & objTy.vDiscName

proc mvAxisView(mv: IRType; axisIx: int): IRType =
  ## RFC-0005 S8l. Axis `axisIx` of the multi-variant `mv`, as the
  ## single-axis variant the ADR-0013 heap arms already model: the axis's
  ## discriminator and arms, the object's plain fields, and `mv`'s own
  ## `Ref_<id>` (`vNominalId` is `refPointeeTypeId(mv)`, which that proc
  ## returns unchanged). The axes of one object are independent in Nim --
  ## each field, discriminator included, lives at its own slot -- so the
  ## object's heap is exactly the union of its axis views' heaps.
  let ax = mv.mvAxes[axisIx]
  result = tVariant(objectName = mv.mvObjectName, discName = ax.discName,
                    discTy = ax.discTy, arms = ax.arms,
                    plainFieldNames = mv.mvPlainFieldNames,
                    plainFieldTypes = mv.mvPlainFieldTypes,
                    discTags = ax.discTags,
                    nominalId = refPointeeTypeId(mv))
  result.vIsAxisView = true

proc mvAxisOfField(mv: IRType; field: string): int =
  ## RFC-0005 S8l. The axis whose discriminator or arm declares `field`;
  ## 0 for a plain field (every view carries the plain fields).
  for i, ax in mv.mvAxes:
    if ax.discName == field: return i
    for arm in ax.arms:
      if field in arm.fieldNames: return i
  0

proc heapStepOf(p: Path; ptrExpr: IRExpr): int =
  ## RFC-0005 S8ar. The heap step a deref through `ptrExpr` takes: one more
  ## than the ref's own steps from a root (`refSteps`). A parameter's or a
  ## `new`'s field is step 1, the field of a ref read out of it step 2.
  heapStepsOf(lowerLeafInExpr(p, ptrExpr)[0]) + 1   # the caller lowers it again, with its taint

var heapChainKinds {.threadvar.}: tuple[ready: bool, select, ite: int]
  ## RFC-0005 S8bd. The `Z3_decl_kind` ordinals `heapChainDepth` matches
  ## on, read off terms built once per thread (`seqCapKinds`' discipline).

proc heapChainDepth*(ctx: Z3Context; refAst: Z3AnyAst): int =
  ## RFC-0005 S8bd. How many heap dereferences the ref `refAst` itself was
  ## reached through: 0 for a root (a parameter, a global, a fresh `new`,
  ## a local bound to one), and for a ref read out of a heap cell
  ## (`select(H, r)`, `H` keyed by a `Ref_T` sort) one more than `r`'s.
  ## A merge (`ite`) is its deeper side; a read out of a seq's or array's
  ## backing (`select` at an Int index) is its container's depth. Every
  ## other term is a root.
  if not heapChainKinds.ready:
    let ctx = probeContext()   # RFC-0005 S8bp
    let b = mkBoolVar(ctx, "__s8bd_kind_probe_b")
    let x = mkIntVar(ctx, "__s8bd_kind_probe_x")
    let arr = mkArrayVar[Z3Int, Z3Int](ctx, "__s8bd_kind_probe_arr")
    proc kindOf(a: RawZ3Ast): int =
      ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
    heapChainKinds = (ready: true, select: kindOf(select(arr, x).raw),
                      ite: kindOf(ite(b, x, x + mkInt(ctx, 1)).raw))
  let kinds = heapChainKinds
  var memo: Table[int, int]
  proc go(a: Z3AnyAst; level = 0): int =
    # RFC-0005 S8ct: past the limit, a chain as deep as the limit, which the
    # caller's dereference budget declines.
    if level > termWalkMaxDepth: return termWalkMaxDepth
    if getAstKind(a) != akApp: return 0
    let id = astId(ctx, a.raw)
    if id in memo: return memo[id]
    let (decl, args) = unpackApp(a)
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    var d = 0
    if k == kinds.select and args.len == 2:
      let dom = arrayKey(ctx, ctx.checkErr Z3_get_sort(ctx.raw, args[0].raw))
      d = if getSortKind(ctx, dom) == skUninterpreted: 1 + go(args[1], level + 1)
          else: go(args[0], level + 1)
    elif k == kinds.ite and args.len == 3:
      d = max(go(args[1], level + 1), go(args[2], level + 1))
    memo[id] = d
    d
  go(refAst)

const heapDerefsPerPathCap* = 4096
  ## RFC-0005 S8bd. The hard cap on the dereferences one path makes in all
  ## (`Path.heapDepth` counts them), whatever their depth. The walk of a
  ## path is finite without it (`maxLoopUnwind` and `maxCallDepth` bound
  ## every loop and recursion); it bounds the heap terms one query can hold.

func heapDerefDecline*(chainDepth, derefCount, limit: int): string =
  ## RFC-0005 S8bd. The decline a dereference makes, or "" when it is within
  ## budget. `chainDepth` is the dereference's own depth (one more than its
  ## ref's, `heapChainDepth`), `derefCount` the path's count including it,
  ## `limit` the effective `maxHeapDepth` (`effectiveHeapDepthLimit`).
  ## The budget bounds the depth of a chain (`n.next.next...`), as its name
  ## and its doc say. Before S8bd it was compared with the path's count of
  ## every dereference, so a straight-line SUT that touched one object's
  ## fields nine times declined under the default of 8 (`o.inner.x`, read
  ## and written through a call: S8ba's `hn`, `hr`).
  if limit > 0 and chainDepth >= limit:
    "heap depth budget of " & $limit & " exceeded (maxHeapDepth): a " &
      "dereference " & $chainDepth & " heap reads from its root"
  elif derefCount > heapDerefsPerPathCap:
    "heap dereference hard cap of " & $heapDerefsPerPathCap & " on one " &
      "path exceeded (heapDerefsPerPathCap)"
  else: ""

proc heapDepthExhausted(p: Path, w: var WalkCtx; step: int;
                        refAst: Z3AnyAst): bool =
  ## Phase 15 R9. The SOLE heap-depth check site, shared by `of isDeref:` and
  ## `of isDerefWrite:`. Count the dereference (`p.heapDepth`, per-path;
  ## threaded/deep-copied at every fork via H1) and test its depth against
  ## the effective limit. On exhaustion: record a classified
  ## `heDepthExhausted` (sevError) into the heap-depth sink via `degrade`
  ## (RFC-0005 S1), and return `true` so the caller HALTS this path (binds
  ## nothing, contributes no survivor → sxUnknown). Otherwise return `false`
  ## and the deref/store proceeds normally. Per-path: a shallower path's
  ## deref does not exhaust and continues.
  ##
  ## RFC-0005 S8ar / S8bd: the budget bounds how deep a dereference is, not
  ## how many a path makes. Before them every deref incremented
  ## `p.heapDepth` and the count was compared with the limit, so a path
  ## reading nine fields of one parameter exhausted a budget of 8 though
  ## every read was one step from the root. Both slices measured the depth
  ## independently -- S8ar by the heap `step` stamped on the ref's value
  ## (`heapStepOf`), S8bd by the chain the ref's term was reached through
  ## (`heapChainDepth` of `refAst`, plus this hop) -- and the batch-3 stack
  ## keeps both, deciding on the deeper; the count is held only to
  ## `heapDerefsPerPathCap` (`heapDerefDecline`).
  inc p.heapDepth
  let limit = effectiveHeapDepthLimit(w.settings)
  let depth = max(step, heapChainDepth(w.z3, refAst) + 1)
  let msg = heapDerefDecline(depth, p.heapDepth, limit)
  if msg.len > 0:
    # RFC-0005 S1: a HALT site — the caller drops `p` (no survivor), so the
    # former `p.uncertain = true` mutation carried nothing anywhere and is
    # gone; the token is discarded. `dsHeapDepth` writes the threadvar +
    # LIVE WalkCtx field exactly as the two hand-written adds did, and the
    # run act is derived at drain from that entry (was `w.sawUnknown`).
    w.halted(heDepthExhausted, msg, sink = dsHeapDepth, cap = ckHeapDepth)
    return true
  false

proc nilDerefFork(p: Path, refAst: Z3AnyAst, elemTy: IRType,
                  w: var WalkCtx): seq[Path] =
  ## Phase 15 R5 (Cluster R, ADR-0010). Fork a `p[]` deref (READ or WRITE) of a
  ## possibly-nil ref/ptr `p` into:
  ##   * a NIL sub-path — `p == nil` asserted — which is the NilAccessDefect
  ##     finding (`sxRaised("NilAccessDefect")`). It is forked under EVERY
  ##     target (Phase 16 D1a; the `stkNilAccess` gate this comment once
  ##     described is gone): the path is marked `nilDeref` (RFC-0005 S8k, so
  ##     replay never runs the real SIGSEGV it models) and handed to
  ##     `crashRaise` (RFC-0005 S8cu), a crash no `except` or `finally` sees,
  ##     which a raise target matches like any other raise. The nil path is
  ##     TERMINAL — it never continues into the select/store.
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
  let eqNil = wrap[Z3Bool](ctx, checkedEq(ctx, refAst.raw, nilConst.raw))
  # NIL sub-path — NilAccessDefect fork. Phase 16 D1a unconditional.
  # RFC-0005 S8k: the nil edge is marked (`Path.nilDeref`), so its finding
  # carries it to replay, which must never run the real SIGSEGV this edge
  # models. RFC-0005 S8cu: it is a crash, not a raise any `except` or
  # `finally` sees (`crashRaise`); before, a handler caught it.
  let nilPath = forkPath(p, p.pc & @[eqNil], p.env)
  nilPath.nilDeref = true
  crashRaise(nilPath, "NilAccessDefect", w)
  # NON-NIL continuation: assert `p != nil` and continue the deref normally.
  @[forkPath(p, p.pc & @[not eqNil], p.env)]

# ---- RFC-0005 S8ax: address cells ------------------------------------------
#
# `addr x` of a routine's variable `x` is a pointer like any other: stored in
# an object, returned, compared, re-pointed under a branch. The walk gives
# `x` a heap cell (a fresh `ptr` of `x`'s type, allocated by the first `addr
# x` the frame evaluates and reused after) and keeps the two equal statement
# by statement (`walk`): `x` stays the frame's own binding, so every
# statement that reads or writes it by name is unchanged, and the cell is
# what a pointer reads and writes, wherever it travels.

type VariantSlot = tuple[kind: char; ord: int; name, key: string;
                         ty, variantTy: IRType]
  ## RFC-0005 S8be. One heap of a case object's cell (ADR-0013 D1): its
  ## discriminator (`kind` 'd'), a plain field ('p') or an arm's field ('a',
  ## of arm `ord`), with the heap key, value type and the variant type its
  ## heap is materialised with -- the slots `isNew` zero-writes.

proc variantSlots(ty: IRType): seq[VariantSlot] =
  ## RFC-0005 S8be. The heaps a cell of the case object type `ty` lives in.
  let baseId = refPointeeTypeId(ty)
  result.add ('d', 0, ty.vDiscName, variantDiscHeapKey(ty), ty.vDiscTy, ty)
  for i, fname in ty.vPlainFieldNames:
    result.add ('p', 0, fname, fieldHeapKey(ty, fname), ty.vPlainFieldTypes[i],
                IRType(nil))
  for arm in ty.vArms:
    for i, fname in arm.fieldNames:
      result.add ('a', arm.tagOrdinal, fname,
                  baseId & "__@" & $arm.tagOrdinal & "__" & fname,
                  arm.fieldTypes[i], ty)

# RFC-0016 PRC-07 (ref variants). A heap cell of a case object carries the
# union image a value variant does (`SymVal.vImage`: n data cells then n
# indeterminate-byte mask cells, 64-bit little-endian words over
# `variant_layout`'s offsets, `unionImageGate` deciding when), in heaps
# beside its per-tag field heaps: `<id>__@img<i>` and `<id>__@msk<i>`. One
# image per object, so an alias reads what its referent's writes made, and
# a merge joins the heaps as any other (`__@img`/`__@msk`, like `__@disc`,
# are no field family: `ptrFamilyKey` skips them).
#
# The bytes the active arm's fields cover are the pack of those fields'
# cells, by construction at every read (`cellImage` overlays them on the
# stored heaps), so any writer of an active arm field (a field store, a
# pointer into the field, an opaque call's havoc) keeps the image without
# touching it, and an input ref's image agrees with its free fields at its
# first read. The stored heaps answer for the other bytes. An untouched
# data heap is the free input constant (an input ref's bytes are free, as a
# free parameter's), an untouched mask heap the zero array (determinate).
# What writes the stored heaps: `isNew` (zero for `new`, every byte
# indeterminate for an uninit constructor, `isNew.nUninit`), a whole-cell
# store (`variantCellStore`), and a branch-changing discriminator store,
# which first fixes the old arm's bytes in them, then re-reads the new arm's
# fields from the image. An out-of-arm arm-field store is exact in the arms it
# leaves with a value in every field (`outOfArmFieldStore`: its bytes into the
# stored heaps, the mask cleared, the covered fields of those arms re-read);
# the rest is declined (`writeExactArm`). An opaque call's havoc gives the
# data heaps fresh contents and the mask heaps the zero array (`havocOpaqueHeaps`).
#
# cpp (`activeMemberTracked`): the union's active member, `vActive`, lives
# in two heaps, `<id>__@act` (the arm's tag) and `<id>__@acton` (set once it
# may differ from the discriminator; an untouched cell's active member is its
# discriminator's arm, as a value variant's at construction). A field write
# makes its arm active (any arm: defined); a discriminator store fixes the
# old member as active; a read through another arm is
# `ubInactiveVariantField`. A variant with an `else` arm is not tracked.

proc imageHeapKey(baseId: string; i: int; mask: bool): string =
  baseId & (if mask: "__@msk" else: "__@img") & $i

proc imageHeapCells(ctx: Z3Context; p: Path; baseId: string;
                    refSort: RawZ3Sort; lay: vl.VariantLayout): HeapCell =
  ## The stored image heaps of the case object `baseId` on `p`: data cells
  ## then mask cells. Reads `p`, never writes it.
  let n = unionCellCount(lay)
  let zero = mkBitVec[64](0'i64)
  let bvSort = sortOfRaw(ctx, zero.raw)
  for i in 0 ..< 2 * n:
    let k = imageHeapKey(baseId, i mod n, i >= n)
    if p.heaps.hasKey(k):
      result.add (k, p.heaps[k])
    elif i < n:
      let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, bvSort)
      let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
                                                 heapInputName(p, k).cstring)
      result.add (k, wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                                   arrSort)))
    else:
      result.add (k, wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const_array(
        ctx.raw, refSort, zero.raw)))

proc imageSelect(ctx: Z3Context; cells: HeapCell;
                 refAst: Z3AnyAst): seq[Z3BitVec[64]] =
  for c in cells:
    result.add wrap[Z3BitVec[64]](ctx, checkedSelect(ctx, c.arr.raw, refAst.raw))

proc imageStore(ctx: Z3Context; p: Path; cells: HeapCell; refAst: Z3AnyAst;
                img: seq[Z3BitVec[64]]) =
  ## `p` with the cell at `refAst` holding `img`.
  for i, c in cells:
    p.heaps[c.key] = wrap[Z3AnyAst](ctx, checkedStore(ctx, c.arr.raw, refAst.raw,
                                                      img[i].raw))

proc keepHeaps(p: Path; cell: HeapCell) =
  ## `p` holding the heaps of `cell` it read (an input heap's constant): the
  ## heaps a value read is built from are the path's own, which the witness
  ## pins (`modelPins`) and a join compares.
  for c in cell:
    if not p.heaps.hasKey(c.key): p.heaps[c.key] = c.arr

proc cellDisc(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst): SymVal =
  ## The discriminator of the case object at `refAst` on `p`.
  let cell = heapCellArrays(ctx, p, variantDiscHeapKey(ty), allocRefSort(ctx, ty),
                            ty.vDiscTy, ty)
  keepHeaps(p, cell)
  heapCellSelect(ctx, cell, refAst, ty.vDiscTy)

proc cellImage(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
               lay: vl.VariantLayout): seq[Z3BitVec[64]] =
  ## The union image of the case object at `refAst` on `p`: the stored heaps
  ## with the active arm's fields packed over the bytes they cover. Each
  ## field's declared range is asserted on `p` (a free input field's cell is
  ## otherwise any bit pattern, which another arm would then read), and the
  ## heaps read are kept on `p` (`keepHeaps`).
  let refSort = allocRefSort(ctx, ty)
  let baseId = refPointeeTypeId(ty)
  let cells = imageHeapCells(ctx, p, baseId, refSort, lay)
  keepHeaps(p, cells)
  let stored = imageSelect(ctx, cells, refAst)
  let disc = cellDisc(ctx, p, ty, refAst)
  var seeded = false
  for ai in countdown(ty.vArms.len - 1, 0):
    let arm = ty.vArms[ai]
    if arm.isElse or not lay.arms.hasKey(arm.tagOrdinal) or
       lay.arms[arm.tagOrdinal].len != arm.fieldNames.len: continue
    var img = stored
    for j, f in lay.arms[arm.tagOrdinal]:
      let fty = arm.fieldTypes[j]
      let cell = heapCellArrays(ctx, p, baseId & "__@" & $arm.tagOrdinal & "__" &
                                arm.fieldNames[j], refSort, fty, ty)
      keepHeaps(p, cell)
      let v = heapCellSelect(ctx, cell, refAst, fty)
      for c in rangeCondsIfNeeded(v, fty): p.pc.add c
      let bits = placeBits(v, f)
      if bits.isSome:
        img = imgWrite(img, f.off - lay.unionOff, f.size, bits.get)
    if not seeded:
      result = img
      seeded = true
    else:
      let c = variantDiscEq(disc, int64(arm.tagOrdinal))
      for i in 0 ..< img.len: result[i] = ite(c, img[i], result[i])
  if not seeded: result = stored

proc heapActiveTracked(ty: IRType): bool =
  ## cpp: the heap cell of `ty` tracks its active member (no `else` arm,
  ## whose member no single tag names).
  if not activeMemberTracked(ty): return false
  for arm in ty.vArms:
    if arm.isElse: return false
  true

proc activeHeaps(ctx: Z3Context; p: Path; ty: IRType):
    tuple[act, on: tuple[key: string; arr: Z3AnyAst]] =
  ## The active-member heaps of `ty` on `p` (untouched: `on` false).
  let refSort = allocRefSort(ctx, ty)
  let baseId = refPointeeTypeId(ty)
  let ka = baseId & "__@act"
  let ko = baseId & "__@acton"
  result.act = (ka, if p.heaps.hasKey(ka): p.heaps[ka]
                    else: wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const_array(
                      ctx.raw, refSort, rawAnyAstOf(discConst(ty.vDiscTy, 0)))))
  result.on = (ko, if p.heaps.hasKey(ko): p.heaps[ko]
                   else: wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const_array(
                     ctx.raw, refSort, mkBool(false).raw)))

proc cellActive(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                disc: SymVal): SymVal =
  ## The active member's tag of the case object at `refAst` (`disc` its
  ## discriminator).
  let (act, on) = activeHeaps(ctx, p, ty)
  let isOn = wrap[Z3Bool](ctx, checkedSelect(ctx, on.arr.raw, refAst.raw))
  iteSV(isOn, liftHeapValue(ctx, checkedSelect(ctx, act.arr.raw, refAst.raw),
                            ty.vDiscTy), disc)

proc storeActive(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                 active: Option[SymVal]) =
  ## `p` with the cell at `refAst`'s active member `active` (`none`: its
  ## discriminator's arm).
  let (act, on) = activeHeaps(ctx, p, ty)
  if active.isSome:
    p.heaps[act.key] = wrap[Z3AnyAst](ctx, checkedStore(ctx, act.arr.raw,
      refAst.raw, rawAnyAstOf(active.get)))
  p.heaps[on.key] = wrap[Z3AnyAst](ctx, checkedStore(ctx, on.arr.raw,
    refAst.raw, mkBool(active.isSome).raw))

proc variantCellValue(ctx: Z3Context; p: Path; ty: IRType;
                      refAst: Z3AnyAst): SymVal =
  ## RFC-0005 S8be. The case object held at `refAst` on `p`: a value of
  ## `ty` whose discriminator and every field, of every arm, are the selects
  ## of their heaps at `refAst`.
  var scratchPC: seq[Z3Bool]
  result = allocateSym(ty, "__addrCellProto", scratchPC)
  let refSort = allocRefSort(ctx, ty)
  for sl in variantSlots(ty):
    let cell = heapCellArrays(ctx, p, sl.key, refSort, sl.ty, sl.variantTy)
    let v = heapCellSelect(ctx, cell, refAst, sl.ty)
    case sl.kind
    of 'd':
      var d = new SymVal
      d[] = v
      result.vDisc = d
    of 'p':
      let i = result.vPlainFieldNames.find(sl.name)
      if i >= 0: result.vPlainFields[i] = v
    else:
      if result.vArmFieldNames.hasKey(sl.ord):
        let i = result.vArmFieldNames[sl.ord].find(sl.name)
        if i >= 0: result.vArmFields[sl.ord][i] = v
  # RFC-0016 PRC-07 (ref variants): the cell's union image is the value's
  # (c), its active member the value's `vActive` (cpp).
  let gate = unionImageGate(ty)
  if gate.isSome:
    result.vImage = cellImage(ctx, p, ty, refAst, gate.get)
  if heapActiveTracked(ty) and result.vDisc != nil:
    result.vActive = activeOf(cellActive(ctx, p, ty, refAst, result.vDisc[]))

proc variantCellStore(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                      v: SymVal) =
  ## RFC-0005 S8be. Store the case object `v` into its cell at `refAst` on
  ## `p`, heap by heap (a field `v` does not hold keeps its heap's value).
  let refSort = allocRefSort(ctx, ty)
  for sl in variantSlots(ty):
    var fv: SymVal
    var have = false
    case sl.kind
    of 'd':
      if v.vDisc != nil:
        fv = v.vDisc[]
        have = true
    of 'p':
      let i = v.vPlainFieldNames.find(sl.name)
      if i >= 0 and i < v.vPlainFields.len:
        fv = v.vPlainFields[i]
        have = true
    else:
      if v.vArmFieldNames.hasKey(sl.ord):
        let i = v.vArmFieldNames[sl.ord].find(sl.name)
        if i >= 0 and v.vArmFields.hasKey(sl.ord) and
           i < v.vArmFields[sl.ord].len:
          fv = v.vArmFields[sl.ord][i]
          have = true
    if not have: continue
    let cell = heapCellArrays(ctx, p, sl.key, refSort, sl.ty, sl.variantTy)
    var scratchPC: seq[Z3Bool]
    let proto = allocateSym(sl.ty, "__addrCellProto", scratchPC)
    for c in heapCellStore(ctx, cell, refAst,
                           heapStoreValue(fv, proto, sl.ty), sl.ty):
      p.heaps[c.key] = c.arr
  # RFC-0016 PRC-07 (ref variants): the value's union image goes with it. A
  # value with no derived image (`vImage` empty under the gate) marks every
  # byte its active arm's fields do not cover indeterminate, so no later
  # read of them is exact.
  let gate = unionImageGate(ty)
  if gate.isSome:
    let cells = imageHeapCells(ctx, p, refPointeeTypeId(ty), refSort, gate.get)
    var img = v.vImage
    if img.len != cells.len:
      img = imageSelect(ctx, cells, refAst)
      for i in cells.len div 2 ..< cells.len: img[i] = mkBitVec[64](-1'i64)
    imageStore(ctx, p, cells, refAst, img)
  # cpp: the value's active member (untracked: its discriminator's arm).
  if heapActiveTracked(ty):
    storeActive(ctx, p, ty, refAst,
                (if v.vActive != nil: some(v.vActive[]) else: none(SymVal)))

proc outOfArmFieldExactArms(ty: IRType; lay: vl.VariantLayout; tp: vl.Place;
                            hitTags: seq[int]; disc: SymVal): Option[Z3Bool] =
  ## RFC-0016 PRC-07 (c). The discriminator values of the arms an out-of-arm
  ## store of `tp` is exact in: every arm that does not name the field and
  ## that the write leaves with a value in each field (`writeExactArm`).
  var seeded = false
  var ok: Z3Bool
  for arm in ty.vArms:
    if arm.isElse or arm.tagOrdinal in hitTags or
       not lay.arms.hasKey(arm.tagOrdinal) or
       lay.arms[arm.tagOrdinal].len != arm.fieldNames.len or
       not writeExactArm(lay, arm.tagOrdinal, tp):
      continue
    let c = variantDiscEq(disc, int64(arm.tagOrdinal))
    ok = (if seeded: ok or c else: c)
    seeded = true
  if seeded: some(ok) else: none(Z3Bool)

proc outOfArmFieldStore(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                        lay: vl.VariantLayout; tp: vl.Place; disc: SymVal;
                        written: SymVal; hitTags: seq[int]): bool =
  ## RFC-0016 PRC-07 (c). A store of `written` to the field at `tp` while the
  ## active arm is one that does not name it (`outOfArmFieldExactArms`): its
  ## bytes go into the stored image heaps at their offset, clearing the mask
  ## over them, and every field of an exact arm those bytes cover takes its
  ## value from the image (the active arm's fields are what a read overlays).
  ## `false` (nothing written) when the value has no bytes.
  let bits = placeBits(written, tp)
  if bits.isNone: return false
  let refSort = allocRefSort(ctx, ty)
  let baseId = refPointeeTypeId(ty)
  var img = cellImage(ctx, p, ty, refAst, lay)
  img = imgWrite(img, tp.off - lay.unionOff, tp.size, bits.get)
  imageStore(ctx, p, imageHeapCells(ctx, p, baseId, refSort, lay), refAst, img)
  for arm in ty.vArms:
    if arm.isElse or arm.tagOrdinal in hitTags or
       not lay.arms.hasKey(arm.tagOrdinal) or
       lay.arms[arm.tagOrdinal].len != arm.fieldNames.len or
       not writeExactArm(lay, arm.tagOrdinal, tp):
      continue
    let sel = variantDiscEq(disc, int64(arm.tagOrdinal))
    for j, f in lay.arms[arm.tagOrdinal]:
      if not overlaps(f, tp): continue
      let nv = bitsPlace(imgReadDef(img, f.off - lay.unionOff, f.size), f,
                         some((tp, written)))
      if nv.isNone: continue
      let fty = arm.fieldTypes[j]
      let cell = heapCellArrays(ctx, p, baseId & "__@" & $arm.tagOrdinal & "__" &
                                arm.fieldNames[j], refSort, fty, ty)
      var scratch: seq[Z3Bool]
      let proto = allocateSym(fty, "__armImageProto", scratch)
      let merged = heapCellIte(ctx, sel, heapStoreValue(nv.get, proto, fty),
                               heapCellSelect(ctx, cell, refAst, fty), fty)
      for c in heapCellStore(ctx, cell, refAst, merged, fty):
        p.heaps[c.key] = c.arr
  true

proc multiVariantCellValue(ctx: Z3Context; p: Path; ty: IRType;
                           refAst: Z3AnyAst): SymVal =
  ## RFC-0005 S8cb (item 3). The multi-axis case object held at `refAst` on
  ## `p`: the union of its axis views' heaps (`mvAxisView`), which `p[].f` reads
  ## and writes.
  var scratchPC: seq[Z3Bool]
  result = allocateSym(ty, "__addrCellProto", scratchPC)
  let refSort = allocRefSort(ctx, ty)
  for xi in 0 ..< ty.mvAxes.len:
    let view = mvAxisView(ty, xi)
    for sl in variantSlots(view):
      let cell = heapCellArrays(ctx, p, sl.key, refSort, sl.ty, sl.variantTy)
      let v = heapCellSelect(ctx, cell, refAst, sl.ty)
      case sl.kind
      of 'd':
        var d = new SymVal
        d[] = v
        result.mvAxes[xi].disc = d
      of 'p':
        let i = result.mvPlainFieldNames.find(sl.name)
        if i >= 0: result.mvPlainFields[i] = v
      else:
        if result.mvAxes[xi].armFieldNames.hasKey(sl.ord):
          let i = result.mvAxes[xi].armFieldNames[sl.ord].find(sl.name)
          if i >= 0: result.mvAxes[xi].armFields[sl.ord][i] = v

proc multiVariantCellStore(ctx: Z3Context; p: Path; ty: IRType;
                           refAst: Z3AnyAst; v: SymVal) =
  ## RFC-0005 S8cb (item 3). Store the multi-axis case object `v` into its cell
  ## at `refAst` on `p`, heap by heap (`multiVariantCellValue`'s).
  let refSort = allocRefSort(ctx, ty)
  for xi in 0 ..< ty.mvAxes.len:
    let view = mvAxisView(ty, xi)
    for sl in variantSlots(view):
      var fv: SymVal
      var have = false
      case sl.kind
      of 'd':
        if v.mvAxes[xi].disc != nil:
          fv = v.mvAxes[xi].disc[]
          have = true
      of 'p':
        let i = v.mvPlainFieldNames.find(sl.name)
        if i >= 0 and i < v.mvPlainFields.len:
          fv = v.mvPlainFields[i]
          have = true
      else:
        if v.mvAxes[xi].armFieldNames.hasKey(sl.ord):
          let i = v.mvAxes[xi].armFieldNames[sl.ord].find(sl.name)
          if i >= 0 and v.mvAxes[xi].armFields.hasKey(sl.ord) and
             i < v.mvAxes[xi].armFields[sl.ord].len:
            fv = v.mvAxes[xi].armFields[sl.ord][i]
            have = true
      if not have: continue
      let cell = heapCellArrays(ctx, p, sl.key, refSort, sl.ty, sl.variantTy)
      var scratchPC: seq[Z3Bool]
      let proto = allocateSym(sl.ty, "__addrCellProto", scratchPC)
      for c in heapCellStore(ctx, cell, refAst,
                             heapStoreValue(fv, proto, sl.ty), sl.ty):
        p.heaps[c.key] = c.arr

proc objectCellValue(ctx: Z3Context; p: Path; ty: IRType;
                     refAst: Z3AnyAst): SymVal =
  ## RFC-0005 S8bs. The object (a `fieldSplitPointee` tuple) held at
  ## `refAst` on `p`: each field the select of its own field heap
  ## (`fieldHeapKey`), the heaps `p[].f` reads and writes.
  let refSort = allocRefSort(ctx, ty)
  var fields: seq[SymVal]
  for i, fname in ty.fieldNames:
    let cell = heapCellArrays(ctx, p, fieldHeapKey(ty, fname), refSort,
                              ty.fields[i])
    fields.add heapCellSelect(ctx, cell, refAst, ty.fields[i])
  SymVal(kind: svTuple, fields: fields, fieldNames: ty.fieldNames)

proc objectCellStore(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                     v: SymVal) =
  ## RFC-0005 S8bs. Store the object `v` into its cell at `refAst` on `p`,
  ## field by field (`objectCellValue`'s heaps).
  let refSort = allocRefSort(ctx, ty)
  for i, fname in ty.fieldNames:
    if v.kind != svTuple or i >= v.fields.len: return
    let cell = heapCellArrays(ctx, p, fieldHeapKey(ty, fname), refSort,
                              ty.fields[i])
    var scratchPC: seq[Z3Bool]
    let proto = allocateSym(ty.fields[i], "__addrCellProto", scratchPC)
    for c in heapCellStore(ctx, cell, refAst,
                           heapStoreValue(v.fields[i], proto, ty.fields[i]),
                           ty.fields[i]):
      p.heaps[c.key] = c.arr

proc addrCellValue(ctx: Z3Context; p: Path; ty: IRType;
                   refAst: Z3AnyAst): SymVal =
  ## RFC-0005 S8ax. The value of the address cell at `refAst` on `p`.
  ## RFC-0005 S8be: a case object's, from its field-split heaps.
  ## RFC-0005 S8bs: and an object's (`objectCellValue`). It was read from
  ## the whole-pointee heap (`<T>__@.f`), which no `p[].f` reads or writes:
  ## a write through a pointer to the variable (`gpb[].x = 5`, in its own
  ## frame or a callee's) never reached it, and a write to it by name never
  ## reached the pointer.
  if ty.kind == itVariant: return variantCellValue(ctx, p, ty, refAst)
  if ty.kind == itMultiVariant: return multiVariantCellValue(ctx, p, ty, refAst)
  if fieldSplitPointee(ty): return objectCellValue(ctx, p, ty, refAst)
  let cell = heapCellArrays(ctx, p, refPointeeTypeId(ty), allocRefSort(ctx, ty),
                            ty)
  heapCellSelect(ctx, cell, refAst, ty)

func keepStrBuf*(stored, v: SymVal): SymVal =
  ## RFC-0005 S8ca. `stored`, the value of a cell `v` was just stored into
  ## and read back from, with `v`'s `StrBuf`: the heap holds the string's
  ## bytes, not whose memory they are, and the variable is still `v`.
  result = stored
  if result.kind == svString and v.kind == svString:
    result.strBuf = v.strBuf

proc addrCellStore(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                   v: SymVal): SymVal =
  ## RFC-0005 S8ax. Store `v` into the address cell at `refAst` on `p` (a
  ## path the caller just forked) and return the cell's value read back:
  ## the variable's new binding, so the two stay one term.
  if ty.kind == itVariant:   # RFC-0005 S8be
    if v.kind == svVariant: variantCellStore(ctx, p, ty, refAst, v)
    return variantCellValue(ctx, p, ty, refAst)
  if ty.kind == itMultiVariant:   # RFC-0005 S8cb
    if v.kind == svMultiVariant: multiVariantCellStore(ctx, p, ty, refAst, v)
    return multiVariantCellValue(ctx, p, ty, refAst)
  if fieldSplitPointee(ty):   # RFC-0005 S8bs
    objectCellStore(ctx, p, ty, refAst, v)
    return objectCellValue(ctx, p, ty, refAst)
  let cell = heapCellArrays(ctx, p, refPointeeTypeId(ty), allocRefSort(ctx, ty),
                            ty)
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(ty, "__addrCellProto", scratchPC)
  let stored = heapCellStore(ctx, cell, refAst, heapStoreValue(v, proto, ty), ty)
  for c in stored: p.heaps[c.key] = c.arr
  heapCellSelect(ctx, stored, refAst, ty)

proc arrayLocIx(ix: SymVal; n: int): Option[int] =
  ## RFC-0005 S8bu. The position an array step's index (`locGet`) names,
  ## when its term folds to a numeral in `0 ..< n`.
  if ix.kind notin {svInt, svBV8, svBV16, svBV32, svBV64}: return none(int)
  let folded = simplify(toZ3Int(ix))
  if getAstKind(folded) != akNumeral: return none(int)
  try:
    let k = parseInt(getNumeralString(folded))
    if k >= 0 and k < n: return some(k)
  except CatchableError: discard
  none(int)

proc locGet(v: SymVal; path: seq[string]; ixs: seq[SymVal];
            k = 0; j = 0): Option[SymVal] =
  ## RFC-0005 S8bs. The part of `v` at `path` (`AddrCellEntry`): a field of
  ## an object or tuple, a plain or arm field of a case object, an element
  ## of a seq of scalars or strings (`[`, the next of `ixs`). none for a
  ## step the walk does not follow.
  if k >= path.len: return some(v)
  let st = path[k]
  if st.startsWith("[") and v.kind == svArray:
    # RFC-0005 S8bu: an array's element; a symbolic index selects through
    # an `ite` over the elements, as a read `a[i]` does (`iekIndex`). The
    # caller checked the index in bounds where it evaluated the actual.
    if j >= ixs.len or v.arrElems.len == 0: return none(SymVal)
    let at = arrayLocIx(ixs[j], v.arrElems.len)
    if at.isSome:
      return locGet(v.arrElems[at.get], path, ixs, k + 1, j + 1)
    var parts: seq[SymVal]
    for e in v.arrElems:
      let r = locGet(e, path, ixs, k + 1, j + 1)
      if r.isNone: return none(SymVal)
      parts.add r.get
    var res = parts[0]
    for q in 1 ..< parts.len:
      res = iteSV(symEq(ixs[j], coerceIntLit(ixs[j], int64(q))), parts[q], res)
    return some(res)
  if st.startsWith("["):
    if j >= ixs.len or v.kind != svSeq or isTreeSeqElemTy(v.seqElemTy) or
       not isBackedSeqElemTy(v.seqElemTy) or
       v.seqElemTy.kind notin {itInt, itBool, itFloat32, itFloat64, itString}:
      return none(SymVal)
    return locGet(seqElemAt(v, toZ3Int(ixs[j])), path, ixs, k + 1, j + 1)
  case v.kind
  of svTuple:
    let i = v.fieldNames.find(st)
    if i >= 0 and i < v.fields.len:
      return locGet(v.fields[i], path, ixs, k + 1, j)
  of svVariant:
    let i = v.vPlainFieldNames.find(st)
    if i >= 0 and i < v.vPlainFields.len:
      return locGet(v.vPlainFields[i], path, ixs, k + 1, j)
    for o, names in v.vArmFieldNames.pairs:
      let a = names.find(st)
      if a >= 0 and v.vArmFields.hasKey(o) and a < v.vArmFields[o].len:
        return locGet(v.vArmFields[o][a], path, ixs, k + 1, j)
  else: discard
  none(SymVal)

proc locSet(v: SymVal; path: seq[string]; ixs: seq[SymVal]; x: SymVal;
            k = 0; j = 0): Option[SymVal] =
  ## RFC-0005 S8bs. `v` with its part at `path` (`locGet`) replaced by `x`.
  if k >= path.len: return some(x)
  let st = path[k]
  if st.startsWith("[") and v.kind == svArray:
    # RFC-0005 S8bu: an array's element (`locGet`): the named one, or each
    # one under its index's `ite`.
    if j >= ixs.len or v.arrElems.len == 0: return none(SymVal)
    let at = arrayLocIx(ixs[j], v.arrElems.len)
    var nv = v
    for q in 0 ..< v.arrElems.len:
      if at.isSome and at.get != q: continue
      let r = locSet(v.arrElems[q], path, ixs, x, k + 1, j + 1)
      if r.isNone: return none(SymVal)
      nv.arrElems[q] =
        if at.isSome: r.get
        else: iteSV(symEq(ixs[j], coerceIntLit(ixs[j], int64(q))), r.get,
                    v.arrElems[q])
    return some(nv)
  if st.startsWith("["):
    if locGet(v, path[k .. k], ixs[j .. ^1]).isNone: return none(SymVal)
    let idx = toZ3Int(ixs[j])
    let r = locSet(seqElemAt(v, idx), path, ixs, x, k + 1, j + 1)
    if r.isNone: return none(SymVal)
    var nv = v
    nv.seqDataRaw = storeSeqElem(v.seqDataRaw, v.seqElemTy, idx, r.get) # [placeholder-audited]
    return some(nv)
  case v.kind
  of svTuple:
    let i = v.fieldNames.find(st)
    if i >= 0 and i < v.fields.len:
      let r = locSet(v.fields[i], path, ixs, x, k + 1, j)
      if r.isNone: return none(SymVal)
      var nv = v
      nv.fields[i] = r.get
      return some(nv)
  of svVariant:
    let i = v.vPlainFieldNames.find(st)
    if i >= 0 and i < v.vPlainFields.len:
      let r = locSet(v.vPlainFields[i], path, ixs, x, k + 1, j)
      if r.isNone: return none(SymVal)
      var nv = v
      nv.vPlainFields[i] = r.get
      return some(nv)
    for o, names in v.vArmFieldNames.pairs:
      let a = names.find(st)
      if a >= 0 and v.vArmFields.hasKey(o) and a < v.vArmFields[o].len:
        let r = locSet(v.vArmFields[o][a], path, ixs, x, k + 1, j)
        if r.isNone: return none(SymVal)
        var nv = v
        var arm = v.vArmFields[o]
        arm[a] = r.get
        nv.vArmFields[o] = arm
        return some(nv)
  else: discard
  none(SymVal)

proc addrEntryValue(ctx: Z3Context; p: Path; c: AddrCellEntry;
                    refAst: Z3AnyAst): Option[SymVal] =
  ## RFC-0005 S8bs. The value of `c`'s location on `p`: its cell's
  ## (`addrCellValue`), or, for a `bound` entry, the part of it at its path.
  let whole = addrCellValue(ctx, p, c.ty, refAst)
  if c.path.len == 0: return some(whole)
  locGet(whole, c.path, c.ixs)

proc addrEntryStore(ctx: Z3Context; p: Path; c: AddrCellEntry;
                    refAst: Z3AnyAst; x: SymVal): Option[SymVal] =
  ## RFC-0005 S8bs. `addrCellStore` for `c`'s location: a `bound` entry's
  ## part is stored into the whole value its cell holds.
  if c.path.len == 0: return some(addrCellStore(ctx, p, c.ty, refAst, x))
  let nw = locSet(addrCellValue(ctx, p, c.ty, refAst), c.path, c.ixs, x)
  if nw.isNone: return none(SymVal)
  locGet(addrCellStore(ctx, p, c.ty, refAst, nw.get), c.path, c.ixs)

proc danglingFork(p: Path; refAst: Z3AnyAst; w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8ax. A `ptr` dereference on `p` that may reach the address
  ## cell of a variable whose frame has returned (`Path.addrOwners`): Nim
  ## reads or writes a dead stack slot there, which the walk does not model.
  ## The edge where it does is tainted (`feUnsupportedOp`, the cell's last
  ## value substituting for the slot's) when it is feasible; the rest
  ## continues untouched.
  ##
  ## RFC-0005 S8be: likewise an element cell whose memory Nim may have
  ## freed (`deadElemRefs`: its seq was resized or assigned whole since
  ## `addr` took it, or its routine returned).
  var dead: seq[Z3AnyAst]
  for o in p.addrOwners:
    if not liveFrame(w, o.frame): dead.add o.refAst
  let elemDead = deadElemRefs(p, w)
  if dead.len == 0 and elemDead.len == 0: return @[p]
  let ctx = w.z3
  var hits: seq[Z3Bool]
  for d in dead & elemDead:
    hits.add wrap[Z3Bool](ctx, checkedEq(ctx, refAst.raw, d.raw))
  var anyHit = hits[0]
  for i in 1 ..< hits.len: anyHit = anyHit or hits[i]
  let hitPath = forkPath(p, p.pc & @[anyHit], p.env)
  if not pathInfeasible(ctx, hitPath, w.settings):
    let d =
      if elemDead.len == 0:
        w.degrade(feUnsupportedOp,
          "RFC-0005 S8ax: a pointer dereferenced here may hold the address " &
               "of a variable whose routine has returned; Nim reads or " &
               "writes a dead stack slot, which the walk does not model " &
               "(feUnsupportedOp)")
      else:
        w.degrade(feUnsupportedOp,
          "RFC-0005 S8be: a pointer dereferenced here may hold the address " &
               "of a seq element whose memory Nim may have freed (the seq " &
               "was resized or assigned whole since `addr` took it, or its " &
               "routine returned), of an arm field of a case object that " &
               "may have changed arm since (RFC-0005 S8bo), or of a " &
               "returned routine's variable; the walk does not model freed " &
               "memory (feUnsupportedOp)")
    result.add forkPathTainted(p, p.pc & @[anyHit], p.env, d)
  result.add forkPath(p, p.pc & @[not anyHit], p.env)

proc walkAddrCell(stmt: IRStmt; paths: seq[Path]; w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8ax. `addr x` (`isNew` with `nAddrOf = x`): bind
  ## `stmt.nRetName` to `x`'s address cell, allocating it on the first
  ## `addr x` of the frame: a fresh `ptr`, distinct from every other address
  ## and from nil, holding `x`'s value, recorded in
  ## `CallFrameCtx.addrCells` (the frame's statements keep the two equal)
  ## and `Path.addrOwners`. Declined (`feUnsupportedOp`, the cell then a
  ## pointer the walk does not keep equal to the variable): a variable an
  ## enclosing routine owns (a nested routine's capture: its frame is not
  ## this one; in a closure body, its captures), one a closure captures
  ## (its env cell is a second copy), and a variable whose type
  ## has no heap cell the walk keeps equal by handle (an array, a table, a
  ## set, a case object, a ref, a distinct or opaque type).
  let ctx = w.z3
  let ty = stmt.nRefTy.ptrPointeeTy
  let local = stmt.nAddrOf
  let typeId = refPointeeTypeId(ty)
  for p in paths:
    if w.shouldStop: return
    if p.env.hasKey(stmt.nRetName) and p.env[stmt.nRetName].kind == svPtr:
      result.add p
      continue
    var why = ""
    # RFC-0005 S8be: a case object's cell is its field-split heaps
    # (`variantSlots`), as a `ref` to one is.
    if ty.kind notin {itInt, itBool, itFloat32, itFloat64, itString, itTuple,
                      itSeq, itVariant, itMultiVariant}:
      why = "of a variable of type " & $ty
    elif local in w.frame.outerNames or isGlobalEnvName(local):
      why = "of a variable an enclosing routine owns"
    elif not p.env.hasKey(local):
      why = "of a variable this frame does not hold"
    else:
      for (cl, _) in w.frame.capCells:
        if cl == local: why = "of a variable a closure captures"
    let refSort = allocRefSort(ctx, ty)
    var child = forkPath(p, p.pc, p.env)
    let newRef = freshRef(ctx, refSort, typeId, child)
    assertFreshness(ctx, child, typeId, newRef, w.settings)
    var env2 = child.env
    env2[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: newRef, ptrFamily: true,
                                 ptrPointee: ty)
    if why.len > 0:
      child.env = env2
      let d = w.degrade(feUnsupportedOp,
        "RFC-0005 S8ax: `addr " & displayName(local) & "` " & why &
             " is not modelled: the pointer is not kept equal to the " &
             "variable (feUnsupportedOp)")
      result.add forkPathTainted(child, child.pc, child.env, d)
      continue
    block:
      var known = false
      for c in w.frame.addrCells:
        if c.local == local and not c.bound: known = true   # RFC-0005 S8bs
      if not known:
        w.frame.addrCells.add (local: local, cell: stmt.nRetName, ty: ty,
                               path: @[], ixs: @[], bound: false, view: false, slot: "")
    child.addrOwners.add (refAst: newRef, frame: w.frame.frameId)
    env2[local] = keepStrBuf(addrCellStore(ctx, child, ty, newRef,
                                           env2[local]), env2[local])
    child.env = env2
    result.add drainPendingLowerEffects(child)

proc foldedBool(ctx: Z3Context; b: Z3Bool): Option[bool] =
  ## RFC-0005 S8ca. `b` simplified, when that is `true` or `false`.
  let s = simplify(b)
  case Z3_get_bool_value(ctx.raw, s.raw)
  of Z3_L_TRUE: some(true)
  of Z3_L_FALSE: some(false)
  else: none(bool)

proc walkElemCell(stmt: IRStmt; paths: seq[Path]; w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8be. `addr s[i]` (`isNew` with `nAddrOf = s`, `nAddrIdx = i`;
  ## the parser checked `i` against `s.len` just before): bind
  ## `stmt.nRetName` to the address of that element, as `addr` evaluates
  ## the index -- the cell `s[j]` already has in this frame when `j` equals
  ## `i` (`Path.elemCells`), else a fresh `ptr`, distinct from every other
  ## address and from nil, holding the element. The walk then keeps the
  ## element and the heap at the cell equal (`syncElemCells`) until `s` is
  ## resized. Declined (`feUnsupportedOp`) as `walkAddrCell` declines: a
  ## seq an enclosing routine owns, or one a closure captures.
  let ctx = w.z3
  let ty = stmt.nRefTy.ptrPointeeTy
  let root = stmt.nAddrOf
  let typeId = refPointeeTypeId(ty)
  for p in paths:
    if w.shouldStop: return
    var why = ""
    if root in w.frame.outerNames or isGlobalEnvName(root):
      why = "of an element of a seq an enclosing routine owns"
    elif not p.env.hasKey(root) or p.env[root].kind != svSeq:
      why = "of an element of a seq this frame does not hold"
    else:
      for (cl, _) in w.frame.capCells:
        if cl == root: why = "of an element of a seq a closure captures"
    let (idxSV, ip) = lowerInExpr(p, stmt.nAddrIdx, w)
    let idx = toZ3Int(idxSV)
    let refSort = allocRefSort(ctx, ty)
    var child = forkPath(ip, ip.pc, ip.env)
    let newRef = freshRef(ctx, refSort, typeId, child)
    assertFreshness(ctx, child, typeId, newRef, w.settings)
    var env2 = child.env
    if why.len > 0:
      env2[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: newRef,
                                   ptrFamily: true, ptrPointee: ty)
      child.env = env2
      let d = w.degrade(feUnsupportedOp,
        "RFC-0005 S8be: `addr " & displayName(root) & "[i]` " & why &
             " is not modelled: the pointer is not kept equal to the " &
             "element (feUnsupportedOp)")
      result.add forkPathTainted(child, child.pc, child.env, d)
      continue
    # The address `s[j]` already has, when `j` is this index.
    # (Each term owned as it is built: Z3 keeps an unowned result only
    # until the next call.)
    var addrAst = newRef
    for k in countdown(child.elemCells.high, 0):
      let e = child.elemCells[k]
      if e.frame != w.frame.frameId or e.root != root or e.dead or
         e.field.len > 0:
        continue
      let same = idx == e.idx
      # RFC-0005 S8ca: an index equal (or unequal) by its terms picks the
      # older cell (or not) outright: the pointer is then the cell's own
      # ref, which `ptrTargets` knows, and no store builds an `ite` address.
      let f = foldedBool(ctx, same)
      if f.isSome:
        if f.get: addrAst = e.refAst
        continue
      addrAst = wrap[Z3AnyAst](ctx,
        checkedIte(ctx, same.raw, e.refAst.raw, addrAst.raw))
    child.elemCells.add ElemCell(refAst: newRef, frame: w.frame.frameId,
                                 root: root, ty: ty, idx: idx)
    discard addrCellStore(ctx, child, ty, newRef, seqElemAt(env2[root], idx))
    env2[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: addrAst,
                                 ptrFamily: true, ptrPointee: ty)
    child.env = env2
    result.add drainPendingLowerEffects(child)

proc tupleFieldIx(v: SymVal; field: string): int =
  ## RFC-0005 S8cb. The index of field `field` of the tuple `v`: `#i` is the
  ## positional `t[i]`. -1 for none.
  if field.len > 1 and field[0] == '#':
    let i = parseInt(field[1 .. ^1])
    return (if i < v.fields.len: i else: -1)
  v.fieldNames.find(field)

proc armFieldTags(v: SymVal; field: string): seq[int] =
  ## RFC-0005 S8cb. The arms of the case object `v` declaring `field`.
  if v.kind == svVariant:
    for t, names in v.vArmFieldNames:
      if field in names: result.add t
  elif v.kind == svMultiVariant:
    for ax in v.mvAxes:
      for t, names in ax.armFieldNames:
        if field in names: result.add t

proc armFieldValue(v: SymVal; field: string; tags: seq[int]): SymVal =
  ## RFC-0005 S8bo. Arm field `field` of the case object `v`, declared by
  ## the arms `tags`: the slot of the arm `v`'s discriminator selects (an
  ## `ite` over them; one arm, its slot). RFC-0005 S8cb: of a multi-axis one,
  ## over the discriminator of the axis declaring it; of a tuple, its field.
  if v.kind == svTuple:
    return v.fields[tupleFieldIx(v, field)]
  var vals: seq[(int, SymVal)]
  var disc: SymVal
  if v.kind == svMultiVariant:
    for ax in v.mvAxes:
      var inAxis = false
      for t in tags:
        if ax.armFieldNames.hasKey(t):
          let i = ax.armFieldNames[t].find(field)
          if i >= 0:
            vals.add (t, ax.armFields[t][i])
            inAxis = true
      if inAxis:
        disc = ax.disc[]
        break
  else:
    disc = v.vDisc[]
    for t in tags:
      if v.vArmFieldNames.hasKey(t):
        let i = v.vArmFieldNames[t].find(field)
        if i >= 0: vals.add (t, v.vArmFields[t][i])
  result = vals[^1][1]
  for k in countdown(vals.len - 2, 0):
    result = iteSV(variantDiscEq(disc, int64(vals[k][0])), vals[k][1], result)

proc withArmField(v: SymVal; field: string; tags: seq[int];
                  x: SymVal): SymVal =
  ## RFC-0005 S8bo. The case object `v` with arm field `field` set to `x` in
  ## every arm of `tags` (as `lowerVariantFieldSet` writes it). RFC-0005 S8cb:
  ## as `armFieldValue`.
  result = v
  if v.kind == svTuple:
    result.fields[tupleFieldIx(v, field)] = x
  elif v.kind == svMultiVariant:
    for xi in 0 ..< result.mvAxes.len:
      for t in tags:
        if result.mvAxes[xi].armFieldNames.hasKey(t):
          let i = result.mvAxes[xi].armFieldNames[t].find(field)
          if i >= 0: result.mvAxes[xi].armFields[t][i] = x
  else:
    for t in tags:
      if result.vArmFieldNames.hasKey(t):
        let i = result.vArmFieldNames[t].find(field)
        if i >= 0: result.vArmFields[t][i] = x

proc fieldMemorySame(a, b: SymVal; field: string): bool =
  ## RFC-0005 S8cb. A field cell of `field` still names the same memory from
  ## the object `b` to the object `a`: its discriminator is the same term (the
  ## arm's memory is reused), the discriminator of the axis declaring it for a
  ## multi-axis object (the other axes' are independent, ADR-0003 D1). A
  ## tuple's fields never move.
  if a.kind != b.kind: return false
  case a.kind
  of svTuple: true
  of svVariant:
    a.vDisc != nil and b.vDisc != nil and sameSymVal(a.vDisc[], b.vDisc[])
  of svMultiVariant:
    if a.mvAxes.len != b.mvAxes.len: return false
    for xi in 0 ..< a.mvAxes.len:
      var inAxis = false
      for _, names in a.mvAxes[xi].armFieldNames:
        if field in names: inAxis = true
      if inAxis:
        return a.mvAxes[xi].disc != nil and b.mvAxes[xi].disc != nil and
               sameSymVal(a.mvAxes[xi].disc[], b.mvAxes[xi].disc[])
    false
  else: false

proc walkFieldCell(stmt: IRStmt; paths: seq[Path]; w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8bo. `addr o.a` of an arm field (`isNew` with `nAddrOf = o`,
  ## `nAddrField = a`; the parser checked the arm just before): bind
  ## `stmt.nRetName` to the field's cell -- the one it already has in this
  ## frame (`Path.elemCells`), else a fresh `ptr`, distinct from every other
  ## address and from nil, holding the field. The walk then keeps the field
  ## and the heap at the cell equal (`syncElemCells`) until the object may
  ## change arm, when the pointer names another arm's memory and the cell
  ## dies (a dereference that may reach it declines). Declined
  ## (`feUnsupportedOp`) as `walkElemCell` declines: an object an enclosing
  ## routine owns, or one a closure captures. Before S8bo such a pointer
  ## that could escape was `heUnsafeCast`.
  let ctx = w.z3
  let ty = stmt.nRefTy.ptrPointeeTy
  let root = stmt.nAddrOf
  let field = stmt.nAddrField
  let typeId = refPointeeTypeId(ty)
  for p in paths:
    if w.shouldStop: return
    var why = ""
    var tags: seq[int]
    if root in w.frame.outerNames or isGlobalEnvName(root):
      why = "of a field of an object an enclosing routine owns"
    elif not p.env.hasKey(root) or
         p.env[root].kind notin {svVariant, svMultiVariant, svTuple}:
      why = "of a field of an object this frame does not hold"
    else:
      for (cl, _) in w.frame.capCells:
        if cl == root: why = "of a field of an object a closure captures"
      tags = armFieldTags(p.env[root], field)
      if why.len == 0 and tags.len == 0 and
         (p.env[root].kind != svTuple or tupleFieldIx(p.env[root], field) < 0):
        why = "of a field no arm of the object holds"
    var known = -1
    if why.len == 0:
      for k, e in p.elemCells:
        if e.frame == w.frame.frameId and e.root == root and
           e.field == field and not e.dead:
          known = k
    if known >= 0:
      var env1 = p.env
      env1[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: p.elemCells[known].refAst,
                                   ptrFamily: true, ptrPointee: ty)
      result.add forkPath(p, p.pc, env1)
      continue
    let refSort = allocRefSort(ctx, ty)
    var child = forkPath(p, p.pc, p.env)
    let newRef = freshRef(ctx, refSort, typeId, child)
    assertFreshness(ctx, child, typeId, newRef, w.settings)
    var env2 = child.env
    env2[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: newRef,
                                 ptrFamily: true, ptrPointee: ty)
    if why.len > 0:
      child.env = env2
      let d = w.degrade(feUnsupportedOp,
        "RFC-0005 S8bo: `addr " & displayName(root) & "." & field & "` " &
             why & " is not modelled: the pointer is not kept equal to the " &
             "field (feUnsupportedOp)")
      result.add forkPathTainted(child, child.pc, child.env, d)
      continue
    child.elemCells.add ElemCell(refAst: newRef, frame: w.frame.frameId,
                                 root: root, ty: ty, field: field, tags: tags)
    discard addrCellStore(ctx, child, ty, newRef,
                          armFieldValue(env2[root], field, tags))
    child.env = env2
    result.add drainPendingLowerEffects(child)

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

# ---- RFC-0005 S8bh (item 2): the target of a ptr of unknown origin ----------
#
# A `ptr T` deref read and wrote only the pointer's own family heap (the
# whole-pointee heap `<T>` a `ref T` shares). Nim's `ptr` addresses any
# location of type T: a ref object's field (`addr q.x`), a global (`addr g`),
# a `var` parameter (`addr v`). A pointer the SUT is handed -- a parameter,
# a global, a field it reads, a callee's result -- may be any of them, so
# `q.x = 1; pi[] = 2; if q.x == 2` was a false `sxUnsat`.
#
# The model: each address `P` of the pointer sort has a TARGET, chosen by the
# free input array `<T>__@ptrsel` (`sel(P)`, a 64-bit code): 0 is the
# pointer's own cell (`<T>[P]`, the pre-S8bh model), `ptrTargetCode(K)` the
# field family `K` (a field-split heap of value type T) at the object
# `<T>__@ptrobj__<K>[P]` (a free input array too), `ptrTargetCode(g)` the
# variable `g` (a global, or a `var` parameter of the SUT). Both arrays are
# functions of the address, so every deref of one pointer -- and of every
# pointer equal to it -- agrees on its target. A read is the `ite` chain over
# the candidates; a write stores into each candidate under its own `sel`
# guard (and into the own cell as before: no reader of `<T>[P]` other than
# a pointer equal to `P`, which reads its target, can see that store).
#
# The candidates are the field families the path has MATERIALISED, the
# globals in its env, and the SUT's `var` parameters. A family the path has
# not touched yet is not one; a write through `P` it would have received is
# then lost, and a later read of that family reads its input cell -- a free
# value, so whatever the write stored stays possible (an over-approximation,
# never a false `sxUnsat`). An allocation (`new`, an `addr` cell) stores
# `sel = 0` at its fresh address: a pointer the SUT makes is its own cell. A
# pointer of unknown origin also predates every object the SUT allocates,
# so its field target is asserted distinct from them (`ptrPreKey`).
#
# Declined (`feUnsupportedOp`, the path tainted) where the location may be
# one this model has no cell for: an element of a seq/table/set held in a
# heap cell, a part of a by-value aggregate global or `var` parameter, and
# the SUT's `var` parameter while a callee runs (its frame does not hold
# the caller's variables).

proc tyMayHold(t, pointee: IRType; depth = 0): bool =
  ## RFC-0005 S8bh. A by-value aggregate of type `t` may hold a location of
  ## type `pointee` (conservative: an unknown shape may).
  if t == nil or depth > 8: return true
  if t == pointee: return true
  case t.kind
  of itInt, itBool, itFloat32, itFloat64, itString, itRef, itPtr, itUninterp:
    false
  of itTuple:
    for f in t.fields:
      if tyMayHold(f, pointee, depth + 1): return true
    false
  of itArray: tyMayHold(t.elemTy, pointee, depth + 1)
  of itSeq: tyMayHold(t.seqElemTy, pointee, depth + 1)
  of itSet:
    # RFC-0005 S8bn (item 4): no Nim operation yields the address of a
    # HashSet's member (it has no `var` accessor), so no pointer has one.
    false
  of itTable:
    tyMayHold(t.tabKeyTy, pointee, depth + 1) or
      tyMayHold(t.tabValTy, pointee, depth + 1)
  of itDistinct: tyMayHold(t.distinctBase, pointee, depth + 1)
  else: true

proc svMayHold(sv: SymVal; pointee: IRType; depth = 0): bool =
  ## RFC-0005 S8bh. A by-value aggregate VALUE may hold a location of type
  ## `pointee` (conservative: an unknown kind may).
  if depth > 8: return true
  case sv.kind
  of svTuple:
    for f in sv.fields:
      if svMayHold(f, pointee, depth + 1): return true
    false
  of svArray:
    for e in sv.arrElems:
      if svMayHold(e, pointee, depth + 1): return true
    false
  of svSeq: tyMayHold(sv.seqElemTy, pointee)
  of svDistinct:
    let b = ejectBase(sv)
    b.kind notin {svBV8, svBV16, svBV32, svBV64, svInt, svBool, svFloat32,
                  svFloat64, svString} and svMayHold(b, pointee, depth + 1)
  of svBV8: pointee.kind == itInt and pointee.width == 8
  of svBV16: pointee.kind == itInt and pointee.width == 16
  of svBV32: pointee.kind == itInt and pointee.width == 32
  of svBV64: pointee.kind == itInt and pointee.width == 64
  of svInt: pointee.kind == itInt and sv.ziWidth in [0, pointee.width]
  of svBool: pointee.kind == itBool
  of svFloat32: pointee.kind == itFloat32
  of svFloat64: pointee.kind == itFloat64
  of svString: pointee.kind == itString
  of svRef, svPtr, svClosure: false
  else: true

type PtrOverlap = object
  ## RFC-0005 S8bz (item 6). A case object's inactive branch field and a field
  ## of the active branch at the same offset, of one size, both scalars: Nim's
  ## dereference reads and writes the active field's bytes (`ptrArmOverlaps`).
  cond: Z3Bool        ## the active branch is this one
  nan: Z3Bool         ## ... and its float holds a NaN, whose bits Z3 leaves
                      ## free: read as an integer, those bytes are not known
  step: int           ## the active field's path step (by-value)
  famKey: string      ## or its field family (held in a heap)
  ty: IRType          ## the active field's type (held in a heap)

type PtrTarget = object
  ## RFC-0005 S8bh. One candidate target of a pointer: a field family (its
  ## heap `famKey`, the object `objAddr`) or a variable (`envName`).
  ## RFC-0005 S8bn (item 4): or a part of a variable -- the field / element
  ## `path` below it, its last step the pointer's seq index (`seqIdx`) for
  ## a seq element -- or an element of a seq held in a field family
  ## (`famKey` with `seqIdx`). `idx` is the index (`ptrIdxKey`).
  code: int64
  famKey: string
  objAddr: Z3AnyAst
  envName: string
  path: seq[int]
  seqIdx: bool
  idx: Z3AnyAst
  tabKey: bool        ## RFC-0005 S8bn (item 4): a `Table[string, V]` value
                      ## at the pointer's key (`idx`, `ptrKeyAt`)
  elemPath: seq[int]  ## RFC-0005 S8bz (items 1, 2): the part of an aggregate
                      ## element or value the pointer addresses
  aggregate: bool     ## RFC-0005 S8bz (items 1, 2): the element or value is
                      ## held leaf-split (`isTreeSeqElemTy`), `elemPath` below
                      ## it
  famElemTy: IRType   ## RFC-0005 S8bz (items 1, 2): the seq's or table's
                      ## type, for one held in a field family (`ptrFamSeq`)
  hasArm: bool        ## RFC-0005 S8bw (item 3): a field of a case object's
  armCond: Z3Bool     ## branch, there only while `armCond` (its branch is
                      ## the active one) holds
  overlaps: seq[PtrOverlap]  ## RFC-0005 S8bz (item 6): while another branch
                             ## is active, what the same bytes hold there

proc svHoldsAggregate(sv: SymVal; pointee: IRType; depth = 0): bool =
  ## RFC-0005 S8bz (item 1). A by-value variable's value `sv` may hold a whole
  ## `pointee` aggregate a pointer could address (conservative beyond the
  ## depth bound).
  if depth > 8: return true
  case sv.kind
  of svTuple:
    if svFitsHeapTy(sv, pointee): return true
    for f in sv.fields:
      if svHoldsAggregate(f, pointee, depth + 1): return true
    false
  of svArray:
    if svFitsHeapTy(sv, pointee): return true
    for e in sv.arrElems:
      if svHoldsAggregate(e, pointee, depth + 1): return true
    false
  of svVariant, svMultiVariant: svFitsHeapTy(sv, pointee)
  of svSeq: tyMayHold(sv.seqElemTy, pointee)
  of svTable: tyMayHold(sv.tabValTy, pointee)
  of svDistinct: svHoldsAggregate(ejectBase(sv), pointee, depth + 1)
  else: false

proc ptrAggregateDecline(w: WalkCtx; p: Path; ptrAst: Z3AnyAst;
                         pointee: IRType; typeId: string): string =
  ## RFC-0005 S8bz (item 1). A `ptr T` of a whole aggregate `T` holds its own
  ## field-split cells: this model has no candidate targets for it
  ## (`ptrScalarPointee`), so a dereference that may address a variable's
  ## aggregate, a seq element, a table value or a heap-held part was a false
  ## `sxUnsat` (`p[] = v`, then a read of the variable). The dereference
  ## declines when such a location exists. A pointer the walk allocated on
  ## this path is its own cell.
  if pointee == nil or ptrScalarPointee(pointee): return ""
  for r in p.liveRefs.getOrDefault(typeId, @[]):
    if r.raw == ptrAst.raw: return ""
  template msg(where: string): string =
    "a `ptr " & $pointee & "` of unknown origin may address " & where &
      ", whose aggregate this model holds no pointer identity for -- not " &
      "modelled (RFC-0005 S8bz; feUnsupportedOp)"
  for name, sv in p.env.pairs:
    if isGlobalEnvName(name) and svHoldsAggregate(sv, pointee):
      return msg("the global `" & displayName(name) & "`")
  for cf in w.callStack:
    for formal in cf.ptrRiskFormals:
      if tyMayHold(formal.ty, pointee):
        return msg("the `var` formal `" & formal.name & "` of `" & cf.callee & "`")
  for prm in w.params:
    if prm.isVar and tyMayHold(prm.ty, pointee):
      return msg("the `var` parameter `" & prm.name & "`")
  for key in p.heaps.keys:
    if key == typeId or key.startsWith(typeId & "__"): continue
    let vt = heapKeyValTy(key)
    if vt != nil and heapCompoundTy(vt) and tyMayHold(vt, pointee):
      return msg("a part held in a heap cell (`" & key & "`)")
    # A by-value part of a heap object, held in a leaf heap per part: every
    # leaf of the pointee, below one key.
    let sfx = if heapCompoundTy(pointee): heapLeafSuffixes(pointee)
              else: newSeq[string]()
    if sfx.len > 0 and sfx[0].len > 0 and key.endsWith(sfx[0]):
      let base = key[0 ..< key.len - sfx[0].len]
      var whole = true
      for sf in sfx:
        if not p.heaps.hasKey(base & sf): whole = false
      if whole: return msg("a part held in a heap cell (`" & base & "`)")
  ""

proc ptrSeqElemMatches(e, pointee: IRType): bool =
  ## RFC-0005 S8bn (item 4). A seq of `e` holds locations a `ptr pointee`
  ## may address directly (a scalar or string element of the type).
  e != nil and ptrScalarPointee(pointee) and
    (e == pointee or (e.kind == itInt and pointee.kind == itInt and
                      e.width == pointee.width and e.signed == pointee.signed))

proc ptrTabValMatches(v, pointee: IRType): bool =
  ## RFC-0005 S8bn (item 4). A `Table[string, V]`'s values are locations a
  ## `ptr pointee` may address, held as the model's 64-bit cells: an
  ## integer `V` of the pointee's type. RFC-0005 S8bw (item 3): any value
  ## type the table holds (`isContainerIntLeaf`: an integer of any width, a
  ## char, an enum, a `bool`), each read and written through its cell
  ## (`cellValue` / `cellOf`); was a 64-bit integer only.
  ## RFC-0005 S8bz (item 2): a string or float value too, a term of its own
  ## sort (`tvStr`, `tvF32`, `tvF64`).
  if v == nil or pointee == nil: return false
  if v.kind in {itString, itFloat32, itFloat64}: return v.kind == pointee.kind
  isContainerIntLeaf(v) and
    ((v.kind == itBool and pointee.kind == itBool) or
     (v.kind == itInt and pointee.kind == itInt and
      v.width == pointee.width and v.signed == pointee.signed))

proc ptrTabCellRead(ctx: Z3Context; cell: RawZ3Ast; pointee: IRType): SymVal =
  ## RFC-0005 S8bw (item 3). The `pointee` value a table's 64-bit cell
  ## holds.
  cellValue(wrap[Z3BitVec[64]](ctx, cell), pointee)

proc ptrTabCellOf(val: SymVal; pointee: IRType): RawZ3Ast =
  ## RFC-0005 S8bw (item 3). The 64-bit table cell of the `pointee` value
  ## `val` (sign- or zero-extended, a `bool` as 0 / 1).
  let c = cellOf(val, pointee)
  if c.isSome: c.get.raw else: rawAnyAstOf(val)

type PtrLeaf = tuple[path: seq[int]; steps: seq[string]; seqIdx, tabKey: bool;
                     aggregate: bool; elemPath: seq[int]; elemSteps: seq[string]]
  ## RFC-0005 S8bn (item 4). A part of a variable: its `path` below the
  ## root. RFC-0005 S8bw (item 3): and its `steps` as the witness names them
  ## (`ptrAimInto`): a position, or `f<name>` for a case object's field.
  ## RFC-0005 S8bz (items 1, 2): a part of a leaf-split seq element or table
  ## value: the container at `path`, the part at `elemPath` / `elemSteps`
  ## below the element the pointer's index or key names.

const ptrArmBase = 4096
  ## RFC-0005 S8bw (item 3). A case object's branch field is the path step
  ## `-(1 + j + (tag + 1) * B + axis * B * B)` (`ptrArmStep`): field `j` of
  ## the branch of tag ordinal `tag` (-1 for `else`) on discriminator axis
  ## `axis`; a plain field is its position.

proc ptrArmStep(axis, tag, j: int): int =
  -(1 + j + (tag + 1) * ptrArmBase + axis * ptrArmBase * ptrArmBase)

proc ptrArmStepOf(s: int): tuple[axis, tag, j: int] =
  let v = -s - 1
  (v div (ptrArmBase * ptrArmBase), (v div ptrArmBase) mod ptrArmBase - 1,
   v mod ptrArmBase)

proc ptrArmView(sv: SymVal; axis: int): tuple[disc: SymVal;
    fields: OrderedTable[int, seq[SymVal]];
    names: OrderedTable[int, seq[string]]] =
  ## RFC-0005 S8bw (item 3). Axis `axis` of the case object `sv`.
  if sv.kind == svVariant: (sv.vDisc[], sv.vArmFields, sv.vArmFieldNames)
  else: (sv.mvAxes[axis].disc[], sv.mvAxes[axis].armFields,
         sv.mvAxes[axis].armFieldNames)

proc ptrTagCond(disc: SymVal; fields: OrderedTable[int, seq[SymVal]];
                tag: int): Z3Bool =
  ## RFC-0005 S8bw (item 3). The discriminator selects the branch of `tag`:
  ## an `else` branch (-1) is every ordinal no other branch lists.
  if tag != -1: return variantDiscEq(disc, int64(tag))
  result = mkBool(true)
  for t in fields.keys:
    if t != -1: result = result and not variantDiscEq(disc, int64(t))

proc ptrArmTags(names: OrderedTable[int, seq[string]]; nm: string): seq[int] =
  ## RFC-0005 S8bw (item 3). The tags whose branch declares the field `nm`
  ## (one branch: Nim forbids a field name in two; one tag per ordinal it
  ## lists, each holding its own copy).
  for t, ns in names:
    if nm in ns: result.add t

proc ptrArmCond(sv: SymVal; s: int): Z3Bool =
  ## RFC-0005 S8bw (item 3). The branch of the step `s` is active in `sv`.
  let (axis, tag, j) = ptrArmStepOf(s)
  let v = ptrArmView(sv, axis)
  let nm = v.names[tag][j]
  var first = true
  for t in ptrArmTags(v.names, nm):
    let c = ptrTagCond(v.disc, v.fields, t)
    if first: result = c; first = false
    else: result = result or c

proc ptrVarLeaves(sv: SymVal; pointee: IRType; path: seq[int]; depth: int;
                  acc: var seq[PtrLeaf]; steps: seq[string] = @[]): bool

proc ptrElemLeaves(elemTy, pointee: IRType; depth: int;
                   acc: var seq[PtrLeaf]): bool =
  ## RFC-0005 S8bz (items 1, 2). The parts of a leaf-split element or value of
  ## `elemTy` a `ptr pointee` may address, below the element. False when a
  ## part is itself a seq or table holding such a location: two indices, and
  ## the pointer has one (`ptrIdxAt`).
  var parts: seq[PtrLeaf]
  if not ptrVarLeaves(seqElemProto(elemTy), pointee, @[], depth + 1, parts):
    return false
  for e in parts:
    if e.seqIdx or e.tabKey: return false
    acc.add e
  true

proc ptrVarLeaves(sv: SymVal; pointee: IRType; path: seq[int]; depth: int;
                  acc: var seq[PtrLeaf]; steps: seq[string] = @[]): bool =
  ## RFC-0005 S8bn (item 4). The parts of the by-value value `sv` a
  ## `ptr pointee` may address, each a (path, seq index) below the root --
  ## S8ax's element-alias identity (root, path, snapshot index): a scalar or
  ## string leaf, a field of a tuple or object, an element of an array (each
  ## position a step), an element of a seq (a step the pointer's index
  ## names). False when a part may hold one but has no such identity here.
  ## RFC-0005 S8bz (item 1): a part of a seq's aggregate element, per
  ## element; a container inside that element holds no identity yet
  ## (`ptrElemLeaves`).
  ## RFC-0005 S8bw (item 3): a case object's plain fields and the fields of
  ## each branch (`ptrArmStep`); a pointer to a branch field addresses it
  ## only while its branch is active (`ptrArmCond`, checked at the
  ## dereference).
  if depth > 8: return not svMayHold(sv, pointee)
  case sv.kind
  of svBV8, svBV16, svBV32, svBV64, svInt, svBool, svFloat32, svFloat64,
     svString:
    if svMayHold(sv, pointee):
      acc.add (path, steps, false, false, false, newSeq[int](), newSeq[string]())
    true
  of svTuple:
    for i, f in sv.fields:
      if not ptrVarLeaves(f, pointee, path & @[i], depth + 1, acc,
                          steps & @[$i]): return false
    true
  of svArray:
    for i, e in sv.arrElems:
      if not ptrVarLeaves(e, pointee, path & @[i], depth + 1, acc,
                          steps & @[$i]): return false
    true
  of svVariant, svMultiVariant:
    let plain = if sv.kind == svVariant: sv.vPlainFields else: sv.mvPlainFields
    let plainNames = if sv.kind == svVariant: sv.vPlainFieldNames
                     else: sv.mvPlainFieldNames
    for i, f in plain:
      if not ptrVarLeaves(f, pointee, path & @[i], depth + 1, acc,
                          steps & @["f" & plainNames[i]]): return false
    let axes = if sv.kind == svVariant: 1 else: sv.mvAxes.len
    for axis in 0 ..< axes:
      let v = ptrArmView(sv, axis)
      var seen: seq[string]
      for tag, fs in v.fields:
        for j, f in fs:
          let nm = v.names[tag][j]
          if nm in seen: continue
          seen.add nm
          if not ptrVarLeaves(f, pointee, path & @[ptrArmStep(axis, tag, j)],
                              depth + 1, acc, steps & @["f" & nm]):
            return false
    true
  of svSeq:
    if not sv.isUnsupportedFieldPlaceholder and # [placeholder-audited]
       ptrSeqElemMatches(sv.seqElemTy, pointee):
      acc.add (path, steps, true, false, false, newSeq[int](), newSeq[string]())
      true
    elif not sv.isUnsupportedFieldPlaceholder and # [placeholder-audited]
         isTreeSeqElemTy(sv.seqElemTy):
      var parts: seq[PtrLeaf]
      if not ptrElemLeaves(sv.seqElemTy, pointee, depth, parts): return false
      for e in parts:
        acc.add (path, steps, true, false, true, e.path, e.steps)
      true
    else: not tyMayHold(sv.seqElemTy, pointee)
  of svTable:
    if sv.tabKeyTy != nil and sv.tabKeyTy.kind == itString and
       ptrTabValMatches(sv.tabValTy, pointee):
      acc.add (path, steps, false, true, false, newSeq[int](), newSeq[string]())
      true
    elif sv.tabKeyTy != nil and sv.tabKeyTy.kind == itString and
         heapTreeTy(sv.tabValTy):
      # RFC-0005 S8bz (item 2): a part of an aggregate value, per key.
      var parts: seq[PtrLeaf]
      if not ptrElemLeaves(sv.tabValTy, pointee, depth, parts): return false
      for e in parts:
        acc.add (path, steps, false, true, true, e.path, e.steps)
      true
    else: not tyMayHold(sv.tabValTy, pointee)
  of svSet: true      # a set's members have no address (`tyMayHold`)
  else: not svMayHold(sv, pointee)

proc svAtPath(sv: SymVal; path: seq[int]; i = 0): SymVal =
  ## RFC-0005 S8bn (item 4). The part of `sv` at `path[i ..]`.
  ## RFC-0005 S8bw (item 3): a case object's branch field is the copy the
  ## active tag holds (`isVariantField`'s fold over the branch's tags).
  if i >= path.len: return sv
  case sv.kind
  of svTuple: return svAtPath(sv.fields[path[i]], path, i + 1)
  of svArray: return svAtPath(sv.arrElems[path[i]], path, i + 1)
  of svVariant, svMultiVariant:
    if path[i] >= 0:
      let plain = if sv.kind == svVariant: sv.vPlainFields else: sv.mvPlainFields
      return svAtPath(plain[path[i]], path, i + 1)
    let (axis, tag, j) = ptrArmStepOf(path[i])
    let v = ptrArmView(sv, axis)
    let nm = v.names[tag][j]
    let tags = ptrArmTags(v.names, nm)
    result = svAtPath(v.fields[tags[^1]][v.names[tags[^1]].find(nm)], path, i + 1)
    for k in countdown(tags.len - 2, 0):
      let t = tags[k]
      result = iteSV(ptrTagCond(v.disc, v.fields, t),
                     svAtPath(v.fields[t][v.names[t].find(nm)], path, i + 1),
                     result)
  else: return sv

proc ptrInputOf(w: WalkCtx; vnm: string; path: seq[int]): SymVal =
  ## RFC-0005 S8bz (item 1). The container at `path` of the variable `vnm` when
  ## the run began: a parameter's input, or a global's entry value (S8as). A
  ## `svBool` stand-in for a variable with neither.
  if w.initialEnv.hasKey(vnm): svAtPath(w.initialEnv[vnm], path)
  elif globalEntryVals.hasKey(vnm): svAtPath(globalEntryVals[vnm], path)
  else: SymVal(kind: svBool)

proc svWithPath(sv: SymVal; path: seq[int]; v: SymVal; i = 0): SymVal =
  ## RFC-0005 S8bn (item 4). `sv` with its part at `path[i ..]` replaced.
  ## RFC-0005 S8bw (item 3): a case object's branch field in every tag's
  ## copy (one location in Nim's memory).
  if i >= path.len: return v
  result = sv
  case sv.kind
  of svTuple: result.fields[path[i]] = svWithPath(sv.fields[path[i]], path, v, i + 1)
  of svArray: result.arrElems[path[i]] = svWithPath(sv.arrElems[path[i]], path, v, i + 1)
  of svVariant:
    if path[i] >= 0:
      result.vPlainFields[path[i]] = svWithPath(sv.vPlainFields[path[i]], path,
                                                v, i + 1)
    else:
      let (_, tag, j) = ptrArmStepOf(path[i])
      let nm = sv.vArmFieldNames[tag][j]
      for t in ptrArmTags(sv.vArmFieldNames, nm):
        let k = sv.vArmFieldNames[t].find(nm)
        result.vArmFields[t][k] = svWithPath(sv.vArmFields[t][k], path, v, i + 1)
  of svMultiVariant:
    if path[i] >= 0:
      result.mvPlainFields[path[i]] = svWithPath(sv.mvPlainFields[path[i]],
                                                 path, v, i + 1)
    else:
      let (axis, tag, j) = ptrArmStepOf(path[i])
      let nm = sv.mvAxes[axis].armFieldNames[tag][j]
      for t in ptrArmTags(sv.mvAxes[axis].armFieldNames, nm):
        let k = sv.mvAxes[axis].armFieldNames[t].find(nm)
        result.mvAxes[axis].armFields[t][k] = svWithPath(
          sv.mvAxes[axis].armFields[t][k], path, v, i + 1)
  else: discard

proc svPathArmCond(sv: SymVal; path: seq[int]): tuple[has: bool; cond: Z3Bool] =
  ## RFC-0005 S8bw (item 3). Every case object branch the part at `path`
  ## lies in is active in `sv` (`has` false when it lies in none).
  var cur = sv
  for i, s in path:
    if cur.kind in {svVariant, svMultiVariant} and s < 0:
      let c = ptrArmCond(cur, s)
      result.cond = if result.has: result.cond and c else: c
      result.has = true
    cur = svAtPath(cur, @[s])

proc ptrIdxAt(ctx: Z3Context; p: Path; typeId: string; refSort: RawZ3Sort;
              ptrAst: Z3AnyAst): Z3AnyAst =
  ## RFC-0005 S8bn (item 4). `<T>__@ptridx[P]`: the element index of a
  ## pointer whose target is a seq element (an input array, never stored).
  let k = ptrIdxKey(typeId)
  if not p.heaps.hasKey(k):
    let intSort = ctx.checkErr Z3_mk_int_sort(ctx.raw)
    let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, intSort)
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & k).cstring)
    p.heaps[k] = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                               arrSort))
  wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[k].raw, ptrAst.raw))

proc ptrKeyAt(ctx: Z3Context; p: Path; typeId: string; refSort: RawZ3Sort;
              ptrAst: Z3AnyAst): Z3AnyAst =
  ## RFC-0005 S8bn (item 4). `<T>__@ptrkey[P]`: the key of a pointer whose
  ## target is a `Table[string, V]` value (an input array, never stored).
  ## Noted with the table keys (`noteTableKey`), so a witness renders it.
  let k = ptrKeyKey(typeId)
  if not p.heaps.hasKey(k):
    let strSort = ctx.checkErr Z3_mk_string_sort(ctx.raw)
    let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, strSort)
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & k).cstring)
    p.heaps[k] = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                               arrSort))
  result = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[k].raw, ptrAst.raw))
  noteTableKey(wrap[Z3String](ctx, result.raw))

proc ptrIdxInRange(ctx: Z3Context; idx: Z3AnyAst; len: Z3AnyAst): Z3Bool =
  ## RFC-0005 S8bn (item 4). `0 <= idx < len` over Z3 integers.
  let zero = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_int64(ctx.raw, 0,
    ctx.checkErr Z3_get_sort(ctx.raw, idx.raw)))
  let lo = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_le(ctx.raw, zero.raw, idx.raw))
  let hi = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_lt(ctx.raw, idx.raw, len.raw))
  lo and hi

proc z3OpName(ctx: Z3Context; a: RawZ3Ast): string =
  ## RFC-0005 S8bn (item 4). The operator of an application term ("store",
  ## "select", "ite", ...), "" for a non-application.
  if Z3_get_ast_kind(ctx.raw, a) != Z3_APP_AST: return ""
  $Z3_get_symbol_string(ctx.raw, Z3_get_decl_name(ctx.raw,
    Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))

proc z3Arg(ctx: Z3Context; a: RawZ3Ast; i: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, Z3_get_app_arg(ctx.raw, Z3_to_app(ctx.raw, a), cuint(i)))

proc lenUntouched(ctx: Z3Context; arr: Z3AnyAst; inLen: Z3AnyAst;
                  depth = 0): bool =
  ## RFC-0005 S8bn (item 4). The length heap `arr` (stores and merges over
  ## its input array) holds the input lengths by construction: every store
  ## into it stores a read of a length cell back (an element write
  ## re-stores the length it read), never a computed length. A length that
  ## changed and changed back (`add` then `pop`, which may move the
  ## elements) stores a computed term and fails.
  if depth > 64: return false
  let a = wrap[Z3AnyAst](ctx, arr.raw)
  case z3OpName(ctx, a.raw)
  of "store":
    # The value re-stored is a read of the length cell at the store's own
    # address (not another object's length: a seq replaced by another).
    let v = z3Arg(ctx, a.raw, 2)
    if v.raw != inLen.raw:
      if z3OpName(ctx, v.raw) != "select": return false
      if z3Arg(ctx, v.raw, 1).raw != z3Arg(ctx, a.raw, 1).raw: return false
    lenUntouched(ctx, z3Arg(ctx, a.raw, 0), inLen, depth + 1)
  of "ite":
    lenUntouched(ctx, z3Arg(ctx, a.raw, 1), inLen, depth + 1) and
      lenUntouched(ctx, z3Arg(ctx, a.raw, 2), inLen, depth + 1)
  else: true              # the input constant

proc tabNoDeletion(ctx: Z3Context; arr: Z3AnyAst; depth = 0): bool =
  ## RFC-0005 S8bn (item 4). The present array `arr` stores no `false`: no
  ## key was deleted on the path (a deletion may shift other entries).
  if depth > 64: return false
  let a = wrap[Z3AnyAst](ctx, arr.raw)
  case z3OpName(ctx, a.raw)
  of "store":
    let v = z3Arg(ctx, a.raw, 2)
    if $simplify(wrap[Z3Bool](ctx, v.raw)) != "true": return false
    tabNoDeletion(ctx, z3Arg(ctx, a.raw, 0), depth + 1)
  of "ite":
    tabNoDeletion(ctx, z3Arg(ctx, a.raw, 1), depth + 1) and
      tabNoDeletion(ctx, z3Arg(ctx, a.raw, 2), depth + 1)
  else: true

proc sameTerm(ctx: Z3Context; w: WalkCtx; p: Path; a, b: Z3AnyAst): bool =
  ## RFC-0005 S8bn (item 4). `a` and `b` are equal on path `p`: one term,
  ## equal by simplification, or their difference infeasible on the path
  ## (`loopArmInfeasible`, bounded; an undecided query is "not equal").
  if a.raw == b.raw: return true
  let eq = wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, b.raw))
  if $simplify(eq) == "true": return true
  loopArmInfeasible(ctx, p, not eq, w.settings)

proc ptrHeapArmCond(ctx: Z3Context; p: Path; key: string; objAddr: Z3AnyAst):
    tuple[has, decline: bool; cond: Z3Bool] =
  ## RFC-0005 S8bw (item 3). For the field family `key` of a case object's
  ## branch (`<O>__@<ord>__<f>`): the object at `objAddr` has the branch
  ## active (its discriminator heap, `variantDiscHeapKey`). `decline` when
  ## no discriminator heap of the type is known.
  let at = key.find("__@")
  if at < 0: return
  let rest = key[at + 3 .. ^1]
  let sep = rest.find("__")
  if sep <= 0: return
  let ord = try: parseInt(rest[0 ..< sep]) except ValueError: return
  let field = rest[sep + 2 .. ^1]
  let baseId = key[0 ..< at]
  result.has = true
  var vty: IRType = nil
  var dk = ""
  for k, shape in heapKeyShapes:
    if not k.startsWith(baseId & "__@disc") or shape.variantTy == nil: continue
    if variantDiscHeapKey(shape.variantTy) != k: continue
    for arm in shape.variantTy.vArms:
      if arm.tagOrdinal == ord and field in arm.fieldNames:
        vty = shape.variantTy
        dk = k
  if vty == nil:
    result.decline = true
    return
  let heap = if p.heaps.hasKey(dk): p.heaps[dk]
             else: mkHeapArrayVar(ctx, allocRefSort(ctx, vty), vty.vDiscTy,
                                  "heap_" & dk, vty)
  let disc = heapSelect(ctx, heap, objAddr, vty.vDiscTy)
  if ord != -1:
    result.cond = variantDiscEq(disc, int64(ord))
  else:
    result.cond = mkBool(true)
    for arm in vty.vArms:
      if not arm.isElse:
        result.cond = result.cond and not variantDiscEq(disc, int64(arm.tagOrdinal))

proc ptrRouteDecline(p: Path; ptrAst: Z3AnyAst; what: string): string =
  ## RFC-0005 S8cs. A dereference of a pointer the walk did not allocate on this
  ## path reads whatever it addresses, as a read of its name does (`lower`'s
  ## `iekVar` arm): a variable a store the walk does not see may reach, one the
  ## program does not name included. The decline message, or "".
  let hidden = globalHiddenRoute(routeAnyStore)
  if hidden.len == 0: return ""
  for rs in p.liveRefs.values:
    for r in rs:
      if r.raw == ptrAst.raw: return ""
  "a `ptr " & what & "` of unknown origin may address a variable a store the " &
    "walk does not see may reach: " & hidden & " (feGlobalRouteUnproved)"

proc svScalarSize(sv: SymVal): int =
  ## RFC-0005 S8bz (item 6). The bytes a scalar value occupies, 0 for a shape
  ## whose layout this model does not compute.
  case sv.kind
  of svBV8, svBool: 1
  of svBV16: 2
  of svBV32, svFloat32: 4
  of svBV64, svFloat64: 8
  of svInt: (if sv.ziWidth == 0: 8 else: sv.ziWidth div 8)
  else: 0

proc tyScalarSize(ty: IRType): int =
  ## RFC-0005 S8bz (item 6). `svScalarSize` by type.
  if ty == nil: return 0
  case ty.kind
  of itInt: ty.width div 8
  of itBool: 1
  of itFloat32: 4
  of itFloat64: 8
  else: 0

proc armOffsets(sizes: seq[int]; packed: bool): seq[int] =
  ## RFC-0005 S8bz (item 6). The offsets of a branch's fields from the start of
  ## the object's union: C's layout of the struct Nim emits for a branch, each
  ## scalar at its natural alignment (native suite), or with none under
  ## `{.packed.}`. -1 from the first field whose layout is not computed on.
  var o = 0
  var known = true
  for sz in sizes:
    if sz <= 0: known = false
    if not known:
      result.add -1
      continue
    if not packed and o mod sz != 0: o += sz - (o mod sz)
    result.add o
    o += sz

proc overlapPair(a, b: SymVal): bool =
  ## RFC-0005 S8bz (item 6). Same-size scalars whose bytes both spell a value of
  ## the other: integers and floats. A `bool` overlaps only a `bool` (any other
  ## byte is no `bool`).
  svScalarSize(a) == svScalarSize(b) and svScalarSize(a) > 0 and
    (a.kind == svBool) == (b.kind == svBool)

proc ptrArmOverlaps(v: SymVal; step: int): seq[PtrOverlap] =
  ## RFC-0005 S8bz (item 6). For the branch field at `step` of the case object
  ## `v`, a by-value `svVariant`: each other branch with a field of its size at
  ## its offset. A branch without one stays the scoped decline (`ptrInactive`):
  ## a partial overlap, or bytes that branch does not hold.
  if v.kind != svVariant or step >= 0: return
  let (_, tag, j) = ptrArmStepOf(step)
  let target = v.vArmFields[tag][j]
  var ts: seq[int]
  for f in v.vArmFields[tag]: ts.add svScalarSize(f)
  # The IR does not say `{.packed.}`: an overlap holds under both layouts.
  let off = armOffsets(ts, false)[j]
  let offP = armOffsets(ts, true)[j]
  if off < 0: return
  let nm = v.vArmFieldNames[tag][j]
  for t, fs in v.vArmFields:
    if nm in v.vArmFieldNames[t]: continue
    var szs: seq[int]
    for f in fs: szs.add svScalarSize(f)
    let offs = armOffsets(szs, false)
    let offsP = armOffsets(szs, true)
    for k, f in fs:
      if offs[k] == off and offsP[k] == offP and overlapPair(f, target):
        let c = ptrTagCond(v.vDisc[], v.vArmFields, t)
        result.add PtrOverlap(cond: c, step: ptrArmStep(0, t, k),
          nan: (case f.kind
                of svFloat64: c and isNaN(f.fp64)
                of svFloat32: c and isNaN(f.fp32)
                else: mkBool(false)))
        break

proc ptrReinterpret(ctx: Z3Context; v: SymVal; like: SymVal): SymVal =
  ## RFC-0005 S8bz (item 6). The value of `like`'s kind that `v`'s bytes spell
  ## (same size: `overlapPair`). Native suite: Nim's dereference reads those
  ## bytes as the pointer's type.
  if v.kind == like.kind and (v.kind notin {svBV8, svBV16, svBV32, svBV64} or
                              v.signed == like.signed):
    return v
  if like.kind == svBool: return v
  var bits =
    case v.kind
    of svFloat32: ctx.checkErr Z3_mk_fpa_to_ieee_bv(ctx.raw, v.fp32.raw)
    of svFloat64: ctx.checkErr Z3_mk_fpa_to_ieee_bv(ctx.raw, v.fp64.raw)
    of svInt: ctx.checkErr Z3_mk_int2bv(ctx.raw, cuint(svScalarSize(v) * 8), v.zi.raw)
    else: rawAnyAstOf(v)
  case like.kind
  of svFloat32:
    SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, ctx.checkErr(
      Z3_mk_fpa_to_fp_bv(ctx.raw, bits, ctx.checkErr Z3_get_sort(ctx.raw, like.fp32.raw)))))
  of svFloat64:
    SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, ctx.checkErr(
      Z3_mk_fpa_to_fp_bv(ctx.raw, bits, ctx.checkErr Z3_get_sort(ctx.raw, like.fp64.raw)))))
  of svBV8: liftBV(wrap[Z3BitVec[8]](ctx, bits), like.signed)
  of svBV16: liftBV(wrap[Z3BitVec[16]](ctx, bits), like.signed)
  of svBV32: liftBV(wrap[Z3BitVec[32]](ctx, bits), like.signed)
  of svBV64: liftBV(wrap[Z3BitVec[64]](ctx, bits), like.signed)
  of svInt:
    # A heap's `Int` cell: the signed value of the bits (`intHeapCell`).
    let n = svScalarSize(like)
    var r = like
    r.zi = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, bits, true))
    discard n
    r
  else: v

proc ptrOverlapsOfHeap(ctx: Z3Context; p: Path; key: string; objAddr: Z3AnyAst):
    seq[PtrOverlap] =
  ## RFC-0005 S8bz (item 6). `ptrArmOverlaps` for the field family `key` of a
  ## case object's branch held in a heap (`<O>__@<ord>__<f>`).
  let at = key.find("__@")
  if at < 0: return
  let rest = key[at + 3 .. ^1]
  let sep = rest.find("__")
  if sep <= 0: return
  let ordS = rest[0 ..< sep]
  if ordS != "-1" and not ordS.allCharsInSet(Digits): return
  let ord = parseInt(ordS)
  let field = rest[sep + 2 .. ^1]
  let baseId = key[0 ..< at]
  var vty: IRType = nil
  var dk = ""
  for k, shape in heapKeyShapes:
    if not k.startsWith(baseId & "__@disc") or shape.variantTy == nil: continue
    if variantDiscHeapKey(shape.variantTy) != k: continue
    vty = shape.variantTy
    dk = k
  if vty == nil: return
  var off = -1
  var offP = -1
  var size = 0
  var isBool = false
  for arm in vty.vArms:
    if arm.tagOrdinal == ord and field in arm.fieldNames:
      var szs: seq[int]
      for f in arm.fieldTypes: szs.add tyScalarSize(f)
      let ix = arm.fieldNames.find(field)
      off = armOffsets(szs, false)[ix]
      offP = armOffsets(szs, true)[ix]
      size = szs[ix]
      isBool = arm.fieldTypes[ix].kind == itBool
  if off < 0: return
  let heap = if p.heaps.hasKey(dk): p.heaps[dk]
             else: mkHeapArrayVar(ctx, allocRefSort(ctx, vty), vty.vDiscTy,
                                  "heap_" & dk, vty)
  let disc = heapSelect(ctx, heap, objAddr, vty.vDiscTy)
  for arm in vty.vArms:
    if field in arm.fieldNames: continue
    var szs: seq[int]
    for f in arm.fieldTypes: szs.add tyScalarSize(f)
    let offs = armOffsets(szs, false)
    let offsP = armOffsets(szs, true)
    for k, f in arm.fieldTypes:
      if offs[k] == off and offsP[k] == offP and szs[k] == size and
         (f.kind == itBool) == isBool:
        var c: Z3Bool
        if arm.isElse:
          c = mkBool(true)
          for o in vty.vArms:
            if not o.isElse: c = c and not variantDiscEq(disc, int64(o.tagOrdinal))
        else:
          c = variantDiscEq(disc, int64(arm.tagOrdinal))
        let fk = baseId & "__@" &
          $(if arm.isElse: -1 else: arm.tagOrdinal) & "__" & arm.fieldNames[k]
        # A NaN's bytes are not one value: as `ptrArmOverlaps`, a decline.
        var nan = mkBool(false)
        if f.kind in {itFloat32, itFloat64}:
          let arr = if p.heaps.hasKey(fk): p.heaps[fk]
                    else: mkHeapArrayVar(ctx, sortOfRaw(ctx, objAddr.raw), f,
                                         "heap_" & fk)
          let cur = heapSelect(ctx, arr, objAddr, f)
          nan = c and (if f.kind == itFloat64: isNaN(cur.fp64)
                       else: isNaN(cur.fp32))
        result.add PtrOverlap(cond: c, famKey: fk, ty: f, nan: nan)
        break

proc ptrHeapDiscFact(ctx: Z3Context; p: Path; key: string;
                     objAddr: Z3AnyAst): Option[Z3Bool] =
  ## RFC-0005 S8bz (item 6). The object at `objAddr` holds a value of its case
  ## type: its discriminator names a branch (an `else` branch takes the rest).
  let at = key.find("__@")
  if at < 0: return
  let baseId = key[0 ..< at]
  for k, shape in heapKeyShapes:
    if not k.startsWith(baseId & "__@disc") or shape.variantTy == nil: continue
    if variantDiscHeapKey(shape.variantTy) != k: continue
    let vty = shape.variantTy
    let heap = if p.heaps.hasKey(k): p.heaps[k]
               else: mkHeapArrayVar(ctx, allocRefSort(ctx, vty), vty.vDiscTy,
                                    "heap_" & k, vty)
    let disc = heapSelect(ctx, heap, objAddr, vty.vDiscTy)
    var c = mkBool(false)
    for arm in vty.vArms:
      if arm.isElse: return none(Z3Bool)
      c = c or variantDiscEq(disc, int64(arm.tagOrdinal))
    return some(c)

proc ptrFamSeq(ctx: Z3Context; p: Path; t: PtrTarget): SymVal =
  ## RFC-0005 S8bz (items 1, 2). The seq or table of aggregates the target's
  ## field family holds at its object, whole (every leaf heap).
  var cell: HeapCell
  for sfx in heapLeafSuffixes(t.famElemTy):
    cell.add (sfx, p.heaps[t.famKey & sfx])
  heapCellSelect(ctx, cell, t.objAddr, t.famElemTy)

proc ptrTargets(ctx: Z3Context; w: var WalkCtx; p: Path; ptrAst: Z3AnyAst;
                pointee: IRType; refSort: RawZ3Sort; typeId: string):
    tuple[sel: Z3AnyAst; targets: seq[PtrTarget]; decline: string] =
  ## RFC-0005 S8bh. The candidate targets of the pointer `ptrAst` on path `p`
  ## (see the section comment), and `sel(ptrAst)`. Materialises the arrays
  ## it reads into `p.heaps` and asserts each field target's freshness
  ## facts into `p.pc` (`p` is the caller's own fork). `decline` names a
  ## location the model has no cell for.
  # A pointer the walk allocated on this path (a `new`, an `addr` cell) is
  # its own cell (`ptrSelOwnAtAlloc`): no candidates, nothing to decline.
  # Hash-consing makes the allocation's constant the same AST wherever the
  # pointer flowed (a callee's formal, a closure's argument).
  for r in p.liveRefs.getOrDefault(typeId, @[]):
    if r.raw == ptrAst.raw: return
  result.decline = ptrRouteDecline(p, ptrAst, $pointee)   # RFC-0005 S8cs
  if result.decline.len > 0: return
  if not ptrScalarPointee(pointee): return
  var scratch: seq[Z3Bool]
  let proto = allocateSym(pointee, "__ptrTargetProto", scratch)
  let valSort = heapValueSort(ctx, proto, pointee)
  # The variables: globals, and the SUT's `var` parameters.
  # RFC-0005 S8bn (item 4): a part of a by-value aggregate variable -- a
  # field, an array element, a seq element -- is a target too, named by
  # its path below the variable (`ptrVarLeaves`). A seq element is the
  # pointer's index (`ptrIdxAt`) into the seq: within its INPUT length (the
  # pointer addressed an element when the run began), and only while the
  # path has not changed that length (a resize may move the buffer, which
  # would leave the pointer dangling).
  template addVarLeaves(vnm: string; vsv: SymVal; vwhat: string) =
    var leaves: seq[PtrLeaf]
    if not ptrVarLeaves(vsv, pointee, @[], 0, leaves):
      result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
        "address a part of " & vwhat & ", a table value or seq element " &
        "this model holds no element identity for -- not modelled " &
        "(RFC-0005 S8bn; feUnsupportedOp)"
      return
    for lf in leaves:
      if lf.path.len == 0 and not lf.seqIdx and not lf.tabKey:
        result.targets.add PtrTarget(code: ptrTargetCode(vnm), envName: vnm)
        continue
      let code = ptrTargetCode(vnm & ptrLeafPathStr(lf.steps, lf.seqIdx) &
                               (if lf.tabKey: "/#" else: "") &
                               ptrLeafPathStr(lf.elemSteps, false))
      var t = PtrTarget(code: code, envName: vnm, path: lf.path,
                        seqIdx: lf.seqIdx, tabKey: lf.tabKey,
                        aggregate: lf.aggregate, elemPath: lf.elemPath)
      # RFC-0005 S8bw (item 3): a field of a case object's branch, while
      # the branch is active.
      (t.hasArm, t.armCond) = svPathArmCond(vsv, lf.path)
      if lf.tabKey:
        # A table value: the pointer's key, present in the input table; the
        # entries stay where they are only while the path has not changed
        # which keys are present (a resize or a deletion may move them).
        let cur = svAtPath(vsv, lf.path)
        let ini = ptrInputOf(w, vnm, lf.path)
        if ini.kind != svTable or cur.kind != svTable or
           not sameTerm(ctx, w, p, cur.tabPresentRaw, ini.tabPresentRaw) or
           not tabNoDeletion(ctx, cur.tabPresentRaw) or
           not sameTerm(ctx, w, p, wrap[Z3AnyAst](ctx, cur.tabSize.raw),
                        wrap[Z3AnyAst](ctx, ini.tabSize.raw)):
          result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
            "address a value of the table " & vwhat & ", whose keys this " &
            "path changed: its entries may have moved, so the pointer may " &
            "dangle -- not modelled (RFC-0005 S8bn; feUnsupportedOp)"
          return
        t.idx = ptrKeyAt(ctx, p, typeId, refSort, ptrAst)
        idxFacts.add (code, wrap[Z3Bool](ctx, checkedSelect(ctx,
                                         ini.tabPresentRaw.raw, t.idx.raw)))
        if lf.aggregate:
          # RFC-0005 S8bz (item 2): the value's own branch.
          let ea = svPathArmCond(tabValAt(ctx, cur, t.idx.raw), lf.elemPath)
          if ea.has:
            t.armCond = if t.hasArm: t.armCond and ea.cond else: ea.cond
            t.hasArm = true
      if lf.seqIdx:
        let cur = svAtPath(vsv, lf.path)
        let ini = ptrInputOf(w, vnm, lf.path)
        if ini.kind != svSeq or cur.kind != svSeq or
           cur.seqLen.raw != ini.seqLen.raw:
          result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
            "address an element of the seq " & vwhat & ", whose length " &
            "this path changed: a resize may move its elements, so the " &
            "pointer may dangle -- not modelled (RFC-0005 S8bn; " &
            "feUnsupportedOp)"
          return
        t.idx = ptrIdxAt(ctx, p, typeId, refSort, ptrAst)
        idxFacts.add (code, ptrIdxInRange(ctx, t.idx,
                                          wrap[Z3AnyAst](ctx, ini.seqLen.raw)))
        if lf.aggregate:
          # RFC-0005 S8bz (item 1): the element's own branch.
          let elemV = seqElemAt(cur, wrap[Z3Int](ctx, t.idx.raw))
          # The element holds a value of its type (its discriminator names a
          # branch), as a read of it asserts.
          for c in svCellWf(elemV, cur.seqElemTy, false, false):
            idxFacts.add (code, c)
          let ea = svPathArmCond(elemV, lf.elemPath)
          if ea.has:
            t.armCond = if t.hasArm: t.armCond and ea.cond else: ea.cond
            t.hasArm = true
      # RFC-0005 S8bz (item 6): the one branch step of its path, its last.
      if t.hasArm:
        var branches = 0
        for st in lf.path & lf.elemPath:
          if st < 0: inc branches
        if branches == 1:
          if lf.aggregate and lf.elemPath[^1] < 0:
            let cont = svAtPath(vsv, lf.path)
            let elem =
              if lf.tabKey: tabValAt(ctx, cont, t.idx.raw)
              else: seqElemAt(cont, wrap[Z3Int](ctx, t.idx.raw))
            t.overlaps = ptrArmOverlaps(svAtPath(elem, lf.elemPath[0 .. ^2]),
                                        lf.elemPath[^1])
          elif not lf.aggregate and not lf.seqIdx and not lf.tabKey and
               lf.path[^1] < 0:
            t.overlaps = ptrArmOverlaps(svAtPath(vsv, lf.path[0 .. ^2]),
                                        lf.path[^1])
      ptrLeafAims[code] = PtrLeafAim(name: vnm, path: lf.path, steps: lf.steps,
                                     seqIdx: lf.seqIdx, tabKey: lf.tabKey,
                                     elemSteps: lf.elemSteps, typeId: typeId)
      result.targets.add t
  var idxFacts: seq[tuple[code: int64; inRange: Z3Bool]]
  # RFC-0005 S8cd: a global the walk has only read (or not met yet) is a
  # target too: its cell holds its entry value, which is what `env` gets
  # here, shared with every read (`entryValueOf`). Scanning only the bound
  # ones lost the alias: `let a = g; p[] = 7; if g != a` came back `sxUnsat`
  # for the `p` that addresses `g`. A name a callee holds withheld for its
  # own copy-in/copy-out stays withheld (`callGuardedNames`).
  if not isFollowConcreteWalk():
    var unbound: seq[string]
    for name, g in w.statics.globals.pairs:
      if g.isVar and not p.env.hasKey(name) and name notin callGuardedNames and
         tyMayHold(g.ty, pointee):
        unbound.add name
    unbound.sort()
    for name in unbound:
      p.env[name] = if programGlobal(name).isSome: entryValueOf(name)
                    else: globalInitValue(name, w.statics.globals[name].ty)
  for name, sv in p.env.pairs:
    if not isGlobalEnvName(name): continue
    addVarLeaves(name, sv, "the global `" & displayName(name) & "`")
  # A callee's `var` formal is a copy of its actual, written back when the
  # callee returns (copy-in/copy-out). Nim passes the location: a store
  # through the pointer into the actual's location is visible through the
  # formal at once. With the formal standing for a location this model has
  # no cell for in the callee's frame, a formal that may be of type T
  # declines (every frame on the stack: an outer callee's formal is not in
  # this frame's env either). RFC-0005 S8bn (item 3): only a formal whose
  # actual a pointer may address (`ptrRiskFormals`); a local whose address
  # is never taken is no pointer's target. A closure's formals are its
  # lambda's, recorded at the call like a proc's.
  for cf in w.callStack:
    for formal in cf.ptrRiskFormals:
      if tyMayHold(formal.ty, pointee):
        result.decline = "a `ptr " & $pointee & "` of unknown origin, " &
          "dereferenced while `" & cf.callee & "` runs, may address the " &
          "location of its `var` formal `" & formal.name & "`, which the " &
          "walk copies in and out -- not modelled (RFC-0005 S8bh; " &
          "feUnsupportedOp)"
        return
  for prm in w.params:
    if not prm.isVar: continue
    if w.frameStack.len > 0:
      if tyMayHold(prm.ty, pointee):
        result.decline = "a `ptr " & $pointee & "` of unknown origin, " &
          "dereferenced in a callee, may address the `var` parameter `" &
          prm.name & "` of the SUT, which the callee's frame does not " &
          "hold -- not modelled (RFC-0005 S8bh; feUnsupportedOp)"
        return
      continue
    if not p.env.hasKey(prm.name): continue
    let sv = p.env[prm.name]
    if prm.ty == pointee or (prm.ty != nil and prm.ty.kind == itInt and
                             pointee.kind == itInt and svMayHold(sv, pointee)):
      result.targets.add PtrTarget(code: ptrTargetCode(prm.name),
                                   envName: prm.name)
    elif tyMayHold(prm.ty, pointee):
      addVarLeaves(prm.name, sv, "the `var` parameter `" & prm.name & "`")
  # The field families the path has materialised.
  var famKeys: seq[string]
  var seqFamKeys: seq[string]
  var tabFamKeys: seq[string]
  for key in p.heaps.keys:
    if key == typeId or key.startsWith(typeId & "__@"): continue
    # RFC-0005 S8bz (item 1): a by-value part of a heap object, in a leaf heap
    # of its own (`<O>__<f>__@.<part>`). It was no target: a store through the
    # pointer was never seen by a read of the part (a false `sxUnsat`). A
    # case object's or container's leaf there stays a stated decline.
    let leafAt = key.find("__@.")
    if leafAt >= 0 and not key.startsWith(typeId & "__"):
      let leafRange = ctx.checkErr Z3_get_array_sort_range(ctx.raw,
        sortOfRaw(ctx, p.heaps[key].raw))
      if leafRange != valSort: continue
      if key[leafAt + 4 .. ^1].replace("__@.", ".").contains("@"):
        result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
          "address a part of a case object or container held by value in a " &
          "heap cell (`" & key & "`), which this model holds no cell " &
          "identity for -- not modelled (RFC-0005 S8bz; feUnsupportedOp)"
        return
      famKeys.add key
      continue
    let vt = heapKeyValTy(key)
    if vt == nil: continue
    if heapCompoundTy(vt) and "__@len" notin key and "__@present" notin key:
      # RFC-0005 S8bn (item 4): an element of a seq held in a field family:
      # the family's object (as a scalar family's) and the pointer's index.
      if vt.kind == itSeq and ptrSeqElemMatches(vt.seqElemTy, pointee):
        seqFamKeys.add key
        continue
      # RFC-0005 S8bz (item 1): a part of a seq's aggregate element.
      if vt.kind == itSeq and seqBackedTy(vt) and isTreeSeqElemTy(vt.seqElemTy):
        var parts: seq[PtrLeaf]
        if ptrElemLeaves(vt.seqElemTy, pointee, 0, parts):
          if parts.len > 0: seqFamKeys.add key
          continue
      if vt.kind == itTable and vt.tabKeyTy != nil and
         vt.tabKeyTy.kind == itString and ptrTabValMatches(vt.tabValTy, pointee):
        tabFamKeys.add key
        continue
      # RFC-0005 S8bz (item 2): a part of a table's aggregate value.
      if vt.kind == itTable and vt.tabKeyTy != nil and
         vt.tabKeyTy.kind == itString and heapTreeTy(vt.tabValTy):
        var parts: seq[PtrLeaf]
        if ptrElemLeaves(vt.tabValTy, pointee, 0, parts):
          if parts.len > 0: tabFamKeys.add key
          continue
      if tyMayHold(vt, pointee):
        result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
          "address an element of a " & $vt.kind & " held in a heap cell " &
          "(`" & key & "`), which this model holds no cell for -- not " &
          "modelled (RFC-0005 S8bh; feUnsupportedOp)"
        return
      continue
    if not ptrFamilyKey(key) or vt != pointee: continue
    famKeys.add key
  famKeys.sort()
  for key in famKeys:
    let arrSort = sortOfRaw(ctx, p.heaps[key].raw)
    if ctx.checkErr(Z3_get_array_sort_range(ctx.raw, arrSort)) != valSort:
      continue
    let objSort = ctx.checkErr Z3_get_array_sort_domain(ctx.raw, arrSort)
    let ok = ptrObjKey(typeId, key)
    if not p.heaps.hasKey(ok):
      let mapSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, objSort)
      let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & ok).cstring)
      p.heaps[ok] = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                                 mapSort))
    let objAddr = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[ok].raw,
                                                    ptrAst.raw))
    # The object predates every allocation of the walk: distinct from each
    # so far, and -- recorded under `ptrPreKey` -- from every later one
    # (`assertFreshness`). Not under the type's own `liveRefs` key: two
    # pointers may address one object, so its addresses are never asserted
    # distinct from each other.
    var oid = ""
    for tid, srt in currentRefSorts:
      if srt == objSort: oid = tid
    if oid.len > 0:
      template neq(a, b: Z3AnyAst): Z3Bool =
        not wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, b.raw))
      if currentNilConsts.hasKey(oid):
        p.pc.add neq(objAddr, currentNilConsts[oid])
      for r in p.liveRefs.getOrDefault(oid, @[]):
        p.pc.add neq(objAddr, r)
      let pk = ptrPreKey(oid)
      var seen = false
      for r in p.liveRefs.getOrDefault(pk, @[]):
        if r.raw == objAddr.raw: seen = true
      if not seen:
        if p.liveRefs.hasKey(pk): p.liveRefs[pk].add objAddr
        else: p.liveRefs[pk] = @[objAddr]
    var t = PtrTarget(code: ptrTargetCode(key), famKey: key, objAddr: objAddr)
    # RFC-0005 S8bw (item 3): a field of a case object's branch is there
    # only while the object's discriminator selects the branch.
    let arm = ptrHeapArmCond(ctx, p, key, objAddr)
    if arm.decline:
      result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
        "address the branch field `" & key & "` of a case object whose " &
        "discriminator this model holds no heap for -- not modelled " &
        "(RFC-0005 S8bw; feUnsupportedOp)"
      return
    (t.hasArm, t.armCond) = (arm.has, arm.cond)
    if arm.has:   # RFC-0005 S8bz (item 6)
      t.overlaps = ptrOverlapsOfHeap(ctx, p, key, objAddr)
      let d = ptrHeapDiscFact(ctx, p, key, objAddr)
      if d.isSome: idxFacts.add (t.code, d.get)
    result.targets.add t
  seqFamKeys.sort()
  for key in seqFamKeys:
    let arrSort = sortOfRaw(ctx, p.heaps[key].raw)
    let objSort = ctx.checkErr Z3_get_array_sort_domain(ctx.raw, arrSort)
    let lenKey = key & "__@len"
    let ok = ptrObjKey(typeId, key)
    if not p.heaps.hasKey(ok):
      let mapSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, objSort)
      let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & ok).cstring)
      p.heaps[ok] = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                                 mapSort))
    let objAddr = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[ok].raw,
                                                    ptrAst.raw))
    # The seq's input length at the object, and its length on this path:
    # one term, or the elements may have moved (see `addVarLeaves`).
    let lsym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
                                                ("heap_" & lenKey).cstring)
    let intSort = ctx.checkErr Z3_mk_int_sort(ctx.raw)
    let inArr = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, lsym,
      ctx.checkErr Z3_mk_array_sort(ctx.raw, objSort, intSort)))
    let inLen = wrap[Z3AnyAst](ctx, checkedSelect(ctx, inArr.raw, objAddr.raw))
    if p.heaps.hasKey(lenKey):
      let curLen = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[lenKey].raw,
                                                     objAddr.raw))
      if not sameTerm(ctx, w, p, curLen, inLen) or
         not lenUntouched(ctx, p.heaps[lenKey], inLen):
        result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
          "address an element of a seq held in a heap cell (`" & key &
          "`) whose length this path changed: a resize may move its " &
          "elements, so the pointer may dangle -- not modelled (RFC-0005 " &
          "S8bn; feUnsupportedOp)"
        return
    var oid = ""
    for tid, srt in currentRefSorts:
      if srt == objSort: oid = tid
    if oid.len > 0:
      template neq2(a, b: Z3AnyAst): Z3Bool =
        not wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, b.raw))
      if currentNilConsts.hasKey(oid):
        p.pc.add neq2(objAddr, currentNilConsts[oid])
      for r in p.liveRefs.getOrDefault(oid, @[]):
        p.pc.add neq2(objAddr, r)
      let pk = ptrPreKey(oid)
      var seen = false
      for r in p.liveRefs.getOrDefault(pk, @[]):
        if r.raw == objAddr.raw: seen = true
      if not seen:
        if p.liveRefs.hasKey(pk): p.liveRefs[pk].add objAddr
        else: p.liveRefs[pk] = @[objAddr]
    let idx = ptrIdxAt(ctx, p, typeId, refSort, ptrAst)
    let vt = heapKeyValTy(key)
    if isTreeSeqElemTy(vt.seqElemTy):
      # RFC-0005 S8bz (item 1): each part of the object's element.
      var parts: seq[PtrLeaf]
      discard ptrElemLeaves(vt.seqElemTy, pointee, 0, parts)
      var missing = false
      for sfx in heapLeafSuffixes(vt):
        if not p.heaps.hasKey(key & sfx): missing = true
      if missing:
        result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
          "address an element of a seq held in a heap cell (`" & key &
          "`), part of whose element this path holds no heap for -- not " &
          "modelled (RFC-0005 S8bz; feUnsupportedOp)"
        return
      for e in parts:
        let code = ptrTargetCode(key & "/*" & ptrLeafPathStr(e.steps, false))
        idxFacts.add (code, ptrIdxInRange(ctx, idx, inLen))
        ptrLeafAims[code] = PtrLeafAim(fam: key, seqIdx: true, typeId: typeId,
                                       elemSteps: e.steps)
        var t = PtrTarget(code: code, famKey: key, objAddr: objAddr,
                          seqIdx: true, idx: idx, aggregate: true,
                          elemPath: e.path, famElemTy: vt)
        (t.hasArm, t.armCond) = svPathArmCond(
          seqElemAt(ptrFamSeq(ctx, p, t), wrap[Z3Int](ctx, idx.raw)), e.path)
        result.targets.add t
      continue
    let code = ptrTargetCode(key & "/*")
    idxFacts.add (code, ptrIdxInRange(ctx, idx, inLen))
    ptrLeafAims[code] = PtrLeafAim(fam: key, seqIdx: true, typeId: typeId)
    result.targets.add PtrTarget(code: code, famKey: key, objAddr: objAddr,
                                 seqIdx: true, idx: idx)
  # RFC-0005 S8bn (item 4): a value of a `Table[string, V]` held in a field
  # family, at the pointer's key: present in the object's input table, and
  # only while the path has not changed which keys are present there.
  tabFamKeys.sort()
  for key in tabFamKeys:
    let arrSort = sortOfRaw(ctx, p.heaps[key].raw)
    let objSort = ctx.checkErr Z3_get_array_sort_domain(ctx.raw, arrSort)
    let ok = ptrObjKey(typeId, key)
    if not p.heaps.hasKey(ok):
      let mapSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, objSort)
      let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & ok).cstring)
      p.heaps[ok] = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                                                 mapSort))
    let objAddr = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[ok].raw,
                                                    ptrAst.raw))
    var inPresent: Z3AnyAst
    var moved = false
    for leaf in ["__@present", "__@len"]:
      let lk = key & leaf
      let leafSort =
        if p.heaps.hasKey(lk): sortOfRaw(ctx, p.heaps[lk].raw)
        else: ctx.checkErr Z3_mk_array_sort(ctx.raw, objSort,
          (if leaf == "__@len": ctx.checkErr Z3_mk_int_sort(ctx.raw)
           else: ctx.checkErr Z3_mk_array_sort(ctx.raw,
                   ctx.checkErr Z3_mk_string_sort(ctx.raw),
                   ctx.checkErr Z3_mk_bool_sort(ctx.raw))))
      let lsym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & lk).cstring)
      let inArr = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, lsym,
                                                               leafSort))
      let inVal = wrap[Z3AnyAst](ctx, checkedSelect(ctx, inArr.raw, objAddr.raw))
      if leaf == "__@present": inPresent = inVal
      if p.heaps.hasKey(lk):
        let curVal = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[lk].raw,
                                                       objAddr.raw))
        if not sameTerm(ctx, w, p, curVal, inVal): moved = true
        if leaf == "__@present" and not tabNoDeletion(ctx, p.heaps[lk]):
          moved = true
    if moved:
      result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
        "address a value of a table held in a heap cell (`" & key & "`) " &
        "whose keys this path changed: its entries may have moved, so the " &
        "pointer may dangle -- not modelled (RFC-0005 S8bn; feUnsupportedOp)"
      return
    var oid = ""
    for tid, srt in currentRefSorts:
      if srt == objSort: oid = tid
    if oid.len > 0:
      template neq3(a, b: Z3AnyAst): Z3Bool =
        not wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, b.raw))
      if currentNilConsts.hasKey(oid):
        p.pc.add neq3(objAddr, currentNilConsts[oid])
      for r in p.liveRefs.getOrDefault(oid, @[]):
        p.pc.add neq3(objAddr, r)
      let pk = ptrPreKey(oid)
      var seen = false
      for r in p.liveRefs.getOrDefault(pk, @[]):
        if r.raw == objAddr.raw: seen = true
      if not seen:
        if p.liveRefs.hasKey(pk): p.liveRefs[pk].add objAddr
        else: p.liveRefs[pk] = @[objAddr]
    let kt = ptrKeyAt(ctx, p, typeId, refSort, ptrAst)
    let tvt = heapKeyValTy(key)
    if heapTreeTy(tvt.tabValTy):
      # RFC-0005 S8bz (item 2): each part of the object's table value.
      var parts: seq[PtrLeaf]
      discard ptrElemLeaves(tvt.tabValTy, pointee, 0, parts)
      var missing = false
      for sfx in heapLeafSuffixes(tvt):
        if not p.heaps.hasKey(key & sfx): missing = true
      if missing:
        result.decline = "a `ptr " & $pointee & "` of unknown origin may " &
          "address a value of a table held in a heap cell (`" & key &
          "`), part of whose value this path holds no heap for -- not " &
          "modelled (RFC-0005 S8bz; feUnsupportedOp)"
        return
      for e in parts:
        let code = ptrTargetCode(key & "/#" & ptrLeafPathStr(e.steps, false))
        idxFacts.add (code, wrap[Z3Bool](ctx, checkedSelect(ctx, inPresent.raw,
                                                            kt.raw)))
        ptrLeafAims[code] = PtrLeafAim(fam: key, tabKey: true, typeId: typeId,
                                       elemSteps: e.steps)
        var t = PtrTarget(code: code, famKey: key, objAddr: objAddr,
                          tabKey: true, idx: kt, aggregate: true,
                          elemPath: e.path, famElemTy: tvt)
        (t.hasArm, t.armCond) = svPathArmCond(
          tabValAt(ctx, ptrFamSeq(ctx, p, t), kt.raw), e.path)
        result.targets.add t
      continue
    let code = ptrTargetCode(key & "/#")
    idxFacts.add (code, wrap[Z3Bool](ctx, checkedSelect(ctx, inPresent.raw,
                                                         kt.raw)))
    ptrLeafAims[code] = PtrLeafAim(fam: key, tabKey: true, typeId: typeId)
    result.targets.add PtrTarget(code: code, famKey: key, objAddr: objAddr,
                                 tabKey: true, idx: kt)
  if result.targets.len == 0: return
  let sk = ptrSelKey(typeId)
  if not p.heaps.hasKey(sk):
    p.heaps[sk] = mkHeapArrayVar(ctx, refSort, tInt(64, signed = true),
                                 "heap_" & sk)
  result.sel = wrap[Z3AnyAst](ctx, checkedSelect(ctx, p.heaps[sk].raw,
                                                 ptrAst.raw))
  # RFC-0005 S8bn (item 4): a seq element target's index is within the
  # seq's input length.
  for f in idxFacts:
    let s = sortOfRaw(ctx, result.sel.raw)
    let isT = wrap[Z3Bool](ctx, checkedEq(ctx, result.sel.raw,
      wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_int64(ctx.raw, f.code, s)).raw))
    p.pc.add((not isT) or f.inRange)

proc ptrSelIs(ctx: Z3Context; sel: Z3AnyAst; code: int64): Z3Bool =
  ## RFC-0005 S8bh. `sel == code`.
  let s = sortOfRaw(ctx, sel.raw)
  wrap[Z3Bool](ctx, checkedEq(ctx, sel.raw,
                              ctx.checkErr Z3_mk_int64(ctx.raw, code, s)))

proc ptrIteSV(ctx: Z3Context; cond: Z3Bool; t, e: SymVal): SymVal =
  ## RFC-0005 S8bn (item 2). `iteSV` over a pointer's candidate values: a
  ## string target (a `ptr string` aimed at a string global or `var`
  ## parameter) merges as one Z3 `ite` over the String sort, where `iteSV`
  ## havocs every string merge (an index fold's hazard, not this one's: the
  ## candidates here are whole values under disjoint `sel` guards).
  if t.kind == svString and e.kind == svString:
    return SymVal(kind: svString, str: wrap[Z3String](ctx,
      checkedIte(ctx, cond.raw, t.str.raw, e.str.raw)))
  iteSV(cond, t, e)

proc elemTermIn(ctx: Z3Context; val: SymVal; arr: Z3AnyAst): RawZ3Ast =
  ## RFC-0005 batch 6 (S8bn item 4 on S8ax). `val` as a term of the element
  ## sort of the data array `arr`. A seq's or table's data holds a signed
  ## `int` element as a bit-vector in a by-value variable and as an Int in
  ## a heap field family (`heapLeafRaw`, S8ax), while a `ptr int` heap is
  ## Int-sorted (`intHeapCell`): the store through a pointer must meet the
  ## array's own sort (it was an ill-sorted store, a walker fault).
  let rng = ctx.checkErr Z3_get_array_sort_range(ctx.raw, sortOfRaw(ctx, arr.raw))
  let intS = ctx.checkErr Z3_mk_int_sort(ctx.raw)
  if rng == intS:
    if val.kind in {svBV8, svBV16, svBV32, svBV64}:
      return toSvIntPreserving(val).zi.raw
    return rawAnyAstOf(val)
  if val.kind == svInt:
    case int(Z3_get_bv_sort_size(ctx.raw, rng))
    of 8:  return intToBv[8](val.zi, Z3BitVec[8]).raw
    of 16: return intToBv[16](val.zi, Z3BitVec[16]).raw
    of 32: return intToBv[32](val.zi, Z3BitVec[32]).raw
    else:  return intToBv[64](val.zi, Z3BitVec[64]).raw
  rawAnyAstOf(val)

proc elemValueOf(ctx: Z3Context; raw: RawZ3Ast; pointee: IRType): SymVal =
  ## RFC-0005 batch 6. An element read from a seq's or table's data array
  ## (either sort, see `elemTermIn`) as the value a `ptr pointee` read
  ## yields: in the pointee heap's own sort, so it merges with the other
  ## candidates and the pointer's own cell.
  let intS = ctx.checkErr Z3_mk_int_sort(ctx.raw)
  let v =
    if pointee.kind == itInt and ctx.checkErr(Z3_get_sort(ctx.raw, raw)) == intS:
      SymVal(kind: svInt, zi: wrap[Z3Int](ctx, raw), ziWidth: pointee.width,
             ziSigned: pointee.signed)
    elif pointee.kind == itInt:
      case pointee.width
      of 8:  liftBV(wrap[Z3BitVec[8]](ctx, raw), pointee.signed)
      of 16: liftBV(wrap[Z3BitVec[16]](ctx, raw), pointee.signed)
      of 32: liftBV(wrap[Z3BitVec[32]](ctx, raw), pointee.signed)
      else:  liftBV(wrap[Z3BitVec[64]](ctx, raw), pointee.signed)
    else: liftHeapValue(ctx, raw, pointee)
  heapStoreValue(v, v, pointee)

proc tabValueOf(ctx: Z3Context; raw: RawZ3Ast; pointee: IRType): SymVal =
  ## RFC-0005 batch 6 (S8bw item 3 on S8ax). A table value a `ptr pointee`
  ## reads: through its 64-bit cell (`ptrTabCellRead`), which a heap field
  ## family holds as an Int (`elemTermIn`); a 64-bit integer's cell is the
  ## value (`elemValueOf`).
  ## RFC-0005 S8bz (item 2): a string or float value is a term of its sort.
  case pointee.kind
  of itString: return SymVal(kind: svString, str: wrap[Z3String](ctx, raw))
  of itFloat32: return SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, raw))
  of itFloat64: return SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, raw))
  else: discard
  if pointee.kind == itInt and pointee.width == 64:
    return elemValueOf(ctx, raw, pointee)
  var cell = raw
  if ctx.checkErr(Z3_get_sort(ctx.raw, raw)) == ctx.checkErr(Z3_mk_int_sort(ctx.raw)):
    cell = ctx.checkErr Z3_mk_int2bv(ctx.raw, 64, raw)
  let v = ptrTabCellRead(ctx, cell, pointee)
  heapStoreValue(v, v, pointee)

proc tabTermIn(ctx: Z3Context; val: SymVal; pointee: IRType;
               arr: Z3AnyAst): RawZ3Ast =
  ## RFC-0005 batch 6. `tabValueOf`'s inverse: `val`'s 64-bit cell
  ## (`cellOf`), in the sort of the table's data array `arr`.
  ## RFC-0005 S8bz (item 2): a string or float value is a term of its sort.
  if pointee.kind in {itString, itFloat32, itFloat64}: return rawAnyAstOf(val)
  if pointee.kind == itInt and pointee.width == 64:
    return elemTermIn(ctx, val, arr)
  let c = cellOf(val, pointee)
  if c.isNone: return elemTermIn(ctx, val, arr)
  elemTermIn(ctx, SymVal(kind: svBV64, signed: true, bv64: c.get), arr)

proc ptrAggregateMsg(pointee: IRType): string =
  ## RFC-0005 S8bz (item 1). A store through a pointer whose target's element
  ## the value does not fit (`seqStoreArrs` none).
  "a `ptr " & $pointee & "` store into an aggregate element or table value " &
    "whose layout the value does not fit -- not modelled (RFC-0005 S8bz; " &
    "feUnsupportedOp)"

proc ptrStoredPart(ctx: Z3Context; c: SymVal; t: PtrTarget;
                   val: SymVal): Option[SymVal] =
  ## RFC-0005 S8bz (items 1, 2). The seq or table `c` with the part
  ## `t.elemPath` of the element or value at the target's index or key set to
  ## `val`. none when the value does not fit.
  if t.tabKey:
    let terms = tabValTerms(svWithPath(tabValAt(ctx, c, t.idx.raw), t.elemPath,
                                       val), c.tabValTy)
    if terms.isNone or terms.get.len != 1 + c.tabDataMore.len:
      return none(SymVal)
    var r = c
    r.tabDataRaw = wrap[Z3AnyAst](ctx, checkedStore(ctx, c.tabDataRaw.raw,
                                                    t.idx.raw, terms.get[0].raw))
    for i in 0 ..< c.tabDataMore.len:
      r.tabDataMore[i] = wrap[Z3AnyAst](ctx, checkedStore(ctx,
        c.tabDataMore[i].raw, t.idx.raw, terms.get[i + 1].raw))
    return some(r)
  let i = wrap[Z3Int](ctx, t.idx.raw)
  let arrs = seqStoreArrs(c, i, svWithPath(seqElemAt(c, i), t.elemPath, val))
  if arrs.isNone: return none(SymVal)
  some(withSeqArrsOf(c, arrs.get))

proc ptrGuardedArrs(ctx: Z3Context; guard: Z3Bool; a, b: SymVal): SymVal =
  ## RFC-0005 S8bz (items 1, 2). `a` under `guard`, else `b`: two seqs or two
  ## tables, of one length and key set, data array by data array.
  template pick(x, y: Z3AnyAst): Z3AnyAst =
    wrap[Z3AnyAst](ctx, checkedIte(ctx, guard.raw, x.raw, y.raw))
  result = b
  if a.kind == svTable:
    result.tabDataRaw = pick(a.tabDataRaw, b.tabDataRaw)
    for i in 0 ..< a.tabDataMore.len:
      result.tabDataMore[i] = pick(a.tabDataMore[i], b.tabDataMore[i])
  else:
    let xs = seqArrs(a)
    let ys = seqArrs(b)
    var merged: seq[Z3AnyAst]
    for i in 0 ..< xs.len: merged.add pick(xs[i], ys[i])
    result = withSeqArrsOf(b, merged)

proc ptrInactiveMsg(pointee: IRType): string =
  "a `ptr " & $pointee & "` may address a field of a case object's " &
    "branch that is not the active one: Nim's dereference reads or " &
    "writes whatever the active branch holds at that address, which this " &
    "model lays out only for a same-size scalar at one offset; or a " &
    "location this path first held after a store through a pointer that may " &
    "address it, which that store did not reach -- not modelled (RFC-0005 " &
    "S8bw, S8bz; feUnsupportedOp)"

proc ptrMissedBy(p: Path; typeId: string; code: int64): seq[int] =
  ## RFC-0005 S8bz. The stores through a pointer on this path, at `typeId`,
  ## that have not reached the candidate `code`: `ptrTargets` lists what the
  ## path holds so far, so a location it holds later missed them.
  for i, st in p.ptrStores:
    if st.typeId == typeId and code notin st.reached: result.add i

proc ptrApplyMissed(ctx: Z3Context; p: Path; typeId: string;
                    targets: seq[PtrTarget]) =
  ## RFC-0005 S8bz. A scalar field family the path holds only now: every read
  ## and write of it came after the earlier stores, so the location each last
  ## store names holds that value in the family's initial constant. Without
  ## this a dereference naming it was a false `sxSat`
  ## (`p[] = 1; h.n = 4; if p[] != 1 and p[] != 4`).
  for t in targets:
    if t.famKey.len == 0 or t.seqIdx or t.tabKey or t.aggregate or t.hasArm:
      continue
    let missed = ptrMissedBy(p, typeId, t.code)
    if missed.len == 0: continue
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
                                               ("heap_" & t.famKey).cstring)
    let init = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym,
                                     sortOfRaw(ctx, p.heaps[t.famKey].raw)))
    var named: seq[tuple[hit: Z3Bool; obj: Z3AnyAst]]
    for i in missed:
      let st = p.ptrStores[i]
      let selE = wrap[Z3AnyAst](ctx, checkedSelect(ctx,
        p.heaps[ptrSelKey(typeId)].raw, st.ptrAst.raw))
      named.add((ptrSelIs(ctx, selE, t.code), wrap[Z3AnyAst](ctx, checkedSelect(
        ctx, p.heaps[ptrObjKey(typeId, t.famKey)].raw, st.ptrAst.raw))))
      p.ptrStores[i].reached.add t.code
    for a, i in missed:
      var last = named[a].hit
      for b in a + 1 .. named.high:
        last = last and not (named[b].hit and wrap[Z3Bool](ctx, checkedEq(ctx,
          named[b].obj.raw, named[a].obj.raw)))
      let cell = wrap[Z3AnyAst](ctx, checkedSelect(ctx, init.raw,
                                                   named[a].obj.raw))
      p.pc.add (not last) or wrap[Z3Bool](ctx, checkedEq(ctx, cell.raw,
                                                         p.ptrStores[i].val.raw))

proc ptrInactive(ctx: Z3Context; p: Path; typeId: string; sel: Z3AnyAst;
                 targets: seq[PtrTarget]): Option[Z3Bool] =
  ## RFC-0005 S8bw (item 3). `sel` names a case object's branch field whose
  ## branch is not active: Nim's dereference reads (or writes) whatever the
  ## active branch holds there, which this model does not lay out. RFC-0005
  ## S8bz: or a candidate `ptrApplyMissed` could not give an earlier store, so
  ## its value here is not Nim's (a false `sxSat`).
  var c: Z3Bool
  var any = false
  template add(bad: Z3Bool) =
    c = if any: c or bad else: bad
    any = true
  for t in targets:
    for i in ptrMissedBy(p, typeId, t.code):
      let selE = wrap[Z3AnyAst](ctx, checkedSelect(ctx,
        p.heaps[ptrSelKey(typeId)].raw, p.ptrStores[i].ptrAst.raw))
      add(ptrSelIs(ctx, sel, t.code) and ptrSelIs(ctx, selE, t.code))
    if not t.hasArm: continue
    # RFC-0005 S8bz (item 6): an inactive branch's overlapping field reads
    # the active field's bytes (`ptrOverlapRead`).
    var known = t.armCond
    for ov in t.overlaps: known = known or (ov.cond and not ov.nan)
    add(ptrSelIs(ctx, sel, t.code) and not known)
  if any: some(c) else: none(Z3Bool)

proc ptrOverlapPart(ctx: Z3Context; p: Path; t: PtrTarget; ov: PtrOverlap): SymVal =
  ## RFC-0005 S8bz (item 6). The active field `ov` of the target's case object.
  if ov.famKey.len > 0:
    let arr = if p.heaps.hasKey(ov.famKey): p.heaps[ov.famKey]
              else: mkHeapArrayVar(ctx, sortOfRaw(ctx, t.objAddr.raw), ov.ty,
                                   "heap_" & ov.famKey)
    return heapSelect(ctx, arr, t.objAddr, ov.ty)
  if t.aggregate:
    let cont =
      if t.famKey.len > 0: ptrFamSeq(ctx, p, t)
      else: svAtPath(p.env[t.envName], t.path)
    let elem =
      if t.tabKey: tabValAt(ctx, cont, t.idx.raw)
      else: seqElemAt(cont, wrap[Z3Int](ctx, t.idx.raw))
    return svAtPath(elem, t.elemPath[0 .. ^2] & @[ov.step])
  svAtPath(p.env[t.envName], t.path[0 .. ^2] & @[ov.step])

proc ptrOverlapWrite(ctx: Z3Context; p: Path; t: PtrTarget; ov: PtrOverlap;
                     guard: Z3Bool; val: SymVal): bool =
  ## RFC-0005 S8bz (item 6). `val`'s bytes into the active field `ov` of the
  ## target's case object, under `guard`. False when they do not fit.
  let g = guard and ov.cond
  let old = ptrOverlapPart(ctx, p, t, ov)
  let bytes = ptrReinterpret(ctx, val, old)
  if ov.famKey.len > 0:
    let arr = if p.heaps.hasKey(ov.famKey): p.heaps[ov.famKey]
              else: mkHeapArrayVar(ctx, sortOfRaw(ctx, t.objAddr.raw), ov.ty,
                                   "heap_" & ov.famKey)
    let stored = checkedStore(ctx, arr.raw, t.objAddr.raw, rawAnyAstOf(bytes))
    p.heaps[ov.famKey] = wrap[Z3AnyAst](ctx, checkedIte(ctx, g.raw, stored, arr.raw))
    return true
  if t.aggregate:
    var alt = t
    alt.elemPath = t.elemPath[0 .. ^2] & @[ov.step]
    if t.famKey.len > 0:
      let sq = ptrFamSeq(ctx, p, t)
      let neu = ptrStoredPart(ctx, sq, alt, bytes)
      if neu.isNone: return false
      let merged = ptrGuardedArrs(ctx, g, neu.get, sq)
      let oldLeaves = svLeafAsts(sq, t.famElemTy)
      let leaves = svLeafAsts(merged, t.famElemTy)
      for li, sfx in heapLeafSuffixes(t.famElemTy):
        if leaves[li] == oldLeaves[li]: continue
        p.heaps[t.famKey & sfx] = wrap[Z3AnyAst](ctx, checkedStore(ctx,
          p.heaps[t.famKey & sfx].raw, t.objAddr.raw, leaves[li]))
      return true
    let root = p.env[t.envName]
    let sq = svAtPath(root, t.path)
    let neu = ptrStoredPart(ctx, sq, alt, bytes)
    if neu.isNone: return false
    p.env[t.envName] = svWithPath(root, t.path, ptrGuardedArrs(ctx, g, neu.get, sq))
    return true
  let root = p.env[t.envName]
  let path = t.path[0 .. ^2] & @[ov.step]
  p.env[t.envName] = svWithPath(root, path,
    ptrIteSV(ctx, g, bytes, svAtPath(root, path)))
  true

proc ptrTargetRead(ctx: Z3Context; w: var WalkCtx; p: Path; ptrAst: Z3AnyAst;
                   pointee: IRType; refSort: RawZ3Sort; typeId: string;
                   own: SymVal): tuple[val: SymVal; decline: string;
                                       inactive: Option[Z3Bool];
                                       written: SymVal;
                                       unwritten: Option[Z3Bool];
                                       part: string] =
  ## RFC-0005 S8bh. `P[]` over the candidate targets: `own` (the own cell's
  ## value) unless `sel(P)` names a candidate. RFC-0005 S8bw (item 3):
  ## `inactive`, when some candidate is a case object's branch field, holds
  ## when `sel(P)` names one whose branch is not active.
  ## RFC-0005 S8bz (item 4): `unwritten` holds when `sel(P)` names a target
  ## holding a part no write reached (`part` names one), and `written` is the
  ## value on every other execution: only that sub-path observes the part.
  result.val = own
  result.written = own
  let tg = ptrTargets(ctx, w, p, ptrAst, pointee, refSort, typeId)
  if tg.decline.len > 0:
    result.decline = tg.decline
    return
  ptrApplyMissed(ctx, p, typeId, tg.targets)
  result.inactive = ptrInactive(ctx, p, typeId, tg.sel, tg.targets)
  for i in countdown(tg.targets.high, 0):
    let t = tg.targets[i]
    let tv =
      if t.aggregate and t.famKey.len > 0 and t.tabKey:
        svAtPath(tabValAt(ctx, ptrFamSeq(ctx, p, t), t.idx.raw),
                 t.elemPath)   # RFC-0005 S8bz (item 2)
      elif t.aggregate and t.famKey.len > 0:
        svAtPath(seqElemAt(ptrFamSeq(ctx, p, t), wrap[Z3Int](ctx, t.idx.raw)),
                 t.elemPath)   # RFC-0005 S8bz (item 1)
      elif t.aggregate and t.seqIdx:
        svAtPath(seqElemAt(svAtPath(p.env[t.envName], t.path),
                           wrap[Z3Int](ctx, t.idx.raw)),
                 t.elemPath)   # RFC-0005 S8bz (item 1)
      elif t.aggregate:
        svAtPath(tabValAt(ctx, svAtPath(p.env[t.envName], t.path), t.idx.raw),
                 t.elemPath)   # RFC-0005 S8bz (item 2)
      elif t.famKey.len > 0 and (t.seqIdx or t.tabKey):
        # RFC-0005 S8bn (item 4): the element of the object's seq, or the
        # value of its table at the pointer's key.
        let data = wrap[Z3AnyAst](ctx, checkedSelect(ctx,
          p.heaps[t.famKey].raw, t.objAddr.raw))
        if t.tabKey:   # RFC-0005 S8bw: through its 64-bit cell
          tabValueOf(ctx, checkedSelect(ctx, data.raw, t.idx.raw), pointee)
        else:
          elemValueOf(ctx, checkedSelect(ctx, data.raw, t.idx.raw), pointee)
      elif t.famKey.len > 0: heapSelect(ctx, p.heaps[t.famKey], t.objAddr, pointee)
      elif t.seqIdx:
        let sq = svAtPath(p.env[t.envName], t.path)
        elemValueOf(ctx, checkedSelect(ctx, sq.seqDataRaw.raw, t.idx.raw),
                    pointee)
      elif t.tabKey:
        let tb = svAtPath(p.env[t.envName], t.path)
        tabValueOf(ctx, checkedSelect(ctx, tb.tabDataRaw.raw, t.idx.raw),
                   pointee)   # RFC-0005 S8bw: through its 64-bit cell
      else: svAtPath(p.env[t.envName], t.path)
    # RFC-0005 S8bz (item 6): while another branch is active, its bytes.
    var tvv = tv
    for ov in t.overlaps:
      tvv = ptrIteSV(ctx, ov.cond,
                     ptrReinterpret(ctx, ptrOverlapPart(ctx, p, t, ov), tv), tvv)
    let tvFinal = tvv
    let isT = ptrSelIs(ctx, tg.sel, t.code)
    result.val = ptrIteSV(ctx, isT, tvFinal, result.val)
    let part = unwrittenIn(tvFinal)
    if part.len > 0:
      result.part = part
      result.unwritten = some(if result.unwritten.isSome:
                                result.unwritten.get or isT
                              else: isT)
    else:
      result.written = ptrIteSV(ctx, isT, tvFinal, result.written)

proc ptrTargetWrite(ctx: Z3Context; w: var WalkCtx; p: Path; ptrAst: Z3AnyAst;
                    pointee: IRType; refSort: RawZ3Sort; typeId: string;
                    val: SymVal; inactive: var Option[Z3Bool]): string =
  ## RFC-0005 S8bh. `P[] = val` into each candidate target under its `sel`
  ## guard (the own cell's store is the caller's). The decline message, or
  ## "". RFC-0005 S8bw (item 3): `inactive` as `ptrTargetRead`'s.
  let tg = ptrTargets(ctx, w, p, ptrAst, pointee, refSort, typeId)
  if tg.decline.len > 0: return tg.decline
  # RFC-0005 batch 4: a field family's value in the heap's sort
  # (`heapStoreValue`). `ptrTargets` keeps only families of
  # `heapValueSort(pointee)`, which is the Int sort for a signed `int` heap
  # under S8ax (`intHeapCell`); the operand may be a bit-vector.
  var scratch: seq[Z3Bool]
  let proto = allocateSym(pointee, "__ptrTargetStoreProto", scratch)
  let famVal = heapStoreValue(val, proto, pointee)
  ptrApplyMissed(ctx, p, typeId, tg.targets)
  inactive = ptrInactive(ctx, p, typeId, tg.sel, tg.targets)
  # RFC-0005 S8bz: for the candidates a later dereference finds. Only a store
  # of the family heaps' sort can be applied there (`ptrApplyMissed`).
  var logged = PtrStore(typeId: typeId, ptrAst: ptrAst,
                        val: wrap[Z3AnyAst](ctx, rawAnyAstOf(famVal)))
  for t in tg.targets: logged.reached.add t.code
  p.ptrStores.add logged
  for t in tg.targets:
    let guard = ptrSelIs(ctx, tg.sel, t.code)
    # RFC-0005 S8bz (item 6): while another branch is active, its bytes.
    for ov in t.overlaps:
      if not ptrOverlapWrite(ctx, p, t, ov, guard, val):
        return ptrAggregateMsg(pointee)
    if t.aggregate and t.famKey.len > 0:
      # RFC-0005 S8bz (item 1): the part of the object's element, in each
      # leaf heap under the guard.
      let sq = ptrFamSeq(ctx, p, t)
      let neu = ptrStoredPart(ctx, sq, t, val)
      if neu.isNone: return ptrAggregateMsg(pointee)
      let old = svLeafAsts(sq, t.famElemTy)
      let leaves = svLeafAsts(neu.get, t.famElemTy)
      for li, sfx in heapLeafSuffixes(t.famElemTy):
        if leaves[li] == old[li]: continue
        let arr = p.heaps[t.famKey & sfx]
        let stored = wrap[Z3AnyAst](ctx, checkedStore(ctx, arr.raw,
                                                      t.objAddr.raw, leaves[li]))
        p.heaps[t.famKey & sfx] = wrap[Z3AnyAst](ctx, checkedIte(ctx, guard.raw,
                                                  stored.raw, arr.raw))
    elif t.aggregate:
      # RFC-0005 S8bz (items 1, 2): the part of the element or value, in each
      # leaf's array under the guard.
      let root = p.env[t.envName]
      let sq = svAtPath(root, t.path)
      let neu = ptrStoredPart(ctx, sq, t, val)
      if neu.isNone: return ptrAggregateMsg(pointee)
      p.env[t.envName] = svWithPath(root, t.path,
                                    ptrGuardedArrs(ctx, guard, neu.get, sq))
    elif t.famKey.len > 0 and (t.seqIdx or t.tabKey):
      # RFC-0005 S8bn (item 4): the element of the object's seq, or the
      # value of its table at the pointer's key.
      let arr = p.heaps[t.famKey]
      let data = wrap[Z3AnyAst](ctx, checkedSelect(ctx, arr.raw, t.objAddr.raw))
      let data2 = wrap[Z3AnyAst](ctx, checkedStore(ctx, data.raw, t.idx.raw,
        if t.tabKey: tabTermIn(ctx, val, pointee, data)   # RFC-0005 S8bw
        else: elemTermIn(ctx, val, data)))
      let stored = wrap[Z3AnyAst](ctx, checkedStore(ctx, arr.raw,
                                                    t.objAddr.raw, data2.raw))
      p.heaps[t.famKey] = wrap[Z3AnyAst](ctx, checkedIte(ctx, guard.raw,
                                                          stored.raw, arr.raw))
    elif t.seqIdx:
      let root = p.env[t.envName]
      var sq = svAtPath(root, t.path)
      let data2 = wrap[Z3AnyAst](ctx, checkedStore(ctx, sq.seqDataRaw.raw,
                                                   t.idx.raw,
                                                   elemTermIn(ctx, val, sq.seqDataRaw)))
      sq.seqDataRaw = wrap[Z3AnyAst](ctx, checkedIte(ctx, guard.raw, data2.raw, # [placeholder-audited]
                                                     sq.seqDataRaw.raw)) # [placeholder-audited]
      p.env[t.envName] = svWithPath(root, t.path, sq)
    elif t.tabKey:
      let root = p.env[t.envName]
      var tb = svAtPath(root, t.path)
      let data2 = wrap[Z3AnyAst](ctx, checkedStore(ctx, tb.tabDataRaw.raw,
                                                   t.idx.raw,
        tabTermIn(ctx, val, pointee, tb.tabDataRaw)))   # RFC-0005 S8bw
      tb.tabDataRaw = wrap[Z3AnyAst](ctx, checkedIte(ctx, guard.raw, data2.raw,
                                                     tb.tabDataRaw.raw))
      p.env[t.envName] = svWithPath(root, t.path, tb)
    elif t.path.len > 0:
      let root = p.env[t.envName]
      p.env[t.envName] = svWithPath(root, t.path,
        ptrIteSV(ctx, guard, val, svAtPath(root, t.path)))
    elif t.famKey.len > 0:
      let arr = p.heaps[t.famKey]
      let stored = checkedStore(ctx, arr.raw, t.objAddr.raw, rawAnyAstOf(famVal))
      p.heaps[t.famKey] = wrap[Z3AnyAst](ctx, checkedIte(ctx, guard.raw,
                                                          stored, arr.raw))
    else:
      p.env[t.envName] = ptrIteSV(ctx, guard, val, p.env[t.envName])
  ""

proc ptrSelOwnAtAlloc(ctx: Z3Context; p: Path; pointee: IRType;
                      refSort: RawZ3Sort; typeId: string; newRef: Z3AnyAst) =
  ## RFC-0005 S8bh. A pointer the SUT allocates (`new`, `create`, an `addr`
  ## cell) is its own cell: `sel = 0` at its fresh address.
  if not ptrScalarPointee(pointee): return
  let sk = ptrSelKey(typeId)
  let arr = if p.heaps.hasKey(sk): p.heaps[sk]
            else: mkHeapArrayVar(ctx, refSort, tInt(64, signed = true),
                                 "heap_" & sk)
  let s = ctx.checkErr Z3_get_array_sort_range(ctx.raw, sortOfRaw(ctx, arr.raw))
  p.heaps[sk] = wrap[Z3AnyAst](ctx, checkedStore(ctx, arr.raw, newRef.raw,
                                                 ctx.checkErr Z3_mk_int64(ctx.raw, 0, s)))

proc heapArmDegrade(kind: SymexErrorKind; msg: string): Degrade =
  ## RFC-0005 S1. The `walkHeapArm` decline arms' funnel: records through
  ## `allocDegrade` (the lowering sink `loweringDegradeErrors` these sites
  ## have always used — the sink distinction survives; `w.degrade` would move
  ## them to the walk sink) AND returns the kind's `Degrade` token, which the
  ## caller hands to `degradeHeapArmForPath` for every surviving path. The
  ## pending lowering taint `allocDegrade` joins is deliberately left pending
  ## (drained by the next `drainPendingLowerEffects`, exactly as the old
  ## `loweringDidDegrade` flag was) so S1 moves no verdict.
  allocDegrade(kind, msg)
  Degrade(path: pathTaint(classOf(kind)))

proc degradeHeapArmForPath(p: Path, elemTy: IRType, retName,
                            placeholderTag: string; d: Degrade): Path =
  ## Round-6 mechanical-debt slice: the shared per-path FORK half of the
  ## `allocDegrade` + fresh `allocateSym` + env-rebind + `forkPathTainted`
  ## idiom `walkHeapArm`'s READ-side `refSV.kind`-mismatch/multi-variant-
  ## pointee decline arms repeat (deref read, arm-field read, ref-to-multi-
  ## variant field read — each independently converted off a raw raise at
  ## walker v113/v113). The caller has ALREADY recorded the degrade via
  ## `allocDegrade(kind, msg)` (RFC-0005 S1: via `heapArmDegrade`, whose
  ## returned token is `d`) at whatever granularity its own site calls
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
  forkPathTainted(p, p.pc, newEnv, d)

proc degradeHeapArmForPath(p: Path; d: Degrade): Path =
  ## WRITE-side sibling of the 4-arg overload above: a write statement has
  ## no `dRetName`/`dwRetName` to bind, so the shared shape degenerates to
  ## "taint this path and DROP the write" — the pre-write env/heap carries
  ## forward unchanged (mirrors `isUnsupported`'s own walk-arm idiom for an
  ## unmodeled statement). Same "caller already called `allocDegrade`"
  ## contract as the read-side overload (RFC-0005 S1: `d` is the token
  ## `heapArmDegrade` returned).
  forkPathTainted(p, p.pc, p.env, d)

# RFC-0005 S8at. `p[]` of a ref / ptr case object. ADR-0013 lays a REF case
# object out field by field -- the discriminator heap, a heap per plain
# field and one per arm field (`<id>__@<tag>__<field>`), the heaps `p.kind`,
# `p.f` and `new` read and write. `p[]` read and `p[] = v` wrote a separate,
# whole-pointee heap no field access sees: a store `p[] = V(kind: b)` left
# `p.kind` reading the old discriminator (a false `sxUnsat`), and the read
# was the S8ar decline. Both now go through the field heaps, in the
# by-value layout's part order (`heapParts`), so the value moved is the
# `svVariant` the field reads see. No FieldDefect: a whole copy reads no
# field by name.

proc refVariantSlots(ty: IRType): seq[tuple[key: string; ty, variantTy: IRType]] =
  ## RFC-0005 S8at. The ADR-0013 heap of each `heapParts(ty)` part of a ref
  ## case object, in that order, with the variant (axis view) its key's
  ## shape records (`isNew`'s zero slots use the same keys).
  let baseId = refPointeeTypeId(ty)
  case ty.kind
  of itVariant:
    result.add (variantDiscHeapKey(ty), ty.vDiscTy, ty)
    for i, f in ty.vPlainFieldTypes:
      result.add (fieldHeapKey(ty, ty.vPlainFieldNames[i]), f, IRType(nil))
    for arm in ty.vArms:
      for j, f in arm.fieldTypes:
        result.add (baseId & "__@" & $arm.tagOrdinal & "__" & arm.fieldNames[j],
                    f, ty)
  of itMultiVariant:
    let view0 = mvAxisView(ty, 0)
    for i, f in ty.mvPlainFieldTypes:
      result.add (fieldHeapKey(view0, ty.mvPlainFieldNames[i]), f, IRType(nil))
    for xi in 0 ..< ty.mvAxes.len:
      let view = mvAxisView(ty, xi)
      result.add (variantDiscHeapKey(view), view.vDiscTy, view)
      for arm in view.vArms:
        for j, f in arm.fieldTypes:
          result.add (baseId & "__@" & $arm.tagOrdinal & "__" & arm.fieldNames[j],
                      f, view)
  else: discard

proc refVariantWhole(ty: IRType): bool =
  ## RFC-0005 S8at. `p[]` of this pointee goes through the field heaps: a
  ## case object whose every part a cell holds (a part that is not keeps
  ## the stated decline of the read and the store).
  ty != nil and ty.kind in {itVariant, itMultiVariant} and heapCompoundTy(ty)

proc refVariantWholeRead(ctx: Z3Context; p: Path; refSort: RawZ3Sort;
                         refAst: Z3AnyAst; ty: IRType):
                         tuple[val: SymVal; cells: HeapCell; conds: seq[Z3Bool]] =
  ## RFC-0005 S8at. The case object at `refAst`: each part selected from its
  ## field heap, with the facts a field read of it asserts -- an input
  ## cell's well-formedness (`heapCellWfConds`), a scalar's declared range,
  ## each discriminator's legal domain.
  var parts: seq[SymVal]
  for s in refVariantSlots(ty):
    let cell = heapCellArrays(ctx, p, s.key, refSort, s.ty, s.variantTy)
    let v = heapCellSelect(ctx, cell, refAst, s.ty)
    parts.add v
    for c in cell: result.cells.add c
    result.conds.add heapCellWfConds(ctx, s.key, refSort, s.ty, refAst)
    result.conds.add rangeCondsIfNeeded(v, s.ty)
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(ty, "__refVariantWholeProto", scratchPC)
  result.val = svWithParts(proto, ty, parts)
  if result.val.kind == svVariant:
    let r = refVariantDiscRangeClause(ty, result.val.vDisc[])
    if r.isSome: result.conds.add r.get
  elif result.val.kind == svMultiVariant:
    for xi in 0 ..< ty.mvAxes.len:
      let r = refVariantDiscRangeClause(mvAxisView(ty, xi),
                                        result.val.mvAxes[xi].disc[])
      if r.isSome: result.conds.add r.get

proc refVariantWholeStore(ctx: Z3Context; p: Path; refSort: RawZ3Sort;
                          refAst: Z3AnyAst; ty: IRType; val: SymVal): HeapCell =
  ## RFC-0005 S8at. `val` stored at `refAst`, part by part into the field
  ## heaps. Precondition: `svFitsHeapTy(val, ty)`. An `int` part is stored
  ## in its heap's sort (`heapCellStore`, through `heapLeafRaw`).
  let parts = svPartsOf(val, ty)
  for i, s in refVariantSlots(ty):
    let cell = heapCellArrays(ctx, p, s.key, refSort, s.ty, s.variantTy)
    for c in heapCellStore(ctx, cell, refAst, parts[i], s.ty): result.add c

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
  ##   heapKeyShapes, SymexErrorInfo, hePtrFamily, sevHint,
  ##   SymexRefUnresolvedError,
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
    # ADR-0013: itVariant's discriminant, plain and arm fields are modelled
    # (Slices 1-3); an itMultiVariant's through its axis views (RFC-0005 S8l).
    if isField and stmt.dObjTy.kind == itMultiVariant:
      # RFC-0005 S8l (ADR-0013 D6, "Slice 4"). A field of a multi-variant
      # read through a ref is a field of ONE axis's view (`mvAxisView`): its
      # discriminator, an arm field (FieldDefect-forked against that axis's
      # discriminator alone, as Nim checks it), or a plain field. Until S8l
      # this was a recorded decline (`heRefVariantUnsupported`, N46
      # follow-up) -- every field access through an inline `ref MV`.
      let view = mvAxisView(stmt.dObjTy, mvAxisOfField(stmt.dObjTy, stmt.dField))
      return walkHeapArm(IRStmt(kind: isDeref, dRetName: stmt.dRetName,
                                dPtr: stmt.dPtr, dElemTy: stmt.dElemTy,
                                dPtrFamily: stmt.dPtrFamily, dField: stmt.dField,
                                dObjTy: view), paths, w)
    # For itVariant: classify the field — disc, plain, or arm-specific.
    let isVariantPointee = isField and stmt.dObjTy.kind == itVariant
    let isDiscDeref = isVariantPointee and stmt.dField == stmt.dObjTy.vDiscName
    # RFC-0005 S8bn (item 8): a run-type tag level (`@lvl<j>`) of a
    # case-object hierarchy is no arm's field.
    let isArmField = isVariantPointee and not isDiscDeref and
                     stmt.dField notin stmt.dObjTy.vPlainFieldNames and
                     not stmt.dField.startsWith("@lvl") and
                     not stmt.dField.startsWith("@pf_")   ## RFC-0005 S8bn
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
      let discHeapKey = variantDiscHeapKey(objTy)
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
        raise (ref SymexClassifiedDegradeError)(kind: weInternalWalkerFault,  # [raise-audited: verified-unreachable: dField is parser-resolved against objTy's real field names before this arm-scan runs; a Nim SUT with an undeclared field reference does not compile, so armHits.len==0 is degenerate IR only]
          msg: "arm-specific field `." & stmt.dField & "` is declared by no arm " &
               "of variant `" & $objTy & "` (degenerate IR — should not occur)")
      var survivors: seq[Path]
      for p0 in paths:
        if w.shouldStop: return survivors
        let step = heapStepOf(p0, stmt.dPtr)   ## RFC-0005 S8ar
        let (refSV, p) = lowerLeafInExpr(p0, stmt.dPtr)   ## RFC-0005 S8bw
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
            let d = heapArmDegrade(heUnresolvedRef,
              "arm-field deref of non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind))
            survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
              "__armFieldReadUnresolvedRef", d)
            continue
        # RFC-0005 S8bd: the budget bounds the depth of the chain the ref
        # was reached through (`heapChainDepth`), so it is read off the
        # lowered ref.
        if heapDepthExhausted(p, w, step, refAst): continue
        if refSV.kind == svPtr:
          let ptrHint = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
            msg: "witness involves unmanaged ptr")
          ptrFamilyHints.add ptrHint
          w.ptrFamilyHints.add ptrHint
          let routeWhy = ptrRouteDecline(p, refAst, $objTy)   # RFC-0005 S8cs
          if routeWhy.len > 0:
            survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
              "__ptrRouteRead", heapArmDegrade(feGlobalRouteUnproved, routeWhy))
            continue
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
                                      heapInputName(cp0, discHeapKey), objTy)
          # N42: drain any `allocateSym` degrade from the disc-heap value-sort
          # probe above into this path's own taint (SND-1) — see the main
          # (non-variant-field) `isDeref` arm's own N42 comment, above, for
          # the full rationale; the disc type is always a primitive ordinal
          # by variant-discriminant construction so this is a defensive no-op
          # in practice, kept for audit completeness (every `mkHeapArrayVar`
          # call site on this READ path gets the same treatment).
          let cpA = drainPendingLowerEffects(cp0)
          let discReal = heapSelect(ctx, discHeap, refAst, objTy.vDiscTy)
          # RFC-0016 PRC-07 (cpp): the arm a read is defined through is the
          # union's active member, not the discriminator's.
          let discSV = if fieldsUnchecked() and heapActiveTracked(objTy):
                         cellActive(ctx, cpA, objTy, refAst, discReal)
                       else: discReal
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
              raise (ref SymexClassifiedDegradeError)(kind: weInternalWalkerFault,  # [raise-audited: verified-unreachable: vDiscTy is always itInt (types.nim invariant) and liftHeapValue's itInt arm is width-exhaustive, so heapSelect can only yield svBV8/16/32/64 for a disc value -- this else is dead]
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
                  raise (ref SymexClassifiedDegradeError)(kind: weInternalWalkerFault,  # [raise-audited: verified-unreachable: Nim case syntax requires >=1 `of` branch before an optional `else`, so an else-only variant with zero non-else arms is not constructible from valid Nim -- degenerate IR only]
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
          let rangeOpt = refVariantDiscRangeClause(objTy, discReal)
          if rangeOpt.isSome:
            basePc = basePc & @[rangeOpt.get]
          # FieldDefect fork — Phase 16 D1a unconditional (same call shape as the
          # value-variant `isVariantField` arm); forked off the ranged base.
          if fieldsUnchecked():
            # RFC-0016 PRC-07: no `FieldDefect`; a union read outside the arm.
            # Ref variants: the field's bytes of the cell's union image,
            # exact where they are a value of it (a value variant's
            # `isVariantField` read); a read of a byte no write reached
            # taints the side (`imgReadDef`); the rest is declined on its
            # own path.
            var denv = cpA.env
            var scratch: seq[Z3Bool]
            denv[stmt.dRetName] = allocateSym(stmt.dElemTy,
              freshDegradeName("__declinedFieldRead"), scratch)
            var imageVal: Option[SymVal]
            var imageFacts: seq[Z3Bool]
            let gate = unionImageGate(objTy)
            if gate.isSome:
              var tags: seq[int]
              for hit in armHits: tags.add hit.tagOrd
              let tp = vl.accessPlace(gate.get, tags, stmt.dField)
              if tp.isSome:
                let n0 = cpA.pc.len
                let img = cellImage(ctx, cpA, objTy, refAst, gate.get)
                imageFacts = cpA.pc[n0 .. ^1]
                imageVal = bitsPlace(imgReadDef(img, tp.get.off - gate.get.unionOff,
                                                tp.get.size),
                                     tp.get, none((vl.Place, SymVal)))
            if imageVal.isSome:
              if guardLiteral(not inArmCond) != glFalse:
                var envX = cpA.env
                envX[stmt.dRetName] = imageVal.get
                var exact = forkPath(cpA, basePc & imageFacts & @[not inArmCond],
                                     envX)
                # simplified: an out-of-arm store rewrote the cell word, which
                # still mentions the unwritten bytes it overwrote
                let part = unwrittenIn(imageVal.get, simplified = true)
                if part.len > 0:
                  taintInPlace(exact, w.degrade(unwrittenKind(part),
                                                unwrittenMsg(part),
                                                ub = unwrittenUb(part)))
                survivors.add exact
            else:
              survivors.add inactiveFieldSide(forkPath(cpA, basePc, cpA.env),
                                              not inArmCond, denv, "", w)
          else:
            discard forkDefect(forkPath(cpA, basePc, cpA.env),
                               not inArmCond, "FieldDefect", none(string), w)
          if w.shouldStop: return survivors
          # In-arm continuation: assert inArmCond on the range-constrained base.
          var childPc = basePc & @[inArmCond]
          # Materialise each matching arm's field heap (D1 `__@<ord>__<field>`),
          # `select` the field value, and bind an ite-chain over the matching arms.
          var armHeaps: seq[(string, Z3AnyAst)]
          var armSelects: seq[(int, SymVal)]
          # RFC-0005 S8ap: a compound arm field is a leaf-split cell
          # (`heapCellArrays`), its input cell well-formed (`heapCellWfConds`).
          var armWf: seq[Z3Bool]
          for hit in armHits:
            let armHeapKey = baseId & "__@" & $hit.tagOrd & "__" & stmt.dField
            let refSort = allocRefSort(ctx, objTy)
            let armCell = heapCellArrays(ctx, cpA, armHeapKey, refSort,
                                         hit.fieldTy, objTy)
            for c in armCell: armHeaps.add (c.key, c.arr)
            armSelects.add (hit.tagOrd, heapCellSelect(ctx, armCell, refAst, hit.fieldTy))
            armWf.add heapCellWfConds(ctx, armHeapKey, refSort, hit.fieldTy, refAst)
          # Issue #163 review R3 (Part A). A ranged arm-specific field never
          # passed through `allocateSym`'s `itInt` arm either (the per-(arm,
          # field) heap array above is materialised lazily, right here, on
          # the first arm-field read) — mirror the `isDeref` (non-arm) sibling
          # a few hundred lines down (`bvRangeConds` on the freshly-selected
          # value when `hit.fieldTy.hasRange`). Asserted unconditionally per
          # arm-select, not gated on `inArmCond`: each `armHeapKey` is a
          # distinct array keyed on (objType, tagOrdinal, field), so bounding
          # one arm's projection can never over-constrain a sibling arm's
          # (different-array) value, and Nim's own declared range for that
          # field holds independent of which arm is currently active.
          # Review R11: routed through `rangeCondsIfNeeded`.
          for idx, hit in armHits:
            childPc = childPc & rangeCondsIfNeeded(armSelects[idx][1], hit.fieldTy)
          childPc = childPc & armWf
          # N42: second drain — covers a degrade from any arm-field heap just
          # materialised above (each iteration can independently degrade via
          # `allocateSym`; `loweringDidDegrade` is idempotent to drain once
          # after the loop, since nothing resets it between iterations).
          # RFC-0005 S6b: the arm fold runs BEFORE the drain, so a merge
          # degrade inside `iteSV` (a direct call, no `lower()` wrapper)
          # lands on this path too, not on whichever path lowers next.
          var bound = armSelects[armSelects.len - 1][1]
          for k in countdown(armSelects.len - 2, 0):
            bound = heapCellIte(ctx, discEq(int64(armSelects[k][0])),
                                armSelects[k][1], bound, stmt.dElemTy)
          let cpB = drainPendingLowerEffects(cpA)
          var newEnv = cpB.env
          stampHeapSteps(bound, step)   ## RFC-0005 S8ar
          newEnv[stmt.dRetName] = bound
          var child = forkPath(cpB, childPc, newEnv)
          child.heaps[discHeapKey] = discHeap
          for (hk, hh) in armHeaps:
            child.heaps[hk] = hh
          # RFC-0016 PRC-07 (ref variants): a field a discriminator store
          # re-read from indeterminate bytes taints the path that reads it.
          # simplified: a field an out-of-arm store re-read from the image
          # mentions the cell word it rewrote, whose overwritten bytes the
          # field's own extract does not reach
          let partIn = unwrittenIn(bound, simplified = true)
          if partIn.len > 0:
            taintInPlace(child, w.degrade(unwrittenKind(partIn),
                                          unwrittenMsg(partIn),
                                          ub = unwrittenUb(partIn)))
          survivors.add child
      return survivors
    let sortTy = if isField: stmt.dObjTy else: stmt.dElemTy
    let typeId = refPointeeTypeId(sortTy)
    # ADR-0013 D1: disc field uses the __@disc heap key (@ prefix is collision
    # guard — Nim identifiers cannot start with @). Plain/non-variant fields
    # keep the existing fieldHeapKey unchanged.
    let heapKey =
      if isDiscDeref: variantDiscHeapKey(stmt.dObjTy)
      elif isField:   fieldHeapKey(stmt.dObjTy, stmt.dField)
      else:           typeId
    var survivors: seq[Path]
    for p0 in paths:
      if w.shouldStop: return survivors
      # Phase 15 R9: bound recursive heap traversal. HALT this path (no
      # survivor → sxUnknown) if the deref's heap step reaches the effective
      # budget BEFORE the select. Per-path: a shallower path continues.
      # RFC-0005 S8ar: the step is the ref's distance from a root plus one,
      # not a count of the path's derefs.
      # RFC-0005 S8an: an `addr` cell's read-back is not a program
      # dereference; it does not count against the budget. Its value is
      # still stamped with the step (below), as any heap read's is.
      # (RFC-0005 S8bd: the check is made once the ref is lowered, below.)
      let step = heapStepOf(p0, stmt.dPtr)   ## RFC-0005 S8ar
      ## Drain-coverage audit: `stmt.dPtr` is always an env-resident var —
      ## the parser A-normalises so deref operands are named bindings (no
      ## complex expression as the ref/ptr operand). A violation here means
      ## the parser emitted a non-var deref operand and drains would be needed.
      let (refSV, p) = lowerLeafInExpr(p0, stmt.dPtr)   ## RFC-0005 S8bw
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
          let d = heapArmDegrade(heUnresolvedRef,
            "deref of non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind) &
            " (Cluster R R1 expects an svRef/svPtr at the deref site)")
          survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
            "__derefReadUnresolvedRef", d)
          continue
      # RFC-0005 S8bd: the budget bounds the depth of the chain the ref
      # was reached through (`heapChainDepth`), so it is read off the
      # lowered ref.
      if not stmt.dCell and heapDepthExhausted(p, w, step, refAst): continue
      # Phase 15 R8. An UNMANAGED `ptr T` deref routes through the SAME heap as
      # a `ref T` (the `of svPtr` arm above), but emits a non-halting
      # `hePtrFamily` hint so a consumer can distinguish unmanaged ptr from
      # managed ref in the finding. A `ref T` deref emits NOTHING.
      if refSV.kind == svPtr:
        let ptrHint = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
          msg: "witness involves unmanaged ptr")
        ptrFamilyHints.add ptrHint   # threadvar: fallback
        w.ptrFamilyHints.add ptrHint # CR-9 Stage 5: LIVE WalkCtx field
        # RFC-0005 S8cs: a scalar pointee or a field, a whole object: all of them.
        if not stmt.dCell:
          let routeWhy = ptrRouteDecline(p, refAst, $sortTy)
          if routeWhy.len > 0:
            survivors.add degradeHeapArmForPath(p, stmt.dElemTy, stmt.dRetName,
              "__ptrRouteRead", heapArmDegrade(feGlobalRouteUnproved, routeWhy))
            continue
      # Phase 15 R5: fork the nil path (the defect) off; continue on non-nil.
      # The nil-fork keys on the OBJECT ref sort (`sortTy`) so a field access
      # through a possibly-nil object ref forks correctly (R5 composition).
      # RFC-0005 S8ax: first, a `ptr` that may hold a dead frame's address
      # cell (`danglingFork`).
      var nilForks: seq[Path]
      for pd in (if refSV.kind == svPtr: danglingFork(p, refAst, w) else: @[p]):
        nilForks.add nilDerefFork(pd, refAst, sortTy, w)
      for cp0 in nilForks:
        if w.shouldStop: return survivors
        if not isField and refVariantWhole(stmt.dElemTy):
          # RFC-0005 S8at: `p[]` of a case object reads its field heaps
          # (`refVariantWholeRead`).
          let rd = refVariantWholeRead(ctx, cp0, allocRefSort(ctx, sortTy),
                                       refAst, stmt.dElemTy)
          let cpW = drainPendingLowerEffects(cp0)
          var envW = cpW.env
          var valW = rd.val
          stampHeapSteps(valW, step)
          envW[stmt.dRetName] = valW
          var childW = forkPath(cpW, cpW.pc & rd.conds, envW)
          for c in rd.cells: childW.heaps[c.key] = c.arr
          survivors.add childW
          continue
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
        # RFC-0005 S8ap: a compound field / pointee is a leaf-split cell
        # (`heapCellArrays`: one array per leaf, a scalar's single array
        # unchanged).
        let refSort = allocRefSort(ctx, sortTy)
        let cell = heapCellArrays(ctx, cp0, heapKey, refSort, stmt.dElemTy,
                                  (if isDiscDeref: stmt.dObjTy else: nil))
        let cp = drainPendingLowerEffects(cp0)   ## N42 per-path taint drain
        newEnv = cp.env
        var valSV = heapCellSelect(ctx, cell, refAst, stmt.dElemTy)
        stampHeapSteps(valSV, step)   ## RFC-0005 S8ar
        # N46-followup (walker v113): a SECOND drain, immediately after the
        # select — `liftHeapValue` (called from inside `heapSelect`) can now
        # degrade in-band (its own `else` arm, converted this slice) for a
        # pointee kind it does not lift (string/table/set/distinct/…). The
        # drain above (`cp`, before this select) only covers `mkHeapArrayVar`/
        # `heapValueSort`'s OWN degrade; this one covers a degrade from the
        # select's VALUE lift, the same "second drain" shape already used
        # below for the arm-field select loop (N42).
        var cp2 = drainPendingLowerEffects(cp)
        # RFC-0005 S8bh (item 2). A bare `p[]` through a `ptr` reads the
        # pointer's TARGET (`ptrTargetRead`): its own cell, or the field,
        # global or `var` parameter of type T it addresses. Not an `addr`
        # cell's read-back (`dCell`, the variable itself) nor a field deref
        # (`p.f`: the pointer addresses the object). The target's facts go
        # onto this statement's own fork.
        # RFC-0005 S8bz (item 1): a whole aggregate's pointer has no such
        # targets; it declines where it may address one.
        if refSV.kind == svPtr and not stmt.dCell:
          let aggMsg = ptrAggregateDecline(w, cp2, refAst,
            (if isField: stmt.dObjTy else: stmt.dElemTy), typeId)
          if aggMsg.len > 0:
            survivors.add degradeHeapArmForPath(cp2, stmt.dElemTy,
              stmt.dRetName, "__ptrTargetRead",
              w.degrade(feUnsupportedOp, aggMsg))
            continue
        if refSV.kind == svPtr and not isField and not stmt.dCell and
           ptrScalarPointee(stmt.dElemTy):
          cp2 = forkPath(cp2, cp2.pc, cp2.env)
          for c in cell: cp2.heaps[c.key] = c.arr
          let tr = ptrTargetRead(ctx, w, cp2, refAst, stmt.dElemTy, refSort,
                                 typeId, valSV)
          if tr.decline.len > 0:
            # RFC-0005 S8bz: the walk's own degrade, as below: this arm's
            # pending lowering taint leaked when no drain followed.
            survivors.add degradeHeapArmForPath(cp2, stmt.dElemTy,
              stmt.dRetName, "__ptrTargetRead",
              w.degrade(feUnsupportedOp, tr.decline))
            continue
          # RFC-0005 S8bw (item 3): the pointer may address a case object's
          # branch field whose branch is not active -- declined there.
          if tr.inactive.isSome:
            if not loopArmInfeasible(ctx, cp2, tr.inactive.get, w.settings):
              # The walk's own degrade (`w.degrade`): `heapArmDegrade`'s
              # pending lowering taint would reach this statement's in-arm
              # path too, at its next drain.
              survivors.add degradeHeapArmForPath(
                forkPath(cp2, cp2.pc & @[tr.inactive.get], cp2.env),
                stmt.dElemTy, stmt.dRetName, "__ptrTargetRead",
                w.degrade(feUnsupportedOp, ptrInactiveMsg(stmt.dElemTy)))
            cp2.pc.add not tr.inactive.get
          # RFC-0005 S8bw (item 2): a candidate target is a part of a
          # global no write has reached; reading it through the pointer
          # observes it, as a direct read does.
          # RFC-0005 batch 6: an S8as global's part is its entry value,
          # any of its type -- read on, the path tainted (`unwrittenKind`).
          # RFC-0005 S8bz (item 4): only the sub-path whose `sel` names such
          # a part is tainted; the rest read written memory.
          valSV = tr.written
          if tr.unwritten.isSome:
            if not loopArmInfeasible(ctx, cp2, tr.unwritten.get, w.settings):
              var hitEnv = newEnv
              hitEnv[stmt.dRetName] = tr.val
              let hit = forkPath(cp2, cp2.pc & @[tr.unwritten.get], hitEnv)
              taintInPlace(hit, w.degrade(unwrittenKind(tr.part),
                                          unwrittenMsg(tr.part),
                                          ub = unwrittenUb(tr.part)))
              survivors.add hit
            cp2.pc.add not tr.unwritten.get
          # The pointer's own cell may hold one (an `addr` actual's copy).
          let unwritten = unwrittenIn(valSV)
          if unwritten.len > 0 and unwrittenKind(unwritten) == feGlobalHavoc:
            taintInPlace(cp2, w.degrade(feGlobalHavoc, unwrittenMsg(unwritten),
                                        ub = unwrittenUb(unwritten)))
          elif unwritten.len > 0:
            survivors.add degradeHeapArmForPath(cp2, stmt.dElemTy,
              stmt.dRetName, "__ptrTargetRead",
              heapArmDegrade(feGlobalReadUnmodelled,
                             unwrittenReadMsg(unwritten)))
            continue
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
        # Issue #163 wiring-audit W4: a range-typed FIELD (or bare pointee)
        # of a `ref`/`ptr` object never passed through `allocateSym`'s
        # `itInt` arm either — `allocateSym(itRef/itPtr)`'s own comment
        # says no heap read happens at allocation, the per-path heap array
        # is materialised lazily right HERE, on the first deref. Assert the
        # declared bounds on the freshly-selected value, same as the
        # `isIndex`/svSeq arm (`runtime.nim`) does for a seq element — and
        # the same documented limitation applies: this bounds the address
        # actually dereffed on THIS path; a sibling address sharing the
        # same field-split heap that is never itself dereffed stays free
        # (`renderLeafFieldAt`'s witness-side clamp covers that case).
        # Review R11: routed through `rangeCondsIfNeeded` (defined in
        # runtime.nim, beside `bvRangeConds`; this file is `include`d there).
        childPc = childPc & rangeCondsIfNeeded(valSV, stmt.dElemTy)
        # RFC-0005 S8ap: the input cell of a compound / string value is one
        # Nim can hold (see `heapCellWfConds`).
        childPc = childPc & heapCellWfConds(ctx, heapKey, refSort, stmt.dElemTy,
                                            refAst)
        # Carry the (possibly freshly-materialised) heap forward on the surviving
        # path so a SECOND deref of the SAME ref reads the SAME array (a genuine
        # functional read — `p[] == 42 and p[] == 43` is unsat).
        var child = forkPath(cp2, childPc, newEnv)
        for c in cell: child.heaps[c.key] = c.arr
        survivors.add child
    survivors
  of isNew:
    if stmt.nAddrIdx != nil:
      return walkElemCell(stmt, paths, w)   # RFC-0005 S8be
    if stmt.nAddrField.len > 0:
      return walkFieldCell(stmt, paths, w)  # RFC-0005 S8bo
    if stmt.nAddrOf.len > 0:
      return walkAddrCell(stmt, paths, w)   # RFC-0005 S8ax
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
      # RFC-0005 S8bh (item 2). A fresh cell of a scalar / string pointee is
      # its own target (`sel = 0`): a pointer the SUT allocates, or makes
      # with `addr` (an `addr` cell is a `new`), never addresses a field, a
      # global or a `var` parameter.
      ptrSelOwnAtAlloc(ctx, child, pointee, refSort, typeId, newRef)
      # Cluster H Step C (ADR-0022): universal isNew zero-write. A fresh
      # field-split heap array is a FREE Z3 const (`mkHeapArrayVar`), so an
      # unwritten field `select` is UNCONSTRAINED — without this, `new Node`
      # then reading `p.next != nil` would be falsely SAT (Invariant-3
      # violation). Zero-write EVERY field of an OBJECT pointee (not just the
      # fields a `Node(...)` constructor happened to write — the P2b
      # construction arm's per-PRESENT-field `mkFieldDerefWrite`s then
      # overwrite the fields it actually set). A non-object pointee (a plain
      # `ref int`/`ref float`/… inline allocation) has no fields to split —
      # its whole cell is zero-written (RFC-0005 S8g, the `else` below).
      # RFC-0005 S8l: a VARIANT pointee is an object too (a named `ref object`
      # case type or a `ref VObj` alias now classifies to `itRef(itVariant)`,
      # and a ref-variant constructor lowers to this `isNew`). Nim zeroes the
      # whole cell: the discriminator reads ordinal 0 and every field -- plain
      # or of any arm -- reads its zero. Each lives in its own heap (ADR-0013
      # D1: `__@disc`, `<obj>__<plain>`, `__@<ord>__<armField>`); all are
      # zero-written. Before S8l a variant pointee never reached `isNew`. A
      # multi-variant pointee (`new(p)` on an inline `ref MV`) likewise.
      var zeroSlots: seq[tuple[fname, key: string; ty, variantTy: IRType]]
      # RFC-0005 S8at: an ANONYMOUS tuple pointee (`ref (int, int)`) is held
      # whole -- `p[]` and `p[0]` read the whole-pointee heap (the parser's
      # `wholeObjectPointee` is false: no names to split it by) -- so it is
      # zeroed there, below. The field loop zeroed `<id>__` (an empty field
      # name) for every element, a heap no read sees: `p[1] != 0` after
      # `new(p)` was a false `sxSat`.
      var anonTuple = false
      if pointee.kind == itTuple and not pointee.isPlaceholder:
        for fname in pointee.fieldNames:
          if fname.len == 0: anonTuple = true
      if pointee.kind == itTuple and not anonTuple:
        for i, fname in pointee.fieldNames:
          zeroSlots.add (fname, fieldHeapKey(pointee, fname), pointee.fields[i],
                         IRType(nil))
      elif pointee.kind in {itVariant, itMultiVariant}:
        # A multi-variant is the union of its axis views (`mvAxisView`): each
        # axis's discriminator and arm fields, and the plain fields once.
        var views: seq[IRType]
        if pointee.kind == itVariant: views.add pointee
        else:
          for ai in 0 ..< pointee.mvAxes.len: views.add mvAxisView(pointee, ai)
        let baseId = refPointeeTypeId(pointee)
        for vi, view in views:
          zeroSlots.add (view.vDiscName, variantDiscHeapKey(view), view.vDiscTy,
                         view)
          if vi == 0:
            for i, fname in view.vPlainFieldNames:
              zeroSlots.add (fname, fieldHeapKey(view, fname),
                             view.vPlainFieldTypes[i], IRType(nil))
          for arm in view.vArms:
            for i, fname in arm.fieldNames:
              zeroSlots.add (fname, baseId & "__@" & $arm.tagOrdinal & "__" & fname,
                             arm.fieldTypes[i], view)
      if hierChain(pointee).len > 0:
        # RFC-0005 S8bh (item 3). The run-type tag of a hierarchy object:
        # its ancestor's `inheritTagCode` at each depth `1..m` and the
        # sentinel 0 at depth `m + 1` (see `inheritTagKey`). Depth 0 is the
        # root, which every object of the hierarchy shares: no check reads it.
        # RFC-0005 S8bn (item 8): a case object's chain too (`hierChain`).
        let chain = hierChain(pointee)
        let depth = chain.len - 1
        for lvl in 1 .. depth + 1:
          let code = if lvl <= depth: inheritTagCode(chain[lvl])
                     else: 0'i64
          let key = inheritTagKey(pointee, lvl)
          let tagTy = tInt(64, signed = true)
          let fheap = if child.heaps.hasKey(key): child.heaps[key]
                      else: mkHeapArrayVar(ctx, refSort, tagTy, "heap_" & key)
          var scratchPC: seq[Z3Bool]
          let proto = allocateSym(tagTy, "__isNewTagProto", scratchPC)
          let (tagRaw, childAfter) = lowerInExpr(child, mkIntLit(code), w,
                                                 some(proto))
          # RFC-0005 batch 4: in the heap's value sort (`heapStoreValue`).
          # The tag heap is a signed `int` heap, Int-sorted under S8ax
          # (`intHeapCell`), and the down-conversion reads it back through
          # `liftHeapValue` as an Int; the bit-vector stored here was
          # ill-sorted against it.
          let tagSV = heapStoreValue(tagRaw, proto, tagTy)
          child = childAfter
          child.heaps[key] = wrap[Z3AnyAst](ctx, checkedStore(ctx, fheap.raw,
            newRef.raw, rawAnyAstOf(tagSV)))
      if pointee.kind in {itTuple, itVariant, itMultiVariant} and not anonTuple:
        for slot in zeroSlots:
          let fname = slot.fname
          let fty = slot.ty
          if heapCompoundTy(fty) and defaultZeroTotal(fty):
            # RFC-0005 S8at: a case object field too (its zero: ordinal 0 and
            # each field's zero; a type whose zero is no legal value keeps
            # the taint below).
            # RFC-0005 S8ap. A seq / Table / HashSet field is a leaf-split
            # cell; Nim zeroes it to the empty container (`defaultZero`), stored
            # into every leaf. It was the `heNewFieldZeroUnsupported` taint
            # below (`zeroIRExprForType` has no IR zero for a container), so
            # every `RNode(...)` with such a field ran on a tainted path.
            let cell = heapCellArrays(ctx, child, slot.key, refSort, fty,
                                      slot.variantTy)
            for c in heapCellStore(ctx, cell, newRef, heapCellZero(fty), fty):
              child.heaps[c.key] = c.arr
            continue
          if fty.kind == itUninterp and fty.uninterpName == "__closure" and
             slot.variantTy == nil:
            # RFC-0005 S8bn (item 6). A proc field is held as its shadow
            # code (`@pf_<f>`, `dsl_parser.procFieldCallIR`): `new` stores 0,
            # nil. The field's own cell is never written or read as a value
            # (a read of it allocates a proc value with no lambda, declined).
            let sk = fieldHeapKey(pointee, "@pf_" & fname)
            let tagTy = tInt(64, signed = true)
            let sheap = if child.heaps.hasKey(sk): child.heaps[sk]
                        else: mkHeapArrayVar(ctx, refSort, tagTy, "heap_" & sk)
            let zero = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_int64(ctx.raw, 0,
              ctx.checkErr Z3_get_array_sort_range(ctx.raw,
                                                   sortOfRaw(ctx, sheap.raw))))
            child.heaps[sk] = wrap[Z3AnyAst](ctx, checkedStore(ctx, sheap.raw,
              newRef.raw, zero.raw))
            continue
          let zeroExpr = zeroIRExprForType(fty)
          if zeroExpr == nil:
            # SND-1: no clean zero encoding for this field's type this cycle
            # (seq/table/set/array/variant/distinct/uninterp) — taint-and-
            # continue (mirrors the `isUnsupported` walk arm exactly) rather
            # than leaving the field's heap cell silently unconstrained.
            # RFC-0005 S1: the one mutation-shaped site — `child` is this
            # statement's own fresh fork, so the token is joined in place
            # (`taintInPlace`), not re-forked. `dsNewFieldZero` keeps the
            # threadvar + LIVE WalkCtx dual store.
            taintInPlace(child, w.degrade(heNewFieldZeroUnsupported,
              "new " & $stmt.nRefTy & ": field `" & fname &
                   "` of type " & $fty.kind & " has no clean zero-value " &
                   "encoding — isNew zero-write skipped for this field " &
                   "(SND-1 taint)", dsNewFieldZero))
            continue
          let fieldKey = slot.key
          var fheap: Z3AnyAst
          if child.heaps.hasKey(fieldKey):
            fheap = child.heaps[fieldKey]
          else:
            fheap = mkHeapArrayVar(ctx, refSort, fty,
                                   heapInputName(child, fieldKey),
                                   slot.variantTy)
          var scratchPC: seq[Z3Bool]
          let proto = allocateSym(fty, "__isNewZeroProto", scratchPC)
          let (valSVRaw, childAfter) = lowerInExpr(child, zeroExpr, w, some(proto))
          var valSV = valSVRaw
          # Reconcile svInt↔BV sort mismatch (same idiom as isDerefWrite):
          # a literal int/bool zero may lower to svInt (Z3Int) while the
          # field-split heap's value sort is BV — coerce via int2bv.
          valSV = heapStoreValue(valSV, proto, fty)   # RFC-0005 S8as
          let storedRaw = checkedStore(ctx, fheap.raw, newRef.raw, rawAnyAstOf(valSV))
          child = childAfter
          child.heaps[fieldKey] = wrap[Z3AnyAst](ctx, storedRaw)
        # RFC-0016 PRC-07 (ref variants): the cell's union image. `new` is
        # `nimNewObj`, zero; a constructor naming every field of its arm is
        # `nimNewObjUninit` (`nUninit`): every byte indeterminate until the
        # constructor's field writes reach it (generated C, pinned in
        # `tests/tsymex_0016_fieldref.nim`).
        if pointee.kind == itVariant:
          let gate = unionImageGate(pointee)
          if gate.isSome:
            imageStore(ctx, child, imageHeapCells(ctx, child, typeId, refSort, gate.get),
                       newRef, (if stmt.nUninit: unwrittenImage(gate.get)
                                else: zeroImage(gate.get)))
          # cpp: the fresh cell's active member is its discriminator's arm
          # (the constructor's initialising discriminator store included).
          if heapActiveTracked(pointee):
            storeActive(ctx, child, pointee, newRef, none(SymVal))
      else:
        # RFC-0005 S8g: a NON-object pointee (`new int`, `new bool`, ...) is
        # zero-initialised too (probe: `new int` reads 0, `new float` 0.0,
        # `new bool` false, `new string` ""). It was skipped ("no fields to
        # split"), so `p[]` read the whole-pointee heap cell (`typeId`, the
        # key `isDeref`/`isDerefWrite` use for a non-field access) at a fresh
        # address: a free value, and `p[] != 0` a false `sxSat`. Same store
        # as the field loop above, into the whole-pointee heap.
        # RFC-0005 S8ap: a compound pointee (`new seq[int]`) likewise, leaf
        # by leaf.
        let zeroExpr = zeroIRExprForType(pointee)
        if heapCompoundTy(pointee) and defaultZeroTotal(pointee):
          let cell = heapCellArrays(ctx, child, typeId, refSort, pointee)
          for c in heapCellStore(ctx, cell, newRef, heapCellZero(pointee), pointee):
            child.heaps[c.key] = c.arr
        elif zeroExpr == nil:
          # SND-1 twin of the field loop's decline: no clean zero encoding
          # for this pointee type -- the cell stays fresh, on a tainted path.
          taintInPlace(child, w.degrade(heNewFieldZeroUnsupported,
            "new " & $stmt.nRefTy & ": pointee of type " & $pointee.kind &
                 " has no clean zero-value encoding — isNew zero-write " &
                 "skipped (SND-1 taint)", dsNewFieldZero))
        else:
          var heap: Z3AnyAst
          if child.heaps.hasKey(typeId):
            heap = child.heaps[typeId]
          else:
            heap = mkHeapArrayVar(ctx, refSort, pointee,
                                  heapInputName(child, typeId))
          var scratchPC: seq[Z3Bool]
          let proto = allocateSym(pointee, "__isNewZeroProto", scratchPC)
          let (valSVRaw, childAfter) = lowerInExpr(child, zeroExpr, w, some(proto))
          var valSV = valSVRaw
          valSV = heapStoreValue(valSV, proto, pointee)   # RFC-0005 S8as
          let storedRaw = checkedStore(ctx, heap.raw, newRef.raw, rawAnyAstOf(valSV))
          child = childAfter
          child.heaps[typeId] = wrap[Z3AnyAst](ctx, storedRaw)
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
    # ADR-0013: itVariant's discriminant, plain and arm-field writes are
    # modelled (Slices 1-3); an itMultiVariant's through its axis views
    # (RFC-0005 S8l).
    if isField and stmt.dwObjTy.kind == itMultiVariant:
      # RFC-0005 S8l. The write-side sibling of the `isDeref` arm's view
      # dispatch: a discriminator write is checked against its own axis's
      # branches, an arm-field write against its own axis's discriminator.
      let view = mvAxisView(stmt.dwObjTy, mvAxisOfField(stmt.dwObjTy, stmt.dwField))
      return walkHeapArm(IRStmt(kind: isDerefWrite, dwPtr: stmt.dwPtr,
                                dwValue: stmt.dwValue, dwElemTy: stmt.dwElemTy,
                                dwPtrFamily: stmt.dwPtrFamily, dwField: stmt.dwField,
                                dwObjTy: view, dwInit: stmt.dwInit), paths, w)
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
      let discHeapKeyW = variantDiscHeapKey(objTy)
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
        raise (ref SymexClassifiedDegradeError)(kind: weInternalWalkerFault,  # [raise-audited: verified-unreachable: dwField is parser-resolved against objTy's real field names before this arm-scan runs; a Nim SUT with an undeclared field reference does not compile, so armHitsW.len==0 is degenerate IR only]
          msg: "arm-specific field write `." & stmt.dwField & "` declared by no arm " &
               "of variant `" & $objTy & "` (degenerate IR — should not occur)")
      var survivors: seq[Path]
      for p0 in paths:
        if w.shouldStop: return survivors
        let (refSV, p) = lowerLeafInExpr(p0, stmt.dwPtr)   ## RFC-0005 S8bw
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
            let d = heapArmDegrade(heUnresolvedRef,
              "arm-field deref-write of non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind))
            survivors.add degradeHeapArmForPath(p, d)
            continue
        # RFC-0005 S8bd: the budget bounds the depth of the chain the ref
        # was reached through (`heapChainDepth`), so it is read off the
        # lowered ref.
        if heapDepthExhausted(p, w, heapStepsOf(refSV) + 1, refAst): continue
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
                                      heapInputName(cp, discHeapKeyW), objTy)
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
              raise (ref SymexClassifiedDegradeError)(kind: weInternalWalkerFault,  # [raise-audited: verified-unreachable: vDiscTy is always itInt (types.nim invariant) and liftHeapValue's itInt arm is width-exhaustive, so heapSelect can only yield svBV8/16/32/64 for a disc value -- this else is dead]
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
                  raise (ref SymexClassifiedDegradeError)(kind: weInternalWalkerFault,  # [raise-audited: verified-unreachable: Nim case syntax requires >=1 `of` branch before an optional `else`, so an else-only variant with zero non-else arms is not constructible from valid Nim -- degenerate IR only]
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
          # RFC-0016 PRC-07 (cpp, a tracked cell): a write to any member is
          # defined and makes it the active one: no side to decline.
          let cppActiveW = fieldsUnchecked() and heapActiveTracked(objTy)
          # c, with the union image: a store out of the active arm is exact
          # in the arms it leaves with a value in every field
          # (`outOfArmFieldStore`); only the rest is declined.
          var exactCondW: Option[Z3Bool]
          var exactLay: vl.VariantLayout
          var exactPlace: vl.Place
          var hitTagsW: seq[int]
          for hit in armHitsW: hitTagsW.add hit.tagOrd
          if fieldsUnchecked() and not cppActiveW:
            let gateW = unionImageGate(objTy)
            if gateW.isSome:
              let tpW = vl.accessPlace(gateW.get, hitTagsW, stmt.dwField)
              if tpW.isSome:
                exactCondW = outOfArmFieldExactArms(objTy, gateW.get, tpW.get,
                                                    hitTagsW, discSV)
                exactLay = gateW.get
                exactPlace = tpW.get
          if cppActiveW:
            discard
          elif fieldsUnchecked():
            survivors.add inactiveFieldSide(
              forkPath(cpDW, basePcW, cpDW.env),
              (if exactCondW.isSome: (not inArmCondW) and (not exactCondW.get)
               else: not inArmCondW), cpDW.env, "", w, isWrite = true)
          else:
            discard forkDefect(forkPath(cpDW, basePcW, cpDW.env),
                               not inArmCondW, "FieldDefect", none(string), w)
          if w.shouldStop: return survivors
          # In-arm continuation: build the child path, THEN lower the RHS on it.
          # Disc heap is carried unchanged (D3: the disc is not mutated by an
          # arm-field write — only the arm's data heap changes).
          var childPcW =
            if cppActiveW: basePcW
            elif exactCondW.isSome: basePcW & @[inArmCondW or exactCondW.get]
            else: basePcW & @[inArmCondW]
          var cpChild = forkPath(cpDW, childPcW, cpDW.env)
          cpChild.heaps[discHeapKeyW] = discHeap
          # Lower RHS on the in-arm path (proto from the field type) — BV coercion
          # mirrors the plain-field write path (svInt↔BV reconciliation).
          var scratchPC: seq[Z3Bool]
          let proto = allocateSym(stmt.dwElemTy, "__armWriteProto", scratchPC)
          let (valSVRaw, cpInArmLowered) = lowerInExpr(cpChild, stmt.dwValue, w, some(proto))
          # RFC-0005 S8g: the RHS's scalar raise / conversion forks (this site
          # dropped them: an overflowing `p.f = a + b` never raised, and a
          # float -> int conversion's out-of-range continuation was lost).
          for cpInArm in drainScalarRaiseForks(cpInArmLowered, w):
            var valSV = valSVRaw
            # #163 review R22 site 2: an ARM-specific field write forks exactly
            # like the plain field write (site 1, above) and `isAssign`'s own
            # local-variable case -- see `forkAssignRangeCheck`'s doc comment.
            # All arms sharing this field NAME carry the SAME field TYPE by
            # Nim's own case-object rule, so `stmt.dwElemTy` (the type this
            # write's proto was already built from) is the correct target type
            # regardless of which arm(s) `armHitsW` matched. Checked BEFORE the
            # svInt->BV coercion below so the discharge can still see `valSV`'s
            # `ziIvl`.
            let cpInArmChecked =
              if stmt.dwElemTy.kind == itInt and stmt.dwElemTy.hasRange and
                 not carriesRangeCheck(stmt.dwValue, stmt.dwElemTy):   # RFC-0005 S8j
                forkAssignRangeCheck(cpInArm, valSV, stmt.dwElemTy, w)
              else: cpInArm
            valSV = heapStoreValue(valSV, proto, stmt.dwElemTy)   # RFC-0005 S8as
            var cpInArmRanged = cpInArmChecked
            if exactCondW.isSome:
              var cpX = forkPath(cpInArmRanged, cpInArmRanged.pc & @[exactCondW.get],
                                 cpInArmRanged.env)
              if outOfArmFieldStore(ctx, cpX, objTy, refAst, exactLay,
                                    exactPlace, discSV, valSV, hitTagsW):
                survivors.add drainPendingLowerEffects(cpX)
              else:
                survivors.add degradeHeapArmForPath(cpX, w.degrade(
                  feUnsupportedOp, "an out-of-branch field store through a " &
                  "`ref` whose value has no bytes (fieldChecksOffLayout) -- " &
                  "path degraded to sxUnknown"))
              # the arm the field names is not the active one: the in-arm
              # continuation has no execution (a read on it would taint the
              # run over bytes it never holds)
              if guardLiteral(inArmCondW) == glFalse: continue
              cpInArmRanged = forkPath(cpInArmRanged,
                                       cpInArmRanged.pc & @[inArmCondW],
                                       cpInArmRanged.env)
            # Store RHS into each matching arm's field heap.
            # RFC-0005 S8ap: a compound arm field stores every leaf.
            for hit in armHitsW:
              let armHeapKey = baseId & "__@" & $hit.tagOrd & "__" & stmt.dwField
              let armCell = heapCellArrays(ctx, cpInArmRanged, armHeapKey,
                                           allocRefSort(ctx, objTy), hit.fieldTy,
                                           objTy)
              for c in heapCellStore(ctx, armCell, refAst, valSV, hit.fieldTy):
                cpInArmRanged.heaps[c.key] = c.arr
            # N42 audit (round-6 fix round 7): unlike the plain-field write path
            # (below, in this same proc) and the disc-heap materialisation
            # above, THIS loop's `mkHeapArrayVar` calls happen AFTER the RHS's
            # own `lowerInExpr` (which produced `cpInArm` and already drained
            # sink (a) once) -- so a degrade from an ARM's OWN field type here
            # (a different, possibly-unsupported per-arm shape than the RHS's
            # own `stmt.dwElemTy` proto) would otherwise sit undrained past
            # `survivors.add` below. Same fix as the read-side arm-field path.
            # RFC-0016 PRC-07 (cpp): the member written is now the active
            # one (a field several tags share: the tag the discriminator
            # names among them, as a value variant's `lowerVariantFieldSet`).
            # On c the image needs no store: its active arm's bytes are read
            # from the field heaps (`cellImage`).
            if cppActiveW:
              var act = discConst(objTy.vDiscTy, int64(armHitsW[0].tagOrd))
              for k in 1 ..< armHitsW.len:
                let t = int64(armHitsW[k].tagOrd)
                act = iteSV(variantDiscEq(discSV, t),
                            discConst(objTy.vDiscTy, t), act)
              storeActive(ctx, cpInArmRanged, objTy, refAst, some(act))
            let cpInArmDrained = drainPendingLowerEffects(cpInArmRanged)
            survivors.add cpInArmDrained
      return survivors
    let sortTy = if isField: stmt.dwObjTy else: stmt.dwElemTy
    let typeId = refPointeeTypeId(sortTy)
    # ADR-0013 D1: disc write uses __@disc heap key; plain/non-variant use fieldHeapKey.
    let heapKey =
      if isDiscWrite: variantDiscHeapKey(stmt.dwObjTy)
      elif isField:   fieldHeapKey(stmt.dwObjTy, stmt.dwField)
      else:           typeId
    var survivors: seq[Path]
    for p0 in paths:
      if w.shouldStop: return survivors
      # Phase 15 R9: a deref-WRITE also bounds heap depth (the same step
      # and effective budget as the read). HALT this path before the store if it
      # reaches the budget.
      # RFC-0005 S8an: an `addr` cell's store is not a program write; it
      # does not count. (RFC-0005 S8bd: the check is made once the ref is
      # lowered, below.)
      ## Drain-coverage audit: `stmt.dwPtr` is always an env-resident var —
      ## the parser A-normalises so deref-write operands are named bindings.
      ## A violation here means the parser emitted a non-var write-ptr and
      ## drains would be needed before the lower call.
      let (refSV, p) = lowerLeafInExpr(p0, stmt.dwPtr)   ## RFC-0005 S8bw
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
          let d = heapArmDegrade(heUnresolvedRef,
            "deref-write through non-ref/ptr SymVal kind=" & plainEnglishSymValKind(refSV.kind) &
            " (Cluster R R4 expects an svRef/svPtr at the write site)")
          survivors.add degradeHeapArmForPath(p, d)
          continue
      # RFC-0005 S8bd: the budget bounds the depth of the chain the ref
      # was reached through (`heapChainDepth`), so it is read off the
      # lowered ref.
      if not stmt.dwCell and
         heapDepthExhausted(p, w, heapStepsOf(refSV) + 1, refAst): continue
      # Phase 15 R8. A write THROUGH an unmanaged `ptr T` also flags hePtrFamily
      # (same heap store as ref; sevHint, non-halting).
      if refSV.kind == svPtr:
        let ptrHintW = SymexErrorInfo(kind: hePtrFamily, severity: sevHint,
          msg: "witness involves unmanaged ptr")
        ptrFamilyHints.add ptrHintW   # threadvar: fallback
        w.ptrFamilyHints.add ptrHintW # CR-9 Stage 5: LIVE WalkCtx field
      # RFC-0005 S8ax: a `ptr` that may hold a dead frame's address cell
      # (`danglingFork`), before the nil fork.
      var nilForks: seq[Path]
      for pd in (if refSV.kind == svPtr: danglingFork(p, refAst, w) else: @[p]):
        nilForks.add nilDerefFork(pd, refAst, sortTy, w)
      for cp in nilForks:
        if w.shouldStop: return survivors
        if not isField and refVariantWhole(stmt.dwElemTy):
          # RFC-0005 S8at: `p[] = v` of a case object stores each part into
          # its field heap (`refVariantWholeStore`), the heaps `p.kind` and
          # `p.f` read. A whole assignment is not a discriminator assignment:
          # no FieldDefect.
          var scratchW: seq[Z3Bool]
          let protoW = allocateSym(stmt.dwElemTy, "__derefWriteProto", scratchW)
          let (valW, cpLoweredW) = lowerInExpr(cp, stmt.dwValue, w, some(protoW))
          for cpL in drainScalarRaiseForks(cpLoweredW, w):
            var child = forkPath(cpL, cpL.pc, cpL.env)
            if svFitsHeapTy(valW, stmt.dwElemTy):
              for c in refVariantWholeStore(ctx, cpL, allocRefSort(ctx, sortTy),
                                            refAst, stmt.dwElemTy, valW):
                child.heaps[c.key] = c.arr
            else:
              # A value some upstream degrade produced: no parts to store.
              # Each part's cell is havocked (a fresh term of its sort), as
              # `heapCellStore` does for a compound value of the wrong kind.
              allocDegrade(seUnsupportedCompoundSortLeaf,
                "heap store of a " & plainEnglishSymValKind(valW.kind) &
                " into a `" & $stmt.dwElemTy & "` cell: the value has no " &
                "parts of that type (seUnsupportedCompoundSortLeaf)")
              let refSortW = allocRefSort(ctx, sortTy)
              for sl in refVariantSlots(stmt.dwElemTy):
                for c in heapCellArrays(ctx, cpL, sl.key, refSortW, sl.ty,
                                        sl.variantTy):
                  let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, c.arr.raw)
                  let fresh = freshOfSort(ctx,
                    ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort))
                  child.heaps[c.key] = wrap[Z3AnyAst](ctx,
                    checkedStore(ctx, c.arr.raw, refAst.raw, fresh))
            survivors.add drainPendingLowerEffects(child)
          continue
        # Materialise the per-path heap (field-split array for a field write) on
        # first use, exactly as `isDeref` does, so a write before any read still
        # has an array to store into and a later read of the same ref/field reads
        # this stored array. Ref SORT keys on the OBJECT; value sort on the field.
        # RFC-0005 S8ap: a compound field / pointee is a leaf-split cell.
        let cell = heapCellArrays(ctx, cp, heapKey, allocRefSort(ctx, sortTy),
                                  stmt.dwElemTy,
                                  (if isDiscWrite: stmt.dwObjTy else: nil))
        let heap = cell[0].arr
        # Lower the RHS with a pointee-typed prototype so an int literal coerces to
        # the matching BV width / sort the heap array expects (the seq/table store
        # idiom). The raw value-sorted ast feeds `Z3_mk_store` directly.
        # CR-9 Stage 2: build proto (pure allocation, no threadvar side-effects)
        # BEFORE calling lowerInExpr so the wrapper's reset does not interfere.
        var scratchPC: seq[Z3Bool]
        let proto = allocateSym(stmt.dwElemTy, "__derefWriteProto", scratchPC)
        ## Encapsulate seed→reset→lower→drain via wrapper.
        let (valSVRaw, cpLoweredRaw) = lowerInExpr(cp, stmt.dwValue, w, some(proto))
        # RFC-0005 S8g: the RHS's scalar raise / conversion forks (this site
        # dropped them: an overflowing `p[] = a + b` never raised, and a
        # float -> int conversion's out-of-range continuation was lost).
        for cpLowered in drainScalarRaiseForks(cpLoweredRaw, w):
          var valSV = valSVRaw
          # #163 review R22 site 1: a FIELD write (`p.field = v`, isField) whose
          # declared field type is `range[lo..hi]` forks exactly like
          # `isAssign`'s own local-variable case (`forkAssignRangeCheck`, reused
          # unchanged) — the out-of-range sub-path is a routed RangeDefect
          # raise, the survivor's `pc` is hard-narrowed to the in-range domain,
          # and a provably-in-range RHS (`av.ziIvl`) discharges statically with
          # no fork at all. Checked BEFORE the svInt→BV coercion below so the
          # discharge can still see `valSV.ziIvl` (a BV-coerced value carries
          # none). A bare `p[] = v` (not `isField`) is out of this fix's scope
          # — see the handoff's site enumeration.
          # RFC-0005 S8j: not when the RHS is itself the range-checked
          # conversion into this field's bounds (`carriesRangeCheck`).
          let cp = if isField and stmt.dwElemTy.kind == itInt and stmt.dwElemTy.hasRange and
                      not carriesRangeCheck(stmt.dwValue, stmt.dwElemTy):
                     forkAssignRangeCheck(cpLowered, valSV, stmt.dwElemTy, w)
                   else: cpLowered
          # Reconcile svInt↔BV sort mismatch: float→int64 returns svInt (Z3Int)
          # but the heap array value sort is BV64.  Coerce via int2bv here rather
          # than in the heap-read path; equality-only goals are safe (no ordering
          # goal — the F5 int2bv/bv2int pathology does not apply here).
          valSV = heapStoreValue(valSV, proto, stmt.dwElemTy)   # RFC-0005 S8as
          # RFC-0005 S8l. A discriminator write THROUGH a ref is checked exactly
          # like the value model's reassignment (S8f, `sameBranchCond`): Nim
          # raises `FieldDefect` ("assignment to discriminant changes object
          # branch") when the stored discriminator selects a different source
          # branch than the new value -- a zero-initialised `new(V)` cell
          # included (probed on the pinned toolchain). Before S8l this was a
          # plain store: an INLINE `ref V` write was unchecked, and the named
          # ref variant (value-modelled until S8l) reaches this arm now. The
          # constructor's initialising write (`dwInit`) is not an assignment
          # and is not checked. A same-branch move keeps the branch's fields:
          # the ADR-0013 heap keeps one array per TAG, so each field of a
          # multi-tag branch is re-stored at every tag of it from the tag the
          # old discriminator named (an arm-field write already stores to all
          # of them, so this only matters for an unwritten free param cell).
          var cpS = cp
          if isDiscWrite and not stmt.dwInit:
            let objTy = stmt.dwObjTy
            let oldDisc = heapSelect(ctx, heap, refAst, objTy.vDiscTy)
            var basePc = cp.pc
            let rangeOpt = refVariantDiscRangeClause(objTy, oldDisc)
            if rangeOpt.isSome: basePc = basePc & @[rangeOpt.get]
            let groups = branchGroups(objTy.vArms)
            let same = sameBranchSymCond(oldDisc, valSV, groups)
            # RFC-0016 PRC-07 (ref variants): `imageArms`, the arms whose
            # fields the cell's union image answers after the store (c);
            # `fixImage`, the image with the old arm's bytes, which the
            # stored heaps keep once that arm is no longer active.
            var imageArms: seq[(int, seq[SymVal])]
            var fixImage: seq[Z3BitVec[64]]
            var contPc = basePc & @[same]
            let tracked = fieldsUnchecked() and heapActiveTracked(objTy)
            let gate = unionImageGate(objTy)
            if tracked:
              # cpp: no branch-change check, and the store is of the tag
              # alone: the old member stays the active one (fixed below), so
              # a read through the new arm is `ubInactiveVariantField` until
              # a write makes one of its members active.
              contPc = basePc
            elif fieldsUnchecked():
              # RFC-0016 PRC-07: no branch-change check; the new branch holds
              # the old bytes. With the union image (c, a plain-bits type),
              # the store is of the tag alone and the new arm's fields are
              # the image's bytes at their places (a value variant's
              # `discWriteOutcomes`): exact; an arm with a field the bytes
              # are no value of (a bool, a checked range, the `else` arm) is
              # declined on the side that selects it. Without one (a hooked
              # type, an `else` arm on cpp) the branch-changing side is
              # declined whole.
              var declineCond = some(not same)
              var dwhyImg = ""
              if gate.isSome:
                declineCond = none(Z3Bool)
                let lay = gate.get
                let n0 = cp.pc.len
                let img = cellImage(ctx, cp, objTy, refAst, lay)
                basePc = basePc & cp.pc[n0 .. ^1]
                fixImage = img
                for ai, arm in objTy.vArms:
                  var after: seq[SymVal]
                  var why = ""
                  if arm.isElse: why = "the `else` arm"
                  elif not lay.arms.hasKey(arm.tagOrdinal) or
                       lay.arms[arm.tagOrdinal].len != arm.fieldNames.len:
                    why = "arm `" & $arm.tagOrdinal & "` has no layout"
                  else:
                    for j, f in lay.arms[arm.tagOrdinal]:
                      let nv = bitsPlace(imgReadDef(img, f.off - lay.unionOff,
                                                    f.size), f,
                                         none((vl.Place, SymVal)))
                      if nv.isNone:
                        why = "field `" & arm.fieldNames[j] &
                              "` holds only its own values"
                        break
                      after.add nv.get
                  if why.len == 0:
                    imageArms.add (ai, after)
                    continue
                  var selTag: Z3Bool
                  if arm.isElse:
                    var seeded = false
                    for o in objTy.vArms:
                      if o.isElse: continue
                      let neg = not variantDiscEq(valSV, int64(o.tagOrdinal))
                      selTag = (if seeded: selTag and neg else: neg)
                      seeded = true
                    if not seeded: continue
                  else:
                    selTag = variantDiscEq(valSV, int64(arm.tagOrdinal))
                  let c = (not same) and selTag
                  declineCond = some(if declineCond.isSome: declineCond.get or c
                                     else: c)
                  dwhyImg = "; " & why
                contPc = basePc
                if declineCond.isSome: contPc = basePc & @[not declineCond.get]
              if declineCond.isSome and
                 guardLiteral(declineCond.get) != glFalse:
                let (dk, dwhy) = admitDefined(aoField, ocInactiveBytes,
                                              dsField).decline
                survivors.add forkPathTainted(
                  cp, basePc & @[declineCond.get], cp.env,
                  w.degrade(dk.get(feUnsupportedOp),
                    "a discriminator write through a `ref` that changes " &
                    "branch with `fieldChecks` off (fieldChecksOffLayout): " &
                    "the new branch holds the old bytes (" & dwhy & dwhyImg &
                    ") -- path degraded to sxUnknown"))
            else:
              maybeForkDefect(forkPath(cp, basePc, cp.env), not same,
                              "FieldDefect", none(string), w)
            if w.shouldStop: return survivors
            cpS = forkPath(cp, contPc, cp.env)
            if fixImage.len > 0:
              imageStore(ctx, cpS, imageHeapCells(ctx, cpS, refPointeeTypeId(objTy),
                         allocRefSort(ctx, objTy), gate.get), refAst, fixImage)
            if tracked:
              storeActive(ctx, cpS, objTy, refAst,
                          some(cellActive(ctx, cp, objTy, refAst, oldDisc)))
            let baseId = refPointeeTypeId(objTy)
            for g in groups:
              if g.len < 2: continue
              var armIx = -1
              for ai, arm in objTy.vArms:
                if arm.tagOrdinal == g[0]: armIx = ai
              if armIx < 0: continue
              let arm0 = objTy.vArms[armIx]
              for j, fname in arm0.fieldNames:
                let fty = arm0.fieldTypes[j]
                # RFC-0005 S8ap: per-tag leaf-split cells; the carried
                # value is read from the INPUT-or-current cells, so the
                # input cells' well-formedness is asserted with it.
                var cells: seq[HeapCell]
                var wf: seq[Z3Bool]
                let refSortC = allocRefSort(ctx, objTy)
                for t in g:
                  let k = baseId & "__@" & $t & "__" & fname
                  cells.add heapCellArrays(ctx, cpS, k, refSortC, fty, objTy)
                  wf.add heapCellWfConds(ctx, k, refSortC, fty, refAst)
                var carried = heapCellSelect(ctx, cells[^1], refAst, fty)
                for k in countdown(g.len - 2, 0):
                  carried = heapCellIte(ctx, variantDiscEq(oldDisc, int64(g[k])),
                                        heapCellSelect(ctx, cells[k], refAst, fty),
                                        carried, fty)
                for k in 0 ..< g.len:
                  for c in heapCellStore(ctx, cells[k], refAst, carried, fty):
                    cpS.heaps[c.key] = c.arr
                for c in wf: cpS.pc.add c
            # RFC-0016 PRC-07 (ref variants): the arm the new tag selects
            # reads its fields from the union image (the bytes stay).
            for (ai, after) in imageArms:
              let arm = objTy.vArms[ai]
              let sel = variantDiscEq(valSV, int64(arm.tagOrdinal))
              let refSortI = allocRefSort(ctx, objTy)
              for j, fname in arm.fieldNames:
                let fty = arm.fieldTypes[j]
                let k = baseId & "__@" & $arm.tagOrdinal & "__" & fname
                let cellI = heapCellArrays(ctx, cpS, k, refSortI, fty, objTy)
                var scratchI: seq[Z3Bool]
                let protoI = allocateSym(fty, "__armImageProto", scratchI)
                let nv = heapCellIte(ctx, sel, heapStoreValue(after[j], protoI, fty),
                                     heapCellSelect(ctx, cellI, refAst, fty), fty)
                for c in heapCellStore(ctx, cellI, refAst, nv, fty):
                  cpS.heaps[c.key] = c.arr
          let stored = heapCellStore(ctx, cell, refAst, valSV, stmt.dwElemTy)
          # REPLACE the per-path heap binding with the stored array on the surviving
          # path (PER-PATH — an unforked branch never sees this update).
          # RFC-0005 S8ap: every leaf of a compound cell.
          var child = forkPath(cpS, cpS.pc, cpS.env)
          for c in stored: child.heaps[c.key] = c.arr
          # RFC-0005 S8bh (item 2). A bare `p[] = v` through a `ptr` also
          # stores into each candidate TARGET under its `sel` guard
          # (`ptrTargetWrite`; the own cell's store is the one above). Not
          # an `addr` cell's store (`dwCell`) nor a field write.
          # RFC-0005 S8bz (item 1): a whole aggregate's pointer has no such
          # targets; it declines where it may address one.
          if refSV.kind == svPtr and not stmt.dwCell:
            let aggMsg = ptrAggregateDecline(w, child, refAst,
              (if isField: stmt.dwObjTy else: stmt.dwElemTy), typeId)
            if aggMsg.len > 0:
              survivors.add degradeHeapArmForPath(child,
                w.degrade(feUnsupportedOp, aggMsg))
              continue
          if refSV.kind == svPtr and not isField and not stmt.dwCell and
             ptrScalarPointee(stmt.dwElemTy):
            let pre = forkPath(child, child.pc, child.env)
            var inactive: Option[Z3Bool]
            let msg = ptrTargetWrite(ctx, w, child, refAst, stmt.dwElemTy,
                                     allocRefSort(ctx, sortTy), typeId, valSV,
                                     inactive)
            if msg.len > 0:
              # RFC-0005 S8bz: the walk's own degrade (`tr.decline`'s note).
              survivors.add degradeHeapArmForPath(child,
                w.degrade(feUnsupportedOp, msg))
              continue
            # RFC-0005 S8bw (item 3): as the read's (`ptrTargetRead`).
            if inactive.isSome:
              if not loopArmInfeasible(ctx, child, inactive.get, w.settings):
                survivors.add degradeHeapArmForPath(
                  forkPath(pre, child.pc & @[inactive.get], pre.env),
                  w.degrade(feUnsupportedOp, ptrInactiveMsg(stmt.dwElemTy)))
              child.pc.add not inactive.get
          # RFC-0005 S1c (S1b's measured leak, `tsymex_r6_n40_alloc_totality`
          # N40-4). `rawAnyAstOf(valSV)` in the store above runs AFTER
          # `lowerInExpr`'s drain, and for a value with no single-leaf Z3 sort
          # (a `Table[int, _]` field) it degrades in-band via `allocDegrade` --
          # so its pending taint was never folded onto ANY path and surfaced
          # only as the walk-end leak stamp. Drain it onto the path that
          # carries the stored value: the same post-allocation drain the READ
          # arm's N42 note establishes above (idempotent; a no-op when nothing
          # degraded).
          child = drainPendingLowerEffects(child)
          survivors.add child
    survivors
  else:
    raise newException(ValueError,  # [raise-audited: category-c: documented single-caller dispatch invariant (walk's own case restricts stmt.kind to isDeref/isNew/isDerefWrite before ever calling walkHeapArm)]
      "walkHeapArm: unexpected stmt.kind=" & $stmt.kind &
      " (not isDeref/isNew/isDerefWrite)")
