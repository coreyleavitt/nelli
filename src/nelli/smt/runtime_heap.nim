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
  ##
  ## RFC-0005 S8j: a variant pointee keys on its `vNominalId` the same way.
  ## An inline `ref Obj` field's pointee is the empty-fielded placeholder
  ## tuple, keyed on `nominalId(Obj)`; when `Obj` is a case object, every
  ## other position (the nil in `h.v != nil`, the pointee of `h.v.kind`)
  ## carries the full variant. Keyed structurally, the two were distinct
  ## sorts for one Nim type: a Z3 sort error, or a false `sxUnsat`.
  ## RFC-0005 S8l: a multi-variant keys on its `mvNominalId` for the same
  ## reason (an inline `ref MV` field was that sort error).
  let base = if pointeeTy.kind == itTuple and pointeeTy.nominalId.len > 0:
               pointeeTy.nominalId
             elif pointeeTy.kind == itVariant and pointeeTy.vNominalId.len > 0:
               pointeeTy.vNominalId
             elif pointeeTy.kind == itMultiVariant and pointeeTy.mvNominalId.len > 0:
               pointeeTy.mvNominalId   # RFC-0005 S8l
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

proc distinctGround(ty: IRType): IRType =
  ## RFC-0005 S8ar. The base a `distinct` (chain) ejects to.
  result = ty
  while result != nil and result.kind == itDistinct: result = result.distinctBase

proc heapUnitTy(ty: IRType): bool =
  ## RFC-0005 S8ar. A value a heap cell can hold: a scalar one Z3 term
  ## carries (`liftHeapValue`'s kinds), or a leaf-split compound value.
  ty != nil and (ty.kind in {itInt, itBool, itFloat32, itFloat64, itString,
                             itRef, itPtr} or heapCompoundTy(ty))

proc heapTreeTy(ty: IRType): bool =
  ## RFC-0005 S8ar. A by-value aggregate held as the leaves of its parts: a
  ## tuple or object (`itTuple`), an array, a `distinct` (its base's
  ## leaves; a distinct value IS its base value, every read ejects).
  ## RFC-0005 S8at: a by-value case object (`heapParts`).
  heapCompoundTy(ty) and
    ty.kind in {itTuple, itArray, itDistinct, itVariant, itMultiVariant}

proc heapCompoundTy(ty: IRType): bool =
  ## RFC-0005 S8ap. A heap value held leaf-split: a seq whose elements
  ## `allocateSeqDataRaw` backs, a `Table[string, V]` and a `HashSet[T]`
  ## `allocateSym` backs. A placeholder seq (an unbacked element type) is not
  ## -- its value is inert by construction and keeps the pre-S8ap decline.
  ##
  ## RFC-0005 S8ar: also a by-value tuple / object, array and `distinct`
  ## whose parts are all `heapUnitTy` (`heapTreeTy`). They were
  ## `seUnsupportedCompoundSortLeaf` (a tuple is not one Z3 term) and a
  ## `distinct` field was havocked. Still not a cell value, each stated:
  ## an empty object (no leaf to hold its cell), and any part that is
  ## itself not a cell value.
  ##
  ## RFC-0005 S8at: a by-value case object (`itVariant`/`itMultiVariant`)
  ## is a tree too: its discriminator, its plain fields, and every arm's
  ## fields, each a part (`heapParts`). The value is the walker's
  ## `svVariant`, which holds a slot for every arm; the discriminator says
  ## which arm a read may see (`isVariantField`'s FieldDefect fork runs on
  ## the selected value, as on any value variant). S8ar declined it (its
  ## fields depend on the discriminator).
  if ty == nil: return false
  case ty.kind
  of itSeq:
    ty.seqUnsupportedFieldReason.len == 0 and isBackedSeqElemTy(ty.seqElemTy)
  of itTable:
    isBackedTableTy(ty.tabKeyTy, ty.tabValTy)
  of itSet: isBackedSetElemTy(ty.setElemTy)
  of itTuple:
    if ty.isPlaceholder or ty.fields.len == 0: return false
    for f in ty.fields:
      if not heapUnitTy(f): return false
    true
  of itArray: ty.size > 0 and heapUnitTy(ty.elemTy)
  of itVariant, itMultiVariant:
    # RFC-0005 S8at. An axis view (`mvAxisView`) is the REF layout's
    # (ADR-0013), never a by-value cell.
    if ty.kind == itVariant and ty.vIsAxisView: return false
    for part in heapParts(ty):
      if not heapUnitTy(part.ty): return false
    true
  of itDistinct:
    # RFC-0005 S8at: a composite base too. S8ar admitted a scalar base only,
    # since a composite base had no distinct sort (`ensureDistinctSort`
    # derived inject/eject over one Z3 term of the base); it now has one
    # without them, so a distinct over a compound cell value is held as its
    # base's leaves (`heapLeafSuffixes`) and re-boxed on a read.
    let g = distinctGround(ty)
    g != nil and (g.kind in {itInt, itBool, itFloat32, itFloat64, itString} or
                  heapCompoundTy(g))
  else: false

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

proc heapPartLabel(ty: IRType; i: int): string =
  ## RFC-0005 S8ar. The name of part `i` of a `heapTreeTy` tuple or array:
  ## a field's name, `Field<i>` for an anonymous tuple's (`fieldPairs`'
  ## spelling, which the witness reader walks), the position of an array
  ## element.
  if ty.kind == itTuple:
    (if ty.fieldNames[i].len > 0: ty.fieldNames[i] else: "Field" & $i)
  else: $i

proc heapParts(ty: IRType): seq[tuple[label: string; ty: IRType]] =
  ## RFC-0005 S8ar. The parts of a `heapTreeTy` value, in leaf order.
  ## RFC-0005 S8at: a case object's are its discriminator, its plain fields
  ## and each arm's fields, an arm field labelled `@<arm>_<field>` (`<arm>`
  ## the arm's position in `vArms`: `of a, b: f` is two arms, each with its
  ## own slot, as the walker's `svVariant` holds them). A multi-variant's
  ## are its plain fields, then per axis its discriminator and arm fields
  ## (`@<axis>_<arm>_<field>`).
  case ty.kind
  of itTuple:
    for i, f in ty.fields: result.add (heapPartLabel(ty, i), f)
  of itArray:
    for i in 0 ..< ty.size: result.add (heapPartLabel(ty, i), ty.elemTy)
  of itVariant:
    result.add (ty.vDiscName, ty.vDiscTy)
    for i, f in ty.vPlainFieldTypes: result.add (ty.vPlainFieldNames[i], f)
    for ai, arm in ty.vArms:
      for j, f in arm.fieldTypes:
        result.add ("@" & $ai & "_" & arm.fieldNames[j], f)
  of itMultiVariant:
    for i, f in ty.mvPlainFieldTypes: result.add (ty.mvPlainFieldNames[i], f)
    for xi, ax in ty.mvAxes:
      result.add (ax.discName, ax.discTy)
      for ai, arm in ax.arms:
        for j, f in arm.fieldTypes:
          result.add ("@" & $xi & "_" & $ai & "_" & arm.fieldNames[j], f)
  else: discard

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
  of itSeq:   @["", "__@len"]
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
  of svSeq:   @[sv.seqDataRaw.raw, sv.seqLen.raw] # [placeholder-audited]
  of svTable:
    var r = @[sv.tabDataRaw.raw, sv.tabPresentRaw.raw, sv.tabSize.raw]
    for m in sv.tabDataMore: r.add m.raw   ## RFC-0005 S8at
    r
  of svSet:   @[sv.setMembersRaw.raw, sv.setSize.raw]
  else:       @[rawAnyAstOf(sv)]

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
  of itSeq: sv.kind == svSeq and not sv.isUnsupportedFieldPlaceholder # [placeholder-audited]
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
    let probe = mkArrayVar[Z3Int, Z3Int](ctx, "__s8ax_store_probe")
    let st = checkedStore(ctx, probe.raw, mkInt(ctx, 0).raw,
                          mkInt(ctx, 0).raw)
    storeDeclKind = ord(Z3_get_decl_kind(ctx.raw,
      Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, st)))) + 1
  if Z3_get_ast_kind(ctx.raw, arr) != Z3_APP_AST: return none(RawZ3Ast)
  let app = Z3_to_app(ctx.raw, arr)
  if ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1 !=
     storeDeclKind or Z3_get_app_num_args(ctx.raw, app) != 3:
    return none(RawZ3Ast)
  if cast[pointer](Z3_get_app_arg(ctx.raw, app, 1)) != cast[pointer](idx):
    return none(RawZ3Ast)
  some(Z3_get_app_arg(ctx.raw, app, 2))

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
    let a = mkArrayVar[Z3Int, Z3Int](ctx, "__s8ax_chain_probe_a")
    let b = mkArrayVar[Z3Int, Z3Int](ctx, "__s8ax_chain_probe_b")
    let st = checkedStore(ctx, a.raw, mkInt(ctx, 0).raw, mkInt(ctx, 0).raw)
    storeDeclKind = ord(Z3_get_decl_kind(ctx.raw,
      Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, st)))) + 1
    let it = checkedIte(ctx, mkBoolVar(ctx, "__s8ax_chain_probe_c").raw,
                        a.raw, b.raw)
    iteDeclKind = ord(Z3_get_decl_kind(ctx.raw,
      Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, it)))) + 1
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

proc svCellWf(sv: SymVal; ty: IRType; nested: bool): seq[Z3Bool] =
  ## RFC-0005 S8ap (was `heapCellWfConds`' body); S8ar: recursive over a
  ## tree value's parts. The facts a free value of `ty` has (`allocateSym`'s
  ## init facts): a string of bytes, a length or size in `[0, 1024]`, a
  ## table's and a set's size tied to its keys (`ContainerCardRegistry`),
  ## and -- for a NESTED scalar part, which no read site sees -- its declared
  ## range (`rangeCondsIfNeeded`; a cell's own scalar range is the read
  ## site's).
  case sv.kind
  of svString:
    @[matches(sv.str, star(range(mkString("\x00"), mkString("\xff"))))]
  of svSeq:
    @[sv.seqLen >= mkInt(0), sv.seqLen <= mkInt(1024)] # [placeholder-audited]
  of svTable:
    registerTableBase(sv.tabPresentRaw, sv.tabSize, ty.tabKeyTy)
    registerTabTreeBase(sv)   ## RFC-0005 S8at
    @[sv.tabSize >= mkInt(0), sv.tabSize <= mkInt(1024)]
  of svSet:
    registerSetBase(sv.setMembersRaw, sv.setSize, ty.setElemTy)
    @[sv.setSize >= mkInt(0),
      sv.setSize <= mkInt(min(1024'i64, cellDomainSize(ty.setElemTy)))]
  of svTuple:
    var r: seq[Z3Bool]
    for i, f in sv.fields: r.add svCellWf(f, ty.fields[i], true)
    r
  of svArray:
    var r: seq[Z3Bool]
    for e in sv.arrElems: r.add svCellWf(e, ty.elemTy, true)
    r
  of svDistinct:
    svCellWf(ejectBase(sv), distinctGround(ty), nested)
  of svVariant, svMultiVariant:
    # RFC-0005 S8at. Each part's facts, and each discriminator in its
    # legal domain (`allocateSym`'s clause: an `else` arm's ordinals
    # included, its sentinel not).
    var r: seq[Z3Bool]
    if not heapTreeTy(ty) or not svFitsHeapTy(sv, ty): return r
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty): r.add svCellWf(ps[i], part.ty, true)
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
  refPointeeTypeId(objTy) & "__" & field

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
  heapStepsOf(lowerLeafInExpr(p, ptrExpr)) + 1

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
  proc go(a: Z3AnyAst): int =
    if getAstKind(a) != akApp: return 0
    let id = astId(ctx, a.raw)
    if id in memo: return memo[id]
    let (decl, args) = unpackApp(a)
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    var d = 0
    if k == kinds.select and args.len == 2:
      let dom = arrayKey(ctx, ctx.checkErr Z3_get_sort(ctx.raw, args[0].raw))
      d = if getSortKind(ctx, dom) == skUninterpreted: 1 + go(args[1])
          else: go(args[0])
    elif k == kinds.ite and args.len == 3:
      d = max(go(args[1]), go(args[2]))
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
    discard w.degrade(heDepthExhausted, msg, dsHeapDepth)
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
  let eqNil = wrap[Z3Bool](ctx, checkedEq(ctx, refAst.raw, nilConst.raw))
  # NIL sub-path — NilAccessDefect fork. Phase 16 D1a unconditional.
  # RFC-0005 S8k: the nil edge is marked (`Path.nilDeref`) before it is
  # routed, so a handler continuation and an escaping finding both carry it
  # to replay, which must never run the real SIGSEGV this edge models.
  let nilPath = forkPath(p, p.pc & @[eqNil], p.env)
  nilPath.nilDeref = true
  discard routeRaise(nilPath, "NilAccessDefect", none(string), w)
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

proc addrCellValue(ctx: Z3Context; p: Path; ty: IRType;
                   refAst: Z3AnyAst): SymVal =
  ## RFC-0005 S8ax. The value of the address cell at `refAst` on `p`.
  let cell = heapCellArrays(ctx, p, refPointeeTypeId(ty), allocRefSort(ctx, ty),
                            ty)
  heapCellSelect(ctx, cell, refAst, ty)

proc addrCellStore(ctx: Z3Context; p: Path; ty: IRType; refAst: Z3AnyAst;
                   v: SymVal): SymVal =
  ## RFC-0005 S8ax. Store `v` into the address cell at `refAst` on `p` (a
  ## path the caller just forked) and return the cell's value read back:
  ## the variable's new binding, so the two stay one term.
  let cell = heapCellArrays(ctx, p, refPointeeTypeId(ty), allocRefSort(ctx, ty),
                            ty)
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(ty, "__addrCellProto", scratchPC)
  let stored = heapCellStore(ctx, cell, refAst, heapStoreValue(v, proto, ty), ty)
  for c in stored: p.heaps[c.key] = c.arr
  heapCellSelect(ctx, stored, refAst, ty)

proc danglingFork(p: Path; refAst: Z3AnyAst; w: var WalkCtx): seq[Path] =
  ## RFC-0005 S8ax. A `ptr` dereference on `p` that may reach the address
  ## cell of a variable whose frame has returned (`Path.addrOwners`): Nim
  ## reads or writes a dead stack slot there, which the walk does not model.
  ## The edge where it does is tainted (`feUnsupportedOp`, the cell's last
  ## value substituting for the slot's) when it is feasible; the rest
  ## continues untouched.
  var dead: seq[Z3AnyAst]
  for o in p.addrOwners:
    if not liveFrame(w, o.frame): dead.add o.refAst
  if dead.len == 0: return @[p]
  let ctx = w.z3
  var hits: seq[Z3Bool]
  for d in dead:
    hits.add wrap[Z3Bool](ctx, checkedEq(ctx, refAst.raw, d.raw))
  var anyHit = hits[0]
  for i in 1 ..< hits.len: anyHit = anyHit or hits[i]
  let hitPath = forkPath(p, p.pc & @[anyHit], p.env)
  if not pathInfeasible(ctx, hitPath, w.settings):
    let d = w.degrade(feUnsupportedOp,
      "RFC-0005 S8ax: a pointer dereferenced here may hold the address of " &
           "a variable whose routine has returned; Nim reads or writes a " &
           "dead stack slot, which the walk does not model (feUnsupportedOp)")
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
    if ty.kind notin {itInt, itBool, itFloat32, itFloat64, itString, itTuple,
                      itSeq}:
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
        if c.local == local: known = true
      if not known:
        w.frame.addrCells.add (local: local, cell: stmt.nRetName, ty: ty)
    child.addrOwners.add (refAst: newRef, frame: w.frame.frameId)
    env2[local] = addrCellStore(ctx, child, ty, newRef, env2[local])
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
      for p in paths:
        if w.shouldStop: return survivors
        let step = heapStepOf(p, stmt.dPtr)   ## RFC-0005 S8ar
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
    for p in paths:
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
      let step = heapStepOf(p, stmt.dPtr)   ## RFC-0005 S8ar
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
      for p in paths:
        if w.shouldStop: return survivors
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
            let cpInArmRanged =
              if stmt.dwElemTy.kind == itInt and stmt.dwElemTy.hasRange and
                 not carriesRangeCheck(stmt.dwValue, stmt.dwElemTy):   # RFC-0005 S8j
                forkAssignRangeCheck(cpInArm, valSV, stmt.dwElemTy, w)
              else: cpInArm
            valSV = heapStoreValue(valSV, proto, stmt.dwElemTy)   # RFC-0005 S8as
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
    for p in paths:
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
            maybeForkDefect(forkPath(cp, basePc, cp.env), not same,
                            "FieldDefect", none(string), w)
            if w.shouldStop: return survivors
            cpS = forkPath(cp, basePc & @[same], cp.env)
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
          let stored = heapCellStore(ctx, cell, refAst, valSV, stmt.dwElemTy)
          # REPLACE the per-path heap binding with the stored array on the surviving
          # path (PER-PATH — an unforked branch never sees this update).
          # RFC-0005 S8ap: every leaf of a compound cell.
          var child = forkPath(cpS, cpS.pc, cpS.env)
          for c in stored: child.heaps[c.key] = c.arr
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
