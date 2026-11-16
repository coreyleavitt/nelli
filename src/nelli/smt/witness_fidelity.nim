## nelli/smt/witness_fidelity -- how faithfully a reconstructed witness stands
## for the solver's (`WitnessFidelity`), and the splat that applies a typed
## witness to the SUT (`emitWitnessSplat`).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged.

import std/[macros, sets, tables]
import ./dsl
import ./witness_emit

type WitnessFidelity* = enum
  ## RFC-0005 §4.2 "Un-replayable witnesses". How faithfully `emitTyAndReader`
  ## renders a witness shape -- decided at macro time, per parameter, from
  ## the SAME `IRType` the reader walks. Ordered: the worst component wins.
  wfFaithful      ## the rendered value IS the solver's model value
  wfLossy         ## safe to execute, but the render is not the model (a
                  ## `ref` cell with a field kind the logical heap does not
                  ## model, or whose fields are unknown at macro time -- RFC-
                  ## 0005 S8h; `default(Object)` variant stubs; the
                  ## unsupported-field empty seq).
                  ## A HIT still confirms -- any concrete input that reaches the
                  ## target proves reachability -- but a MISS proves nothing
                  ## about the model's witness, so it is inconclusive
  wfUnexecutable  ## a placeholder that must never be run: the nil-proc
                  ## closure stub, the nil `ptr` to a pointee no cell can be
                  ## built for, the `__unsupported:` dummy `int`, a recursive
                  ## ref field with no type symbol (deref would crash or
                  ## misattribute a raise)

proc collectNominals*(ty: IRType; acc: var Table[string, IRType];
                     seen: var HashSet[string]) =
  ## RFC-0005 S8h. Every fielded named object in the type tree `ty`, by
  ## `nominalId`: the only place a recursive field's placeholder pointee can
  ## learn its fields at macro time.
  if ty == nil: return
  case ty.kind
  of itTuple:
    if ty.nominalId.len > 0:
      if ty.isPlaceholder or seen.containsOrIncl(ty.nominalId): return
      acc[ty.nominalId] = ty
    for f in ty.fields: collectNominals(f, acc, seen)
  of itRef: collectNominals(ty.refPointeeTy, acc, seen)
  of itPtr: collectNominals(ty.ptrPointeeTy, acc, seen)
  of itArray: collectNominals(ty.elemTy, acc, seen)
  of itSeq: collectNominals(ty.seqElemTy, acc, seen)
  of itDistinct: collectNominals(ty.distinctBase, acc, seen)
  of itVariant:
    for f in ty.vPlainFieldTypes: collectNominals(f, acc, seen)
    for arm in ty.vArms:
      for f in arm.fieldTypes: collectNominals(f, acc, seen)
  of itMultiVariant:
    for f in ty.mvPlainFieldTypes: collectNominals(f, acc, seen)
    for ax in ty.mvAxes:
      for arm in ax.arms:
        for f in arm.fieldTypes: collectNominals(f, acc, seen)
  else: discard

proc refCellFidelity(ty: IRType; noms: Table[string, IRType];
                     inProgress: var HashSet[string]): WitnessFidelity =
  ## RFC-0005 S8h. The fidelity of a `ref`/`ptr` position: `resolveRef`
  ## renders the model's input heap exactly for the field kinds the logical
  ## heap models (`liftHeapValue`: int -- incl. enums --, bool, float, ref,
  ## ptr), so a cell of only those is faithful, recursively; a field of any
  ## other kind keeps its zero value (lossy), and a cell whose fields cannot
  ## be known at macro time is lossy too.
  if not resolvesByRef(ty): return wfUnexecutable
  var pointee = refPointeeOf(ty)
  if pointee.kind == itTuple and pointee.isPlaceholder:
    if pointee.nominalId.len == 0 or not noms.hasKey(pointee.nominalId):
      return wfLossy
    pointee = noms[pointee.nominalId]
  proc fieldFidelity(f: IRType; inProgress: var HashSet[string]): WitnessFidelity =
    case f.kind
    of itBool, itInt, itFloat32, itFloat64: wfFaithful
    of itRef, itPtr: refCellFidelity(f, noms, inProgress)
    # RFC-0005 S8ap: a string field, and a leaf-split seq / Table / HashSet
    # field whose content `renderHeapCompound` writes and `readCellField`
    # reads (`readCellSeq`/`readCellTable`/`readCellSet`): a seq of int,
    # bool, float or ref/ptr, a `Table[string, int|bool]`, a backed
    # `HashSet`. Any other compound field keeps its zero value (lossy).
    of itString: wfFaithful
    of itSeq:
      if isUnsupportedFieldPlaceholder(f): wfLossy
      else:
        case f.seqElemTy.kind
        of itBool, itInt, itFloat32, itFloat64: wfFaithful
        of itString: wfFaithful   ## RFC-0005 S8ar: `renderHeapCompound`'s string arm
        of itRef, itPtr: refCellFidelity(f.seqElemTy, noms, inProgress)
        else: wfLossy
    of itTable:
      # RFC-0005 S8ar: every backed shape (`readCellTable` reads the real
      # key and value types, so a `char` key or value is faithful here).
      if isBackedTableTy(f.tabKeyTy, f.tabValTy): wfFaithful
      else: wfLossy
    of itSet:
      if isBackedSetElemTy(f.setElemTy): wfFaithful else: wfLossy
    # RFC-0005 S8ar: a by-value object / tuple, array and `distinct` field,
    # held leaf-split (`heapCompoundTy`), written part by part by
    # `renderHeapValue` and read by `readCellField`'s `fieldPairs` / array /
    # distinct arms. A part the heap does not model makes it lossy (its
    # read degrades); so does a by-value case object.
    of itTuple:
      if f.isPlaceholder or f.fields.len == 0: wfLossy
      else:
        var r = wfFaithful
        for g in f.fields: r = max(r, fieldFidelity(g, inProgress))
        r
    of itArray:
      if f.size == 0: wfLossy else: fieldFidelity(f.elemTy, inProgress)
    of itDistinct:
      var g = f.distinctBase
      while g.kind == itDistinct: g = g.distinctBase
      if g.kind in {itInt, itBool, itFloat32, itFloat64, itString}: wfFaithful
      else: wfLossy
    else: wfLossy
  case pointee.kind
  of itBool, itInt, itFloat32, itFloat64: wfFaithful
  of itString, itSeq, itTable, itSet, itArray, itDistinct:   # RFC-0005 S8ap: `ref seq[int]` etc.; S8ar: + array, distinct
    fieldFidelity(pointee, inProgress)
  of itTuple:
    if pointee.objectName.len == 0: return wfLossy   ## `fieldPairs` names differ
    if pointee.nominalId.len > 0:
      # A cycle through this type is faithful if the rest of it is.
      if inProgress.containsOrIncl(pointee.nominalId): return wfFaithful
    var r = wfFaithful
    for f in pointee.fields: r = max(r, fieldFidelity(f, inProgress))
    if pointee.nominalId.len > 0: inProgress.excl pointee.nominalId
    r
  of itVariant:
    var r = fieldFidelity(pointee.vDiscTy, inProgress)
    for f in pointee.vPlainFieldTypes: r = max(r, fieldFidelity(f, inProgress))
    for arm in pointee.vArms:
      for f in arm.fieldTypes: r = max(r, fieldFidelity(f, inProgress))
    r
  else: wfLossy

proc witnessFidelity*(ty: IRType; noms: Table[string, IRType]): WitnessFidelity =
  ## Mirrors `emitTyAndReader`'s arms one-for-one; keep them in lockstep.
  ## `noms`: `collectNominals` over every parameter (RFC-0005 S8h).
  template worst(a, b: WitnessFidelity): WitnessFidelity = max(a, b)
  template wf(t: IRType): WitnessFidelity = witnessFidelity(t, noms)
  case ty.kind
  of itBool, itInt, itFloat32, itFloat64, itString: wfFaithful
  of itDistinct: wf(ty.distinctBase)
  of itUninterp: wfUnexecutable
  of itRef, itPtr:
    var inProgress: HashSet[string]
    refCellFidelity(ty, noms, inProgress)
  of itTuple:
    if rendersAsDefaultObject(ty): wfLossy
    else:
      var r = wfFaithful
      for f in ty.fields: r = worst(r, wf(f))
      r
  of itArray: wf(ty.elemTy)
  of itSeq:
    if isUnsupportedFieldPlaceholder(ty): wfLossy
    else:
      case ty.seqElemTy.kind
      of itInt, itFloat32, itFloat64: wfFaithful
      of itBool, itString: wfFaithful   ## RFC-0005 S8ar
      of itRef: wf(ty.seqElemTy)   ## RFC-0005 S8h
      of itDistinct:   ## RFC-0005 S8bd: the base seq, converted back
        if seqWitnessReader(ty) == swrDistinct: wfFaithful
        else: wfUnexecutable
      else:
        # RFC-0005 S8bz (item 1): a leaf-split element (S8bc) is rendered part
        # by part, so it replays; it was refused unrun here.
        if isTreeSeqElemTy(ty.seqElemTy): wf(ty.seqElemTy)
        else: wfUnexecutable   ## the reader's defensive `error()` arm
  of itTable:   # RFC-0005 S8z: every renderable shape
    if isRenderableTableTy(ty.tabKeyTy, ty.tabValTy): wfFaithful
    else: wfUnexecutable
  of itSet:
    if isRenderableSetElemTy(ty.setElemTy): wfFaithful
    else: wfUnexecutable
  of itBitSet: wfFaithful   ## RFC-0005 S8bq: every member is rendered
  of itVariant:
    var r = wf(ty.vDiscTy)
    for f in ty.vPlainFieldTypes: r = worst(r, wf(f))
    for arm in ty.vArms:
      for f in arm.fieldTypes: r = worst(r, wf(f))
    r
  of itMultiVariant:
    var r = wfFaithful
    for f in ty.mvPlainFieldTypes: r = worst(r, wf(f))
    for ax in ty.mvAxes:
      r = worst(r, wf(ax.discTy))
      for arm in ax.arms:
        for f in arm.fieldTypes: r = worst(r, wf(f))
    r

proc emitWitnessSplat*(callee: NimNode; nParams: int; witId: NimNode;
                      paramTys: seq[NimNode] = @[];
                      afterBind: NimNode = nil;
                      params: seq[IRParam] = @[];
                      globals: seq[NimNode] = @[]): NimNode =
  ## `callee(wit[0], wit[1], …)` with each argument first bound to a fresh
  ## `var` local, so `var T` parameters receive an addressable lvalue (Phase
  ## 14 A7b). Zero-cost for non-var params. Shared by `assertCoveredBy` and
  ## `emitReplayWitness` -- one splat shape for every place the library runs
  ## a SUT on a witness.
  ##
  ## RFC-0005 S10 (replay only; `assertCoveredBy` passes neither): with
  ## `paramTys` (`fn`'s DECLARED parameter types, `var` stripped) each local
  ## is bound as `wit[i]` when the rendered witness type already is the
  ## parameter type and as the conversion `T(wit[i])` otherwise -- the
  ## witness reader renders some parameter types as their carrier (a `Rune`
  ## as `int`, a `distinct` as its base) -- and a non-void `callee` has its
  ## result discarded. `afterBind` is spliced between the bindings and the
  ## call, so a caller can tell a conversion that raised from a `fn` that did.
  ##
  ## RFC-0005 S8bn (item 2): with `params` (`fn`'s IR parameters) and
  ## `globals` (the module-level `var`s `fn` can reach), a `ptr` parameter
  ## the witness aimed at a variable (`ptrAimsAt`) is handed that variable's
  ## address once the arguments are bound: a `var` parameter's own local
  ## (the one `fn` receives), or the global itself. No witness cell can be
  ## either location.
  var preamble = newStmtList()
  var call = newCall(callee)
  var pvars: seq[NimNode]
  for i in 0 ..< nParams:
    let pvar = genSym(nskVar, "pvar" & $i)
    pvars.add pvar
    let elem = nnkBracketExpr.newTree(witId, newLit(i))
    let init =
      if paramTys.len == 0: elem
      else:
        let ty = paramTys[i]
        quote do:
          (when `elem` is `ty`: `elem` else: `ty`(`elem`))
    preamble.add newTree(nnkVarSection,
      newIdentDefs(pvar, newEmptyNode(), init))
    call.add pvar
  for j in 0 ..< min(nParams, params.len):
    if params[j].ty == nil or params[j].ty.kind != itPtr: continue
    let pj = pvars[j]
    for i in 0 ..< min(nParams, params.len):
      if i == j or not params[i].isVar: continue
      let pi = pvars[i]
      let nm = newLit(params[i].name)
      preamble.add quote do:
        when typeof(addr `pi`) is typeof(`pj`):
          if ptrAimsAt(cast[pointer](`pj`), `nm`): `pj` = addr `pi`
        # RFC-0005 S8bn (item 4): or a part of it (`ptrAimPath`).
        when typeof(`pj`) is ptr:
          block:
            let pa = ptrAimPath(cast[pointer](`pj`), `nm`)
            if pa.hit:
              `pj` = ptrAimInto[typeof(`pi`), typeof(`pj`[])](`pi`, pa.path, 0)
    for g in globals:
      let nm = newLit(globalEnvPrefix & macros.strVal(owner(g)) & "." &
                      macros.strVal(g))
      preamble.add quote do:
        when typeof(addr `g`) is typeof(`pj`):
          if ptrAimsAt(cast[pointer](`pj`), `nm`): `pj` = addr `g`
        when typeof(`pj`) is ptr:
          block:
            let pa = ptrAimPath(cast[pointer](`pj`), `nm`)
            if pa.hit:
              `pj` = ptrAimInto[typeof(`g`), typeof(`pj`[])](`g`, pa.path, 0)
  if afterBind != nil: preamble.add afterBind
  if paramTys.len == 0:
    return newStmtList(preamble, call)
  let callStmt = quote do:
    when typeof(`call`) is void: `call`
    else: discard `call`
  newStmtList(preamble, callStmt)
