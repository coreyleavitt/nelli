## nelli/smt/witness_emit -- the macro-time emitters that rebuild a typed
## witness from the runtime's flat reader (`emitTyAndReader`, the witness
## tuple, the ref-cell witness context).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. `emitTyAndReader` is
## re-exported by `symex.nim`; the `{.compileTime.}` ref-witness context lives
## here and nowhere else.

import std/[macros, sets, tables, algorithm, strutils]
import ./dsl

# ---- Macro helpers (at module scope so they can recurse cleanly) ----------

proc primTyAndReader(ty: IRType): (string, string) =
  case ty.kind
  of itBool: ("bool", "readBool")
  of itInt:
    if ty.signed:
      case ty.width
      of 8:  ("int8",  "readInt8")
      of 16: ("int16", "readInt16")
      of 32: ("int32", "readInt32")
      of 64: ("int",   "readInt")
      else: ("int", "readInt")
    elif ty.width == 8 and ty.isChar:
      # RFC-0005 S8am (S8z's remainder, item 3): render a Nim `char` as
      # `char`, not `uint8` -- `isChar` is the only thing that tells a
      # `char` witness apart from a `byte`/`uint8` one (see `IRType.isChar`'s
      # field doc: all three share one structural `itInt` shape).
      ("char", "readChar")
    else:
      case ty.width
      of 8:  ("uint8",  "readUInt8")
      of 16: ("uint16", "readUInt16")
      of 32: ("uint32", "readUInt32")
      of 64: ("uint",   "readUInt")
      else: ("uint", "readUInt")
  of itFloat32: ("float32", "readFloat32")   ## Phase 15 F1
  of itFloat64: ("float",   "readFloat")     ## Phase 15 F1
  else: ("", "")

proc rendersAsDefaultObject*(ty: IRType): bool =
  ## The `itTuple` arm of `emitTyAndReader` below renders a nominal object
  ## that LOOKS like a variant (a leading `kind` field + more than two
  ## fields) as `default(Object)` instead of reading its fields -- the
  ## witness value is then NOT the solver's model. Factored out (RFC-0005
  ## S2) so `witnessFidelity` classifies exactly the shapes the reader stubs;
  ## two copies of the heuristic could drift and let a stubbed witness be
  ## replayed as if it were faithful.
  ty.kind == itTuple and ty.objectName.len > 0 and
    ty.fields.len > 2 and ty.fieldNames.len > 0 and ty.fieldNames[0] == "kind"

proc stdName(name: string): NimNode =
  ## RFC-0005 S8e. The symbol of a system/stdlib type, constructor or witness
  ## reader that `emitTyAndReader` writes into the CALLER's scope. An
  ## identifier there resolves in that scope: a caller that did not import
  ## `std/tables` has no `Table`, and a caller that declares its own `seq`
  ## or `readSeqInt` would have the witness built through it. Bound here,
  ## each name means what this module means by it, in any scope.
  case name
  of "bool": bindSym"bool"
  of "int": bindSym"int"
  of "int8": bindSym"int8"
  of "int16": bindSym"int16"
  of "int32": bindSym"int32"
  of "int64": bindSym"int64"
  of "uint": bindSym"uint"
  of "uint8": bindSym"uint8"
  of "char": bindSym"char"               # RFC-0005 S8am
  of "uint16": bindSym"uint16"
  of "uint32": bindSym"uint32"
  of "uint64": bindSym"uint64"
  of "float": bindSym"float"
  of "float32": bindSym"float32"
  of "string": bindSym"string"
  of "array": bindSym"array"
  of "seq": bindSym"seq"
  of "newSeq": bindSym"newSeq"
  of "Table": bindSym"Table"
  of "HashSet": bindSym"HashSet"
  of "readBool": bindSym"readBool"
  of "readInt": bindSym"readInt"
  of "readInt8": bindSym"readInt8"
  of "readInt16": bindSym"readInt16"
  of "readInt32": bindSym"readInt32"
  of "readUInt": bindSym"readUInt"
  of "readUInt8": bindSym"readUInt8"
  of "readChar": bindSym"readChar"       # RFC-0005 S8am
  of "readUInt16": bindSym"readUInt16"
  of "readUInt32": bindSym"readUInt32"
  of "readFloat": bindSym"readFloat"
  of "readFloat32": bindSym"readFloat32"
  of "readString": bindSym"readString"
  of "readSeqInt": bindSym"readSeqInt"
  of "readSeqInt8": bindSym"readSeqInt8"
  of "readSeqInt16": bindSym"readSeqInt16"
  of "readSeqInt32": bindSym"readSeqInt32"
  of "readSeqUInt8": bindSym"readSeqUInt8"
  of "readSeqUInt16": bindSym"readSeqUInt16"
  of "readSeqUInt32": bindSym"readSeqUInt32"
  of "readSeqUInt64": bindSym"readSeqUInt64"
  of "readSeqFloat64": bindSym"readSeqFloat64"
  of "readSeqFloat32": bindSym"readSeqFloat32"
  of "readSeqBool": bindSym"readSeqBool"          # RFC-0005 S8ar
  of "readSeqString": bindSym"readSeqString"      # RFC-0005 S8ar
  of "readTableStrInt": bindSym"readTableStrInt"
  of "readSetInt": bindSym"readSetInt"
  of "readTableAs": bindSym"readTableAs"   # RFC-0005 S8ar
  of "readSetIntAs": bindSym"readSetIntAs"             # RFC-0005 S8z
  of "readSeqAs": bindSym"readSeqAs"                   # RFC-0005 S8bc
  of "set": bindSym"set"                               # RFC-0005 S8bq
  of "readBitSetAs": bindSym"readBitSetAs"             # RFC-0005 S8bq
  of "range": bindSym"range"                           # RFC-0005 S8bv
  of "witnessIntAs": bindSym"witnessIntAs"             # RFC-0005 S8bv
  of "readSeqLen": bindSym"readSeqLen"
  of "newRefWitness": bindSym"newRefWitness"      # RFC-0005 S8h
  of "resolveRef": bindSym"resolveRef"            # RFC-0005 S8h
  of "refElemPos": bindSym"refElemPos"            # RFC-0005 S8h
  of "registerCellType": bindSym"registerCellType"  # RFC-0016 INT-81
  of "buildCellAs": bindSym"buildCellAs"            # RFC-0016 INT-81
  of "WitnessCellBuild": bindSym"WitnessCellBuild"  # RFC-0016 INT-81
  of "pointer": bindSym"pointer"                  # RFC-0016 INT-83
  of "resolvePointer": bindSym"resolvePointer"    # RFC-0016 INT-83
  else:
    error("symex RFC-0005 S8e: stdName has no binding for `" & name & "`")
    nil

proc userTypeName(ty: IRType, spelling: string): NimNode =
  ## RFC-0005 S8e. A named user type in the witness: its own SYMBOL, as
  ## `dsl_typebridge.keyedBySym` recorded it at classification. The spelling
  ## stands in only where no symbol was recorded (a type that reached the IR
  ## from something other than a symbol), which is all the emitter wrote
  ## before.
  let sym = witnessTypeSym(ty)
  if sym == nil: ident(spelling)
  elif sym.kind == nnkSym: copyNimNode(sym)
  else: copyNimTree(sym)   ## RFC-0005 S8bn: a generic instance `G[int]`

proc defaultValueOf(tyNode: NimNode): NimNode =
  ## RFC-0005 S8e. The default value of the type `tyNode` names, as
  ## `block: (var w: T; w)`. `default(T)` needs `T` as a `typedesc`, and a
  ## type SYMBOL recorded from the typed AST (`userTypeName`) carries the
  ## type itself as its node type, which `default`'s overload rejects; a
  ## declaration's type position takes the symbol as it is.
  let w = genSym(nskVar, "dflt")
  quote do:
    block:
      var `w`: `tyNode`
      `w`

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode)

proc emitTyAndReaderShared(ty: IRType, path: string,
                           witId: NimNode): (NimNode, NimNode)

var witnessRefCtx {.compileTime.}: NimNode
  ## RFC-0005 S8h. The `RefWitness` binding of the witness tuple being
  ## emitted (`emitWitnessTuple`): every `ref`/`ptr` position of one witness
  ## resolves through ONE context, so a cell shared by two positions is one
  ## Nim object bound to both.
var witnessRefCtxUsed {.compileTime.}: bool
  ## RFC-0005 S8h. Whether the tuple being emitted resolved any ref.

proc refWitnessCtx(witId: NimNode): NimNode =
  ## RFC-0005 S8h. The context a `ref` position resolves through: the
  ## enclosing `emitWitnessTuple`'s, or -- for a reader emitted outside one --
  ## a context of its own (identity is then shared within the position only).
  witnessRefCtxUsed = true
  if witnessRefCtx != nil: witnessRefCtx
  else: newCall(stdName("newRefWitness"), witId)

proc resolveRefCall(refTy: NimNode; pos, witId: NimNode): NimNode =
  ## RFC-0005 S8h. `resolveRef[refTy](ctx, pos)`. RFC-0016 INT-83: a
  ## `pointer` position is `resolvePointer(ctx, pos)`.
  if refTy.kind in {nnkIdent, nnkSym} and refTy.strVal == "pointer":
    return newCall(stdName("resolvePointer"), refWitnessCtx(witId), pos)
  newCall(nnkBracketExpr.newTree(stdName("resolveRef"), refTy),
          refWitnessCtx(witId), pos)

proc emitRefElemsReader(elemTy: NimNode; path: string; witId, n,
                        init: NimNode): NimNode =
  ## RFC-0005 S8h. The reader of a `seq`/`array` of refs: `init` is the
  ## container, `n` its element count; element `i` is the position `path[i]`.
  let contId = genSym(nskVar, "cont")
  let iId = genSym(nskForVar, "i")
  let nId = genSym(nskLet, "n")
  let pos = newCall(stdName("refElemPos"), newLit(path), iId)
  let elem = resolveRefCall(elemTy, pos, witId)
  quote do:
    block:
      let `nId` = `n`
      var `contId` = `init`
      for `iId` in 0 ..< `nId`:
        `contId`[`iId`] = `elem`
      `contId`

proc refPointeeOf*(ty: IRType): IRType =
  if ty.kind == itRef: ty.refPointeeTy else: ty.ptrPointeeTy

proc resolvesByRef*(ty: IRType): bool =
  ## RFC-0005 S8h. Whether the `ref`/`ptr` position `ty` renders through
  ## `resolveRef`: always, for a `ref`, unless it is a recursive field whose
  ## type reached the IR without a symbol; for a `ptr`, when its pointee is
  ## an object or a scalar `alloc0` can hold.
  if isPointerTy(ty): return true   # RFC-0016 INT-83: `resolvePointer`
  let pointee = refPointeeOf(ty)
  if isRecursionPlaceholder(pointee) and witnessTypeSym(pointee) == nil:
    return false
  # RFC-0005 S8bn: a `ptr string` too (S8bh retargets one like a scalar);
  # `alloc0` holds an empty string.
  ty.kind == itRef or
    pointee.kind in {itTuple, itVariant, itMultiVariant, itInt, itBool,
                     itFloat32, itFloat64, itString}

proc refWitnessTypeNode(ty: IRType; path: string; witId: NimNode): NimNode =
  ## RFC-0005 S8h. The Nim type of the `ref`/`ptr` position `ty`. A named ref
  ## alias (`type Node = ref object`) IS the ref type; a recursive field's IR
  ## pointee is an empty placeholder carrying only the symbol it was
  ## classified from -- the alias itself, or the object an inline `ref Obj`
  ## points to.
  if isPointerTy(ty): return stdName("pointer")   # RFC-0016 INT-83
  let pointee = refPointeeOf(ty)
  proc wrapped(inner: NimNode): NimNode =
    if ty.kind == itRef: nnkRefTy.newTree(inner) else: nnkPtrTy.newTree(inner)
  if isRecursionPlaceholder(pointee):
    let sym = witnessTypeSym(pointee)
    if sym == nil: return wrapped(ident(pointee.objectName))
    if sym.kind == nnkBracketExpr:
      # RFC-0005 S8bn: a generic instance; its head's declaration tells.
      let gi = sym[0].getImpl
      if gi.kind == nnkTypeDef and gi.len >= 3 and
         gi[2].kind in {nnkRefTy, nnkPtrTy}:
        return copyNimTree(sym)
      return wrapped(copyNimTree(sym))
    let impl = sym.getImpl
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind in {nnkRefTy, nnkPtrTy}:
      return copyNimNode(sym)
    return wrapped(copyNimNode(sym))
  # RFC-0005 S8l: a variant pointee of a named `ref object` case type
  # (`type VB = ref object case ...`) is spelled by that ref type itself --
  # as `nameIsRefAlias` says for a plain one. Its symbol's own declaration
  # tells (a `ref VObj` alias's pointee symbol is the value object `VObj`).
  if pointee.kind in {itVariant, itMultiVariant}:
    let sym = witnessTypeSym(pointee)
    if sym != nil and sym.kind == nnkBracketExpr:
      # RFC-0005 S8bw (item 3): a generic case object instance; its head's
      # declaration tells, as for a generic placeholder above.
      let gi = sym[0].getImpl
      if gi.kind == nnkTypeDef and gi.len >= 3 and
         gi[2].kind in {nnkRefTy, nnkPtrTy}:
        return copyNimTree(sym)
      return wrapped(copyNimTree(sym))
    if sym != nil:
      let impl = sym.getImpl
      if impl.kind == nnkTypeDef and impl.len >= 3 and
         impl[2].kind in {nnkRefTy, nnkPtrTy}:
        return copyNimNode(sym)
  # RFC-0005 S8ar: a named object or case object is spelled by its name
  # alone. `resolveRef` fills its cell generically over the Nim type
  # (`readCellField`), so its fields need no reader here; building one
  # reached `emitTyAndReader`'s unrenderable-container arms, which is why
  # `isRenderableWitnessTy` demoted a param whose pointee held one.
  let innerTy =
    if pointee.kind == itTuple and pointee.objectName.len > 0:
      userTypeName(pointee, pointee.objectName)
    elif pointee.kind == itVariant:
      userTypeName(pointee, pointee.vObjectName)
    elif pointee.kind == itMultiVariant:
      userTypeName(pointee, pointee.mvObjectName)
    else:
      emitTyAndReader(pointee, path, witId)[0]
  if pointee.kind == itTuple and pointee.nameIsRefAlias: innerTy
  else: wrapped(innerTy)

proc unrenderedReader(msg: string): NimNode =
  ## RFC-0005 S8bx (item 2). The reader of a container no witness reader
  ## reads: CR-2c's invariant guard, which fails the compile with `msg` when
  ## it is EMITTED -- a parameter whose witness reads the container (the
  ## predicate and the reader drifted). A caller that needs the container's
  ## TYPE only (a placeholder seq's element) discards it, and compiles.
  let m = newLit(msg)
  quote do:
    {.error: `m`.}

proc emitTyAndReaderShared(ty: IRType, path: string,
                           witId: NimNode): (NimNode, NimNode) =
  ## Recursive: returns (Nim type AST, witness-construction expression). The
  ## result may use one node at several places; `emitTyAndReader` unshares.
  case ty.kind
  of itUninterp:
    if ty.uninterpName == "__closure":
      # Phase 15 Cluster C (C2a, Invariant 3). A closure as a top-level SUT
      # param/result type is unsupported: a proc value cannot be reconstructed
      # as a concrete witness. Emit a `proc` placeholder + a compile-time
      # `{.warning.}` (classified, not a silent crash). Closures are constructed
      # IN-BODY (C2a) but never reach the witness reader as a top-level type.
      let placeholder = quote do:
        block:
          {.warning: "symex: a closure as a top-level SUT param/result type " &
                     "is unsupported; witness rendering yields a nil proc " &
                     "placeholder (Phase 15 Cluster C / Invariant 3).".}
          (proc (): void = discard)
      return (nnkProcTy.newTree(nnkFormalParams.newTree(newEmptyNode()),
                                newEmptyNode()), placeholder)
    if ty.uninterpName.startsWith("__unsupported:") or
       ty.uninterpName.startsWith("__unsupported_witness:") or
       ty.uninterpName.startsWith("__ownership:"):
      # RFC-0016 K2c: `__ownership:*` (`owned T`, `Atomic[T]`) is the same
      # shape: `allocateSym` raises `heUnsupportedOwnership` at parameter
      # allocation, so a top-level parameter of it reached this raise as a
      # COMPILE stop (CRH-01) instead of an `sxUnknown`.
      # RFC-chapulin-hardening CR-2b/CR-2c (Cluster 2 — Crash-totality,
      # round-2 Option 2 / Option A). Two distinct catch-alls feed this ONE
      # placeholder arm:
      #   `__unsupported:` (CR-2b)         — classifyType's param-type text-
      #                                       match catch-all.
      #   `__unsupported_witness:` (CR-2c) — `parseProc*`'s SUT parameter-
      #                                       classification loop
      #                                       (`dsl_parser.nim`), via
      #                                       `demoteUnrenderableWitnessTy`,
      #                                       when a parameter's witness
      #                                       type-tree contains — at ANY
      #                                       depth (nested in a tuple /
      #                                       object / array / variant /
      #                                       distinct / ref pointee) — a
      #                                       seq/Table/HashSet shape outside
      #                                       emitTyAndReader's renderable
      #                                       fragment. The RECURSIVE
      #                                       `isRenderableWitnessTy`
      #                                       predicate (`smt/types.nim`,
      #                                       reusing the
      #                                       `isRenderableSeqElemTy`/
      #                                       `isRenderableTableTy`/
      #                                       `isRenderableSetElemTy` leaf
      #                                       checks) decides this —
      #                                       i.e. this is CR-2c's fix for
      #                                       the `itSeq`/`itTable`/`itSet`
      #                                       `error()` sites below: the
      #                                       unrenderable shapes never
      #                                       reach them because
      #                                       `parseProc*` already routed
      #                                       them here instead. (Applied at
      #                                       the top-level parameter, NOT
      #                                       inside `classifyType` itself —
      #                                       that classifier is also used
      #                                       for purely-internal,
      #                                       non-witness types.)
      # In both cases `allocateSym` raises the classified
      # `SymexClassifiedDegradeError` (with `feUnsupportedParamType` or
      # `feUnsupportedWitnessType` respectively) at PARAMETER-ALLOCATION
      # time, before the walker ever solves for a witness — so the
      # `sxSat`/`sxRaised` codegen arms that would read this witness
      # expression are UNREACHABLE for this param (the run always resolves
      # `sxUnknown`). This placeholder therefore only needs to TYPECHECK,
      # never to be evaluated. Emit an `int` placeholder + a compile-time
      # `{.warning.}`, mirroring the `__closure` precedent above.
      # RFC-0005 S8ar: a recursive VALUE object met again inside its own
      # fields (`type O = object; kids: seq[O]`) declines as `__unsupported:`
      # but is keyed on its symbol: it only ever sits as the element type of
      # a scoped-decline field placeholder (an empty `seq[O]`), whose reader
      # needs the type's spelling and never its value.
      let recSym = witnessTypeSym(ty)
      if recSym != nil:
        let tyNode = copyNimNode(recSym)
        return (tyNode, defaultValueOf(tyNode))
      let placeholder = quote do:
        block:
          {.warning: "symex: an unsupported parameter/witness type degrades " &
                     "the whole run to sxUnknown (RFC-chapulin-hardening " &
                     "CR-2b/CR-2c / Invariant 3); witness rendering yields " &
                     "an unused int placeholder.".}
          0
      return (stdName("int"), placeholder)
    raise newException(ValueError,
      "emitTyAndReader(itUninterp): opaque-ref witness reader lands with cluster E")
  of itDistinct:
    # Phase 15 G4 (Breadth-CRIT-1). A `distinct T` param renders through the
    # eject-then-base-reader chain: extract the BASE value at the SAME path
    # (the runtime's `extractFromSymVal(svDistinct)` populated it from
    # `eject_T(distinctConst)`), then wrap it in the distinct type's
    # converter `DistinctName(baseValue)`. Without this the distinct param
    # would produce a silent empty reader.
    let (_, baseReader) = emitTyAndReader(ty.distinctBase, path, witId)
    (userTypeName(ty, ty.distinctName),
     newCall(userTypeName(ty, ty.distinctName), baseReader))
  of itBool, itInt, itFloat32, itFloat64:
    let (tyName, readerName) = primTyAndReader(ty)
    let rawReader = newCall(stdName(readerName), witId, newLit(path))
    if ty.kind == itInt and ty.enumName.len > 0:
      # Issue #163 (rev item 1). `ty` is the lifted `itInt` representation of
      # a Nim `enum` (see `IRType.enumName`'s field doc) — the RAW
      # `readUInt8`/`readUInt16`/... reader above produces a plain unsigned
      # value Nim will NOT implicitly convert back into an enum-typed slot,
      # so a bare `nnkObjConstr` field (or, via the `itArray`/itSeq` arms
      # below, an array/seq element) built from it fails to COMPILE. Wrap it
      # in the enum type's own converter call — `EnumName(rawReader)` — the
      # same `T(ordinalValue)` construction Nim itself accepts for any
      # ordinal-convertible value, sound regardless of signedness or a
      # negative/sparse ordinal domain (R2/R18's fixes already put the
      # correct width/signed/range on `ty` before this ever runs).
      if ty.enumRange:
        # RFC-0005 S8bv: an enum subrange is `range[E(lo)..E(hi)]` (a
        # `set[E]` / `seq[E]` does not fit a `set[SE]` / `seq[SE]` slot),
        # its value the ordinal converted to it.
        let e = userTypeName(ty, ty.enumName)
        let rng = newTree(nnkBracketExpr, stdName("range"),
          infix(newCall(e, newLit(ty.rangeLo)), "..",
                newCall(copyNimTree(e), newLit(ty.rangeHi))))
        (rng, newCall(newTree(nnkBracketExpr, stdName("witnessIntAs"),
                              copyNimTree(rng)),
                      newCall(stdName("int64"), rawReader)))
      else:
        (userTypeName(ty, ty.enumName),
         newCall(userTypeName(ty, ty.enumName), rawReader))
    else:
      (stdName(tyName), rawReader)
  of itTuple:
    if ty.objectName.len > 0:
      # Nominal object. For variant objects (heuristic: any of the
      # later fields would conflict with earlier branches), Nim's
      # constructor rejects per-field initialisation. Phase 5+ ships
      # a stub that returns `default(Object)` for variant cases —
      # downstream user code can examine `r.status` to verify
      # reachability. Variant-aware witness reconstruction is a
      # follow-up (#141 phase 2).
      let objTyId = userTypeName(ty, ty.objectName)
      # Check for variant: the discriminator name on the parsed
      # object is conventionally "kind" + fields after position 0
      # that would be ambiguous to construct all at once.
      # (RFC-0005 S2: the predicate is shared with `witnessFidelity`,
      # which must classify exactly the shapes this reader stubs.)
      if rendersAsDefaultObject(ty):
        (objTyId, defaultValueOf(objTyId))
      else:
        var objVal = newTree(nnkObjConstr, objTyId)
        for i, fty in ty.fields:
          let suffix = "." & ty.fieldNames[i]
          # RFC-0016 K2c: a field the walker declines (`pointer`,
          # `UncheckedArray`, ...) renders as the `int` placeholder, which is
          # not that field's type and stopped the compile. The run declines at
          # allocation, so the witness is never read; leave the field at its
          # zero value.
          if fty.kind == itUninterp and witnessTypeSym(fty) == nil and
             (fty.uninterpName.startsWith("__unsupported:") or
              fty.uninterpName.startsWith("__unsupported_witness:") or
              fty.uninterpName.startsWith("__ownership:")):
            continue
          let (_, sv) = emitTyAndReader(fty, path & suffix, witId)
          objVal.add newTree(nnkExprColonExpr,
            ident(ty.fieldNames[i]), sv)
        (objTyId, objVal)
    else:
      # Anonymous: nnkTupleConstr (positional) or nnkTupleTy (named).
      let named = ty.fieldNames.len > 0 and ty.fieldNames[0].len > 0
      var subTy = if named: newTree(nnkTupleTy) else: newTree(nnkTupleConstr)
      var subVal = newTree(nnkTupleConstr)
      for i, fty in ty.fields:
        let suffix = if ty.fieldNames[i].len > 0: "." & ty.fieldNames[i]
                     else: "." & $i
        let (st, sv) = emitTyAndReader(fty, path & suffix, witId)
        if named:
          subTy.add newTree(nnkIdentDefs,
            ident(ty.fieldNames[i]), st, newEmptyNode())
          subVal.add newTree(nnkExprColonExpr,
            ident(ty.fieldNames[i]), sv)
        else:
          subTy.add st
          subVal.add sv
      (subTy, subVal)
  of itArray:
    let (elemTyNode, _) = emitTyAndReader(ty.elemTy, path & ".0", witId)
    # RFC-0005 S8am (S8z's remainder, item 5): a non-zero-based array
    # (`array[1..3, int]`, `ty.lo == 1`) renders its DECLARED index range
    # (`array[1..3, int]`), not Nim's `array[N, T]` sugar -- that sugar
    # always means `array[0..N-1, T]`, so a witness built from it alone was
    # typed `array[0..2, int]` for a `array[1..3, int]` parameter: same
    # length, same positional values (replay stays exact), but not the
    # parameter's own type (a caller could not assign it back to a slot
    # declared with the real type without a conversion). The element
    # LITERAL stays purely positional either way (`arrLit`, below) -- Nim's
    # `[v0, v1, v2]` bracket literal needs no index annotations regardless
    # of the target array's index origin.
    let arrIdxNode =
      if ty.lo == 0: newLit(ty.size)
      else: infix(newLit(ty.lo), "..", newLit(ty.lo + int64(ty.size) - 1))
    let arrTy = newTree(nnkBracketExpr,
      stdName("array"), arrIdxNode, elemTyNode)
    if ty.elemTy.kind in {itRef, itPtr} and resolvesByRef(ty.elemTy):
      # RFC-0005 S8f/S8h: element `i` is the position `path[i]`.
      return (arrTy, emitRefElemsReader(elemTyNode, path, witId,
                                        newLit(ty.size),
                                        defaultValueOf(arrTy)))
    var arrLit = newTree(nnkBracket)
    for i in 0 ..< ty.size:
      let (_, sv) = emitTyAndReader(ty.elemTy, path & "." & $i, witId)
      arrLit.add sv
    (arrTy, arrLit)
  of itString:
    (stdName("string"), newCall(stdName("readString"), witId, newLit(path)))
  of itSeq:
    # RFC-0005 S8bx (item 2): one classifier, shared with
    # `isRenderableWitnessTy`, picks the reader (`seqWitnessReader`).
    case seqWitnessReader(ty)
    of swrPlaceholder:
      # Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution
      # 2026-08-15): a declared field whose element kind is unbacked (e.g.
      # `seq[(string,string)]`) — `runtime.nim`'s `allocateSym` never
      # populated real witness content for it (`seqLen` was forced `== 0`,
      # `seqDataRaw` is inert), so render a type-correct EMPTY `seq[T]`
      # literal instead of a real reader call — content is never modeled
      # or trusted for this field regardless (any SUT read was already
      # intercepted at parse time, forcing `sxUnknown` before this witness
      # would ever be examined). Recurses ONLY for the element TYPE (the
      # discarded `_` value half never gets emitted, so it is safe even
      # though it would reference witness data that was never written —
      # mirrors the `itArray`/`itRef` arms' existing "type-only" recursion
      # idiom above).
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      let seqTy = newTree(nnkBracketExpr, stdName("seq"), elemTyNode)
      (seqTy, newCall(newTree(nnkBracketExpr, stdName("newSeq"), elemTyNode), newLit(0)))
    of swrDistinct:
      # RFC-0005 S8bd. A `seq[D]`, `D` a chain of `distinct` over an int or
      # float (`seqWitnessReader`): the cells hold the base
      # (`seqCellTy`, S8ba), so they are read as the base seq, and each
      # element is converted back through the chain, innermost first
      # (`Km(Meters(int(x)))`). Every conversion keeps the value.
      let cell = seqCellTy(ty.seqElemTy)
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      let (_, baseReader) = emitTyAndReader(tSeq(cell), path, witId)
      let (cellTyNode, _) = emitTyAndReader(cell, path & ".0", witId)
      let raw = genSym(nskLet, "rawSeq")
      let res = genSym(nskVar, "distinctSeq")
      let k = genSym(nskForVar, "k")
      proc conv(t: IRType; x: NimNode): NimNode =
        if t.kind == itDistinct:
          newCall(userTypeName(t, t.distinctName), conv(t.distinctBase, x))
        else:
          newCall(cellTyNode, x)
      let elemConv = conv(ty.seqElemTy, newTree(nnkBracketExpr, raw, k))
      # System's `len` and `..<`, bound here (RFC-0005 S8e: the caller's
      # scope may shadow either).
      let lenCall = newCall(bindSym"len", raw)
      let upTo = bindSym"..<"
      let newSeqCall = newCall(newTree(nnkBracketExpr, stdName("newSeq"),
                                       elemTyNode), copyNimTree(lenCall))
      let reader = quote do:
        block:
          let `raw` = `baseReader`
          var `res` = `newSeqCall`
          for `k` in `upTo`(0, `lenCall`):
            `res`[`k`] = `elemConv`
          `res`
      (newTree(nnkBracketExpr, stdName("seq"), elemTyNode), reader)
    of swrInt64:
      # Phase 5 cycle 1: only seq[int] tested; specialised reader.
      (newTree(nnkBracketExpr, stdName("seq"), stdName("int")),
       newCall(stdName("readSeqInt"), witId, newLit(path)))
    of swrScalarAs:
      # RFC-0005 S8bc: a `char` or enum element. The fixed-width arm below
      # keys on width and signedness only, so `seq[char]` and `seq[Col]`
      # were spelled `seq[uint8]`: a top-level witness did not replay at
      # the parameter's type, and an object field of either type failed
      # the compile (`seq[uint8]` assigned to a `seq[char]` slot). The
      # element type is rendered as a scalar of it is (`char`, the enum),
      # and read through `readSeqAs[T]`.
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      (newTree(nnkBracketExpr, stdName("seq"), elemTyNode),
       newCall(newTree(nnkBracketExpr, stdName("readSeqAs"),
                       copyNimTree(elemTyNode)),
               witId, newLit(path)))
    of swrFixedInt:
      # RFC-chapulin-hardening M1: fixed-width-int seq elements
      # (`byte`/`uint8..uint64`, `int8..int32` — `int64` is the arm above).
      # `extractSeqElements`/`allocateSeqDataRaw`/`seqElemAt` (runtime.nim)
      # already dispatch on `(signed, width)` for every one of these widths
      # (Phase 15 C4/seqElemAt plumbing); only the POST-SOLVE reader side was
      # missing a case, hard-`error()`ing at macro-expansion (CR-2c's
      # catch-all below). `isRenderableSeqElemTy` (`smt/types.nim`) is widened
      # in lockstep so CR-2c's `demoteUnrenderableWitnessTy` no longer demotes
      # these shapes to a placeholder before this arm is ever reached.
      let sTy = ty.seqElemTy
      let (elemTyName, readerName) =
        if sTy.signed:
          case sTy.width
          of 8:  ("int8",  "readSeqInt8")
          of 16: ("int16", "readSeqInt16")
          of 32: ("int32", "readSeqInt32")
          else:  ("int64", "readSeqInt")   ## unreachable: signed+64 handled above
        else:
          case sTy.width
          of 8:  ("uint8",  "readSeqUInt8")
          of 16: ("uint16", "readSeqUInt16")
          of 32: ("uint32", "readSeqUInt32")
          else:  ("uint64", "readSeqUInt64")
      (newTree(nnkBracketExpr, stdName("seq"), stdName(elemTyName)),
       newCall(stdName(readerName), witId, newLit(path)))
    of swrBool:   ## RFC-0005 S8ar
      (newTree(nnkBracketExpr, stdName("seq"), stdName("bool")),
       newCall(stdName("readSeqBool"), witId, newLit(path)))
    of swrString:   ## RFC-0005 S8ar
      (newTree(nnkBracketExpr, stdName("seq"), stdName("string")),
       newCall(stdName("readSeqString"), witId, newLit(path)))
    of swrFloat64:   ## Phase 15 F9b
      (newTree(nnkBracketExpr, stdName("seq"), stdName("float")),
       newCall(stdName("readSeqFloat64"), witId, newLit(path)))
    of swrFloat32:   ## Phase 15 F9b
      (newTree(nnkBracketExpr, stdName("seq"), stdName("float32")),
       newCall(stdName("readSeqFloat32"), witId, newLit(path)))
    of swrTree:
      # RFC-0005 S8bc (item 3): a seq of a by-value tuple, object, array or
      # case object, held leaf-split. Each element is written in the heap's
      # cell layout (`extractTreeValue`) and read as a cell field is
      # (`readSeqAs` -> `readCellField`); only the element's TYPE comes from
      # the recursion.
      # RFC-0005 S8bl (item 4): an element with a ref part reads through
      # the witness tuple's `RefWitness`, whose positions the element's
      # refs are (`collectTreeRefPositions`).
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      let src = if treeHasRefPart(ty.seqElemTy): refWitnessCtx(witId)
                else: witId
      (newTree(nnkBracketExpr, stdName("seq"), elemTyNode),
       newCall(newTree(nnkBracketExpr, stdName("readSeqAs"),
                       copyNimTree(elemTyNode)),
               src, newLit(path)))
    of swrRef:   ## Phase 15 R3 (ADR-0010): seq[ref T]
      # RFC-0005 S8f/S8h: element `i` is the position `path[i]` -- nil, the
      # same object as any other position holding its address (an earlier
      # element, a param), or its own cell. (R3 rendered each element a
      # fresh default cell; S8f rebuilt each from its leaves, with identity
      # only among elements.)
      let (elemTy, _) = emitTyAndReader(ty.seqElemTy, path & "[0]", witId)
      let lenCall = newCall(stdName("readSeqLen"), witId, newLit(path))
      let reader = emitRefElemsReader(elemTy, path, witId, lenCall,
        newCall(nnkBracketExpr.newTree(stdName("newSeq"), elemTy), lenCall))
      (newTree(nnkBracketExpr, stdName("seq"), elemTy), reader)
    of swrNone:
      # RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality): no
      # parameter whose witness READS this seq reaches here --
      # `demoteUnrenderableWitnessTy` (`dsl_parser.nim`) routes any parameter
      # `isRenderableWitnessTy` rejects to an `__unsupported_witness:`
      # placeholder, and that predicate judges a seq on this same
      # classifier. RFC-0005 S8bx (item 2): a seq whose TYPE alone is
      # needed does reach here -- the element of a placeholder seq of seqs,
      # whose reader is discarded -- so the type is rendered, and the guard
      # rides the reader: it fails the compile only where it is emitted
      # (was a macro-time `error()`, which failed every such type).
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      (newTree(nnkBracketExpr, stdName("seq"), elemTyNode),
       unrenderedReader("seq witness reader for " & $ty &
                        " not yet implemented"))
  of itTable:
    # Phase 5 cycle 5: Table[string, int]. RFC-0005 S8z: and every other
    # renderable value type, read through `readTableAs[K, V]` (S8ar).
    if ty.tabKeyTy.kind == itString and
       ty.tabValTy.kind == itInt and ty.tabValTy.signed and
       ty.tabValTy.width == 64 and ty.tabValTy.enumName.len == 0:
      let tabTy = newTree(nnkBracketExpr,
        stdName("Table"), stdName("string"), stdName("int"))
      (tabTy, newCall(stdName("readTableStrInt"), witId, newLit(path)))
    elif isRenderableTableTy(ty.tabKeyTy, ty.tabValTy):
      # RFC-0005 S8ar: every backed key and value type, `readTableAs[K, V]`
      # (was `readTableStrIntAs[V]`: a string key and an integer value).
      let (keyTyNode, _) = emitTyAndReader(ty.tabKeyTy, path, witId)
      let (valTyNode, _) = emitTyAndReader(ty.tabValTy, path, witId)
      let tabTy = newTree(nnkBracketExpr,
        stdName("Table"), keyTyNode, valTyNode)
      (tabTy, newCall(newTree(nnkBracketExpr, stdName("readTableAs"),
                              copyNimTree(keyTyNode), copyNimTree(valTyNode)),
                      witId, newLit(path)))
    else:
      # CR-2c: no parameter whose witness READS this Table reaches here --
      # see the `itSeq` arm's `swrNone`. `isRenderableWitnessTy` applies
      # `isRenderableTableTy` at every Table leaf. RFC-0005 S8bx (item 2):
      # the type alone is rendered (a field of a placeholder seq's element),
      # and the guard rides the reader.
      let (keyTyNode, _) = emitTyAndReader(ty.tabKeyTy, path, witId)
      let (valTyNode, _) = emitTyAndReader(ty.tabValTy, path, witId)
      (newTree(nnkBracketExpr, stdName("Table"), keyTyNode, valTyNode),
       unrenderedReader("symex Phase 5: only Table[string, int] supported " &
                        "(got " & $ty & ")"))
  of itSet:
    if ty.setElemTy.kind == itInt and ty.setElemTy.signed and
       ty.setElemTy.width == 64 and ty.setElemTy.enumName.len == 0:
      let setTy = newTree(nnkBracketExpr, stdName("HashSet"), stdName("int"))
      (setTy, newCall(stdName("readSetInt"), witId, newLit(path)))
    elif isRenderableSetElemTy(ty.setElemTy):   # RFC-0005 S8z
      let (elemTyNode, _) = emitTyAndReader(ty.setElemTy, path, witId)
      let setTy = newTree(nnkBracketExpr, stdName("HashSet"), elemTyNode)
      (setTy, newCall(newTree(nnkBracketExpr, stdName("readSetIntAs"),
                              copyNimTree(elemTyNode)),
                      witId, newLit(path)))
    else:
      # CR-2c: no parameter whose witness READS this HashSet reaches here --
      # see the `itSeq` arm's `swrNone`. `isRenderableWitnessTy` applies
      # `isRenderableSetElemTy` at every HashSet leaf. RFC-0005 S8bx (item
      # 2): the type alone is rendered, and the guard rides the reader.
      let (elemTyNode, _) = emitTyAndReader(ty.setElemTy, path, witId)
      (newTree(nnkBracketExpr, stdName("HashSet"), elemTyNode),
       unrenderedReader("symex Phase 5: only HashSet[int] supported"))
  of itBitSet:
    # RFC-0005 S8bq: a builtin `set[T]`, from the members the runtime
    # extracted (`bitSetModelMembers`); `T`'s own reader names the type.
    var (elemTyNode, _) = emitTyAndReader(ty.bsElemTy, path, witId)
    let et = ty.bsElemTy
    if et.kind == itInt and et.hasRange and et.enumName.len == 0:
      # RFC-0005 S8bv: a `set[range[lo..hi]]` names its range, not the
      # range's base (`set[int]` does not compile: too large).
      elemTyNode = newTree(nnkBracketExpr, stdName("range"),
        infix(newCall(elemTyNode, newLit(et.rangeLo)), "..",
              newCall(copyNimTree(elemTyNode), newLit(et.rangeHi))))
    let setTy = newTree(nnkBracketExpr, stdName("set"), elemTyNode)
    (setTy, newCall(newTree(nnkBracketExpr, stdName("readBitSetAs"),
                            copyNimTree(elemTyNode)),
                    witId, newLit(path)))
  of itVariant:
    # Phase 11 cycle 7 + plain-field sharing (post-cycle-12) —
    # construct the variant on the arm Z3 picked. Witness layout
    # written by `extractFromSymVal`:
    #   <path>.<discName>            discriminator value
    #   <path>.<plainFieldName>      plain (shared) field values
    #   <path>.@<tagOrdinal>.<field> arm-specific field values
    # Plain fields appear in every arm's constructor at their
    # shared witness path — so the same value is read from the
    # same path in every case branch, which Nim's runtime sees as
    # one shared symbolic value (matching Nim's variant memory
    # layout where plain fields are always-present and shared).
    let objTyId = userTypeName(ty, ty.vObjectName)
    let discPath = path & "." & ty.vDiscName
    let (discTyId, discReaderExpr) =
      emitTyAndReader(ty.vDiscTy, discPath, witId)
    var caseStmt = newTree(nnkCaseStmt, discReaderExpr)
    # Identify the else arm (if any). Phase 14 cycle A2 (ADR-0003 D2):
    # the else arm cannot be rendered as a static-disc nnkObjConstr
    # because its discriminator is dynamic. Render it via
    # `block: var w: V; w.kind = readDisc; w.<plain> = ...; w.<armF> = ...; w`
    # which Nim accepts since each assignment respects the at-that-
    # moment arm shape.
    var elseArm: VariantArm
    var hasElse = false
    for arm in ty.vArms:
      if arm.isElse: elseArm = arm; hasElse = true
    for arm in ty.vArms:
      if arm.isElse: continue
      let tagLit = newCall(discTyId, newLit(arm.tagOrdinal))
      var ctor = newTree(nnkObjConstr, objTyId)
      # Plain fields first (in source order).
      for i, fname in ty.vPlainFieldNames:
        let fty = ty.vPlainFieldTypes[i]
        let plainPath = path & "." & fname
        let (_, fReader) = emitTyAndReader(fty, plainPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      # Discriminator literal. Non-enum discs (Phase 14 A3) carry an
      # empty tagName — Nim accepts an int literal for `range`-typed
      # fields, so fall back to `newLit(tagOrdinal)`. RFC-0005 S8e: an
      # enum member is written `DiscTy(ordinal)` through the disc type's
      # symbol, never by its member name -- the caller's scope need not
      # hold the enum (it imported only the SUT), and may hold another
      # symbol of that spelling.
      let discValExpr =
        if arm.tagName.len > 0: newCall(discTyId, newLit(arm.tagOrdinal))
        else: newLit(arm.tagOrdinal)
      ctor.add nnkExprColonExpr.newTree(
        ident(ty.vDiscName), discValExpr)
      # Arm-specific fields.
      for j, fname in arm.fieldNames:
        let fty = arm.fieldTypes[j]
        let armPath = path & ".@" & $arm.tagOrdinal & "." & fname
        let (_, fReader) = emitTyAndReader(fty, armPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
    if hasElse:
      # For each disc-enum ordinal NOT covered by a non-else arm,
      # emit one `of <tagName>:` branch with a static discriminator
      # literal. Static-disc construction sidesteps the runtime
      # discriminant transition check that breaks the `var w` path.
      # `vDiscTags` carries the enum's full (name, ord) domain so we
      # have a concrete Nim identifier for each else-covered value.
      var nonElseOrds: seq[int]
      for arm in ty.vArms:
        if not arm.isElse: nonElseOrds.add arm.tagOrdinal
      for dt in ty.vDiscTags:
        if dt.ord in nonElseOrds: continue
        let tagLit = newCall(discTyId, newLit(dt.ord))
        var ctor = newTree(nnkObjConstr, objTyId)
        for i, fname in ty.vPlainFieldNames:
          let (_, fReader) = emitTyAndReader(
            ty.vPlainFieldTypes[i], path & "." & fname, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        ctor.add nnkExprColonExpr.newTree(
          ident(ty.vDiscName), newCall(discTyId, newLit(dt.ord)))  # RFC-0005 S8e
        for j, fname in elseArm.fieldNames:
          let armPath = path & ".@" & $elseArm.tagOrdinal & "." & fname
          let (_, fReader) = emitTyAndReader(
            elseArm.fieldTypes[j], armPath, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
      # RFC-0005 S8f. A NON-enum (`range[lo..hi]`) discriminator has no
      # `vDiscTags`, so the loop above rendered no branch for an
      # else-covered value: a `W(kind: 5, e: 42)` witness fell to the
      # `default` below and rendered `kind: 0, e: 0` -- a clean `sxSat`
      # whose witness never reached the target (#163 W6's own fixture).
      # Render ONE branch over the else arm's whole value set -- the
      # declared range minus the explicit tags, as ordinal intervals --
      # constructing with the discriminator bound to the case selector's
      # `let`: Nim accepts a runtime discriminator in an object constructor
      # when the enclosing `case` on that `let` proves its branch -- and
      # only for a discriminator type of at most 2^16 values, the limit
      # Nim puts on that proof (a wider range keeps the old fallback).
      if ty.vDiscTags.len == 0 and ty.vDiscTy.hasRange and
         ty.vDiscTy.rangeHi - ty.vDiscTy.rangeLo < 65536:
        var ranges: seq[NimNode]
        var lo = ty.vDiscTy.rangeLo
        let hi = ty.vDiscTy.rangeHi
        var explicit: seq[int64]
        for o in nonElseOrds: explicit.add int64(o)
        explicit.sort()
        proc addRun(ranges: var seq[NimNode]; a, b: int64) =
          if a > b: return
          let la = newCall(discTyId, newLit(a))
          if a == b: ranges.add la
          else: ranges.add infix(la, "..", newCall(discTyId, newLit(b)))
        for o in explicit:
          if o < lo or o > hi: continue
          addRun(ranges, lo, o - 1)
          lo = o + 1
        addRun(ranges, lo, hi)
        if ranges.len > 0:
          let selId = genSym(nskLet, "discSel")
          var ctor = newTree(nnkObjConstr, objTyId)
          for i, fname in ty.vPlainFieldNames:
            let (_, fReader) = emitTyAndReader(
              ty.vPlainFieldTypes[i], path & "." & fname, witId)
            ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
          ctor.add nnkExprColonExpr.newTree(ident(ty.vDiscName), selId)
          for j, fname in elseArm.fieldNames:
            let armPath = path & ".@" & $elseArm.tagOrdinal & "." & fname
            let (_, fReader) = emitTyAndReader(
              elseArm.fieldTypes[j], armPath, witId)
            ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
          var ofBr = newTree(nnkOfBranch)
          for r in ranges: ofBr.add r
          ofBr.add ctor
          caseStmt.add ofBr
          caseStmt[0] = selId
          caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
          # The selector must have the FIELD's own type (the reader's
          # `discTyId` is the range's base type).
          let fieldTy = newCall(ident"typeof", newDotExpr(
            defaultValueOf(objTyId), ident(ty.vDiscName)))
          let blk = newStmtList(
            newLetStmt(selId, newCall(fieldTy, discReaderExpr)), caseStmt)
          return (objTyId, newBlockStmt(blk))
    caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
    (objTyId, caseStmt)
  of itMultiVariant:
    # Phase 14 cycle A1d per ADR-0003 D1. Emit nested case
    # statements — one per axis, outer to inner — and at the
    # deepest level construct the object with plain fields + each
    # axis's chosen disc + that axis's active-arm fields. Witness
    # paths must match what `extractFromSymVal` writes for
    # svMultiVariant (runtime.nim ~1364-1374):
    #   <path>.<plainName>                         plain (shared)
    #   <path>.<discName>                          axis discriminator
    #   <path>.<discName>.@<tagOrdinal>.<fname>    arm-specific
    # `fields(w)` on the constructed object iterates active-arm
    # order: plain..., axis1, arm1-fields, axis2, arm2-fields...
    # which matches `renderAsChoices`'s iteration contract.
    let objTyId = userTypeName(ty, ty.mvObjectName)
    type AxisBind = tuple[
      discName: string,
      tagVal: NimNode,   ## RFC-0005 S8e: `DiscTy(ordinal)`, not the member name
      armFieldNames: seq[string],
      armFieldReaders: seq[NimNode]]
    proc emitMVBranch(axisIdx: int,
                      chosen: seq[AxisBind]): NimNode =
      if axisIdx == ty.mvAxes.len:
        var ctor = newTree(nnkObjConstr, objTyId)
        for i, fname in ty.mvPlainFieldNames:
          let (_, fReader) = emitTyAndReader(
            ty.mvPlainFieldTypes[i], path & "." & fname, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        for ab in chosen:
          ctor.add nnkExprColonExpr.newTree(
            ident(ab.discName), ab.tagVal)
          for j, fn in ab.armFieldNames:
            ctor.add nnkExprColonExpr.newTree(
              ident(fn), ab.armFieldReaders[j])
        return ctor
      let ax = ty.mvAxes[axisIdx]
      let discPath = path & "." & ax.discName
      let (discTyId, discReaderExpr) =
        emitTyAndReader(ax.discTy, discPath, witId)
      var caseStmt = newTree(nnkCaseStmt, discReaderExpr)
      # RFC-0005 S8s: an `else` arm renders one branch per enum ordinal it
      # covers (`discTags` minus the explicit arms), each with that static
      # discriminator, as the single-`case` emitter does. It used to render
      # its sentinel ordinal (`DiscTy(-1)`, a compile error).
      var nonElseOrds: seq[int]
      for arm in ax.arms:
        if not arm.isElse: nonElseOrds.add arm.tagOrdinal
      for arm in ax.arms:
        var tagOrds: seq[int]
        if arm.isElse:
          for dt in ax.discTags:
            if dt.ord notin nonElseOrds: tagOrds.add dt.ord
        else:
          tagOrds.add arm.tagOrdinal
        for tagOrd in tagOrds:
          let tagLit = newCall(discTyId, newLit(tagOrd))
          var armReaders: seq[NimNode]
          for j, fn in arm.fieldNames:
            let armPath = path & "." & ax.discName &
                          ".@" & $arm.tagOrdinal & "." & fn
            let (_, fr) = emitTyAndReader(arm.fieldTypes[j], armPath, witId)
            armReaders.add fr
          let body = emitMVBranch(axisIdx + 1, chosen & @[
            (discName: ax.discName, tagVal: newCall(discTyId, newLit(tagOrd)),
             armFieldNames: arm.fieldNames, armFieldReaders: armReaders)])
          caseStmt.add nnkOfBranch.newTree(tagLit, body)
      # RFC-0005 S8s: a NON-enum (`range[lo..hi]`) discriminator has no
      # `discTags`, so the loop above rendered no branch for an else-covered
      # value. Since S8s `allocateSym` admits those values (the axis's
      # declared range), so render them as the single-`case` emitter does
      # (RFC-0005 S8f): ONE branch over the range minus the explicit tags,
      # the discriminator bound to the case selector's `let`, only for a
      # discriminator type of at most 2^16 values (Nim's limit on proving a
      # runtime discriminator; a wider range keeps the fallback, whose
      # witness replay refutes).
      var elseArmIx = -1
      for i, arm in ax.arms:
        if arm.isElse: elseArmIx = i
      if elseArmIx >= 0 and ax.discTags.len == 0 and ax.discTy.hasRange and
         ax.discTy.rangeHi - ax.discTy.rangeLo < 65536:
        let elseArm = ax.arms[elseArmIx]
        var ranges: seq[NimNode]
        var lo = ax.discTy.rangeLo
        let hi = ax.discTy.rangeHi
        var explicit: seq[int64]
        for o in nonElseOrds: explicit.add int64(o)
        explicit.sort()
        proc addRun(ranges: var seq[NimNode]; a, b: int64) =
          if a > b: return
          let la = newCall(discTyId, newLit(a))
          if a == b: ranges.add la
          else: ranges.add infix(la, "..", newCall(discTyId, newLit(b)))
        for o in explicit:
          if o < lo or o > hi: continue
          addRun(ranges, lo, o - 1)
          lo = o + 1
        addRun(ranges, lo, hi)
        if ranges.len > 0:
          let selId = genSym(nskLet, "discSel")
          var armReaders: seq[NimNode]
          for j, fn in elseArm.fieldNames:
            let armPath = path & "." & ax.discName &
                          ".@" & $elseArm.tagOrdinal & "." & fn
            let (_, fr) = emitTyAndReader(elseArm.fieldTypes[j], armPath, witId)
            armReaders.add fr
          let body = emitMVBranch(axisIdx + 1, chosen & @[
            (discName: ax.discName, tagVal: selId,
             armFieldNames: elseArm.fieldNames, armFieldReaders: armReaders)])
          var ofBr = newTree(nnkOfBranch)
          for r in ranges: ofBr.add r
          ofBr.add body
          caseStmt.add ofBr
          caseStmt[0] = selId
          caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
          let fieldTy = newCall(ident"typeof", newDotExpr(
            defaultValueOf(objTyId), ident(ax.discName)))
          return newBlockStmt(newStmtList(
            newLetStmt(selId, newCall(fieldTy, discReaderExpr)), caseStmt))
      # Else covers any out-of-set disc value; same defensive
      # fallback as itVariant (line 599).
      caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
      caseStmt
    (objTyId, emitMVBranch(0, @[]))
  of itRef, itPtr:
    # RFC-0005 S8h. A `ref T`/`ptr T` position resolves through the witness's
    # `RefWitness` (`resolveRef`): nil, the object already built for another
    # position holding the same model address, or a cell built once and
    # filled from the model's INPUT heap. The fill is generic over the Nim
    # type, so a recursive field, a cycle and a case object reached through
    # a field render like a top-level param.
    #
    # Replaces Phase 15 R1/R9 and Cluster H Step C's readers, each of which
    # built a fresh object from leaves at `path`: a nil param rendered
    # non-nil, two params at one address rendered two objects, a recursive
    # field (an empty IR placeholder) rendered `nil` even when the path had
    # proved it live, and the fields rendered the heap the SUT had written by
    # the end of the path, not the one it was called with.
    let refTy = refWitnessTypeNode(ty, path, witId)
    if not resolvesByRef(ty):
      # A recursive field whose type reached the IR without a symbol, or a
      # `ptr` to a pointee `resolveRef` cannot allocate (an `UncheckedArray`,
      # a container): no Nim type to build the cell as. `witnessFidelity`
      # classifies it `wfUnexecutable`, so replay never trusts it.
      let placeholder = quote do:
        block:
          {.warning: "symex: this `ref`/`ptr` witness position renders as " &
                     "`nil`: no cell of its pointee type can be built " &
                     "(RFC-0005 S8h).".}
          nil
      return (refTy, placeholder)
    (refTy, resolveRefCall(refTy, newLit(path), witId))

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode) =
  ## Returns (Nim type AST, witness-construction expression) for `ty` at
  ## witness path `path`. RFC-0005 S8e: every node of the result is its own
  ## copy. The builder above places one type node at several positions (a
  ## variant's type in each arm's constructor and in its `default`, a disc
  ## type in every tag conversion). With identifiers that was harmless; a
  ## SYMBOL node is annotated in place by semantic checking, so a shared one
  ## checked as a constructor head reaches the next position already typed as
  ## a value of the type, not the type itself.
  let (t, r) = emitTyAndReaderShared(ty, path, witId)
  (copyNimTree(t), copyNimTree(r))

proc irTypeHoldsPtr(t: IRType; depth = 0): bool =
  ## RFC-0005 S8bn (item 1). A value of type `t` holds a `ptr` somewhere
  ## (conservative past a depth bound).
  if t == nil: return false
  if depth > 8: return true
  case t.kind
  of itPtr: true
  of itRef: irTypeHoldsPtr(t.refPointeeTy, depth + 1)
  of itTuple:
    for f in t.fields:
      if irTypeHoldsPtr(f, depth + 1): return true
    false
  of itArray: irTypeHoldsPtr(t.elemTy, depth + 1)
  of itSeq: irTypeHoldsPtr(t.seqElemTy, depth + 1)
  of itDistinct: irTypeHoldsPtr(t.distinctBase, depth + 1)
  else: false

proc collectHierPointees(ty: IRType; acc: var seq[IRType];
                         seen: var HashSet[string]; depth = 0) =
  ## RFC-0016 INT-81. Every hierarchy object type a `ref`/`ptr` position in
  ## the type tree `ty` points to (a recursive field's placeholder too: it
  ## carries its chain).
  if ty == nil or depth > 16: return
  case ty.kind
  of itRef, itPtr:
    let p = refPointeeOf(ty)
    let c = hierChain(p)
    if c.len > 0 and not seen.containsOrIncl(c.join("/")): acc.add p
    collectHierPointees(p, acc, seen, depth + 1)
  of itTuple:
    for f in ty.fields: collectHierPointees(f, acc, seen, depth + 1)
  of itArray: collectHierPointees(ty.elemTy, acc, seen, depth + 1)
  of itSeq: collectHierPointees(ty.seqElemTy, acc, seen, depth + 1)
  of itDistinct: collectHierPointees(ty.distinctBase, acc, seen, depth + 1)
  of itVariant:
    for f in ty.vPlainFieldTypes: collectHierPointees(f, acc, seen, depth + 1)
    for arm in ty.vArms:
      for f in arm.fieldTypes: collectHierPointees(f, acc, seen, depth + 1)
  of itMultiVariant:
    for f in ty.mvPlainFieldTypes: collectHierPointees(f, acc, seen, depth + 1)
    for ax in ty.mvAxes:
      for arm in ax.arms:
        for f in arm.fieldTypes: collectHierPointees(f, acc, seen, depth + 1)
  else: discard

proc witnessCellTypes*(params: seq[IRParam]): seq[IRType] =
  ## RFC-0016 INT-81. The dynamic types a cell of a witness of `params` may
  ## have: every hierarchy object type its positions point to, and every
  ## type of those hierarchies whose run-type tag a walk tests
  ## (`hierFamily`), each once.
  var seen: HashSet[string]
  var direct: seq[IRType]
  for p in params: collectHierPointees(p.ty, direct, seen)
  var roots: seq[string]
  for t in direct:
    let r = hierChain(t)[0]
    if r notin roots: roots.add r
  result = direct
  for r in roots:
    for t in hierFamily(r):
      if not seen.containsOrIncl(hierChain(t).join("/")): result.add t

proc cellTypeNameable*(t: IRType): bool =
  ## RFC-0016 INT-81. A witness can build a cell as `t`: a symbol names it
  ## (`keyedBySym`) wherever the witness is emitted.
  witnessTypeSym(t) != nil

proc emitCellTypes(params: seq[IRParam]; ctxId, witId: NimNode): NimNode =
  ## RFC-0016 INT-81. Register with the witness's `RefWitness` each dynamic
  ## type a cell may have (`witnessCellTypes`): its run-type tag codes and
  ## its builder (`buildCellAs`), nil for a type no symbol names.
  result = newStmtList()
  for t in witnessCellTypes(params):
    let c = hierChain(t)
    # A root needs none: a cell no deeper is built as its position's type.
    if c.len < 2: continue
    var codes = nnkBracket.newTree()
    for i in 1 ..< c.len: codes.add newLit(inheritTagCode(c[i]))
    let build =
      if cellTypeNameable(t):
        newTree(nnkBracketExpr, stdName("buildCellAs"),
                refWitnessTypeNode(tRef(t), "", witId))
      else:
        newCall(stdName("WitnessCellBuild"), newNilLit())
    result.add newCall(stdName("registerCellType"), ctxId,
                       nnkPrefix.newTree(ident"@", codes), build)

proc emitWitnessTuple*(params: seq[IRParam]; witId: NimNode): (NimNode, NimNode) =
  ## The witness tuple of `params` over the `RawWitness` `witId`: (its type,
  ## its value). RFC-0005 S8h: every `ref`/`ptr` position in it resolves
  ## through ONE `RefWitness`, bound once around the tuple, so a cell held by
  ## two params (or a param and a field, or two elements) is one object.
  let ctxId = genSym(nskLet, "refWit")
  let (savedCtx, savedUsed) = (witnessRefCtx, witnessRefCtxUsed)
  witnessRefCtx = ctxId
  witnessRefCtxUsed = false
  var tupleTy = newTree(nnkTupleConstr)
  var tup = newTree(nnkTupleConstr)
  var vals: seq[NimNode]
  for p in params:
    let (pTy, pVal) = emitTyAndReader(p.ty, p.name, witId)
    tupleTy.add pTy
    tup.add pVal
    vals.add pVal
  let used = witnessRefCtxUsed
  (witnessRefCtx, witnessRefCtxUsed) = (savedCtx, savedUsed)
  if not used:
    return (tupleTy, tup)
  let ctxInit = newCall(stdName("newRefWitness"), witId)
  # RFC-0005 S8bn (item 1). Every position is built before any `ptr` that
  # may address it: a parameter holding no pointer first, then one holding
  # a pointer inside it, then a `ptr` parameter, each group in parameter
  # order. A pointer aimed at a field (`"&<cell>.<field>"`) then finds its
  # object built whichever parameter comes first; in parameter order,
  # `(pi: ptr int; q: Q)` built `pi` first and left it its own cell, so the
  # replay refuted a sound `sxSat`. The tuple keeps parameter order.
  var stmts = newStmtList(newLetStmt(ctxId, ctxInit))
  stmts.add emitCellTypes(params, ctxId, witId)   # RFC-0016 INT-81
  var ids = newSeq[NimNode](params.len)
  for rank in 0 .. 3:
    for i, p in params:
      # RFC-0016 INT-83: a `pointer` after every typed position, whose cell
      # it may be.
      let r = if isPointerTy(p.ty): 3
              elif p.ty != nil and p.ty.kind == itPtr: 2
              elif irTypeHoldsPtr(p.ty): 1
              else: 0
      if r != rank: continue
      ids[i] = genSym(nskLet, "witPos")
      stmts.add newTree(nnkLetSection,
        newIdentDefs(ids[i], copyNimTree(tupleTy[i]), vals[i]))
  var ordered = newTree(nnkTupleConstr)
  for id in ids: ordered.add id
  stmts.add ordered
  (tupleTy, nnkBlockExpr.newTree(newEmptyNode(), stmts))
