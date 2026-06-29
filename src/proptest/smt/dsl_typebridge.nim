## Layer 2 of the predicate DSL (ADR-0002): typedesc → `IRType`.
##
## Phase 2 recognises the fixed-width Nim integer family plus the
## type-derived range subtypes:
##
##   * `bool`                         → `tBool()`
##   * `int`/`uint`                   → `tInt(64, signed=…)`
##   * `int{8,16,32,64}`              → `tInt(W, signed=true)`
##   * `uint{8,16,32,64}`             → `tInt(W, signed=false)`
##   * `range[lo..hi]`                → `tInt(64, signed=true)` + range
##   * `Natural`                      → `tInt(64, signed=true)` + range
##   * `Positive`                     → `tInt(64, signed=true)` + range
##
## `classifyType` returns a `ClassifiedType` carrying the `IRType`
## and an optional type-derived range. The parser plumbs the range
## into the `IRParam`/`IRStmt(isLet)` for downstream consumption by
## the runtime (path-condition tightening) and by the abstraction
## layer (promotion proof obligations).

import std/macros
import std/strutils
import std/sequtils
import ./types

type
  ClassifiedType* = object
    ty*:    IRType
    range*: tuple[hasRange: bool, lo, hi: int64]

proc unranged(ty: IRType): ClassifiedType =
  ClassifiedType(ty: ty, range: (false, 0'i64, 0'i64))

proc ranged(ty: IRType, lo, hi: int64): ClassifiedType =
  ClassifiedType(ty: ty, range: (true, lo, hi))

proc parseRangeBracket(rangeNode: NimNode): tuple[lo, hi: int64] =
  ## Parse `range[lo .. hi]` (already known to be the right shape).
  ## `rangeNode` is the nnkBracketExpr; index 1 is the `lo .. hi` infix.
  let body = rangeNode[1]
  body.expectKind nnkInfix
  if body[0].strVal != "..":
    error("symex (Phase 2): expected `..` in range bound", body)
  result.lo = body[1].intVal
  result.hi = body[2].intVal

proc classifyFieldType*(ty: NimNode): ClassifiedType   ## fwd decl (R9)

proc classifyType*(ty: NimNode): ClassifiedType =
  ## Map a typed-AST type node to a `ClassifiedType`.
  # `var T` strip (lvalue parameter).
  if ty.kind == nnkVarTy and ty.len == 1:
    return classifyType(ty[0])
  # Phase 15 G3: a monomorphised `sink T` / `lent T` formal arrives as an
  # nnkCommand `[sink|lent, concreteType]` which carries NO type, so
  # `getTypeInst` below would raise "node has no type". Strip the ownership
  # wrapper on the RAW node first and classify the concrete inner type.
  if ty.kind == nnkCommand and ty.len == 2 and
     ty[0].kind in {nnkIdent, nnkSym} and ty[0].strVal in ["sink", "lent"]:
    return classifyType(ty[1])
  # Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). `owned T` is an
  # ownership annotation out of scope for the ref cluster — map to the
  # `__ownership:owned` placeholder so `allocateSym` raises the classified
  # `heUnsupportedOwnership` (sxUnknown, Invariant 3) at walk time. `owned T`
  # presents as an nnkCommand `[owned, T]` on the RAW node (no type), so match it
  # before `getTypeInst`.
  if ty.kind == nnkCommand and ty.len == 2 and
     ty[0].kind in {nnkIdent, nnkSym} and ty[0].strVal == "owned":
    return unranged(tUninterp("__ownership:owned"))
  # Phase 15 G7: a `static[N]`-dimensioned array formal `array[N, T]` is
  # monomorphized (by `monomorphize`, with `N → nnkIntLit`) into a SYNTHESIZED
  # `nnkBracketExpr[Ident "array", IntLit n, T]` that carries NO type — so
  # `getTypeInst` below would raise "node has no type". Match it structurally on
  # the RAW node first (size is the literal dimension directly; the element type
  # recurses through the normal path).
  if ty.kind == nnkBracketExpr and ty.len == 3 and
     ty[0].kind in {nnkIdent, nnkSym} and ty[0].strVal == "array" and
     ty[1].kind in nnkIntLit..nnkInt64Lit:
    let elemCls = classifyType(ty[2])
    return unranged(tArray(elemCls.ty, int(ty[1].intVal)))
  # Phase 15 Cluster C (C2b): a proc-typed formal (`f: proc(x: T): T`) of a
  # monomorphized generic (e.g. `applyTwice[T]`) arrives as a SYNTHESIZED
  # `nnkProcTy` on the RAW node that carries NO type — `getTypeInst` below would
  # raise "node has no type". Match it structurally first and map to the
  # "__closure" placeholder (the same target as the resolved-node arm below); a
  # proc-valued PARAM is resolved at the call site as an svClosure, never read
  # back as a top-level witness (Invariant 3).
  if ty.kind == nnkProcTy:
    return unranged(tUninterp("__closure"))
  var resolved = ty.getTypeInst
  if resolved.kind == nnkVarTy and resolved.len == 1:
    resolved = resolved[0]
  # Phase 15 Z3c / G3: `sink T` / `lent T` are ownership annotations; symex is
  # by-value, so strip the wrapper and classify T. The node shape varies:
  # `sink[T]` / `lent[T]` is an nnkBracketExpr, but a GENERIC `sink T` formal
  # (Cluster G) presents as an nnkCommand `[sink|lent, T]` — handle both (there
  # is no nnkSinkTy/nnkLentTy node). After monomorphization the inner `T` is the
  # concrete type, so this recurses to the right IRType (e.g. `sink int`→itInt).
  if resolved.kind in {nnkBracketExpr, nnkCommand} and resolved.len == 2 and
     resolved[0].kind in {nnkIdent, nnkSym} and
     resolved[0].strVal in ["sink", "lent"]:
    return classifyType(resolved[1])
  # ---- structural match: range[lo .. hi] ----
  if resolved.kind == nnkBracketExpr and
     resolved.len == 2 and
     resolved[0].kind in {nnkIdent, nnkSym} and
     resolved[0].strVal == "range":
    let (lo, hi) = parseRangeBracket(resolved)
    return ranged(tInt(64, signed = true), lo, hi)
  # ---- structural match: array[N, T] ----
  if resolved.kind == nnkBracketExpr and
     resolved.len == 3 and
     resolved[0].kind in {nnkIdent, nnkSym} and
     resolved[0].strVal == "array":
    # resolved[1] is the index range (typically `0..N-1` from Nim's
    # array literal sugar); we want N.
    let idxRange = resolved[1]
    var size: int
    if idxRange.kind == nnkInfix and idxRange[0].strVal == ".." and
       idxRange[1].kind in nnkIntLit..nnkInt64Lit and
       idxRange[2].kind in nnkIntLit..nnkInt64Lit:
      size = int(idxRange[2].intVal - idxRange[1].intVal + 1)
    elif idxRange.kind in nnkIntLit..nnkInt64Lit:
      size = int(idxRange.intVal)
    else:
      error("symex (Phase 4): array size must be a static integer", idxRange)
    let elemCls = classifyType(resolved[2])
    return unranged(tArray(elemCls.ty, size))
  # ---- structural match: anonymous tuples ----
  # `(int, int)` parses to nnkTupleConstr; `tuple[a, b: int]` parses
  # to nnkTupleTy after semcheck.
  if resolved.kind == nnkTupleConstr:
    var fields: seq[IRType]
    var names: seq[string]
    for child in resolved:
      fields.add classifyType(child).ty
      names.add ""
    return unranged(tTuple(fields, names))
  if resolved.kind == nnkTupleTy:
    # Each child is an nnkIdentDefs `[name1, name2, ..., type, default]`.
    var fields: seq[IRType]
    var names: seq[string]
    for id in resolved:
      let fty = classifyType(id[id.len - 2]).ty
      for j in 0 ..< id.len - 2:
        fields.add fty
        names.add id[j].strVal
    return unranged(tTuple(fields, names))
  # ---- nominal object / enum: nnkSym → getImpl yields nnkTypeDef ----
  if resolved.kind == nnkSym:
    let s = resolved.strVal
    let impl = resolved.getImpl
    # Phase 15 G4 (ADR-0008 D4). `type Foo = distinct Bar` → the typed AST's
    # `getImpl` yields `nnkTypeDef[name, genericParams, nnkDistinctTy[Bar]]`.
    # Map to `itDistinct(name = Foo, base = classify(Bar))` — a fresh
    # uninterpreted Z3 sort allocated at walk time. The base recurses, so a
    # nested `type KiloMeters = distinct Meters` classifies to an itDistinct
    # whose base is itself an itDistinct ("Meters"). Checked BEFORE the
    # object/enum/alias paths because a distinct over an object/enum base must
    # be walled off (the wall is the whole point), not unwrapped to the base.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkDistinctTy and impl[2].len == 1:
      # A7 (ADR-0017 Path B): `Rune` from std/unicode → svInt pinned [0, 0x10FFFF].
      # Rune = distinct RuneImpl = distinct int32.  We intercept by name-pair
      # ("Rune" / "RuneImpl") to avoid touching any user-defined type also named Rune.
      # Path B is ADDITIVE: the byte-faithful string model (ADR-0006 S-cluster) is untouched.
      if s == "Rune" and impl[2][0].strVal == "RuneImpl":
        return ranged(tInt(64, signed = true), 0'i64, 0x10FFFF'i64)
      let baseCls = classifyType(impl[2][0])
      return unranged(tDistinct(s, baseCls.ty))
    # Phase 14 cycle A3. Named-alias for `range[lo..hi]` with int
    # literal bounds — used as a variant discriminator since Nim
    # rejects plain `int` discs (low(T) must be 0). Aliases with
    # symbolic bounds (e.g. `Natural = range[0..high(int)]`) fall
    # through to the dedicated Natural/Positive handlers below.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkBracketExpr and
       impl[2].len == 2 and
       impl[2][0].kind in {nnkIdent, nnkSym} and
       impl[2][0].strVal == "range" and
       impl[2][1].kind == nnkInfix and
       impl[2][1][1].kind in nnkIntLit..nnkInt64Lit and
       impl[2][1][2].kind in nnkIntLit..nnkInt64Lit:
      let (lo, hi) = parseRangeBracket(impl[2])
      return ranged(tInt(64, signed = true), lo, hi)
    # Enum: lift to BV[w] integer with type-derived range
    # `[0..ordHigh]`. Enums with up to 256 values use BV[8], else BV[16].
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkEnumTy and s notin ["bool"]:
      # Enum lifts to BV[w]. Skip `bool` — it has an enum-shaped impl
      # but is handled below as itBool. Otherwise: don't attach
      # hasRange to avoid promotion routing unsigned readers to intVals.
      let nValues = impl[2].len - 1
      let bits = if nValues <= 256: 8 else: 16
      return unranged(tInt(bits, signed = false))
    # #136: unwrap `ref T` / `ptr T` — symex models the pointee as a
    # value-typed object. Aliasing tracking is a follow-up.
    var underObj: NimNode = nil
    if impl.kind == nnkTypeDef and impl.len >= 3:
      underObj = impl[2]
      if underObj.kind in {nnkRefTy, nnkPtrTy} and underObj.len == 1:
        let inner = underObj[0]
        if inner.kind == nnkObjectTy:
          underObj = inner
        elif inner.kind == nnkSym:
          return classifyType(inner)
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       underObj != nil and underObj.kind == nnkObjectTy:
      let recList = underObj[2]
      recList.expectKind nnkRecList
      # First pass: detect whether this object has any `nnkRecCase`
      # member. If it does, we build an `itVariant` (Phase 11);
      # otherwise the plain-tuple path stays.
      var hasRecCase = false
      for member in recList:
        if member.kind == nnkRecCase:
          hasRecCase = true
          break
      if hasRecCase:
        # ---- Phase 11 single-axis + Phase 14 multi-axis lowering --
        # Each `nnkRecCase` in `recList` becomes one VariantAxis.
        # Plain (non-recCase) fields are shared across all axes.
        # After the loop: 1 axis → `tVariant` (Phase 11 path);
        # 2+ axes → `mkMultiVariant` (Phase 14, ADR-0003 D1).
        var axes: seq[VariantAxis]
        var plainFieldNames: seq[string]
        var plainFieldTypes: seq[IRType]
        for member in recList:
          case member.kind
          of nnkIdentDefs:
            # Plain field group `name1, name2, ..., type, default`.
            let fty = classifyFieldType(member[member.len - 2]).ty  ## R9: ref field → heap ref
            for j in 0 ..< member.len - 2:
              plainFieldNames.add member[j].strVal
              plainFieldTypes.add fty
          of nnkRecCase:
            # Parse one recCase into a VariantAxis. The walker reads
            # each axis independently and conjoins per-axis
            # constraints on the same `pcOut` (ADR-0003 D1).
            var discName = ""
            var discTy: IRType = nil
            var arms: seq[VariantArm]
            let discDef = member[0]
            discName = discDef[0].strVal
            discTy = classifyType(discDef[discDef.len - 2]).ty
            # discDef[1] is the discriminator's typedesc; its sym
            # carries the enum impl from which we read ordinal +
            # name for each tag.
            let discTypeSym = discDef[discDef.len - 2]
            # Build a name → ordinal map for the discriminator's
            # enum. The enum impl is the type-def's nnkEnumTy node.
            var enumOrdinals: seq[tuple[name: string, ordinal: int]]
            let dImpl = discTypeSym.getImpl
            if dImpl.kind == nnkTypeDef and dImpl.len >= 3 and
               dImpl[2].kind == nnkEnumTy:
              # nnkEnumTy children: first is nnkEmpty, rest are
              # enum constants. Each is an nnkSym or nnkEnumFieldDef.
              var nextOrdinal = 0
              for i in 1 ..< dImpl[2].len:
                let c = dImpl[2][i]
                var nm = ""
                var ord = nextOrdinal
                case c.kind
                of nnkSym, nnkIdent:
                  nm = c.strVal
                of nnkEnumFieldDef:
                  # `kind = value` form: c[0] is name, c[1] is ordinal
                  nm = c[0].strVal
                  if c[1].kind in nnkIntLit..nnkInt64Lit:
                    ord = int(c[1].intVal)
                else:
                  error("symex Phase 11: unsupported enum constant " &
                        "shape " & $c.kind, c)
                enumOrdinals.add (nm, ord)
                nextOrdinal = ord + 1
            else:
              # Phase 14 cycle A3. Non-enum disc (e.g. `range[lo..hi]`):
              # tagOrdinals come from explicit `of N:` literals; no
              # enumOrdinals to enumerate. `else:` arms use the same
              # conjunction-of-negations the enum path uses.
              discard
            # Process arms: member[1..^1] are nnkOfBranch (or nnkElse).
            for k in 1 ..< member.len:
              let branch = member[k]
              if branch.kind notin {nnkOfBranch, nnkElse}:
                error("symex Phase 14: unsupported recCase branch kind " &
                      $branch.kind, branch)
              # nnkElse has a single child (the body); nnkOfBranch has
              # 0..^2 tag values + a body at the last child.
              let lastIx = branch.len - 1
              let body = branch[lastIx]
              # Collect this arm's plain-field group.
              var armFieldNames: seq[string]
              var armFieldTypes: seq[IRType]
              let bodyMembers = if body.kind == nnkRecList: toSeq(body.children)
                                elif body.kind == nnkIdentDefs: @[body]
                                else: @[]
              for armMember in bodyMembers:
                if armMember.kind != nnkIdentDefs: continue
                let fty = classifyFieldType(armMember[armMember.len - 2]).ty  ## R9: ref field → heap ref
                for j in 0 ..< armMember.len - 2:
                  armFieldNames.add armMember[j].strVal
                  armFieldTypes.add fty
              # `else:` arm — single VariantArm with isElse=true and
              # tagOrdinal=-1 sentinel. Walker computes the membership
              # constraint lazily as AND_over_non_else(disc != tagOrd).
              if branch.kind == nnkElse:
                arms.add VariantArm(
                  tagOrdinal: -1, tagName: "else",
                  fieldNames: armFieldNames,
                  fieldTypes: armFieldTypes,
                  isElse: true)
                continue
              # Emit one arm per tag literal listed in this branch.
              for tagIx in 0 ..< lastIx:
                let tagNode = branch[tagIx]
                let tagName =
                  case tagNode.kind
                  of nnkSym, nnkIdent: tagNode.strVal
                  of nnkIntLit..nnkInt64Lit: ""  # unusual but legal
                  else: ""
                # Resolve ordinal from enumOrdinals or, if missing,
                # from the literal.
                var tagOrd = -1
                for eo in enumOrdinals:
                  if eo.name == tagName: tagOrd = eo.ordinal; break
                if tagOrd < 0 and tagNode.kind in nnkIntLit..nnkInt64Lit:
                  tagOrd = int(tagNode.intVal)
                if tagOrd < 0:
                  error("symex Phase 11: could not resolve ordinal " &
                        "for tag `" & tagName & "`", tagNode)
                arms.add VariantArm(
                  tagOrdinal: tagOrd, tagName: tagName,
                  fieldNames: armFieldNames,
                  fieldTypes: armFieldTypes)
            # Phase 14 cycle A2. Snapshot the disc enum's full (name,
            # ordinal) domain — walker uses ords to bound the disc
            # range when an `else:` arm is present; witness emitter
            # uses names to render `of <tagName>:` branches for
            # else-covered ordinals.
            var discTags: seq[tuple[name: string, ord: int]]
            for eo in enumOrdinals:
              discTags.add (name: eo.name, ord: eo.ordinal)
            axes.add VariantAxis(discName: discName,
                                 discTy: discTy, arms: arms,
                                 discTags: discTags)
          else:
            error("symex Phase 11: unsupported object member shape " &
                  $member.kind, member)
        # Plain fields stay separate from arm-specific ones — the
        # walker allocates them once (shared across all arms) so
        # they survive discriminator reassignment, matching Nim's
        # runtime memory layout.
        # ADR-0003 D1 invariant: single-axis objects use itVariant;
        # multi-axis objects use itMultiVariant. The two IR kinds
        # are intentionally disjoint.
        if axes.len == 1:
          return unranged(tVariant(objectName = s,
            discName = axes[0].discName, discTy = axes[0].discTy,
            arms = axes[0].arms,
            plainFieldNames = plainFieldNames,
            plainFieldTypes = plainFieldTypes,
            discTags = axes[0].discTags))
        else:
          return unranged(mkMultiVariant(objectName = s,
            axes = axes,
            plainFieldNames = plainFieldNames,
            plainFieldTypes = plainFieldTypes))
      # ---- Phase-4 plain-record path: only plain fields --------------
      var fields: seq[IRType]
      var names: seq[string]
      for member in recList:
        member.expectKind nnkIdentDefs
        # Phase 15 R9: a ref/ptr-to-object field (e.g. recursive `next: Node`)
        # is classified as a heap REF (`tRef`/`tPtr` of a finite named
        # placeholder), NOT unwrapped to the object value — see
        # `classifyFieldType`. This breaks the self-referential compile-time
        # recursion and matches the R6 field-split heap's `Ref_T`-valued field.
        let fty = classifyFieldType(member[member.len - 2]).ty
        for j in 0 ..< member.len - 2:
          fields.add fty
          names.add member[j].strVal
      return unranged(tTuple(fields, names, objectName = s))
  # ---- structural match: seq[T] / Table[K, V] / HashSet[T] ----
  if resolved.kind == nnkBracketExpr and
     resolved[0].kind in {nnkIdent, nnkSym}:
    let head = resolved[0].strVal
    case head
    of "seq":
      if resolved.len != 2:
        error("symex (Phase 5): seq type must be `seq[T]`", resolved)
      let elem = classifyType(resolved[1]).ty
      return unranged(tSeq(elem))
    of "Table":
      if resolved.len != 3:
        error("symex (Phase 5): Table type must be `Table[K, V]`", resolved)
      let kty = classifyType(resolved[1]).ty
      let vty = classifyType(resolved[2]).ty
      return unranged(tTable(kty, vty))
    of "HashSet":
      if resolved.len != 2:
        error("symex (Phase 5): HashSet type must be `HashSet[T]`", resolved)
      let ety = classifyType(resolved[1]).ty
      return unranged(tSet(ety))
    of "WeakRef", "Atomic":
      # Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). `WeakRef[T]` /
      # `Atomic[T]` are out of scope for the ref cluster — map to an
      # `__ownership:*` placeholder so `allocateSym` raises the classified
      # `heUnsupportedOwnership` (sxUnknown, Invariant 3) at walk time rather
      # than a compile error.
      return unranged(tUninterp("__ownership:" & head))
    else: discard
  # Phase 15 Cluster R (R1a, ADR-0010). Inline `ref T` / `ptr T` — classify to
  # `tRef`/`tPtr` of the pointee (REPLACING the pre-R unwrap-to-pointee
  # behaviour, reconciliation §A:128). The walker STUBS these via
  # `allocateSym(itRef/itPtr)` → `heUnresolvedRef` (sxUnknown) until R1+ land the
  # logical-heap semantics.
  if resolved.kind == nnkRefTy and resolved.len == 1:
    return unranged(tRef(classifyType(resolved[0]).ty))
  if resolved.kind == nnkPtrTy and resolved.len == 1:
    return unranged(tPtr(classifyType(resolved[0]).ty))
  # Phase 15 Cluster C (C2a): a proc/closure type (`proc(...): T`) — a closure
  # as a top-level SUT param/result type is UNSUPPORTED (Invariant 3). Map it to
  # an `itUninterp` placeholder with the recognisable "__closure" marker name;
  # `emitTyAndReader` renders a proc placeholder + `{.warning.}` for it rather
  # than crashing (closures are constructed in-body — C2a — but never
  # reconstructed as a top-level witness).
  if resolved.kind == nnkProcTy:
    return unranged(tUninterp("__closure"))
  # ---- otherwise: text match on the resolved type name ----
  let s = resolved.repr.strip
  case s
  of "bool":     unranged(tBool())
  of "string":   unranged(tString())
  of "char":     unranged(tInt(8,  signed = false))  ## Phase 15 Z3c: char = uint8
  of "byte":     unranged(tInt(8,  signed = false))  ## Phase 15 S7a: byte = uint8
                                                     ## (bytes(s) element type)
  of "float", "float64": unranged(tFloat64())        ## Phase 15 F1
  of "float32":  unranged(tFloat32())                ## Phase 15 F1
  of "int":      unranged(tInt(64, signed = true))
  of "int8":     unranged(tInt(8,  signed = true))
  of "int16":    unranged(tInt(16, signed = true))
  of "int32":    unranged(tInt(32, signed = true))
  of "int64":    unranged(tInt(64, signed = true))
  of "uint":     unranged(tInt(64, signed = false))
  of "uint8":    unranged(tInt(8,  signed = false))
  of "uint16":   unranged(tInt(16, signed = false))
  of "uint32":   unranged(tInt(32, signed = false))
  of "uint64":   unranged(tInt(64, signed = false))
  of "Natural":  ranged(tInt(64, signed = true), 0'i64, high(int64))
  of "Positive": ranged(tInt(64, signed = true), 1'i64, high(int64))
  else:
    error("symex (Phase 2): unsupported parameter type `" & s &
          "`; the supported fragment is {bool, int, int{8,16,32,64}, " &
          "uint, uint{8,16,32,64}, range[..], Natural, Positive}.", ty)

proc namedRefPlaceholder(objSym: NimNode): IRType =
  ## Phase 15 R9 (ADR-0010). Build the `tRef`/`tPtr` POINTEE for a ref/ptr-typed
  ## OBJECT FIELD (e.g. the recursive `next: Node` of a linked list). The pointee
  ## is an EMPTY-fielded named `itTuple` placeholder carrying ONLY the object's
  ## name — NOT the object's full field structure. This is deliberate: a
  ## self-referential type (`Node` whose `next: Node`) would make the IR cyclic,
  ## and `$`/`==` over `IRType` recurse STRUCTURALLY into every field — a cyclic
  ## IR would infinite-loop both at compile time (this classifier) and at runtime
  ## (`refPointeeTypeId` = `$pointee`). The walker never needs the pointee's
  ## fields for a ref-typed field: the `Ref_<name>` SORT keys on this stable name
  ## (`refPointeeTypeId`), the field VALUE sort comes from `dElemTy` (the field's
  ## own type, resolved from the TYPED AST at the access site), and the field
  ## type at a deeper `.field` comes from `classifyType(wholeDotExpr)` (again the
  ## typed AST), so an empty-fielded named placeholder is sufficient and FINITE.
  let nm = if objSym.kind in {nnkSym, nnkIdent}: objSym.strVal else: objSym.repr
  tTuple(@[], @[], objectName = nm)

proc isObjectTypeSym(sym: NimNode): bool =
  ## CR-19: Returns true iff `sym` (a nnkSym/nnkIdent) refers to a user-defined
  ## OBJECT type (nnkTypeDef over nnkObjectTy). Primitive built-in types (`int`,
  ## `float`, `bool`, etc.) have `getImpl` returning nnkEmpty or a non-TypeDef
  ## node, so they return false. This guards the placeholder arm in
  ## `classifyFieldType` — only object pointees should use the named placeholder
  ## (to break self-referential cycles); primitive pointees (`ref int`, `ref float`)
  ## should fall through to `classifyType(ty)` which produces `tRef(tInt(64,true))`
  ## etc. via the inline-nnkRefTy arm at lines 411-414 — the same IR as the
  ## deref site's `dElemTy`, keeping the Z3 sort names byte-identical.
  if sym.kind notin {nnkSym, nnkIdent}: return false
  let impl = try: sym.getImpl except: return false
  if impl.kind != nnkTypeDef or impl.len < 3: return false
  impl[2].kind == nnkObjectTy

proc classifyFieldType*(ty: NimNode): ClassifiedType =
  ## Phase 15 R9 (ADR-0010). Classify an OBJECT FIELD's type. A field whose type
  ## is a `ref`/`ptr` to an object (named `type N = ref object` OR an inline
  ## `ref Obj`) is classified as `tRef`/`tPtr` of a finite NAMED PLACEHOLDER
  ## (`namedRefPlaceholder`) rather than UNWRAPPED to the object value. This is
  ## the R9 ref-typed-field extension: a ref-typed field is a ref (a heap address
  ## modelled as `Ref_<name>`), stored/loaded through the R6 field-split heap as
  ## a `Ref_T` value — and crucially it BREAKS the compile-time infinite recursion
  ## a self-referential field (`next: Node`) would otherwise cause in
  ## `classifyType`'s named-`ref object` unwrap. Non-ref/ptr fields delegate to
  ## the ordinary `classifyType` (a plain value field is modelled by value, as
  ## before — no behaviour change for Phase-4 record fields).
  ##
  ## CR-19: for `ref PRIMITIVE` fields (e.g. `p: ref int`), the pointee sym was
  ## previously matched by the `inner.kind in {nnkSym, nnkIdent}` guard and
  ## received the named-tuple placeholder — producing sort `Ref_int__` — while
  ## the deref site's `dElemTy` produced `tInt(64,true)` → sort `Ref_i64_s`,
  ## causing a Z3SortMismatchError → sxUnknown. Fix: gate the placeholder on
  ## `isObjectTypeSym` — only actual object types get the placeholder; primitives
  ## fall through to `classifyType(ty)` which produces `tRef(tInt(64,true))` etc.
  # A NAMED ref/ptr object type, reached either as the field-type node directly
  # (`next: Node`) OR as the resolved TYPE of a derived ref-valued expression
  # (`getTypeInst` of `n.next` yields the `Node` sym). In both cases the sym's
  # `getImpl` is `nnkTypeDef[name, _, nnkRefTy|nnkPtrTy]`.
  var nameSym: NimNode = nil
  if ty.kind == nnkSym:
    nameSym = ty
  else:
    let inst = ty.getTypeInst
    if inst.kind == nnkSym:
      nameSym = inst
  if nameSym != nil:
    let impl = nameSym.getImpl
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind in {nnkRefTy, nnkPtrTy} and impl[2].len == 1:
      let inner = impl[2][0]
      # Only OBJECT pointees route to the heap-ref model here; a `ref int`-style
      # named alias still has a primitive pointee and the existing `classifyType`
      # ref arms (R1a) handle it. We detect the object case structurally.
      # CR-19: `inner.kind in {nnkSym, nnkIdent}` previously matched primitive
      # syms too (e.g. `int`). Now gate on `isObjectTypeSym` to match only real
      # object types and let primitive pointees fall to `classifyType(ty)`.
      if inner.kind == nnkObjectTy or isObjectTypeSym(inner):
        let placeholder = namedRefPlaceholder(nameSym)
        return if impl[2].kind == nnkRefTy: unranged(tRef(placeholder))
               else: unranged(tPtr(placeholder))
  # An INLINE `ref Obj` / `ptr Obj` field (the type node is itself nnkRefTy/PtrTy
  # over an object sym).
  # CR-19: gate inner-sym case on `isObjectTypeSym` (not just `nnkSym/nnkIdent`)
  # so inline `ref int` / `ref float` etc. fall through to `classifyType(ty)`.
  let resolved = ty.getTypeInst
  if resolved.kind in {nnkRefTy, nnkPtrTy} and resolved.len == 1:
    let inner = resolved[0]
    if inner.kind == nnkObjectTy or isObjectTypeSym(inner):
      let nm = if inner.kind in {nnkSym, nnkIdent}: inner.strVal else: ""
      let placeholder = tTuple(@[], @[], objectName = nm)
      return if resolved.kind == nnkRefTy: unranged(tRef(placeholder))
             else: unranged(tPtr(placeholder))
  classifyType(ty)
