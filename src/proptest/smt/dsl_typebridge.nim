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

proc classifyType*(ty: NimNode): ClassifiedType =
  ## Map a typed-AST type node to a `ClassifiedType`.
  if ty.kind == nnkVarTy and ty.len == 1:
    return classifyType(ty[0])
  var resolved = ty.getTypeInst
  if resolved.kind == nnkVarTy and resolved.len == 1:
    resolved = resolved[0]
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
        # ---- Phase 11: itVariant lowering -------------------------
        # We currently support one nnkRecCase per object (the
        # common Nim idiom); plain fields share each arm's
        # always-present prefix. Multiple recCases per object is a
        # follow-up.
        var discName = ""
        var discTy: IRType = nil
        var arms: seq[VariantArm]
        var plainFieldNames: seq[string]
        var plainFieldTypes: seq[IRType]
        for member in recList:
          case member.kind
          of nnkIdentDefs:
            # Plain field group `name1, name2, ..., type, default`.
            let fty = classifyType(member[member.len - 2]).ty
            for j in 0 ..< member.len - 2:
              plainFieldNames.add member[j].strVal
              plainFieldTypes.add fty
          of nnkRecCase:
            if discName.len > 0:
              error("symex Phase 11: more than one variant " &
                    "discriminator per object is unsupported", member)
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
              error("symex Phase 11: discriminator type must be an " &
                    "enum (got " & $dImpl.kind & ")", discTypeSym)
            # Process arms: member[1..^1] are nnkOfBranch (or nnkElse).
            for k in 1 ..< member.len:
              let branch = member[k]
              if branch.kind != nnkOfBranch:
                error("symex Phase 11: variant `else` branches are " &
                      "not yet supported; use exhaustive `of` arms", branch)
              # branch children: 0..^2 are tag values, last is body.
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
                let fty = classifyType(armMember[armMember.len - 2]).ty
                for j in 0 ..< armMember.len - 2:
                  armFieldNames.add armMember[j].strVal
                  armFieldTypes.add fty
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
          else:
            error("symex Phase 11: unsupported object member shape " &
                  $member.kind, member)
        # Plain fields stay separate from arm-specific ones — the
        # walker allocates them once (shared across all arms) so
        # they survive discriminator reassignment, matching Nim's
        # runtime memory layout.
        return unranged(tVariant(objectName = s,
          discName = discName, discTy = discTy, arms = arms,
          plainFieldNames = plainFieldNames,
          plainFieldTypes = plainFieldTypes))
      # ---- Phase-4 plain-record path: only plain fields --------------
      var fields: seq[IRType]
      var names: seq[string]
      for member in recList:
        member.expectKind nnkIdentDefs
        let fty = classifyType(member[member.len - 2]).ty
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
    else: discard
  # ---- otherwise: text match on the resolved type name ----
  let s = resolved.repr.strip
  case s
  of "bool":     unranged(tBool())
  of "string":   unranged(tString())
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
