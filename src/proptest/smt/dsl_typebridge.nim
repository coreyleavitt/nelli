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
  let resolved = ty.getTypeInst
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
  # ---- nominal object: nnkSym → getImpl yields nnkTypeDef ----
  if resolved.kind == nnkSym:
    let s = resolved.strVal
    # Primitive nominal aliases handled below by `case s`.
    # If `getImpl` reveals an nnkObjectTy, lift to itTuple with names.
    let impl = resolved.getImpl
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkObjectTy:
      let recList = impl[2][2]
      recList.expectKind nnkRecList
      var fields: seq[IRType]
      var names: seq[string]
      for member in recList:
        member.expectKind nnkIdentDefs
        let fty = classifyType(member[member.len - 2]).ty
        for j in 0 ..< member.len - 2:
          fields.add fty
          names.add member[j].strVal
      return unranged(tTuple(fields, names, objectName = s))
  # ---- otherwise: text match on the resolved type name ----
  let s = resolved.repr.strip
  case s
  of "bool":     unranged(tBool())
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
