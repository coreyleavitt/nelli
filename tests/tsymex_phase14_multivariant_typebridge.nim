## Phase 14 cycle A1b — typebridge classifies multi-`nnkRecCase`
## objects as `itMultiVariant`.
##
## Pre-Phase-14, `classifyType` errored on objects with more than
## one `nnkRecCase` block (dsl_typebridge.nim:156-158). After A1b:
## the typebridge collects each `nnkRecCase` as a `VariantAxis`
## entry and emits `mkMultiVariant(...)`. Single-`nnkRecCase`
## objects continue to use `tVariant` per ADR-0003 D1's invariant.
import std/[unittest, macros, strutils]
import nelli/smt/types
import nelli/smt/dsl_typebridge

proc innerTypeSym(T: NimNode): NimNode =
  let inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst[1]
  else:
    inst

macro irKindOf(T: typedesc): string =
  let cls = classifyType(innerTypeSym(T))
  newLit($cls.ty.kind)

macro mvAxisCountOf(T: typedesc): int =
  let cls = classifyType(innerTypeSym(T))
  newLit(cls.ty.mvAxes.len)

macro mvDescription(T: typedesc): string =
  let cls = classifyType(innerTypeSym(T))
  newLit($cls.ty)

type
  KindA = enum kaX, kaY
  KindB = enum kbP, kbQ
  TwoAxis = object
    case axis1: KindA
    of kaX: a1: int
    of kaY: a2: int
    case axis2: KindB
    of kbP: b1: int
    of kbQ: b2: int

  # Control: single-recCase must STILL classify as itVariant
  # (preserves the parser invariant from ADR-0003 D1).
  SingleAxis = object
    case kind: KindA
    of kaX: x: int
    of kaY: y: int

suite "symex Phase 14 cycle A1b — multi-recCase typebridge":
  test "two-recCase object classifies as itMultiVariant":
    check irKindOf(TwoAxis) == "itMultiVariant"

  test "two-recCase object has mvAxes.len == 2":
    check mvAxisCountOf(TwoAxis) == 2

  test "itMultiVariant description carries object name and both axes":
    let desc = mvDescription(TwoAxis)
    check "TwoAxis" in desc
    check "axis1" in desc
    check "axis2" in desc
    check "kaX" in desc
    check "kbP" in desc

  test "single-recCase object still classifies as itVariant (invariant)":
    check irKindOf(SingleAxis) == "itVariant"
