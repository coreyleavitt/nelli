## Phase 11 cycle 2 — typebridge classifies variant objects as itVariant.
##
## The walker side of variant soundness arrives in cycles 3-7. This
## test isolates the parser/typebridge transition: when an object
## type definition contains an `nnkRecCase`, `classifyType` must now
## return an `itVariant` instead of the old Phase-4 flat-tuple
## lowering. Plain (non-recCase) records continue to classify as
## `itTuple`.
import std/[unittest, macros, strutils]
import nelli/smt/types
import nelli/smt/dsl_typebridge

# Reach the typebridge directly. classifyType expects a typed-AST
# node; passing a typedesc Sym works because the typebridge calls
# `getTypeInst` internally.
proc innerTypeSym(T: NimNode): NimNode =
  # `T: typedesc` arrives wrapped as `typeDesc[Inner]`. Peel one
  # layer so classifyType sees the actual type.
  let inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst[1]
  else:
    inst

macro irKindOf(T: typedesc): string =
  let cls = classifyType(innerTypeSym(T))
  newLit($cls.ty.kind)

macro irDescription(T: typedesc): string =
  let cls = classifyType(innerTypeSym(T))
  newLit($cls.ty)

type
  ShapeKind = enum skCircle, skSquare
  Shape = object
    case kind: ShapeKind
    of skCircle: radius: int
    of skSquare: side: int

  Point = object       # plain record — control case
    x, y: int

suite "symex Phase 11 cycle 2 — variant typebridge":
  test "plain (non-variant) records still classify as itTuple":
    check irKindOf(Point) == "itTuple"

  test "nnkRecCase object classifies as itVariant":
    check irKindOf(Shape) == "itVariant"

  test "itVariant description carries object name, discriminator name, " &
       "and arm tag names":
    let desc = irDescription(Shape)
    check "Shape" in desc
    check "kind" in desc
    check "skCircle" in desc
    check "skSquare" in desc
    check "radius" in desc
    check "side" in desc
