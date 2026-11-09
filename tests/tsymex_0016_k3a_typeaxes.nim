## RFC-0016 K3a (section 8.1) -- the type-class axis and the type x memory-op
## axis, read through their verbs.
##
## * every `NimTypeKind` has a row in the type-class axis (a missing kind is a
##   test failure here, not a silent decline), and `admitTypeClass` at
##   `tcByValueFormal` reproduces the S8cq by-value allowlist exactly (the
##   table replaced `typeCopiedByValue`'s own `case`);
## * every `IRTypeKind` has a `letCursor` row, `holdsSharedMemory` reads it,
##   and a type that holds shared memory through a variant arm, a multi-variant
##   axis or a distinct base is found (it was `else: false`);
## * STY-04 and STY-06's type cells are `never` rows with a reason.
import std/[unittest, strutils, sequtils, options, macros]
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/typeaxes

# S8cq's allowlist, as it stood before the table (dsl_parser typeCopiedByValue)
const leafKinds = {ntyBool, ntyChar, ntyEnum, ntyRange, ntyRef, ntyPtr,
                   ntyPointer, ntyProc, ntyCString} +
                  {ntyInt .. ntyInt64} + {ntyUInt .. ntyUInt64} +
                  {ntyFloat .. ntyFloat64}
const structKinds = {ntyDistinct, ntyAlias, ntyObject, ntyTuple, ntyGenericInst}

suite "RFC-0016 K3a: the type-class axis":
  test "every NimTypeKind has a row":
    for k in NimTypeKind:
      let a = admitTypeClass(k, tcByValueFormal)
      check a.cell.scope == axTypeClass
      if not a.admitted:
        check "no row" notin a.decline[1]

  test "tcByValueFormal admits exactly the S8cq allowlist":
    for k in NimTypeKind:
      let a = admitTypeClass(k, tcByValueFormal)
      check a.admitted == (k in leafKinds or k in structKinds)
      if a.admitted:
        check a.payload == (if k in structKinds: tmStructural else: tmLeaf)

  test "an unlisted kind declines with the ledger's intent and names its cell":
    let a = admitTypeClass(ntySequence, tcByValueFormal)
    check not a.admitted
    check render(a.cell) == "typeclass:sequence"
    check "typeclass:sequence" in a.decline[1]

  test "STY-04 / STY-06: owned, Atomic, float128 and sNaN payloads are never rows":
    var never: seq[string]
    for c in typeClassTable.cells:
      if not c.admitted and c.intent == iNever: never.add render(c.cell)
    for want in ["typeclass:owned", "typeclass:atomic", "typeclass:float128",
                 "typeclass:float/sNaNPayload"]:
      check want in never

  test "the existing record cells are rows":
    let keys = toSeq(typeClassTable.cells).mapIt(render(it.cell))
    for want in ["typeclass:variant/omittedField/Table",
                 "typeclass:variant/omittedField/HashSet",
                 "typeclass:variant/omittedField/array",
                 "typeclass:variant/omittedField/distinct",
                 "typeclass:variant/omittedField/tuple",
                 "typeclass:array/enumIndex"]:
      check want in keys
    # a declined omitted-field row carries the kind the pin records
    let a = typeClassTable.admit("variant/omittedField/Table", tcFeature)
    check not a.admitted
    check a.decline[0] == some(feUnsupportedOpHavoc)

suite "RFC-0016 K3a: the type x memory-op axis":
  let
    i = tInt()
    sq = tSeq(i)
    vArmSeq = tVariant("V", "k", tInt(), @[
      VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["s"], fieldTypes: @[sq]),
      VariantArm(tagOrdinal: 1, tagName: "b", fieldNames: @["n"], fieldTypes: @[i])])
    vScalar = tVariant("W", "k", tInt(), @[
      VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["a"], fieldTypes: @[i]),
      VariantArm(tagOrdinal: 1, tagName: "b", fieldNames: @["n"], fieldTypes: @[i])])
    vPlainSeq = tVariant("P", "k", tInt(), @[
      VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["a"], fieldTypes: @[i])],
      plainFieldNames = @["s"], plainFieldTypes = @[sq])
    mv = IRType(kind: itMultiVariant, mvObjectName: "M", mvAxes: @[
      VariantAxis(discName: "k", discTy: i, arms: @[
        VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["s"], fieldTypes: @[tString()])]),
      VariantAxis(discName: "j", discTy: i, arms: @[
        VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["n"], fieldTypes: @[i])])])
    mvScalar = IRType(kind: itMultiVariant, mvObjectName: "N", mvAxes: @[
      VariantAxis(discName: "k", discTy: i, arms: @[
        VariantArm(tagOrdinal: 0, tagName: "a", fieldNames: @["n"], fieldTypes: @[i])])])

  test "every IRTypeKind has a letCursor row":
    for k in IRTypeKind:
      let a = admitTypeOp(k, moLetCursor)
      check a.cell.scope == axTypeOp
      if not a.admitted:
        check "no row" notin a.decline[1]
      else:
        check a.payload.share in {msValue, msShared, msComponents}

  test "cells are keyed op first, then the IR kind":
    check render(admitTypeOp(itVariant, moLetCursor).cell) == "typeop:letCursor/variant"
    check render(admitTypeOp(itTuple, moLetCursor).cell) == "typeop:letCursor/tuple"
    check render(admitTypeOp(itMultiVariant, moLetCursor).cell) ==
      "typeop:letCursor/multiVariant"

  test "holdsSharedMemory: the direct containers":
    for t in [tString(), sq, tTable(i, i), tSet(i)]:
      check holdsSharedMemory(t)
    for t in [i, tBool(), tFloat64(), tFloat32(), tBitSet(tBool()),
              tRef(i), tPtr(i), tUninterp("U")]:
      check not holdsSharedMemory(t)

  test "holdsSharedMemory: through tuple, array and distinct":
    check holdsSharedMemory(tTuple(@[i, sq]))
    check not holdsSharedMemory(tTuple(@[i, i]))
    check holdsSharedMemory(tArray(sq, 2))
    check holdsSharedMemory(tDistinct("D", sq))
    check not holdsSharedMemory(tDistinct("D", i))

  test "holdsSharedMemory: through a variant's arms, plain fields and axes (B-04)":
    check holdsSharedMemory(vArmSeq)
    check holdsSharedMemory(vPlainSeq)
    check not holdsSharedMemory(vScalar)
    check holdsSharedMemory(mv)
    check not holdsSharedMemory(mvScalar)
    check not holdsSharedMemory(nil)

  test "a recursive-by-component row has a component walk, never a bare answer":
    for k in IRTypeKind:
      let a = admitTypeOp(k, moLetCursor)
      if a.admitted and a.payload.share == msComponents:
        check k in {itTuple, itArray, itVariant, itMultiVariant, itDistinct}
