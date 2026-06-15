## Phase-2 IR interpreter.
##
## The IR is type-erased after parsing; the runtime determines the
## width of each integer subexpression by probing the env or
## inheriting from the surrounding context (let RHS = let LHS type;
## comparison operands = the matching variable's type).
##
## Storage: `SymVal` is a sum over the Z3 families we need
##
##   { Z3Bool, Z3BitVec[8|16|32|64], Z3Int }
##
## with a `signed: bool` tag for the BV cases (Nim's `int*`/`uint*`
## distinguish signedness at the operator layer, not the bit-pattern).
## `Z3Int` lands as a SymVal variant for Phase-2 cycles 5+ when the
## abstraction layer promotes range-typed integers; the parser/runtime
## here ship with the variant present and the structural plumbing in
## place, so cycle 5 only adds the promotion logic, not new families.

import std/tables
import std/options
import std/sets
import std/hashes
import std/math   ## Phase 15 F2: classify() for float-literal NaN/Inf/-0.0 lowering
import z3

import ./types
import ./abstraction

export tables, sets   ## for `Table` / `HashSet` in witness types

# Once-per-process banner for `isLoose` mode. ADR-0001 calls this out
# as a deliberate footgun; the banner is the documented warning.
var isLooseBannerEmitted = false

proc emitIsLooseBanner() =
  if not isLooseBannerEmitted:
    stderr.writeLine "proptest/symex: WARNING — `isLoose` integer semantics " &
                     "is UNSOUND (Z3Int everywhere, no BV floor). May produce " &
                     "witnesses that overflow at runtime. See ADR-0001."
    isLooseBannerEmitted = true

# ---- SymVal -----------------------------------------------------------------

type
  SVKind* = enum
    svBV8, svBV16, svBV32, svBV64
    svInt
    svBool
    svString  ## Phase 5: Nim string, encoded as Z3String.
    svTuple
    svArray   ## Phase 4: static array, per-element SymVals.
    svSeq     ## Phase 5: dynamic seq[T] — (Z3Int len, Z3Array data).
    svTable   ## Phase 5: Table[K, V] — (data, present).
    svSet     ## Phase 5: HashSet[T] — Z3Array[T, Z3Bool].
    svVariant ## Phase 11: tagged sum (Nim variant object) — disc-
              ## riminator + per-arm symbolic field bindings.
    svMultiVariant ## Phase 14 (ADR-0003 D1): multi-axis variant —
              ## per-axis discriminators + per-axis arm fields.
              ## Symmetric with svVariant but with multiple axes.
    svUninterpRef ## Phase 15 Z3b: uninterpreted reference sort; fields not
              ## modelled symbolically. Produced by cluster E (E8,
              ## getCurrentException). Carries the Z3 uninterpreted-sort
              ## ast plus diagnostic names.
    svFloat32  ## Phase 15 F1: IEEE float32 (Z3Float32).
    svFloat64  ## Phase 15 F1: IEEE float64 (Z3Float64); Nim `float`.

  SymVal* = object
    signed*: bool
    case kind*: SVKind
    of svBV8:  bv8:  Z3BitVec[8]
    of svBV16: bv16: Z3BitVec[16]
    of svBV32: bv32: Z3BitVec[32]
    of svBV64: bv64: Z3BitVec[64]
    of svInt:  zi:   Z3Int
    of svBool: bo:   Z3Bool
    of svTuple:
      fields*:     seq[SymVal]
      fieldNames*: seq[string]
    of svArray:
      arrElems*:  seq[SymVal]
      arrElemTy*: IRType
    of svString:
      str*: Z3String
    of svSeq:
      seqLen*:     Z3Int
      seqDataRaw*: Z3AnyAst       ## erased Z3Array[Z3Int, sortOf(T)]
      seqElemTy*:  IRType
    of svTable:
      tabDataRaw*:    Z3AnyAst
      tabPresentRaw*: Z3AnyAst
      tabSize*:       Z3Int       ## #144: cardinality counter; mutations
                                  ## update this alongside the present
                                  ## array.
      tabKeyTy*:      IRType
      tabValTy*:      IRType
    of svSet:
      setMembersRaw*: Z3AnyAst
      setSize*:       Z3Int       ## #144: same as tabSize, for HashSet
      setElemTy*:     IRType
    of svVariant:
      vDisc*:        ref SymVal           ## discriminator (svBV{8,16})
                                          ## boxed since SymVal is a
                                          ## value type and Nim disallows
                                          ## direct self-recursion
      vDiscName*:    string               ## discriminator field name
      vObjectName*:  string               ## Nim object name (for diagnostics)
      vArmFields*:   OrderedTable[int, seq[SymVal]]
                                          ## tag ordinal → per-arm field
                                          ## SymVals (ARM-SPECIFIC only)
      vArmFieldNames*: OrderedTable[int, seq[string]]
                                          ## arm-parallel field names
      vPlainFields*: seq[SymVal]          ## plain (always-present) field
                                          ## SymVals — shared across all
                                          ## arms; allocated once;
                                          ## survives discriminator
                                          ## reassignment.
      vPlainFieldNames*: seq[string]
    of svMultiVariant:
      ## Phase 14 cycle A1c per ADR-0003 D1. Symmetric with svVariant
      ## but holds one VariantAxisSym per discriminator. Each axis
      ## is independently constrained over `pcOut`; the walker's
      ## field-access path identifies the axis by field-name
      ## membership in any of the axis's arm field-name lists.
      mvObjectName*:      string
      mvAxes*:            seq[VariantAxisSym]
      mvPlainFields*:     seq[SymVal]
      mvPlainFieldNames*: seq[string]
    of svUninterpRef:
      ## Phase 15 Z3b. Opaque reference: an uninterpreted-sort Z3 ast plus
      ## diagnostic names. Fields are not modelled; produced by cluster E.
      uninterpAst*: Z3AnyAst
      sortName*:    string   ## Z3 uninterpreted-sort name (e.g. "ExnRef_ValueError")
      typeTag*:     string   ## Nim type name, for diagnostics
    of svFloat32:
      fp32*: Z3Float32       ## Phase 15 F1
    of svFloat64:
      fp64*: Z3Float64       ## Phase 15 F1

  VariantAxisSym* = object
    discName*:      string
    disc*:          ref SymVal
    armFields*:     OrderedTable[int, seq[SymVal]]
    armFieldNames*: OrderedTable[int, seq[string]]

  Env = OrderedTable[string, SymVal]

  Path = ref object
    pc:        seq[Z3Bool]
    env:       Env
    uncertain: bool   ## true once any call along this path has bailed
                      ## (maxCallDepth exceeded). A target hit on an
                      ## uncertain path can't be reported as a sound
                      ## witness — it degrades to sxUnknown.

  RawWitness = object
    paramOrder: seq[string]
    intVals:    Table[string, int64]
    uintVals:   Table[string, uint64]
    boolVals:   Table[string, bool]
    strVals:    Table[string, string]
    seqLens:    Table[string, int]   ## Phase 5: per-param seq length
    tabKeys:    Table[string, seq[string]]  ## Phase 5: per-Table key list
    setMembers: Table[string, seq[int64]]   ## Phase 5: per-HashSet members

  RawResult* = object
    abstractions*: AbstractionLog
    callStats*:    CallStats
    errors*:       seq[SymexErrorInfo]
      ## Phase 14 cycle C4. Z3-layer errors caught at runSymex's top
      ## level. Always empty on a clean run; populated when a typed
      ## `Z3Error` is thrown by the solver. Translated into per-
      ## target `SymexFinding.errors` by the macro-emitted runtime
      ## in `symex.nim`. `ValueError` and `AssertionDefect` from
      ## walker logic are NOT caught — those are real walker bugs.
    case status*: SymexStatusKind
    of sxSat:
      witness*: RawWitness
    of sxUnsat, sxUnknown:
      discard

# ---- SymVal lifting helpers -------------------------------------------------

template liftBV[W: static int](x: Z3BitVec[W], isSigned: bool): SymVal =
  ## Construct the matching SymVal variant for a given static-width BV.
  when W == 8:
    SymVal(kind: svBV8,  signed: isSigned, bv8:  x)
  elif W == 16:
    SymVal(kind: svBV16, signed: isSigned, bv16: x)
  elif W == 32:
    SymVal(kind: svBV32, signed: isSigned, bv32: x)
  elif W == 64:
    SymVal(kind: svBV64, signed: isSigned, bv64: x)
  else:
    {.error: "liftBV: unsupported width " & $W.}

template ofBool*(x: Z3Bool): SymVal =
  SymVal(kind: svBool, bo: x)

# Construct a SymVal from an IRType + a constant Nim integer value.
proc bvConst(ty: IRType, n: int64): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVec[8](n),  ty.signed)
  of 16: liftBV(mkBitVec[16](n), ty.signed)
  of 32: liftBV(mkBitVec[32](n), ty.signed)
  of 64: liftBV(mkBitVec[64](n), ty.signed)
  else:  raise newException(ValueError,
                            "bvConst: unsupported width " & $ty.width)

proc bvVar(ty: IRType, name: string): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVecVar[8](name),  ty.signed)
  of 16: liftBV(mkBitVecVar[16](name), ty.signed)
  of 32: liftBV(mkBitVecVar[32](name), ty.signed)
  of 64: liftBV(mkBitVecVar[64](name), ty.signed)
  else:  raise newException(ValueError,
                            "bvVar: unsupported width " & $ty.width)

proc allocateSeqDataRaw(elemTy: IRType, name: string): Z3AnyAst =
  ## Dispatch on the element type to instantiate `Z3Array[Z3Int, V]`
  ## with the right typed V, then erase via `toAnyAst`. Cycle 1
  ## supports int/bool elements; more arrive incrementally.
  case elemTy.kind
  of itBool:
    toAnyAst(mkArrayVar[Z3Int, Z3Bool](name))
  of itInt:
    case elemTy.width
    of 8:  toAnyAst(mkArrayVar[Z3Int, Z3BitVec[8]](name))
    of 16: toAnyAst(mkArrayVar[Z3Int, Z3BitVec[16]](name))
    of 32: toAnyAst(mkArrayVar[Z3Int, Z3BitVec[32]](name))
    of 64: toAnyAst(mkArrayVar[Z3Int, Z3BitVec[64]](name))
    else:
      raise newException(ValueError,
        "allocateSeqDataRaw: unsupported int width " & $elemTy.width)
  else:
    raise newException(ValueError,
      "allocateSeqDataRaw: unsupported element kind " & $elemTy.kind)

proc mkZ3IntLit(v: int64): Z3Int {.inline.} =
  ## Phase 14 A6 (moved earlier from the abstraction layer block).
  ## Build a Z3Int from an `int64`. `mkInt` truncates to `cint`
  ## (32 bits on Linux); for values that don't fit, route through
  ## `mkBigInt`'s decimal-string ctor.
  if v >= int64(low(int32)) and v <= int64(high(int32)):
    mkInt(int(v))
  else:
    mkBigInt($v)

proc allocateSym(ty: IRType, baseName: string,
                 pcOut: var seq[Z3Bool]): SymVal =
  ## Recursively allocate a SymVal for `ty`. Init-side constraints
  ## (like `seqLen ≥ 0`) accumulate into `pcOut`.
  case ty.kind
  of itUninterp:
    raise newException(ValueError,
      "allocateSym(itUninterp): uninterpreted-ref allocation lands with cluster E")
  of itFloat32: SymVal(kind: svFloat32, fp32: mkFloat32Var(baseName))
  of itFloat64: SymVal(kind: svFloat64, fp64: mkFloat64Var(baseName))
  of itVariant:
    # Phase 11 cycle 3 — allocate the discriminator and every arm's
    # per-arm field symbols. Constrain the discriminator to the
    # disjunction of legal arm ordinals so Z3 never picks an out-
    # of-range tag.
    let discInner = allocateSym(ty.vDiscTy,
                                 baseName & "." & ty.vDiscName, pcOut)
    let discBoxed = new(SymVal)
    discBoxed[] = discInner
    # Plain fields: allocated ONCE; shared across every arm. Their
    # witness paths are `<baseName>.<plainFieldName>` (no @tag).
    var plainFields: seq[SymVal]
    for i, ft in ty.vPlainFieldTypes:
      let path = baseName & "." & ty.vPlainFieldNames[i]
      plainFields.add allocateSym(ft, path, pcOut)
    var armFields = initOrderedTable[int, seq[SymVal]]()
    var armNames  = initOrderedTable[int, seq[string]]()
    var armEqClauses: seq[Z3Bool]
    var hasElse = false
    proc discEq(d: SymVal, tagOrd: int64): Z3Bool =
      case d.kind
      of svBV8:  d.bv8  == mkBitVec[8](tagOrd)
      of svBV16: d.bv16 == mkBitVec[16](tagOrd)
      of svBV32: d.bv32 == mkBitVec[32](tagOrd)
      of svBV64: d.bv64 == mkBitVec[64](tagOrd)
      of svInt:  d.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
      else:
        raise newException(ValueError,
          "symex Phase 14: variant discriminator must be a BV or " &
          "Z3Int kind (got " & $d.kind & ")")
    for arm in ty.vArms:
      var fields: seq[SymVal]
      for j, ft in arm.fieldTypes:
        let path = baseName & ".@" & arm.tagName & "." & arm.fieldNames[j]
        fields.add allocateSym(ft, path, pcOut)
      armFields[arm.tagOrdinal] = fields
      armNames[arm.tagOrdinal]  = arm.fieldNames
      # Phase 14 cycle A2: else arm contributes NO direct equality
      # disjunct (its membership constraint is the conjunction of
      # negations against the non-else arms — emitted lazily at
      # `isVariantField` lowering time). The else arm's coverage is
      # instead supplied by the dord-fanout below.
      if arm.isElse:
        hasElse = true
        continue
      armEqClauses.add discEq(discInner, int64(arm.tagOrdinal))
    # Phase 14 cycle A2: when an else arm is present, expand the
    # disjunction to cover ALL disc-enum ordinals (not just the
    # non-else arms') so Z3 can pick any legal disc value, including
    # those covered ONLY by the else arm. Without an else arm, the
    # per-arm disjunction is exhaustive by Nim's variant validity
    # rules and no expansion is needed.
    if hasElse:
      for dt in ty.vDiscTags:
        # Skip ordinals already covered by a non-else arm — they're
        # in armEqClauses already.
        var inNonElse = false
        for arm in ty.vArms:
          if (not arm.isElse) and arm.tagOrdinal == dt.ord:
            inNonElse = true; break
        if inNonElse: continue
        armEqClauses.add discEq(discInner, int64(dt.ord))
    if armEqClauses.len > 0:
      var clause = armEqClauses[0]
      for k in 1 ..< armEqClauses.len:
        clause = clause or armEqClauses[k]
      pcOut.add clause
    SymVal(kind: svVariant, vDisc: discBoxed, vDiscName: ty.vDiscName,
           vObjectName: ty.vObjectName,
           vArmFields: armFields, vArmFieldNames: armNames,
           vPlainFields: plainFields,
           vPlainFieldNames: ty.vPlainFieldNames)
  of itMultiVariant:
    # Phase 14 cycle A1c per ADR-0003 D1. Each axis is allocated
    # independently: its discriminator gets a fresh BV symbol and
    # the arm-ordinal disjunction is appended to pcOut. Per-axis
    # arm fields are allocated up front (the walker reads them
    # conditionally on the disc value). Plain fields are shared
    # across all axes — same semantics as Phase 11's plain-field
    # sharing in itVariant.
    var plainFields: seq[SymVal]
    for i, ft in ty.mvPlainFieldTypes:
      let path = baseName & "." & ty.mvPlainFieldNames[i]
      plainFields.add allocateSym(ft, path, pcOut)
    var axisSyms: seq[VariantAxisSym]
    for ax in ty.mvAxes:
      let discInner = allocateSym(ax.discTy,
                                  baseName & "." & ax.discName, pcOut)
      let discBoxed = new(SymVal)
      discBoxed[] = discInner
      var armFields = initOrderedTable[int, seq[SymVal]]()
      var armNames  = initOrderedTable[int, seq[string]]()
      var armEqClauses: seq[Z3Bool]
      for arm in ax.arms:
        var fields: seq[SymVal]
        for j, ft in arm.fieldTypes:
          let path = baseName & "." & ax.discName &
                     ".@" & arm.tagName & "." & arm.fieldNames[j]
          fields.add allocateSym(ft, path, pcOut)
        armFields[arm.tagOrdinal] = fields
        armNames[arm.tagOrdinal]  = arm.fieldNames
        let tagOrd = int64(arm.tagOrdinal)
        let eqBool =
          case discInner.kind
          of svBV8:  discInner.bv8  == mkBitVec[8](tagOrd)
          of svBV16: discInner.bv16 == mkBitVec[16](tagOrd)
          of svBV32: discInner.bv32 == mkBitVec[32](tagOrd)
          of svBV64: discInner.bv64 == mkBitVec[64](tagOrd)
          else:
            raise newException(ValueError,
              "symex Phase 14: multi-variant axis disc must be a BV kind " &
              "(got " & $discInner.kind & ")")
        armEqClauses.add eqBool
      if armEqClauses.len > 0:
        var clause = armEqClauses[0]
        for k in 1 ..< armEqClauses.len:
          clause = clause or armEqClauses[k]
        pcOut.add clause
      axisSyms.add VariantAxisSym(
        discName: ax.discName, disc: discBoxed,
        armFields: armFields, armFieldNames: armNames)
    SymVal(kind: svMultiVariant, mvObjectName: ty.mvObjectName,
           mvAxes: axisSyms,
           mvPlainFields: plainFields,
           mvPlainFieldNames: ty.mvPlainFieldNames)
  of itInt:
    bvVar(ty, baseName)
  of itBool:
    SymVal(kind: svBool, bo: mkBoolVar(baseName))
  of itString:
    SymVal(kind: svString, str: mkStringVar(baseName))
  of itTuple:
    var fields: seq[SymVal]
    for i, ft in ty.fields:
      let suffix = if ty.fieldNames[i].len > 0: "." & ty.fieldNames[i]
                   else: "." & $i
      fields.add allocateSym(ft, baseName & suffix, pcOut)
    SymVal(kind: svTuple, fields: fields, fieldNames: ty.fieldNames)
  of itArray:
    # #142: nested arrays land via the existing recursion. The
    # previous guard was overly cautious — allocateSym recurses
    # naturally through the element type.
    var elems: seq[SymVal]
    for i in 0 ..< ty.size:
      elems.add allocateSym(ty.elemTy, baseName & "." & $i, pcOut)
    SymVal(kind: svArray, arrElems: elems, arrElemTy: ty.elemTy)
  of itSeq:
    let lenSym = mkIntVar(baseName & ".len")
    # Sanity floor + ceiling so the model returns Nim-representable
    # lengths. The ceiling of 1024 is chosen so that any reasonable
    # path-condition is still satisfiable while Z3 doesn't pick
    # values that overflow `cint` during witness extraction.
    pcOut.add (lenSym >= mkInt(0))
    pcOut.add (lenSym <= mkInt(1024))
    let dataRaw = allocateSeqDataRaw(ty.seqElemTy, baseName & ".data")
    SymVal(kind: svSeq, seqLen: lenSym,
           seqDataRaw: dataRaw, seqElemTy: ty.seqElemTy)
  of itTable:
    # Phase 5 cycle 5 narrow scope: Table[string, int]. Other (K, V)
    # pairs land incrementally — the wrap[Z3Array[K, V]] machinery
    # supports them with a per-pair dispatch.
    if ty.tabKeyTy.kind != itString:
      raise newException(ValueError,
        "Phase 5 cycle 5: only Table[string, V] supported (got key=" &
        $ty.tabKeyTy & ")")
    case ty.tabValTy.kind
    of itInt:
      doAssert ty.tabValTy.width == 64 and ty.tabValTy.signed,
        "Phase 5 cycle 5: only Table[string, int] supported"
      let dataAst = toAnyAst(
        mkArrayVar[Z3String, Z3BitVec[64]](baseName & ".data"))
      let presentAst = toAnyAst(
        mkArrayVar[Z3String, Z3Bool](baseName & ".present"))
      let sizeSym = mkIntVar(baseName & ".len")
      pcOut.add (sizeSym >= mkInt(0))
      pcOut.add (sizeSym <= mkInt(1024))   ## same ceiling as seqs
      SymVal(kind: svTable, tabDataRaw: dataAst,
             tabPresentRaw: presentAst, tabSize: sizeSym,
             tabKeyTy: ty.tabKeyTy, tabValTy: ty.tabValTy)
    else:
      raise newException(ValueError,
        "Phase 5 cycle 5: unsupported Table value " & $ty.tabValTy)
  of itSet:
    if ty.setElemTy.kind == itInt and ty.setElemTy.width == 64:
      let memAst = toAnyAst(
        mkArrayVar[Z3BitVec[64], Z3Bool](baseName & ".members"))
      let sizeSym = mkIntVar(baseName & ".len")
      pcOut.add (sizeSym >= mkInt(0))
      pcOut.add (sizeSym <= mkInt(1024))
      SymVal(kind: svSet, setMembersRaw: memAst,
             setSize: sizeSym, setElemTy: ty.setElemTy)
    else:
      raise newException(ValueError,
        "Phase 5 cycle 8: unsupported HashSet element type " & $ty.setElemTy)

proc tyOf(sv: SymVal): IRType =
  case sv.kind
  of svUninterpRef: tUninterp(sv.sortName)
  of svFloat32: tFloat32()
  of svFloat64: tFloat64()
  of svBV8:  tInt(8,  sv.signed)
  of svBV16: tInt(16, sv.signed)
  of svBV32: tInt(32, sv.signed)
  of svBV64: tInt(64, sv.signed)
  of svInt:  tInt(64, true)
  of svBool: tBool()
  of svTuple:
    var ftys: seq[IRType]
    for f in sv.fields: ftys.add tyOf(f)
    tTuple(ftys, sv.fieldNames)
  of svArray:
    tArray(sv.arrElemTy, sv.arrElems.len)
  of svString:
    tString()
  of svSeq:
    tSeq(sv.seqElemTy)
  of svTable:
    tTable(sv.tabKeyTy, sv.tabValTy)
  of svSet:
    tSet(sv.setElemTy)
  of svVariant:
    # Reconstruct the IRType from the live SymVal. Used only for
    # diagnostics; cycle 7's witness emitter consults the SUT's
    # macro-time IR directly.
    var arms: seq[VariantArm]
    for tagOrdinal, fields in sv.vArmFields.pairs:
      var tys: seq[IRType]
      for f in fields: tys.add tyOf(f)
      arms.add VariantArm(tagOrdinal: tagOrdinal,
                          tagName: "",  # not preserved on the SymVal
                          fieldNames: sv.vArmFieldNames[tagOrdinal],
                          fieldTypes: tys)
    tVariant(sv.vObjectName, sv.vDiscName, tyOf(sv.vDisc[]), arms)
  of svMultiVariant:
    # Phase 14 cycle A1c. Diagnostics-only: rebuild the IRType from
    # the SymVal's axes. Tag names are not preserved on the SymVal
    # (same gap as svVariant).
    var axes: seq[VariantAxis]
    for ax in sv.mvAxes:
      var arms: seq[VariantArm]
      for tagOrdinal, fields in ax.armFields.pairs:
        var tys: seq[IRType]
        for f in fields: tys.add tyOf(f)
        arms.add VariantArm(tagOrdinal: tagOrdinal, tagName: "",
                            fieldNames: ax.armFieldNames[tagOrdinal],
                            fieldTypes: tys)
      axes.add VariantAxis(discName: ax.discName,
                           discTy: tyOf(ax.disc[]), arms: arms)
    mkMultiVariant(sv.mvObjectName, axes)

# ---- Prototype probe over the IR --------------------------------------------
#
# Each non-trivial subexpression takes its representation (Z3 BV[W] vs
# Z3Int) from a "prototype" SymVal — the first env-resident variable
# its subtree reaches. Literals coerce to match the prototype; arith
# / comparison ops dispatch on the prototype kind.
#
# When no env-resident var is reachable (e.g. `5 + 6`), no prototype
# exists and the caller defaults to BV[64] signed.

proc probeProto(env: Env, e: IRExpr): Option[SymVal] =
  if e == nil: return none(SymVal)
  case e.kind
  of iekVar:
    if env.hasKey(e.vname): some(env[e.vname]) else: none(SymVal)
  of iekBinop:
    let l = probeProto(env, e.lhs)
    if l.isSome: l else: probeProto(env, e.rhs)
  of iekUnop:
    probeProto(env, e.operand)
  of iekField:
    let inner = probeProto(env, e.obj)
    if inner.isSome and inner.get.kind == svTuple:
      some(inner.get.fields[e.fieldIx])
    else: none(SymVal)
  of iekIndex:
    # For Phase 4: probe propagation through array index is not
    # straightforward without lowering the array. The caller will
    # resolve at the iekIndex lowering site.
    none(SymVal)
  of iekArrayLit:
    for c in e.lelems:
      let p = probeProto(env, c)
      if p.isSome: return p
    none(SymVal)
  of iekSeqAdd, iekSeqDel, iekSeqInsert, iekSeqPop,
     iekTableSet, iekTableDel, iekSetIncl, iekSetExcl:
    # Mutation expressions produce container SymVals; arithmetic
    # surrounding them is rare. Don't return a proto.
    none(SymVal)
  of iekSeqLen:
    # `s.len` produces a Z3Int. Return an svInt sentinel so the
    # surrounding op (comparison, arithmetic) lowers literals at the
    # right representation.
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekStrLit:
    none(SymVal)
  of iekContains:
    none(SymVal)
  of iekIntLit, iekFloatLit, iekBoolLit:
    none(SymVal)

# ---- IR-expr → SymVal -------------------------------------------------------

proc lower(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal

proc bvToZ3Int(sv: SymVal): Z3Int =
  ## Z3-level conversion of a typed BV SymVal to Z3Int. Used when a
  ## BV-shaped value (e.g. a Nim `int` param `i`) meets a Z3Int-shaped
  ## operand (e.g. `s.len`). Z3's `bv2int` is the canonical conversion.
  template wrapIt(bv: untyped): Z3Int =
    wrap[Z3Int](bv.ctx,
      bv.ctx.checkErr Z3_mk_bv2int(bv.ctx.raw, bv.raw, sv.signed))
  case sv.kind
  of svBV8:  wrapIt(sv.bv8)
  of svBV16: wrapIt(sv.bv16)
  of svBV32: wrapIt(sv.bv32)
  of svBV64: wrapIt(sv.bv64)
  else:
    raise newException(ValueError,
      "bvToZ3Int: not a BV — got " & $sv.kind)

proc toZ3Int(sv: SymVal): Z3Int =
  ## Coerce an int-typed SymVal (svInt or BV) to Z3Int.
  case sv.kind
  of svInt: sv.zi
  of svBV8, svBV16, svBV32, svBV64: bvToZ3Int(sv)
  else:
    raise newException(ValueError,
      "toZ3Int: not an int-typed SymVal — got " & $sv.kind)

proc iteSV(cond: Z3Bool, t, e: SymVal): SymVal =
  ## Z3-level if-then-else over SymVals. Both branches must share kind.
  doAssert t.kind == e.kind, "iteSV: kind mismatch " &
    $t.kind & " vs " & $e.kind
  case t.kind
  of svUninterpRef:
    raise newException(ValueError, "iteSV: svUninterpRef merge lands with cluster E")
  of svFloat32, svFloat64:
    raise newException(ValueError, "iteSV: float path-merge lands with F3/F4")
  of svBool: ofBool(ite(cond, t.bo, e.bo))
  of svInt:  SymVal(kind: svInt, zi: ite(cond, t.zi, e.zi))
  of svBV8:  liftBV(ite(cond, t.bv8,  e.bv8),  t.signed)
  of svBV16: liftBV(ite(cond, t.bv16, e.bv16), t.signed)
  of svBV32: liftBV(ite(cond, t.bv32, e.bv32), t.signed)
  of svBV64: liftBV(ite(cond, t.bv64, e.bv64), t.signed)
  of svTuple:
    var fs: seq[SymVal]
    for i, ft in t.fields: fs.add iteSV(cond, ft, e.fields[i])
    SymVal(kind: svTuple, fields: fs, fieldNames: t.fieldNames)
  of svArray:
    var fs: seq[SymVal]
    for i, ae in t.arrElems: fs.add iteSV(cond, ae, e.arrElems[i])
    SymVal(kind: svArray, arrElems: fs, arrElemTy: t.arrElemTy)
  of svString, svSeq, svTable, svSet, svVariant, svMultiVariant:
    raise newException(ValueError,
      "iteSV: not supported for " & $t.kind & " (Phase 5+)")

proc symEq(a, b: SymVal): Z3Bool =
  ## Equality of two same-kind primitive SymVals as a Z3Bool.
  doAssert a.kind == b.kind
  case a.kind
  of svBool: a.bo == b.bo
  of svInt:  a.zi == b.zi
  of svBV8:  a.bv8  == b.bv8
  of svBV16: a.bv16 == b.bv16
  of svBV32: a.bv32 == b.bv32
  of svBV64: a.bv64 == b.bv64
  else:
    raise newException(ValueError,
      "symEq: not a primitive — got " & $a.kind)

proc coerceIntLit(proto: SymVal, ival: int64): SymVal =
  ## Build a SymVal representing literal `ival` at `proto`'s
  ## representation. Used when an `iekIntLit`'s Z3 representation
  ## must match a surrounding variable.
  case proto.kind
  of svUninterpRef:
    raise newException(ValueError, "symLit: svUninterpRef has no integer form (cluster E)")
  of svFloat32, svFloat64:
    raise newException(ValueError, "symLit: float has no integer form (F2 owns float literals)")
  of svBV8:  liftBV(mkBitVec[8](ival),  proto.signed)
  of svBV16: liftBV(mkBitVec[16](ival), proto.signed)
  of svBV32: liftBV(mkBitVec[32](ival), proto.signed)
  of svBV64: liftBV(mkBitVec[64](ival), proto.signed)
  of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(ival))
  of svBool:
    raise newException(ValueError,
      "coerceIntLit: bool prototype for integer literal")
  of svTuple, svArray, svString, svSeq, svTable, svSet, svVariant, svMultiVariant:
    raise newException(ValueError,
      "coerceIntLit: composite prototype for integer literal kind=" & $proto.kind)

# Width-uniform BV arithmetic. Both operands must be the same width.
template binBV(a, b: SymVal, op: untyped): SymVal =
  ## Apply `op(va, vb)` where `va`/`vb` are the typed BV handles.
  ## Asserts both SymVals share a BV kind.
  doAssert a.kind == b.kind, "binBV: width mismatch"
  case a.kind
  of svBV8:
    liftBV(op(a.bv8, b.bv8), a.signed)
  of svBV16:
    liftBV(op(a.bv16, b.bv16), a.signed)
  of svBV32:
    liftBV(op(a.bv32, b.bv32), a.signed)
  of svBV64:
    liftBV(op(a.bv64, b.bv64), a.signed)
  else:
    raise newException(ValueError, "binBV on non-BV SymVal")

template cmpBV(a, b: SymVal, sop, uop: untyped): SymVal =
  ## Apply signed/unsigned comparison and lift to SymVal Bool.
  doAssert a.kind == b.kind, "cmpBV: width mismatch"
  let useSigned = a.signed
  case a.kind
  of svBV8:
    ofBool(if useSigned: sop(a.bv8,  b.bv8)  else: uop(a.bv8,  b.bv8))
  of svBV16:
    ofBool(if useSigned: sop(a.bv16, b.bv16) else: uop(a.bv16, b.bv16))
  of svBV32:
    ofBool(if useSigned: sop(a.bv32, b.bv32) else: uop(a.bv32, b.bv32))
  of svBV64:
    ofBool(if useSigned: sop(a.bv64, b.bv64) else: uop(a.bv64, b.bv64))
  else:
    raise newException(ValueError, "cmpBV on non-BV SymVal")

template divBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: bvsdiv(a.bv8,  b.bv8)  else: bvudiv(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: bvsdiv(a.bv16, b.bv16) else: bvudiv(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: bvsdiv(a.bv32, b.bv32) else: bvudiv(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: bvsdiv(a.bv64, b.bv64) else: bvudiv(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "divBV on non-BV SymVal")

template modBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: bvsmod(a.bv8,  b.bv8)  else: bvurem(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: bvsmod(a.bv16, b.bv16) else: bvurem(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: bvsmod(a.bv32, b.bv32) else: bvurem(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: bvsmod(a.bv64, b.bv64) else: bvurem(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "modBV on non-BV SymVal")

template shrBV(a, b: SymVal): SymVal =
  ## Nim `shr` on signed → arithmetic (ashr); on unsigned → logical (lshr).
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: ashr(a.bv8,  b.bv8)  else: lshr(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: ashr(a.bv16, b.bv16) else: lshr(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: ashr(a.bv32, b.bv32) else: lshr(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: ashr(a.bv64, b.bv64) else: lshr(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "shrBV on non-BV SymVal")

template negBV(a: SymVal): SymVal =
  case a.kind
  of svBV8:  liftBV(-a.bv8,  a.signed)
  of svBV16: liftBV(-a.bv16, a.signed)
  of svBV32: liftBV(-a.bv32, a.signed)
  of svBV64: liftBV(-a.bv64, a.signed)
  else: raise newException(ValueError, "negBV on non-BV SymVal")

template notBV(a: SymVal): SymVal =
  case a.kind
  of svBV8:  liftBV(not a.bv8,  a.signed)
  of svBV16: liftBV(not a.bv16, a.signed)
  of svBV32: liftBV(not a.bv32, a.signed)
  of svBV64: liftBV(not a.bv64, a.signed)
  else: raise newException(ValueError, "notBV on non-BV SymVal")

# ---- Equality across BV widths is uniform -----------------------------------

template eqBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  case a.kind
  of svBV8:  ofBool(a.bv8  == b.bv8)
  of svBV16: ofBool(a.bv16 == b.bv16)
  of svBV32: ofBool(a.bv32 == b.bv32)
  of svBV64: ofBool(a.bv64 == b.bv64)
  else: raise newException(ValueError, "eqBV on non-BV SymVal")

template neBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  case a.kind
  of svBV8:  ofBool(a.bv8  != b.bv8)
  of svBV16: ofBool(a.bv16 != b.bv16)
  of svBV32: ofBool(a.bv32 != b.bv32)
  of svBV64: ofBool(a.bv64 != b.bv64)
  else: raise newException(ValueError, "neBV on non-BV SymVal")

# ---- Lowering ---------------------------------------------------------------

proc mkFloatLitSym(v: float64, width: int): SymVal =
  ## Phase 15 F2: lower a float literal to a Z3 FP numeral, honoring
  ## NaN / ±Inf / -0.0 (ADR-0005) via Nim's `classify`.
  let cls = classify(v)
  if width == 32:
    SymVal(kind: svFloat32, fp32:
      (case cls
       of fcNan:     mkFpNaN[8, 24]()
       of fcInf:     mkFpInf[8, 24](false)
       of fcNegInf:  mkFpInf[8, 24](true)
       of fcNegZero: mkFpZero[8, 24](true)
       else:         mkFloat32(float32(v))))
  else:
    SymVal(kind: svFloat64, fp64:
      (case cls
       of fcNan:     mkFpNaN[11, 53]()
       of fcInf:     mkFpInf[11, 53](false)
       of fcNegInf:  mkFpInf[11, 53](true)
       of fcNegZero: mkFpZero[11, 53](true)
       else:         mkFloat64(v)))

proc cmpFloat(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 F2: IEEE equality via Z3 FP theory (`==`/`!=` on Z3Fp are
  ## IEEE, so NaN == NaN is false). F4 adds ordering (`<` `<=` `>` `>=`).
  doAssert a.kind == b.kind and a.kind in {svFloat32, svFloat64}
  if a.kind == svFloat32:
    case op
    of bEq: ofBool(a.fp32 == b.fp32)
    of bNe: ofBool(a.fp32 != b.fp32)
    else: raise newException(ValueError, "cmpFloat: ordering ops land in F4")
  else:
    case op
    of bEq: ofBool(a.fp64 == b.fp64)
    of bNe: ofBool(a.fp64 != b.fp64)
    else: raise newException(ValueError, "cmpFloat: ordering ops land in F4")

proc arithFloat(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 F3: IEEE arithmetic via Z3 FP theory. The Z3Fp `+ - * /`
  ## operators default to round-to-nearest-even (ADR-0005 / OQ2). Division
  ## by zero follows IEEE (yields ±Inf / NaN) — not a defect.
  doAssert a.kind == b.kind and a.kind in {svFloat32, svFloat64}
  if a.kind == svFloat32:
    SymVal(kind: svFloat32, fp32:
      (case op
       of bAdd: a.fp32 + b.fp32
       of bSub: a.fp32 - b.fp32
       of bMul: a.fp32 * b.fp32
       of bDiv: a.fp32 / b.fp32
       else: raise newException(ValueError, "arithFloat: " & $op & " not a float arith op")))
  else:
    SymVal(kind: svFloat64, fp64:
      (case op
       of bAdd: a.fp64 + b.fp64
       of bSub: a.fp64 - b.fp64
       of bMul: a.fp64 * b.fp64
       of bDiv: a.fp64 / b.fp64
       else: raise newException(ValueError, "arithFloat: " & $op & " not a float arith op")))

proc arithInt(a, b: SymVal, op: IRBinop): SymVal =
  doAssert a.kind == svInt and b.kind == svInt
  case op
  of bAdd: SymVal(kind: svInt, zi: a.zi + b.zi)
  of bSub: SymVal(kind: svInt, zi: a.zi - b.zi)
  of bMul: SymVal(kind: svInt, zi: a.zi * b.zi)
  of bDiv: SymVal(kind: svInt, zi: a.zi div b.zi)
  of bMod: SymVal(kind: svInt, zi: a.zi mod b.zi)
  else: raise newException(ValueError, "arithInt: not an arithmetic op")

proc cmpInt(a, b: SymVal, op: IRBinop): SymVal =
  doAssert a.kind == svInt and b.kind == svInt
  case op
  of bEq: ofBool(a.zi == b.zi)
  of bNe: ofBool(a.zi != b.zi)
  of bLt: ofBool(a.zi <  b.zi)
  of bLe: ofBool(a.zi <= b.zi)
  of bGt: ofBool(a.zi >  b.zi)
  of bGe: ofBool(a.zi >= b.zi)
  else: raise newException(ValueError, "cmpInt: not a comparison op")

proc lower(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal =
  if e == nil:
    raise newException(ValueError, "lower: nil expression")
  case e.kind
  of iekIntLit:
    if proto.isSome and proto.get.kind != svBool:
      coerceIntLit(proto.get, e.ival)
    else:
      bvConst(tInt(64, true), e.ival)
  of iekFloatLit:
    mkFloatLitSym(e.fval, e.fwidth)
  of iekBoolLit:
    ofBool(mkBool(e.bval))
  of iekVar:
    env[e.vname]
  of iekField:
    # Lower the receiver, then pick the field by index (tuple) or
    # by name (variant — Phase 11).
    let recv = lower(env, e.obj)
    case recv.kind
    of svTuple:
      recv.fields[e.fieldIx]
    of svVariant:
      # iekField on a variant: discriminator or plain (shared)
      # field. Arm-specific access takes the `isVariantField`
      # statement-level path (parser A-normalises so the walker
      # can fork). Any arm-field that reaches here is a parser
      # bug — fail loud.
      if e.fieldName == recv.vDiscName:
        recv.vDisc[]
      elif e.fieldName in recv.vPlainFieldNames:
        let ix = recv.vPlainFieldNames.find(e.fieldName)
        recv.vPlainFields[ix]
      else:
        raise newException(ValueError,
          "symex Phase 11: arm-specific field `" & e.fieldName &
          "` reached lower(iekField) on svVariant — parser should " &
          "have A-normalised this through isVariantField")
    of svMultiVariant:
      # Phase 14 cycle A1d. Same contract as svVariant: only the
      # per-axis discriminators and the (shared) plain fields are
      # legal here; arm-specific access is parser-routed through
      # `isVariantField`. Plain fields are matched first because
      # they're shared across all axes.
      if e.fieldName in recv.mvPlainFieldNames:
        let ix = recv.mvPlainFieldNames.find(e.fieldName)
        recv.mvPlainFields[ix]
      else:
        var found: SymVal
        var hit = false
        for ax in recv.mvAxes:
          if e.fieldName == ax.discName:
            found = ax.disc[]; hit = true; break
        if hit: found
        else:
          raise newException(ValueError,
            "symex Phase 14: arm-specific field `" & e.fieldName &
            "` reached lower(iekField) on svMultiVariant — parser " &
            "should have A-normalised this through isVariantField")
    else:
      raise newException(ValueError,
        "iekField on unsupported SymVal kind=" & $recv.kind)
  of iekSeqLen:
    let recv = lower(env, e.lenObj)
    case recv.kind
    of svSeq:   SymVal(kind: svInt, zi: recv.seqLen)
    of svTable: SymVal(kind: svInt, zi: recv.tabSize)
    of svSet:   SymVal(kind: svInt, zi: recv.setSize)
    else:
      raise newException(ValueError,
        "iekSeqLen on non-container kind=" & $recv.kind)
  of iekStrLit:
    SymVal(kind: svString, str: mkString(e.sval))
  of iekSeqAdd:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svSeq, "iekSeqAdd: receiver not svSeq"
    let val = lower(env, e.mutArg)
    # New seq: data = store(old.data, old.len, val); len = old.len + 1
    let oldLen = recv.seqLen
    let newLen = oldLen + mkInt(1)
    var newDataRaw: Z3AnyAst
    case recv.seqElemTy.kind
    of itInt:
      case recv.seqElemTy.width
      of 64:
        let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
          recv.seqDataRaw.ctx, recv.seqDataRaw.raw)
        let vbv = case val.kind
          of svBV64: val.bv64
          of svInt:  mkBitVec[64](0'i64)  ## fallback (shouldn't happen)
          else: mkBitVec[64](0'i64)
        let stored = store(typed, oldLen, vbv)
        newDataRaw = toAnyAst(stored)
      else:
        raise newException(ValueError,
          "iekSeqAdd: unsupported width " & $recv.seqElemTy.width)
    of itBool:
      let typed = wrap[Z3Array[Z3Int, Z3Bool]](
        recv.seqDataRaw.ctx, recv.seqDataRaw.raw)
      doAssert val.kind == svBool
      newDataRaw = toAnyAst(store(typed, oldLen, val.bo))
    else:
      raise newException(ValueError,
        "iekSeqAdd: unsupported elem " & $recv.seqElemTy.kind)
    SymVal(kind: svSeq, seqLen: newLen,
           seqDataRaw: newDataRaw, seqElemTy: recv.seqElemTy)
  of iekTableSet:
    let recv = lower(env, e.tabRecv)
    doAssert recv.kind == svTable
    let keyProto = SymVal(kind: svString, str: mkString(""))
    let keySV = lower(env, e.tabKey, some(keyProto))
    doAssert keySV.kind == svString
    let val = lower(env, e.tabVal)
    # New table: data = store(old.data, k, v); present = store(old.present, k, true).
    # Size: increment if !present[k] before.
    case recv.tabValTy.kind
    of itInt:
      let typedData = wrap[Z3Array[Z3String, Z3BitVec[64]]](
        recv.tabDataRaw.ctx, recv.tabDataRaw.raw)
      let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
        recv.tabPresentRaw.ctx, recv.tabPresentRaw.raw)
      let vbv = case val.kind
        of svBV64: val.bv64
        else: mkBitVec[64](0'i64)
      let newData = store(typedData, keySV.str, vbv)
      let newPresent = store(typedPresent, keySV.str, mkBool(true))
      let wasPresent = select(typedPresent, keySV.str)
      # size += 1 if !wasPresent
      let newSize = SymVal(kind: svInt,
        zi: ite(wasPresent, recv.tabSize, recv.tabSize + mkInt(1)))
      SymVal(kind: svTable,
        tabDataRaw: toAnyAst(newData),
        tabPresentRaw: toAnyAst(newPresent),
        tabSize: newSize.zi,
        tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
    else:
      raise newException(ValueError,
        "iekTableSet: unsupported val " & $recv.tabValTy.kind)
  of iekTableDel:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svTable
    let keyProto = SymVal(kind: svString, str: mkString(""))
    let keySV = lower(env, e.mutArg, some(keyProto))
    let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
      recv.tabPresentRaw.ctx, recv.tabPresentRaw.raw)
    let wasPresent = select(typedPresent, keySV.str)
    let newPresent = store(typedPresent, keySV.str, mkBool(false))
    let newSize = ite(wasPresent, recv.tabSize - mkInt(1), recv.tabSize)
    SymVal(kind: svTable,
      tabDataRaw: recv.tabDataRaw,
      tabPresentRaw: toAnyAst(newPresent),
      tabSize: newSize,
      tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
  of iekSetIncl:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svSet
    let elem = lower(env, e.mutArg)
    doAssert elem.kind == svBV64
    let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
    let wasMember = select(typed, elem.bv64)
    let newMembers = store(typed, elem.bv64, mkBool(true))
    let newSize = ite(wasMember, recv.setSize, recv.setSize + mkInt(1))
    SymVal(kind: svSet,
      setMembersRaw: toAnyAst(newMembers),
      setSize: newSize, setElemTy: recv.setElemTy)
  of iekSetExcl:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svSet
    let elem = lower(env, e.mutArg)
    doAssert elem.kind == svBV64
    let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
    let wasMember = select(typed, elem.bv64)
    let newMembers = store(typed, elem.bv64, mkBool(false))
    let newSize = ite(wasMember, recv.setSize - mkInt(1), recv.setSize)
    SymVal(kind: svSet,
      setMembersRaw: toAnyAst(newMembers),
      setSize: newSize, setElemTy: recv.setElemTy)
  of iekSeqDel, iekSeqInsert, iekSeqPop:
    raise newException(ValueError,
      "Phase 5+: " & $e.kind & " lowering arrives with #143 follow-up")
  of iekContains:
    let recv = lower(env, e.container)
    case recv.kind
    of svTable:
      let keyProto = SymVal(kind: svString, str: mkString(""))
      let keySV = lower(env, e.key, some(keyProto))
      doAssert keySV.kind == svString
      let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
        recv.tabPresentRaw.ctx, recv.tabPresentRaw.raw)
      ofBool(select(typedPresent, keySV.str))
    of svSet:
      # For HashSet[int]: key is BV[64]; select(members, key) → Bool.
      doAssert recv.setElemTy.kind == itInt
      doAssert recv.setElemTy.width == 64
      let bv64Proto = SymVal(kind: svBV64, signed: true,
                             bv64: mkBitVec[64](0'i64))
      let keySV = lower(env, e.key, some(bv64Proto))
      doAssert keySV.kind == svBV64
      let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
        recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
      ofBool(select(typed, keySV.bv64))
    else:
      raise newException(ValueError,
        "iekContains on unsupported kind " & $recv.kind)
  of iekArrayLit:
    # Lower each element with a prototype matching the declared
    # element type. The first element's lowered SymVal becomes the
    # prototype for the rest (and for the array's SymVal kind).
    var elems: seq[SymVal]
    # Build a prototype SymVal from elemTy. For primitive types this
    # is a constant-zero SymVal of the right kind, used only for its
    # `kind`/`signed` shape via coerceIntLit.
    var protoSV: Option[SymVal] = none(SymVal)
    if e.lelemTy.kind == itInt:
      protoSV = some(bvConst(e.lelemTy, 0))
    elif e.lelemTy.kind == itBool:
      protoSV = some(ofBool(mkBool(false)))
    for c in e.lelems:
      elems.add lower(env, c, protoSV)
    SymVal(kind: svArray, arrElems: elems, arrElemTy: e.lelemTy)
  of iekIndex:
    let recv = lower(env, e.arr)
    doAssert recv.kind == svArray,
      "iekIndex on non-array kind=" & $recv.kind
    if e.idx.kind == iekIntLit:
      # Fast path: concrete index. No fork; direct element lookup.
      let ix = int(e.idx.ival)
      if ix < 0 or ix >= recv.arrElems.len:
        raise newException(ValueError,
          "Phase 4: literal index " & $ix & " out of bounds 0..<" &
          $recv.arrElems.len)
      recv.arrElems[ix]
    else:
      # Symbolic index: ite-chain over each element. Z3 picks an i.
      # The "default" branch (i below first match) falls through to
      # element[0] — for OOB-handling cycle 8, the OOB path forks
      # before this point and adds the OOB constraint to its pc.
      let idxSV = lower(env, e.idx)
      doAssert recv.arrElems.len > 0
      var res = recv.arrElems[0]
      for k in 1 ..< recv.arrElems.len:
        let kSV = coerceIntLit(idxSV, int64(k))
        let cond = symEq(idxSV, kSV)
        res = iteSV(cond, recv.arrElems[k], res)
      res
  of iekUnop:
    case e.uop
    of uNeg:
      let inner = lower(env, e.operand, proto)
      if inner.kind == svInt: SymVal(kind: svInt, zi: -inner.zi)
      elif inner.kind == svFloat32: SymVal(kind: svFloat32, fp32: -inner.fp32)  # Phase 15 F3
      elif inner.kind == svFloat64: SymVal(kind: svFloat64, fp64: -inner.fp64)  # Phase 15 F3
      else: negBV(inner)
    of uNot:
      let inner = lower(env, e.operand, some(ofBool(mkBool(true))))
      doAssert inner.kind == svBool
      ofBool(not inner.bo)
  of iekBinop:
    case e.bop
    # ---- comparison ops always produce Bool; operand repr from probe ----
    of bEq, bNe, bLt, bLe, bGt, bGe:
      let pp = probeProto(env, e)
      if pp.isSome:
        var l = lower(env, e.lhs, pp)
        var r = lower(env, e.rhs, pp)
        # Reconcile mixed int reps: bv2int both sides.
        if l.kind != r.kind and
           l.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
           r.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
          l = SymVal(kind: svInt, zi: toZ3Int(l))
          r = SymVal(kind: svInt, zi: toZ3Int(r))
        if l.kind == svInt:
          cmpInt(l, r, e.bop)
        elif l.kind == svBool:
          # Bool ==/!= only.
          case e.bop
          of bEq: ofBool(l.bo == r.bo)
          of bNe: ofBool(l.bo != r.bo)
          else:
            raise newException(ValueError,
              "comparison op " & $e.bop & " not valid on bool operands")
        elif l.kind in {svFloat32, svFloat64}:
          cmpFloat(l, r, e.bop)        # Phase 15 F2: IEEE ==/!=; F4 adds ordering
        else:
          case e.bop
          of bEq: eqBV(l, r)
          of bNe: neBV(l, r)
          of bLt: cmpBV(l, r, bvslt, bvult)
          of bLe: cmpBV(l, r, bvsle, bvule)
          of bGt: cmpBV(l, r, bvsgt, bvugt)
          of bGe: cmpBV(l, r, bvsge, bvuge)
          else: raise newException(ValueError, "unreachable")
      else:
        # No env-resident var via probe — but the lowered LHS might
        # still be svInt (e.g. `iekSeqLen`). Re-dispatch on its kind.
        let l = lower(env, e.lhs, none(SymVal))
        let r = lower(env, e.rhs, some(l))
        if l.kind == svInt:
          cmpInt(l, r, e.bop)
        elif l.kind in {svFloat32, svFloat64}:
          cmpFloat(l, r, e.bop)        # Phase 15 F2
        else:
          case e.bop
          of bEq: eqBV(l, r)
          of bNe: neBV(l, r)
          of bLt: cmpBV(l, r, bvslt, bvult)
          of bLe: cmpBV(l, r, bvsle, bvule)
          of bGt: cmpBV(l, r, bvsgt, bvugt)
          of bGe: cmpBV(l, r, bvsge, bvuge)
          else: raise newException(ValueError, "unreachable")
    # ---- boolean / bitwise dispatch by operand type ----
    of bAnd, bOr, bXor:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r = lower(env, e.rhs, pp)
      if l.kind == svBool:
        doAssert r.kind == svBool
        case e.bop
        of bAnd: ofBool(l.bo and r.bo)
        of bOr:  ofBool(l.bo or  r.bo)
        of bXor: ofBool(l.bo xor r.bo)
        else: raise newException(ValueError, "unreachable")
      elif l.kind == svInt:
        # Bitwise on Z3Int is not in Z3's Int theory; promotion proof
        # should have refused this in the first place (cycle 8 ban list).
        raise newException(ValueError,
          "bitwise op on promoted Z3Int — abstraction layer should " &
          "have declined promotion under bit-twiddling")
      else:
        case e.bop
        of bAnd: binBV(l, r, `and`)
        of bOr:  binBV(l, r, `or`)
        of bXor: binBV(l, r, `xor`)
        else: raise newException(ValueError, "unreachable")
    # ---- bit shifts (always BV; cycle 8 ban list applies) ----
    of bShl, bShr:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r = lower(env, e.rhs, some(l))
      doAssert l.kind notin {svInt, svBool},
        "shift on promoted Z3Int — abstraction should have declined"
      case e.bop
      of bShl: binBV(l, r, `shl`)
      of bShr: shrBV(l, r)
      else: raise newException(ValueError, "unreachable")
    # ---- arithmetic — all preserve representation ----
    of bAdd, bSub, bMul, bDiv, bMod:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r = lower(env, e.rhs, pp)
      if l.kind == svInt:
        arithInt(l, r, e.bop)
      elif l.kind in {svFloat32, svFloat64}:
        arithFloat(l, r, e.bop)        # Phase 15 F3
      else:
        case e.bop
        of bAdd: binBV(l, r, `+`)
        of bSub: binBV(l, r, `-`)
        of bMul: binBV(l, r, `*`)
        of bDiv: divBV(l, r)
        of bMod: modBV(l, r)
        else: raise newException(ValueError, "unreachable")

proc lowerBool(env: Env, e: IRExpr): Z3Bool =
  let sv = lower(env, e, some(ofBool(mkBool(true))))
  doAssert sv.kind == svBool, "lowerBool: expected Bool, got " & $sv.kind
  sv.bo

# ---- Path / solve / walk ----------------------------------------------------

proc extractLeaf(m: Z3Model, w: var RawWitness, path: string, sv: SymVal) =
  ## Populate the flat witness tables for a primitive SymVal at the
  ## given path. Tuple/array roots recurse via `extractFromSymVal`.
  case sv.kind
  of svUninterpRef: discard  ## opaque ref — no witness leaf (hint recorded in cluster E)
  of svFloat32, svFloat64: discard  ## Phase 15 F1: real bit-exact float extraction lands in F7
  of svBool: w.boolVals[path] = m.evalBool(sv.bo)
  of svBV8:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv8))
    else:         w.uintVals[path] = m.evalUint(sv.bv8)
  of svBV16:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv16))
    else:         w.uintVals[path] = m.evalUint(sv.bv16)
  of svBV32:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv32))
    else:         w.uintVals[path] = m.evalUint(sv.bv32)
  of svBV64:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv64))
    else:         w.uintVals[path] = m.evalUint(sv.bv64)
  of svInt:
    let v = int64(m.evalInt(sv.zi))
    w.intVals[path] = v
    # Phase 14 A6: a promoted variant discriminator lands in svInt
    # but the witness reader for its underlying `itInt(unsigned)`
    # disc type reads from `uintVals`. Mirror into both maps so
    # whichever reader path the emitter picks finds the value.
    if v >= 0: w.uintVals[path] = uint64(v)
  of svString:
    w.strVals[path] = m.evalStr(sv.str)
  of svTuple, svArray, svSeq, svTable, svSet, svVariant, svMultiVariant:
    raise newException(ValueError,
      "extractLeaf called on non-primitive kind=" & $sv.kind)

proc collectSetLitMembers(s: IRStmt, paramName: string,
                          members: var HashSet[int64])
proc collectSetLitMembersExpr(e: IRExpr, paramName: string,
                              members: var HashSet[int64]) =
  if e == nil: return
  case e.kind
  of iekBinop:
    collectSetLitMembersExpr(e.lhs, paramName, members)
    collectSetLitMembersExpr(e.rhs, paramName, members)
  of iekUnop:
    collectSetLitMembersExpr(e.operand, paramName, members)
  of iekField:
    collectSetLitMembersExpr(e.obj, paramName, members)
  of iekIndex:
    collectSetLitMembersExpr(e.arr, paramName, members)
    collectSetLitMembersExpr(e.idx, paramName, members)
  of iekContains:
    if e.container != nil and e.container.kind == iekVar and
       e.container.vname == paramName and
       e.key != nil and e.key.kind == iekIntLit:
      members.incl e.key.ival
    collectSetLitMembersExpr(e.container, paramName, members)
    collectSetLitMembersExpr(e.key, paramName, members)
  of iekArrayLit:
    for c in e.lelems: collectSetLitMembersExpr(c, paramName, members)
  of iekSeqLen:
    collectSetLitMembersExpr(e.lenObj, paramName, members)
  else: discard

proc collectSetLitMembers(s: IRStmt, paramName: string,
                          members: var HashSet[int64]) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: collectSetLitMembers(c, paramName, members)
  of isIf:
    for br in s.branches:
      collectSetLitMembersExpr(br.cond, paramName, members)
      collectSetLitMembers(br.body, paramName, members)
    if s.elseBody != nil: collectSetLitMembers(s.elseBody, paramName, members)
  of isLet:
    collectSetLitMembersExpr(s.lvalue, paramName, members)
  of isAssign:
    collectSetLitMembersExpr(s.avalue, paramName, members)
  of isWhile:
    collectSetLitMembersExpr(s.wcond, paramName, members)
    collectSetLitMembers(s.wbody, paramName, members)
  of isBreak, isContinue:
    discard
  of isAssert:
    collectSetLitMembersExpr(s.acond, paramName, members)
  of isCall:
    for a in s.cargs: collectSetLitMembersExpr(a, paramName, members)
  of isIndex:
    collectSetLitMembersExpr(s.ixArr, paramName, members)
    collectSetLitMembersExpr(s.ixIdx, paramName, members)
  of isVariantField:
    collectSetLitMembersExpr(s.vfRecv, paramName, members)
  of isVariantReassign:
    discard
  of isVariantReassignSymbolic:
    if s.vrsRhs != nil:
      collectSetLitMembersExpr(s.vrsRhs, paramName, members)
  of isReturn:
    if s.retExpr != nil: collectSetLitMembersExpr(s.retExpr, paramName, members)
  of isTargetLabel, isUnsupported: discard

proc collectTableLitKeys(s: IRStmt, paramName: string,
                         keys: var HashSet[string])
proc collectTableLitKeysExpr(e: IRExpr, paramName: string,
                             keys: var HashSet[string]) =
  if e == nil: return
  case e.kind
  of iekBinop:
    collectTableLitKeysExpr(e.lhs, paramName, keys)
    collectTableLitKeysExpr(e.rhs, paramName, keys)
  of iekUnop:
    collectTableLitKeysExpr(e.operand, paramName, keys)
  of iekField:
    collectTableLitKeysExpr(e.obj, paramName, keys)
  of iekIndex:
    collectTableLitKeysExpr(e.arr, paramName, keys)
    collectTableLitKeysExpr(e.idx, paramName, keys)
  of iekArrayLit:
    for c in e.lelems: collectTableLitKeysExpr(c, paramName, keys)
  of iekSeqLen:
    collectTableLitKeysExpr(e.lenObj, paramName, keys)
  of iekContains:
    collectTableLitKeysExpr(e.container, paramName, keys)
    collectTableLitKeysExpr(e.key, paramName, keys)
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    collectTableLitKeysExpr(e.mutRecv, paramName, keys)
    collectTableLitKeysExpr(e.mutArg, paramName, keys)
  of iekTableSet:
    if e.tabRecv != nil and e.tabRecv.kind == iekVar and
       e.tabRecv.vname == paramName and
       e.tabKey != nil and e.tabKey.kind == iekStrLit:
      keys.incl e.tabKey.sval
    collectTableLitKeysExpr(e.tabRecv, paramName, keys)
    collectTableLitKeysExpr(e.tabKey, paramName, keys)
    collectTableLitKeysExpr(e.tabVal, paramName, keys)
  of iekSeqDel:
    collectTableLitKeysExpr(e.delSeq, paramName, keys)
    collectTableLitKeysExpr(e.delIdx, paramName, keys)
  of iekSeqInsert:
    collectTableLitKeysExpr(e.insSeq, paramName, keys)
    collectTableLitKeysExpr(e.insVal, paramName, keys)
    collectTableLitKeysExpr(e.insIdx, paramName, keys)
  of iekSeqPop:
    collectTableLitKeysExpr(e.popSeq, paramName, keys)
  else: discard

proc collectTableLitKeys(s: IRStmt, paramName: string,
                         keys: var HashSet[string]) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: collectTableLitKeys(c, paramName, keys)
  of isIf:
    for br in s.branches:
      collectTableLitKeysExpr(br.cond, paramName, keys)
      collectTableLitKeys(br.body, paramName, keys)
    if s.elseBody != nil: collectTableLitKeys(s.elseBody, paramName, keys)
  of isLet:
    collectTableLitKeysExpr(s.lvalue, paramName, keys)
  of isAssign:
    collectTableLitKeysExpr(s.avalue, paramName, keys)
  of isWhile:
    collectTableLitKeysExpr(s.wcond, paramName, keys)
    collectTableLitKeys(s.wbody, paramName, keys)
  of isBreak, isContinue:
    discard
  of isAssert:
    collectTableLitKeysExpr(s.acond, paramName, keys)
  of isCall:
    for a in s.cargs: collectTableLitKeysExpr(a, paramName, keys)
  of isIndex:
    if s.ixArr != nil and s.ixArr.kind == iekVar and
       s.ixArr.vname == paramName and
       s.ixIdx != nil and s.ixIdx.kind == iekStrLit:
      keys.incl s.ixIdx.sval
    collectTableLitKeysExpr(s.ixArr, paramName, keys)
    collectTableLitKeysExpr(s.ixIdx, paramName, keys)
  of isVariantField:
    collectTableLitKeysExpr(s.vfRecv, paramName, keys)
  of isVariantReassign:
    discard
  of isVariantReassignSymbolic:
    if s.vrsRhs != nil:
      collectTableLitKeysExpr(s.vrsRhs, paramName, keys)
  of isReturn:
    if s.retExpr != nil: collectTableLitKeysExpr(s.retExpr, paramName, keys)
  of isTargetLabel, isUnsupported: discard

proc extractTableEntries(m: Z3Model, w: var RawWitness, path: string,
                         sv: SymVal, keys: HashSet[string]) =
  case sv.tabValTy.kind
  of itInt:
    let typedData = wrap[Z3Array[Z3String, Z3BitVec[64]]](
      sv.tabDataRaw.ctx, sv.tabDataRaw.raw)
    let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
      sv.tabPresentRaw.ctx, sv.tabPresentRaw.raw)
    var keyList: seq[string]
    for k in keys:
      if m.evalBool(select(typedPresent, mkString(k))):
        keyList.add k
        let v = m.evalInt(select(typedData, mkString(k)))
        w.intVals[path & "." & k] = int64(v)
    w.tabKeys[path] = keyList
  else: discard

proc extractSeqElements(m: Z3Model, w: var RawWitness, path: string,
                        sv: SymVal, n: int) =
  ## Read elements 0..<n from the seq's Z3Array, dispatching on the
  ## element type to wrap/select with the right typed handle.
  case sv.seqElemTy.kind
  of itInt:
    case sv.seqElemTy.width
    of 8:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[8]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 16:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[16]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 32:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[32]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 64:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    else:
      raise newException(ValueError,
        "extractSeqElements: unsupported int width " & $sv.seqElemTy.width)
  of itBool:
    let typed = wrap[Z3Array[Z3Int, Z3Bool]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
    for i in 0 ..< n:
      w.boolVals[path & "." & $i] = m.evalBool(select(typed, mkInt(i)))
  else:
    raise newException(ValueError,
      "extractSeqElements: unsupported element kind " & $sv.seqElemTy.kind)

proc extractSetMembers(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal, candidates: HashSet[int64]) =
  doAssert sv.setElemTy.kind == itInt and sv.setElemTy.width == 64
  let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
    sv.setMembersRaw.ctx, sv.setMembersRaw.raw)
  var present: seq[int64]
  for v in candidates:
    if m.evalBool(select(typed, mkBitVec[64](v))):
      present.add v
  w.setMembers[path] = present

proc extractFromSymVal(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal,
                       tabKeys: Table[string, HashSet[string]],
                       setMembers: Table[string, HashSet[int64]]) =
  case sv.kind
  of svTuple:
    for i, f in sv.fields:
      let suffix = if sv.fieldNames[i].len > 0: "." & sv.fieldNames[i]
                   else: "." & $i
      extractFromSymVal(m, w, path & suffix, f, tabKeys, setMembers)
  of svArray:
    for i, e in sv.arrElems:
      extractFromSymVal(m, w, path & "." & $i, e, tabKeys, setMembers)
  of svSeq:
    let lenVal = int(m.evalInt(sv.seqLen))
    let n = max(0, min(lenVal, 64))
    w.seqLens[path] = n
    extractSeqElements(m, w, path, sv, n)
  of svTable:
    let keys = if tabKeys.hasKey(path): tabKeys[path] else: initHashSet[string]()
    extractTableEntries(m, w, path, sv, keys)
  of svSet:
    let cands = if setMembers.hasKey(path): setMembers[path]
                else: initHashSet[int64]()
    extractSetMembers(m, w, path, sv, cands)
  of svVariant:
    # Discriminator goes under the standard `.kind` path; arm
    # fields land under `.@<armTag>.<fieldName>`. Cycle 7's
    # witness emitter consumes them via a case dispatch on the
    # discriminator value.
    extractFromSymVal(m, w, path & "." & sv.vDiscName, sv.vDisc[],
                      tabKeys, setMembers)
    # Plain fields under direct sub-paths (no @tag prefix).
    for i, f in sv.vPlainFields:
      let sub = path & "." & sv.vPlainFieldNames[i]
      extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
    for tagOrdinal, fields in sv.vArmFields.pairs:
      let armNames = sv.vArmFieldNames[tagOrdinal]
      for j, f in fields:
        # Use a tag-ordinal-keyed subpath so cycle 7 can resolve
        # by discriminator value rather than by tag name.
        let sub = path & ".@" & $tagOrdinal & "." & armNames[j]
        extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
  of svMultiVariant:
    # Phase 14 cycle A1c. Same shape as svVariant extraction but
    # iterates each axis: extract per-axis disc + arm fields. Plain
    # fields are emitted once (shared across all axes).
    for i, f in sv.mvPlainFields:
      let sub = path & "." & sv.mvPlainFieldNames[i]
      extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
    for ax in sv.mvAxes:
      extractFromSymVal(m, w, path & "." & ax.discName, ax.disc[],
                        tabKeys, setMembers)
      for tagOrdinal, fields in ax.armFields.pairs:
        let armNames = ax.armFieldNames[tagOrdinal]
        for j, f in fields:
          let sub = path & "." & ax.discName &
                    ".@" & $tagOrdinal & "." & armNames[j]
          extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
  else:
    extractLeaf(m, w, path, sv)

proc extractWitness(m: Z3Model, env: Env, params: seq[IRParam],
                    tabKeys: Table[string, HashSet[string]],
                    setMembers: Table[string, HashSet[int64]]
                    ): RawWitness =
  result.paramOrder = newSeq[string](params.len)
  for i, p in params:
    result.paramOrder[i] = p.name
    extractFromSymVal(m, result, p.name, env[p.name], tabKeys, setMembers)

var symexZ3CallCount* {.threadvar.}: int
  ## Phase 13 cycle 1. Increments on every Z3 `s.check()` invocation
  ## inside symex. Always-on (no compile-time gate) — the increment
  ## cost is negligible against a Z3 query and tests observe it to
  ## assert "cache hit, Z3 not called" contracts. Re-exported by
  ## `proptest/symex` so consumers can `import proptest/symex` and
  ## reach it directly.

proc trySolve(ctx: Z3Context,
              path: Path,
              params: seq[IRParam],
              settings: SymexSettings = defaultSymexSettings(),
              tabKeys: Table[string, HashSet[string]] = initTable[string, HashSet[string]](),
              setMembers: Table[string, HashSet[int64]] = initTable[string, HashSet[int64]](),
              initialEnv: Env = initOrderedTable[string, SymVal]()
              ): tuple[status: SymexStatusKind, witness: RawWitness] =
  let s = newSolver(ctx)
  # Z3 bound: deterministic logical-step count (NOT wall-clock) so
  # the same SUT + Z3 build produces identical outcomes across
  # machines. `rlimit = 0` is Z3's documented "unbounded"; non-zero
  # truncates to `Z3_L_UNDEF` (sxUnknown). `random_seed = 0'u`
  # overrides any caller's `setGlobalParam` so the verdict cache's
  # determinism guarantee doesn't depend on undocumented Z3 defaults.
  let solverParams = newParams(ctx)
  solverParams.set("rlimit", settings.queryRLimit)
  solverParams.set("random_seed", 0'u)
  s.setParams(solverParams)
  for c in path.pc:
    s.add(c)
  inc symexZ3CallCount
  let r = s.check()
  case r
  of zsSat:
    let m = s.model()
    # Use initialEnv when provided — mutations may have rebound params
    # to post-store SymVals; the witness wants the pre-call value.
    let envForExtract = if initialEnv.len > 0: initialEnv else: path.env
    (status: sxSat,
     witness: extractWitness(m, envForExtract, params, tabKeys, setMembers))
  of zsUnsat:
    (status: sxUnsat, witness: RawWitness())
  of zsUnknown:
    (status: sxUnknown, witness: RawWitness())

type
  LoopFrame = object
    ## Phase 6: walker-level loop frame. `break`/`continue` consult
    ## the top entry to dispatch correctly.
    breakPaths*:    seq[Path]
    continuePaths*: seq[Path]

  CallFrame = object
    ## A walker-level call frame. The runtime pushes one of these per
    ## active inline-call expansion; isReturn consults the top entry
    ## to wire the returned value into the caller's `retSym`.
    callee:        string
    retSym:        SymVal           ## the fresh symbol returned values bind to
    retName:       string           ## "" for void
    returnedPaths: seq[Path]        ## paths that hit `return` inside this call

  WalkerStatics = object ## Phase 15 Z4: per-walker state, immutable after parse;
                         ## populated later by E1 (userExnHierarchy, exnTable),
                         ## C2a (closureSyms), R1 (refSorts...). Empty until then.
  CallFrameCtx = object  ## Phase 15 Z4: state pushed/popped per call descent;
                         ## populated later by E1 (handlerStack, inFlightExn),
                         ## C2a (closureInlineCount). Empty until then.

  WalkCtx = object
    z3:        Z3Context
    target:    SymexTarget
    params:    seq[IRParam]
    found:     seq[RawResult]   ## Phase 15 Z4: was Option[RawResult]. Accumulated
                                ## findings; shouldStop halts on the first sxSat
                                ## (sxRaised added to the stop set in E2a).
    statics:   WalkerStatics    ## Phase 15 Z4 — populated E1/C2a/R1
    frame:     CallFrameCtx     ## Phase 15 Z4 — populated E1/C2a
    sawUnknown: bool
    settings:  SymexSettings
    procs:     Table[string, ProcSig]
    callStack: seq[CallFrame]
    callStats: Table[string, CallStat]
    loopStack: seq[LoopFrame]   ## Phase 6: nested-loop tracking
    callCache: Table[string, CallCacheEntry]
    activeCalls: HashSet[string]
    synthZ3:   int
    tabKeys:   Table[string, HashSet[string]]
    setMembers: Table[string, HashSet[int64]]
    initialEnv: Env   ## snapshot before walking, used so witness
                      ## extraction reads the INITIAL param SymVals
                      ## (not values after `isAssign` mutations).

  CallCacheEntry = object
    ## Function summary: the (callee, argShape) pair maps to the Z3
    ## variable representing the return value plus the constraint
    ## delta added to the returning path. On a cache hit, the entry's
    ## retSym binds to the caller's retName and the pcDelta extends
    ## the current path's pc — no re-walking required.
    retSym:  SymVal
    pcDelta: seq[Z3Bool]

proc shouldStop(w: WalkCtx): bool {.inline.} =
  ## Phase 15 Z4. Halt once a satisfying finding exists. (E2a extends the
  ## stop set to include sxRaised.) An sxUnknown-only `found` does not halt —
  ## a SAT path may still be found on another branch.
  for r in w.found:
    if r.status == sxSat: return true
  false

proc symValHash(sv: SymVal): uint =
  ## Hash of a SymVal's Z3 representation for use as a call-cache key.
  case sv.kind
  of svUninterpRef: astHash(sv.uninterpAst)
  of svFloat32: astHash(sv.fp32)
  of svFloat64: astHash(sv.fp64)
  of svBool: astHash(sv.bo)
  of svInt:  astHash(sv.zi)
  of svString: astHash(sv.str)
  of svSeq:
    astHash(sv.seqLen) xor astHash(sv.seqDataRaw)
  of svTable:
    astHash(sv.tabDataRaw) xor astHash(sv.tabPresentRaw)
  of svSet:
    astHash(sv.setMembersRaw)
  of svTuple:
    var h: uint = 0
    for f in sv.fields:
      h = (h shl 1) xor symValHash(f)
    h
  of svArray:
    var h: uint = 0
    for e in sv.arrElems:
      h = (h shl 1) xor symValHash(e)
    h
  of svBV8:  astHash(sv.bv8)
  of svBV16: astHash(sv.bv16)
  of svBV32: astHash(sv.bv32)
  of svBV64: astHash(sv.bv64)
  of svVariant:
    var h = symValHash(sv.vDisc[])
    for tagOrdinal, fields in sv.vArmFields.pairs:
      h = (h shl 1) xor uint(tagOrdinal)
      for f in fields:
        h = (h shl 1) xor symValHash(f)
    h
  of svMultiVariant:
    var h: uint = 0
    for ax in sv.mvAxes:
      h = (h shl 1) xor symValHash(ax.disc[])
      for tagOrdinal, fields in ax.armFields.pairs:
        h = (h shl 1) xor uint(tagOrdinal)
        for f in fields:
          h = (h shl 1) xor symValHash(f)
    h

proc argShapeKey(callee: string, args: seq[SymVal]): string =
  ## (callee, argShapeHash) → a string key. Hash combination is XOR
  ## with bit rotation — collisions are merely cache misses, never
  ## correctness bugs.
  var h: uint = 0
  for a in args:
    h = (h shl 1) xor symValHash(a)
  callee & "#" & $h

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path]

proc walkBlock(stmts: seq[IRStmt], paths: seq[Path], w: var WalkCtx): seq[Path] =
  result = paths
  for s in stmts:
    if w.shouldStop: return
    result = walk(s, result, w)
    if result.len == 0: return
    # Phase 14 cycle C3 (ADR-0004). Post-step frontier prune. A
    # `maxFrontierSize` of 0 keeps the unbounded baseline; any
    # positive value triggers highest-uncertainty-first eviction:
    # certain paths sort before uncertain (stable within each
    # tier), and the tail is dropped. Pruned paths' contribution
    # is reported as unknown via `w.sawUnknown = true`, which
    # cascades into the final `sxUnknown` verdict cached under
    # `:unk` (NOT `:unsat`).
    if w.settings.maxFrontierSize > 0 and
       result.len > w.settings.maxFrontierSize:
      var certain, uncertain: seq[Path]
      for p in result:
        if p.uncertain: uncertain.add p
        else:           certain.add p
      var kept: seq[Path]
      for p in certain:
        if kept.len >= w.settings.maxFrontierSize: break
        kept.add p
      for p in uncertain:
        if kept.len >= w.settings.maxFrontierSize: break
        kept.add p
      w.sawUnknown = true
      result = kept

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path] =
  if w.shouldStop or stmt == nil or paths.len == 0:
    return paths
  case stmt.kind
  of isBlock:
    walkBlock(stmt.stmts, paths, w)
  of isIf:
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      var accumNegated: seq[Z3Bool]
      for br in stmt.branches:
        let condBool = lowerBool(p.env, br.cond)
        let armPath = Path(pc: p.pc & accumNegated & @[condBool],
                           env: p.env, uncertain: p.uncertain)
        survivors.add walk(br.body, @[armPath], w)
        accumNegated.add(not condBool)
        if w.shouldStop: return
      let elsePath = Path(pc: p.pc & accumNegated,
                          env: p.env, uncertain: p.uncertain)
      if stmt.elseBody != nil:
        survivors.add walk(stmt.elseBody, @[elsePath], w)
      else:
        survivors.add elsePath
    survivors
  of isLet:
    var out2: seq[Path]
    for p in paths:
      var newEnv = p.env
      newEnv[stmt.lname] = lower(p.env, stmt.lvalue)
      out2.add Path(pc: p.pc, env: newEnv, uncertain: p.uncertain)
    out2
  of isAssign:
    var out2: seq[Path]
    for p in paths:
      var newEnv = p.env
      newEnv[stmt.aname] = lower(p.env, stmt.avalue)
      out2.add Path(pc: p.pc, env: newEnv, uncertain: p.uncertain)
    out2
  of isWhile:
    # Phase 6: k-unroll. Each iteration forks on the guard.
    var survivors: seq[Path] = @[]
    var active = paths
    w.loopStack.add LoopFrame(breakPaths: @[], continuePaths: @[])
    let frameIx = w.loopStack.high
    let unwind = w.settings.maxLoopUnwind
    for iter in 0 ..< unwind:
      if w.shouldStop: break
      if active.len == 0: break
      var nextActive: seq[Path]
      for p in active:
        let cond = lowerBool(p.env, stmt.wcond)
        # cond=true: walk body
        let truePath = Path(pc: p.pc & @[cond],
                            env: p.env, uncertain: p.uncertain)
        let afterBody = walk(stmt.wbody, @[truePath], w)
        # Continue-paths from the body merge into next-iter active.
        let cps = w.loopStack[frameIx].continuePaths
        w.loopStack[frameIx].continuePaths = @[]
        for cp in cps: nextActive.add cp
        for ap in afterBody: nextActive.add ap
        # cond=false: exit loop
        survivors.add Path(pc: p.pc & @[not cond],
                           env: p.env, uncertain: p.uncertain)
      active = nextActive
    # Break-paths exit the loop directly (with their accumulated pc/env).
    for bp in w.loopStack[frameIx].breakPaths:
      survivors.add bp
    # Any paths still active after maxLoopUnwind iterations are
    # exhausted: cond=true was still SAT-able. Mark uncertain.
    if active.len > 0:
      w.sawUnknown = true
      for p in active:
        survivors.add Path(pc: p.pc, env: p.env, uncertain: true)
    discard w.loopStack.pop()
    survivors
  of isBreak:
    if w.loopStack.len == 0:
      w.sawUnknown = true   # break outside any loop — degenerate
      return @[]
    for p in paths:
      w.loopStack[w.loopStack.high].breakPaths.add p
    @[]
  of isContinue:
    if w.loopStack.len == 0:
      w.sawUnknown = true
      return @[]
    for p in paths:
      w.loopStack[w.loopStack.high].continuePaths.add p
    @[]
  of isIndex:
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      let arrSV = lower(p.env, stmt.ixArr)
      # ---- Phase 5: Table[K, V] indexing ----
      if arrSV.kind == svTable:
        let keyProto = SymVal(kind: svString, str: mkString(""))
        let keySV = lower(p.env, stmt.ixIdx, some(keyProto))
        doAssert keySV.kind == svString
        # Nim's `Table[K, V].[]` raises `KeyError` when the key is
        # absent. To preserve that semantics in symex we add a
        # presence constraint to the surviving path.
        let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
          arrSV.tabPresentRaw.ctx, arrSV.tabPresentRaw.raw)
        let presentCond = select(typedPresent, keySV.str)
        case arrSV.tabValTy.kind
        of itInt:
          doAssert arrSV.tabValTy.width == 64
          let typedData = wrap[Z3Array[Z3String, Z3BitVec[64]]](
            arrSV.tabDataRaw.ctx, arrSV.tabDataRaw.raw)
          let v = select(typedData, keySV.str)
          var newEnv = p.env
          newEnv[stmt.ixRetName] = liftBV(v, arrSV.tabValTy.signed)
          survivors.add Path(pc: p.pc & @[presentCond],
                             env: newEnv, uncertain: p.uncertain)
        else:
          raise newException(ValueError,
            "Phase 5: Table value " & $arrSV.tabValTy & " not implemented")
        continue
      # ---- Phase 5: dynamic seq[T] indexing ----
      if arrSV.kind == svSeq:
        # Seq index is Z3Int. Lower with an svInt proto for literals;
        # for env-resident BV-typed Nim ints we coerce via bv2int.
        let intProto = SymVal(kind: svInt, zi: mkInt(0))
        let idxSV = lower(p.env, stmt.ixIdx, some(intProto))
        let lenZi = arrSV.seqLen
        let idxZi = toZ3Int(idxSV)
        let inLoCond = idxZi >= mkInt(0)
        let inHiCond = idxZi <  lenZi
        if w.target.kind == stkIndexError:
          let oobPath = Path(pc: p.pc & @[not (inLoCond and inHiCond)],
                             env: p.env, uncertain: p.uncertain)
          if oobPath.uncertain:
            w.sawUnknown = true
          else:
            let (st, wit) = trySolve(w.z3, oobPath, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
            case st
            of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
            of sxUnknown: w.sawUnknown = true
            of sxUnsat:  discard
        # Bind retName = select(seqData, idx) at element type
        var indexed: SymVal
        case arrSV.seqElemTy.kind
        of itInt:
          case arrSV.seqElemTy.width
          of 8:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[8]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          of 16:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[16]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          of 32:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[32]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          of 64:
            let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
          else:
            raise newException(ValueError,
              "isIndex/seq: unsupported elem width " & $arrSV.seqElemTy.width)
        of itBool:
          let typed = wrap[Z3Array[Z3Int, Z3Bool]](
            arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
          indexed = ofBool(select(typed, idxZi))
        else:
          raise newException(ValueError,
            "isIndex/seq: unsupported elem kind " & $arrSV.seqElemTy.kind)
        var newEnv = p.env
        newEnv[stmt.ixRetName] = indexed
        survivors.add Path(pc: p.pc & @[inLoCond, inHiCond],
                           env: newEnv, uncertain: p.uncertain)
        continue
      # ---- Phase 4: static array (the existing path) ----
      doAssert arrSV.kind == svArray,
        "isIndex on non-array kind=" & $arrSV.kind
      let n = arrSV.arrElems.len
      let idxSV = lower(p.env, stmt.ixIdx)
      # Build the in-bounds & OOB Z3 conditions.
      let loSV  = coerceIntLit(idxSV, 0)
      let hiSV  = coerceIntLit(idxSV, int64(n))
      let inLoCond = case idxSV.kind
        of svBV8:  bvsle(loSV.bv8,  idxSV.bv8)
        of svBV16: bvsle(loSV.bv16, idxSV.bv16)
        of svBV32: bvsle(loSV.bv32, idxSV.bv32)
        of svBV64: bvsle(loSV.bv64, idxSV.bv64)
        of svInt:  loSV.zi <= idxSV.zi
        else: raise newException(ValueError, "isIndex: non-int index kind")
      let inHiCond = case idxSV.kind
        of svBV8:  bvslt(idxSV.bv8,  hiSV.bv8)
        of svBV16: bvslt(idxSV.bv16, hiSV.bv16)
        of svBV32: bvslt(idxSV.bv32, hiSV.bv32)
        of svBV64: bvslt(idxSV.bv64, hiSV.bv64)
        of svInt:  idxSV.zi < hiSV.zi
        else: raise newException(ValueError, "isIndex: non-int index kind")
      # OOB target check.
      if w.target.kind == stkIndexError:
        let oobPath = Path(pc: p.pc & @[not (inLoCond and inHiCond)],
                           env: p.env, uncertain: p.uncertain)
        if oobPath.uncertain:
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, oobPath, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
      # In-bounds path continues with binding; build the value via ite.
      var indexed = arrSV.arrElems[0]
      for k in 1 ..< n:
        let kSV = coerceIntLit(idxSV, int64(k))
        indexed = iteSV(symEq(idxSV, kSV), arrSV.arrElems[k], indexed)
      var newEnv = p.env
      newEnv[stmt.ixRetName] = indexed
      survivors.add Path(pc: p.pc & @[inLoCond, inHiCond],
                         env: newEnv, uncertain: p.uncertain)
    survivors
  of isVariantReassign:
    # Phase 11 cycle 6 — `obj.kind = tagLiteral`. Build a new
    # svVariant whose discriminator IS the literal tag (constant
    # BV) and whose new arm's primitive fields are zero-init'd
    # (Nim runtime semantics on discriminator reassignment).
    proc defaultZero(t: IRType, baseName: string): SymVal =
      ## Phase 14 cycle A5 (ADR-0003 D5). Recursive type-driven
      ## zero-init for arm fields under static-tag disc reassign.
      ## Replaces Phase 11's "primitives only" guard with a full
      ## walk over the IR type tree. Inherits `allocateSym`'s scope
      ## for containers — Table with non-string keys and HashSet
      ## with non-int64 elements still raise (RFC §A5 sub-deferral).
      case t.kind
      of itUninterp:
        raise newException(ValueError, "defaultZero(itUninterp): lands with cluster E")
      of itFloat32, itFloat64:
        raise newException(ValueError, "defaultZero(float): lands with F7")
      of itBool: SymVal(kind: svBool, bo: mkBool(false))
      of itInt:
        case t.width
        of 8:  liftBV(mkBitVec[8](0),  t.signed)
        of 16: liftBV(mkBitVec[16](0), t.signed)
        of 32: liftBV(mkBitVec[32](0), t.signed)
        of 64: liftBV(mkBitVec[64](0), t.signed)
        else:
          raise newException(ValueError,
            "A5 zero-init: int width " & $t.width & " not supported")
      of itString:
        SymVal(kind: svString, str: mkString(""))
      of itTuple:
        var fields: seq[SymVal]
        for i, ft in t.fields:
          let suffix = if t.fieldNames[i].len > 0: "." & t.fieldNames[i]
                       else: "." & $i
          fields.add defaultZero(ft, baseName & suffix)
        SymVal(kind: svTuple, fields: fields, fieldNames: t.fieldNames)
      of itArray:
        var elems: seq[SymVal]
        for i in 0 ..< t.size:
          elems.add defaultZero(t.elemTy, baseName & "." & $i)
        SymVal(kind: svArray, arrElems: elems, arrElemTy: t.elemTy)
      of itSeq:
        # Empty seq: len pinned to 0; the data array is allocated
        # so the SymVal shape is well-formed, but never read past
        # len. Mirrors Nim's `default(seq[T]) == @[]`.
        let dataRaw = allocateSeqDataRaw(t.seqElemTy, baseName & ".data")
        SymVal(kind: svSeq, seqLen: mkInt(0),
               seqDataRaw: dataRaw, seqElemTy: t.seqElemTy)
      of itSet, itTable:
        # RFC §A5 sub-deferral: container fields in reassigned arms
        # inherit `allocateSym`'s scope guard. Empty-container
        # construction requires a fresh Z3Array allocation which
        # the current SymVal shape doesn't expose a constructor
        # for outside `allocateSym`; defer until a concrete
        # consumer demands it.
        raise newException(ValueError,
          "A5 zero-init: container arm field " & $t &
          " in reassigned arm not yet supported " &
          "(RFC §A5 sub-deferral)")
      of itVariant, itMultiVariant:
        # Nested variant in an arm field: zero-initing it requires
        # picking a default disc + recursing. The walker doesn't
        # have access to the constructor here; this remains
        # unsupported until a concrete demand surfaces.
        raise newException(ValueError,
          "A5 zero-init: nested variant " & $t &
          " in reassigned arm not supported")
    var out2: seq[Path]
    for p in paths:
      if not p.env.hasKey(stmt.vrObjName):
        out2.add p
        continue
      let oldSV = p.env[stmt.vrObjName]
      doAssert oldSV.kind == svVariant,
        "isVariantReassign on non-variant kind=" & $oldSV.kind
      let oldDisc = oldSV.vDisc[]
      let tagOrd = int64(stmt.vrNewTag)
      let newDiscInner: SymVal =
        case oldDisc.kind
        of svBV8:  liftBV(mkBitVec[8](tagOrd),  oldDisc.signed)
        of svBV16: liftBV(mkBitVec[16](tagOrd), oldDisc.signed)
        of svBV32: liftBV(mkBitVec[32](tagOrd), oldDisc.signed)
        of svBV64: liftBV(mkBitVec[64](tagOrd), oldDisc.signed)
        of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(tagOrd))  # A6
        else:
          raise newException(ValueError,
            "isVariantReassign: disc must be BV or Z3Int kind")
      let newDiscBoxed = new(SymVal)
      newDiscBoxed[] = newDiscInner
      var newArmFields = oldSV.vArmFields
      let priorFields = oldSV.vArmFields.getOrDefault(stmt.vrNewTag)
      var newFields: seq[SymVal]
      let armNames = oldSV.vArmFieldNames.getOrDefault(stmt.vrNewTag)
      for ix, f in priorFields:
        let fname = if ix < armNames.len: armNames[ix] else: $ix
        let basePath = stmt.vrObjName & ".@" &
                       $stmt.vrNewTag & "." & fname & ".reass"
        newFields.add defaultZero(tyOf(f), basePath)
      newArmFields[stmt.vrNewTag] = newFields
      let newSV = SymVal(kind: svVariant,
                         vDisc: newDiscBoxed,
                         vDiscName: oldSV.vDiscName,
                         vObjectName: oldSV.vObjectName,
                         vArmFields: newArmFields,
                         vArmFieldNames: oldSV.vArmFieldNames,
                         vPlainFields: oldSV.vPlainFields,       # shared:
                         vPlainFieldNames: oldSV.vPlainFieldNames) # preserved.
      var newEnv = p.env
      newEnv[stmt.vrObjName] = newSV
      out2.add Path(pc: p.pc, env: newEnv, uncertain: p.uncertain)
    return out2
  of isVariantReassignSymbolic:
    # Phase 14 cycle A4b (ADR-0003 D4). Symbolic-RHS disc reassign:
    # fork one path per arm-ordinal in the disc's domain. Each path
    # is constrained `rhsSV == k_ord` AND the variant SymVal in env
    # is rebuilt with the new disc SET TO THAT TAG'S CONSTANT.
    # Arm-field SymVals are PRESERVED — no zero-init (that's the
    # static-tag path's job per D4). For itMultiVariant: only the
    # named axis's disc is updated; other axes are preserved as-is.
    var out2: seq[Path]
    for p in paths:
      if not p.env.hasKey(stmt.vrsObjName):
        out2.add p
        continue
      let oldSV = p.env[stmt.vrsObjName]
      let rhsSV = lower(p.env, stmt.vrsRhs)
      proc rhsEq(tagOrd: int64): Z3Bool =
        case rhsSV.kind
        of svBV8:  rhsSV.bv8  == mkBitVec[8](tagOrd)
        of svBV16: rhsSV.bv16 == mkBitVec[16](tagOrd)
        of svBV32: rhsSV.bv32 == mkBitVec[32](tagOrd)
        of svBV64: rhsSV.bv64 == mkBitVec[64](tagOrd)
        of svInt:  rhsSV.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
        else:
          raise newException(ValueError,
            "isVariantReassignSymbolic: RHS must lower to a BV or " &
            "Z3Int kind (got " & $rhsSV.kind & ")")
      case oldSV.kind
      of svVariant:
        for tag in oldSV.vArmFields.keys:
          if tag < 0: continue  # else arm — covered by D4 future work
          let newDiscInner: SymVal =
            case oldSV.vDisc[].kind
            of svBV8:  liftBV(mkBitVec[8](int64(tag)),  oldSV.vDisc[].signed)
            of svBV16: liftBV(mkBitVec[16](int64(tag)), oldSV.vDisc[].signed)
            of svBV32: liftBV(mkBitVec[32](int64(tag)), oldSV.vDisc[].signed)
            of svBV64: liftBV(mkBitVec[64](int64(tag)), oldSV.vDisc[].signed)
            of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(int64(tag)))  # A6
            else:
              raise newException(ValueError,
                "isVariantReassignSymbolic: old disc must be BV or Z3Int")
          let newDiscBoxed = new(SymVal)
          newDiscBoxed[] = newDiscInner
          let newSV = SymVal(kind: svVariant,
                             vDisc: newDiscBoxed,
                             vDiscName: oldSV.vDiscName,
                             vObjectName: oldSV.vObjectName,
                             vArmFields: oldSV.vArmFields,       # PRESERVED
                             vArmFieldNames: oldSV.vArmFieldNames,
                             vPlainFields: oldSV.vPlainFields,
                             vPlainFieldNames: oldSV.vPlainFieldNames)
          var newEnv = p.env
          newEnv[stmt.vrsObjName] = newSV
          out2.add Path(pc: p.pc & @[rhsEq(int64(tag))],
                        env: newEnv, uncertain: p.uncertain)
      of svMultiVariant:
        # Locate the named axis (vrsDiscName); other axes preserve
        # their disc + arm state.
        var axisIx = -1
        for i, ax in oldSV.mvAxes:
          if ax.discName == stmt.vrsDiscName:
            axisIx = i; break
        doAssert axisIx >= 0,
          "isVariantReassignSymbolic on svMultiVariant: no axis named " &
          stmt.vrsDiscName
        let oldAxis = oldSV.mvAxes[axisIx]
        for tag in oldAxis.armFields.keys:
          if tag < 0: continue
          let newDiscInner: SymVal =
            case oldAxis.disc[].kind
            of svBV8:  liftBV(mkBitVec[8](int64(tag)),  oldAxis.disc[].signed)
            of svBV16: liftBV(mkBitVec[16](int64(tag)), oldAxis.disc[].signed)
            of svBV32: liftBV(mkBitVec[32](int64(tag)), oldAxis.disc[].signed)
            of svBV64: liftBV(mkBitVec[64](int64(tag)), oldAxis.disc[].signed)
            of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(int64(tag)))  # A6
            else:
              raise newException(ValueError,
                "isVariantReassignSymbolic: axis disc must be a BV kind")
          let newDiscBoxed = new(SymVal)
          newDiscBoxed[] = newDiscInner
          var newAxes = oldSV.mvAxes
          newAxes[axisIx] = VariantAxisSym(
            discName: oldAxis.discName, disc: newDiscBoxed,
            armFields: oldAxis.armFields,       # PRESERVED
            armFieldNames: oldAxis.armFieldNames)
          let newSV = SymVal(kind: svMultiVariant,
                             mvObjectName: oldSV.mvObjectName,
                             mvAxes: newAxes,
                             mvPlainFields: oldSV.mvPlainFields,
                             mvPlainFieldNames: oldSV.mvPlainFieldNames)
          var newEnv = p.env
          newEnv[stmt.vrsObjName] = newSV
          out2.add Path(pc: p.pc & @[rhsEq(int64(tag))],
                        env: newEnv, uncertain: p.uncertain)
      else:
        doAssert false,
          "isVariantReassignSymbolic on non-variant kind=" & $oldSV.kind
    return out2
  of isVariantField:
    # Phase 11 cycle 5 — A-normalised arm-field access. Forks: the
    # in-arm path adds `disc IN matchingTags` to pc and binds
    # `retName` to an ite-chain over the matching arms' field
    # SymVals; the out-of-arm path adds `disc NOT IN matchingTags`
    # and (under `tFieldDefect`) is solved for a witness.
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      let recv = lower(p.env, stmt.vfRecv)
      # Phase 14 cycle A1c: select the axis-local disc + arm tables
      # by SymVal kind. For svMultiVariant, locate the axis whose
      # arm field-name lists include vfFieldName — the parser
      # selected the same axis via the same membership test.
      var disc: SymVal
      var armFieldsTbl: OrderedTable[int, seq[SymVal]]
      var armFieldNamesTbl: OrderedTable[int, seq[string]]
      case recv.kind
      of svVariant:
        disc            = recv.vDisc[]
        armFieldsTbl    = recv.vArmFields
        armFieldNamesTbl = recv.vArmFieldNames
      of svMultiVariant:
        var found = false
        for ax in recv.mvAxes:
          for _, names in ax.armFieldNames.pairs:
            if stmt.vfFieldName in names:
              disc             = ax.disc[]
              armFieldsTbl     = ax.armFields
              armFieldNamesTbl = ax.armFieldNames
              found = true
              break
          if found: break
        doAssert found,
          "isVariantField on svMultiVariant: no axis owns field " &
          stmt.vfFieldName
      else:
        doAssert false,
          "isVariantField on non-variant SymVal kind=" & $recv.kind
      proc discEq(tagOrd: int64): Z3Bool =
        case disc.kind
        of svBV8:  disc.bv8  == mkBitVec[8](tagOrd)
        of svBV16: disc.bv16 == mkBitVec[16](tagOrd)
        of svBV32: disc.bv32 == mkBitVec[32](tagOrd)
        of svBV64: disc.bv64 == mkBitVec[64](tagOrd)
        of svInt:  disc.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
        else:
          raise newException(ValueError,
            "isVariantField: discriminator must be a BV or Z3Int kind")
      # Build the matching-arm equalities + collect each arm's SymVal
      # for the requested field.
      var armEqs: seq[Z3Bool]
      var armBindings: seq[(int, SymVal)]
      for tag in stmt.vfMatchingTags:
        let armNames  = armFieldNamesTbl[tag]
        let fieldIx   = armNames.find(stmt.vfFieldName)
        if fieldIx < 0: continue
        let armEq =
          if tag == -1:
            # Phase 14 cycle A2: else-arm membership is the
            # conjunction of negations against all non-else arms on
            # the same axis (ADR-0003 D2).
            var conj: Z3Bool
            var seeded = false
            for otherTag in armFieldsTbl.keys:
              if otherTag == -1: continue
              let neg = not discEq(int64(otherTag))
              if not seeded: conj = neg; seeded = true
              else:          conj = conj and neg
            if not seeded:
              raise newException(ValueError,
                "isVariantField: else-only variant has no non-else " &
                "arms to negate against (degenerate; the parser " &
                "should not have emitted such an IR)")
            conj
          else:
            discEq(int64(tag))
        armEqs.add armEq
        armBindings.add (tag, armFieldsTbl[tag][fieldIx])
      doAssert armEqs.len > 0,
        "isVariantField: parser produced an empty matchingTags list"
      var inArmCond = armEqs[0]
      for k in 1 ..< armEqs.len:
        inArmCond = inArmCond or armEqs[k]
      let outOfArmCond = not inArmCond
      # tFieldDefect — solve the out-of-arm branch.
      if w.target.kind == stkFieldDefect:
        let fdPath = Path(pc: p.pc & @[outOfArmCond],
                          env: p.env, uncertain: p.uncertain)
        if fdPath.uncertain:
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, fdPath, w.params, w.settings,
                                   w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
          if w.shouldStop: return
      # In-arm path — bind retName to the ite-chain over arms.
      var bound = armBindings[armBindings.len - 1][1]
      for k in countdown(armBindings.len - 2, 0):
        let eqB = discEq(int64(armBindings[k][0]))
        bound = iteSV(eqB, armBindings[k][1], bound)
      var newEnv = p.env
      newEnv[stmt.vfRetName] = bound
      survivors.add Path(pc: p.pc & @[inArmCond],
                         env: newEnv, uncertain: p.uncertain)
    survivors
  of isReturn:
    if w.callStack.len == 0:
      @[]
    else:
      # Inside a callee: bind the returned value to the retSym and
      # record the path into the call frame's returnedPaths.
      let frameIx = w.callStack.high
      for p in paths:
        if stmt.retExpr == nil:
          w.callStack[frameIx].returnedPaths.add p
        else:
          let retVal = lower(p.env, stmt.retExpr,
                             some(w.callStack[frameIx].retSym))
          let retSym = w.callStack[frameIx].retSym
          # Reconcile mixed int reps (e.g. callee returns svInt because
          # of #135 range propagation while retSym was allocated svBV*).
          let retConstraint =
            if retSym.kind != retVal.kind and
               retSym.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
               retVal.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
              # Cross-rep linkage (e.g. #135 propagation): bv2int both.
              toZ3Int(retSym) == toZ3Int(retVal)
            else:
              # Same-kind native equality so BV-wrap semantics is
              # preserved (and Z3Int = Z3Int when both are Int).
              case retSym.kind
              of svBool: retSym.bo == retVal.bo
              of svInt:  retSym.zi == retVal.zi
              of svBV8:  retSym.bv8  == retVal.bv8
              of svBV16: retSym.bv16 == retVal.bv16
              of svBV32: retSym.bv32 == retVal.bv32
              of svBV64: retSym.bv64 == retVal.bv64
              of svTuple, svArray, svString, svSeq, svTable, svSet, svVariant, svMultiVariant, svUninterpRef, svFloat32, svFloat64:
                raise newException(ValueError,
                  "composite-typed proc return not yet wired")
          w.callStack[frameIx].returnedPaths.add Path(
            pc: p.pc & @[retConstraint], env: p.env, uncertain: p.uncertain)
      @[]
  of isCall:
    # ---- #137: opaque effectful call ----
    if stmt.opaque:
      # Don't resolve a body; allocate fresh retSym; mark path
      # uncertain so any target reached on this path degrades to
      # sxUnknown rather than emitting an unsound witness.
      w.sawUnknown = true
      var out2: seq[Path]
      for p in paths:
        var newEnv = p.env
        if stmt.retName.len > 0:
          inc w.synthZ3
          let z3Name = stmt.retName & "_op" & $w.synthZ3
          let retSym = if stmt.retTy.kind == itBool:
                         SymVal(kind: svBool, bo: mkBoolVar(z3Name))
                       else:
                         bvVar(stmt.retTy, z3Name)
          newEnv[stmt.retName] = retSym
        out2.add Path(pc: p.pc, env: newEnv, uncertain: true)
      return out2
    if not w.procs.hasKey(stmt.callee):
      # Should not happen — parser should have rejected at compile time.
      w.sawUnknown = true
      return paths
    let sig = w.procs[stmt.callee]
    # Statistics
    if not w.callStats.hasKey(stmt.callee):
      w.callStats[stmt.callee] = CallStat(name: stmt.callee, walked: 0, cacheHits: 0)
    # Depth check
    if w.callStack.len >= w.settings.maxCallDepth:
      # Bail: continue with a fresh unconstrained retSym; flag unknown.
      # The surviving paths are marked uncertain so any target hit on
      # them degrades to sxUnknown (the witness would otherwise be
      # an unsoundly-Z3-defaulted value).
      w.sawUnknown = true
      var out2: seq[Path]
      for p in paths:
        var newEnv = p.env
        if stmt.retName.len > 0:
          inc w.synthZ3
          let z3Name = stmt.retName & "_d" & $w.synthZ3
          let retSym = if stmt.retTy.kind == itBool:
                         SymVal(kind: svBool, bo: mkBoolVar(z3Name))
                       else:
                         bvVar(stmt.retTy, z3Name)
          newEnv[stmt.retName] = retSym
        out2.add Path(pc: p.pc, env: newEnv, uncertain: true)
      out2
    else:
      var survivors: seq[Path]
      for p in paths:
        if w.shouldStop: return
        # Lower actuals in the caller env once; reused for cache key
        # and for callee env construction.
        var argVals: seq[SymVal]
        for i, formal in sig.params:
          argVals.add lower(p.env, stmt.cargs[i])
        # Cache lookup — pure procs with deterministic-arg-shape hits
        # are served without re-walking. The cache entry's `pcDelta`
        # carries the returning-path constraints; we extend the
        # current path with them.
        let key = argShapeKey(stmt.callee, argVals)
        if key in w.activeCalls:
          # Mutual / direct recursion with identical args — the call
          # is already being walked further up the stack. Break the
          # cycle: return a fresh symbolic retval, mark uncertain.
          w.callStats[stmt.callee] = CallStat(
            name: stmt.callee,
            walked: w.callStats[stmt.callee].walked,
            cacheHits: w.callStats[stmt.callee].cacheHits + 1)
          var newEnv = p.env
          if stmt.retName.len > 0:
            inc w.synthZ3
            let z3Name = stmt.retName & "_cyc" & $w.synthZ3
            let cycSym =
              if stmt.retTy.kind == itBool:
                SymVal(kind: svBool, bo: mkBoolVar(z3Name))
              else:
                bvVar(stmt.retTy, z3Name)
            newEnv[stmt.retName] = cycSym
          survivors.add Path(pc: p.pc, env: newEnv, uncertain: true)
          continue
        if w.callCache.hasKey(key):
          let entry = w.callCache[key]
          w.callStats[stmt.callee] = CallStat(
            name: stmt.callee,
            walked: w.callStats[stmt.callee].walked,
            cacheHits: w.callStats[stmt.callee].cacheHits + 1)
          var newEnv = p.env
          if stmt.retName.len > 0:
            newEnv[stmt.retName] = entry.retSym
          survivors.add Path(pc: p.pc & entry.pcDelta,
                             env: newEnv, uncertain: p.uncertain)
          continue
        # Build callee env
        var calleeEnv: Env
        # #140: track var-param formal→actual binding for write-back.
        var varArgs: seq[(string, string)]   # (formalName, callerVarName)
        for i, formal in sig.params:
          calleeEnv[formal.name] = argVals[i]
          if formal.isVar and stmt.cargs[i].kind == iekVar:
            varArgs.add (formal.name, stmt.cargs[i].vname)
        # Allocate retSym with a *runtime-fresh* Z3 name.
        inc w.synthZ3
        let z3Name = stmt.retName & "_c" & $w.synthZ3
        let retSym = if sig.isVoid:
                       SymVal(kind: svBool, bo: mkBool(true))  ## placeholder
                     elif stmt.retTy.kind == itBool:
                       SymVal(kind: svBool, bo: mkBoolVar(z3Name))
                     else:
                       bvVar(stmt.retTy, z3Name)
        w.callStack.add CallFrame(
          callee: stmt.callee, retSym: retSym,
          retName: stmt.retName, returnedPaths: @[])
        w.callStats[stmt.callee] = CallStat(
          name: stmt.callee,
          walked: w.callStats[stmt.callee].walked + 1,
          cacheHits: w.callStats[stmt.callee].cacheHits)
        w.activeCalls.incl key
        let calleePath = Path(pc: p.pc, env: calleeEnv,
                              uncertain: p.uncertain)
        let fallThrough = walk(sig.body, @[calleePath], w)
        let frame = w.callStack[w.callStack.high]
        w.callStack.setLen(w.callStack.high)
        w.activeCalls.excl key
        # Cache: single-return, single-fall-through-free, non-uncertain
        # calls cache for argShape-keyed reuse.
        if frame.returnedPaths.len == 1 and fallThrough.len == 0 and
           not frame.returnedPaths[0].uncertain:
          let cp = frame.returnedPaths[0]
          let prefixLen = p.pc.len
          if cp.pc.len >= prefixLen:
            w.callCache[key] = CallCacheEntry(
              retSym: retSym,
              pcDelta: cp.pc[prefixLen ..< cp.pc.len])
        for cp in frame.returnedPaths & fallThrough:
          var newEnv = p.env
          if stmt.retName.len > 0:
            newEnv[stmt.retName] = retSym
          # #140: propagate var-param mutations back to caller's env.
          for (formalName, callerName) in varArgs:
            if cp.env.hasKey(formalName):
              newEnv[callerName] = cp.env[formalName]
          survivors.add Path(pc: cp.pc, env: newEnv,
                             uncertain: p.uncertain or cp.uncertain)
      survivors
  of isAssert:
    var out2: seq[Path]
    for p in paths:
      if w.shouldStop: return
      let cond = lowerBool(p.env, stmt.acond)
      if w.target.kind == stkAssertionViolation:
        let violPath = Path(pc: p.pc & @[not cond], env: p.env,
                            uncertain: p.uncertain)
        if violPath.uncertain:
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, violPath, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
      out2.add Path(pc: p.pc & @[cond], env: p.env, uncertain: p.uncertain)
    out2
  of isTargetLabel:
    if w.target.kind == stkLabel and w.target.label == stmt.tname:
      for p in paths:
        if w.shouldStop: return
        if p.uncertain:
          # Uncertain path: a SAT witness here would be unsound because
          # bailed-call retSyms are unconstrained at the Z3 level.
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, p, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
    paths
  of isUnsupported:
    w.sawUnknown = true
    paths

# ---- Public driver ----------------------------------------------------------

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings): RawResult

proc runSymex*(prog: SymexProgram,
               target: SymexTarget,
               settings: SymexSettings = defaultSymexSettings()): RawResult =
  ## Phase 14 cycle C4. Wrap the implementation in a `try/except` that
  ## catches `Z3Error` (the abstract base class — all 12 typed
  ## subclasses derive from it). On catch, return `sxUnknown` with
  ## the error structured into `errors`. Walker-level
  ## `ValueError` and `AssertionDefect` are NOT caught — those
  ## are real bugs in the symex layer and must surface.
  try:
    runSymexImpl(prog, target, settings)
  except Z3Error as e:
    # Phase 15 Z3: map the Z3Error subclass name to the closed SymexErrorKind.
    # A caught Z3Error -> sxUnknown, so severity is sevError (invariant 7).
    let ek = case $e.name
             of "Z3MemoryError":   ekZ3MemoryError
             of "Z3InternalError": ekZ3InternalError
             of "Z3SolverError":   ekZ3SolverError
             else:                 ekZ3Error
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: ek, severity: sevError, msg: e.msg)])

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings): RawResult =
  let ctx = newContext()
  setCurrentContext(ctx)
  var env: Env
  var initialPC: seq[Z3Bool]
  var log: AbstractionLog
  # ADR-0001 ban scan: variables whose def-use chain contains a
  # bit-twiddling op can't be soundly promoted to Z3Int.
  var intParamNames: HashSet[string]
  for p in prog.params:
    if p.ty.kind == itInt:
      intParamNames.incl p.name
  let banned = collectBan(prog.body, intParamNames)
  # #134: assertion-derived range refinements. Disabled when the
  # user's target is `tAssertionViolation` — the whole point of that
  # search is to find inputs that violate the assertion, so we
  # mustn't fold the assertion into the initial range constraints.
  var assertRanges: Table[string, Interval]
  if target.kind != stkAssertionViolation:
    collectAssertRanges(prog.body, assertRanges)
  if settings.integerSemantics == isLoose:
    emitIsLooseBanner()
  for p in prog.params:
    case p.ty.kind
    of itTuple, itArray, itString, itSeq, itTable, itSet, itMultiVariant, itUninterp, itFloat32, itFloat64:
      # itMultiVariant included here as Phase 14 cycle A1a stub; the
      # `allocateSym` for itMultiVariant raises a clear ValueError
      # (see runtime.nim allocateSym stub). Falling through to the
      # same call site keeps the dispatch surface uniform.
      env[p.name] = allocateSym(p.ty, p.name, initialPC)
    of itVariant:
      env[p.name] = allocateSym(p.ty, p.name, initialPC)
      # Phase 14 cycle A6 (ADR-0003 D6, mandatory). Under
      # `isOptimised`, promote the variant discriminator to Z3Int
      # so it composes cleanly with other Z3Int-promoted operands
      # (mixed BV/Int comparisons crack the abstraction layer).
      # The BV disc allocated above stays in the Z3 context but
      # becomes unreferenced after the swap; its old disjunction
      # in pcOut is harmless (BV is unused; constraints are
      # tautologies w.r.t. the new svInt disc).
      if settings.integerSemantics == isOptimised:
        var minOrd = high(int)
        var maxOrd = low(int)
        for arm in p.ty.vArms:
          if arm.tagOrdinal < 0: continue  # else sentinel
          if arm.tagOrdinal < minOrd: minOrd = arm.tagOrdinal
          if arm.tagOrdinal > maxOrd: maxOrd = arm.tagOrdinal
        # Phase 14 A6: when an `else:` arm is present, the convex
        # hull must also include the else-covered ordinals from
        # `vDiscTags` (the enum's full domain). Without this, the
        # range bound below excludes legal disc values.
        for dt in p.ty.vDiscTags:
          if dt.ord < minOrd: minOrd = dt.ord
          if dt.ord > maxOrd: maxOrd = dt.ord
        if minOrd == high(int):
          # No non-else arms AND no vDiscTags — degenerate.
          minOrd = 0; maxOrd = 0
        let promotedDisc = SymVal(kind: svInt,
          zi: mkIntVar(p.name & "." & p.ty.vDiscName & ".zi"))
        # Tight bound + per-ordinal disjunction on the Z3Int.
        initialPC.add (promotedDisc.zi >= mkZ3IntLit(int64(minOrd)))
        initialPC.add (promotedDisc.zi <= mkZ3IntLit(int64(maxOrd)))
        # Disjunction over legal ordinals (including else-covered
        # ordinals via vDiscTags when populated).
        var ordSet: seq[int]
        for arm in p.ty.vArms:
          if arm.tagOrdinal >= 0: ordSet.add arm.tagOrdinal
        for dt in p.ty.vDiscTags:
          if dt.ord notin ordSet: ordSet.add dt.ord
        if ordSet.len > 0:
          var clause = promotedDisc.zi == mkZ3IntLit(int64(ordSet[0]))
          for k in 1 ..< ordSet.len:
            clause = clause or
              (promotedDisc.zi == mkZ3IntLit(int64(ordSet[k])))
          initialPC.add clause
        env[p.name].vDisc[] = promotedDisc
        let ivl = interval(int64(minOrd), int64(maxOrd))
        log.add AbstractionEntry(
          name: p.name & "." & p.ty.vDiscName,
          interval: ivl,
          evidence: aeVariantDisc,
          derivation: "variant discriminator promoted to Z3Int " &
                      "over " & $ivl & " (" & $p.ty.vArms.len & " arms)")
    of itInt:
      # Type-derived range takes precedence; otherwise look for
      # assertion-derived ranges (#134).
      var hasRange = p.hasRange
      var rangeLo = p.rangeLo
      var rangeHi = p.rangeHi
      var fromAssert = false
      if not hasRange and assertRanges.hasKey(p.name):
        let ai = assertRanges[p.name]
        if not ai.isEmpty:
          hasRange = true
          rangeLo = ai.lo
          rangeHi = ai.hi
          fromAssert = true
      let ivl = interval(rangeLo, rangeHi)
      let promoteLoose = settings.integerSemantics == isLoose
      let promoteSound = settings.integerSemantics == isOptimised and
                         hasRange and
                         fitsBVWindow(ivl, p.ty) and
                         p.name notin banned
      let promote = promoteLoose or promoteSound
      if promote:
        env[p.name] = SymVal(kind: svInt, zi: mkIntVar(p.name))
        if promoteSound:
          initialPC.add (env[p.name].zi >= mkZ3IntLit(rangeLo))
          initialPC.add (env[p.name].zi <= mkZ3IntLit(rangeHi))
          log.add AbstractionEntry(
            name: p.name,
            interval: ivl,
            evidence: if fromAssert: aeNumericFold else: aeTypeRange,
            derivation:
              (if fromAssert: "assertion-derived range "
               else: "type-derived range ") &
              $ivl & " fits " & $p.ty & " BV window")
        # isLoose: no range constraints, no audit entry — by design,
        # the user is told this is unsound and accepts it.
      else:
        env[p.name] = bvVar(p.ty, p.name)
        if p.hasRange:
          # Type-derived range as BV constraints (so `x > 100` is
          # still UNSAT under isExact for range[0..100]).
          initialPC.add lowerBool(env,
            mkBinop(bGe, mkVar(p.name), mkIntLit(p.rangeLo)))
          initialPC.add lowerBool(env,
            mkBinop(bLe, mkVar(p.name), mkIntLit(p.rangeHi)))
    of itBool:
      env[p.name] = SymVal(kind: svBool, bo: mkBoolVar(p.name))
  let initial = Path(pc: initialPC, env: env)
  # Static IR scan: collect string-literal keys accessed on each
  # Table-typed param so witness extraction returns a Nim Table
  # populated for those keys.
  var tabKeys: Table[string, HashSet[string]]
  var setMembers: Table[string, HashSet[int64]]
  for p in prog.params:
    if p.ty.kind == itTable:
      var keys: HashSet[string]
      collectTableLitKeys(prog.body, p.name, keys)
      tabKeys[p.name] = keys
    elif p.ty.kind == itSet:
      var members: HashSet[int64]
      collectSetLitMembers(prog.body, p.name, members)
      setMembers[p.name] = members
  var w = WalkCtx(
    z3: ctx, target: target, params: prog.params,
    found: @[], sawUnknown: false,
    settings: settings, procs: prog.procs,
    callStack: @[], callStats: initTable[string, CallStat](),
    callCache: initTable[string, CallCacheEntry](),
    activeCalls: initHashSet[string](),
    tabKeys: tabKeys,
    setMembers: setMembers,
    initialEnv: env,
  )
  discard walk(prog.body, @[initial], w)
  var statsSeq: CallStats
  for name, st in w.callStats:
    statsSeq.add st
  if w.found.len > 0:
    var r = w.found[0]   ## Phase 15 Z4: found holds sxSat findings; take the first
    r.abstractions = log
    r.callStats = statsSeq
    r
  elif w.sawUnknown:
    RawResult(status: sxUnknown, abstractions: log, callStats: statsSeq)
  else:
    RawResult(status: sxUnsat, abstractions: log, callStats: statsSeq)

# ---- Raw → typed witness ----------------------------------------------------
#
# Per-width readers used by the macro's tuple-construction. The macro
# selects the right reader based on the param's IRType.

proc readBool*(w: RawWitness, name: string): bool =
  w.boolVals[name]

# Phase 15 F1 stubs: float witnesses are not yet bit-exact (RawWitness has no
# float slot until F7). Returns 0.0 so a float-param SUT yields a well-typed
# (if not bit-correct) witness. Real extraction lands in F7.
proc readFloat*(w: RawWitness, name: string): float = 0.0
proc readFloat32*(w: RawWitness, name: string): float32 = 0.0'f32

# Signed widths return the matching Nim signed type.
proc readInt*(w: RawWitness,   name: string): int   = int(  w.intVals[name])
proc readInt8*(w: RawWitness,  name: string): int8  = int8( w.intVals[name])
proc readInt16*(w: RawWitness, name: string): int16 = int16(w.intVals[name])
proc readInt32*(w: RawWitness, name: string): int32 = int32(w.intVals[name])
proc readInt64*(w: RawWitness, name: string): int64 =       w.intVals[name]

# Unsigned widths.
proc readUInt*(w: RawWitness,   name: string): uint   = uint(  w.uintVals[name])
proc readUInt8*(w: RawWitness,  name: string): uint8  = uint8( w.uintVals[name])
proc readUInt16*(w: RawWitness, name: string): uint16 = uint16(w.uintVals[name])
proc readUInt32*(w: RawWitness, name: string): uint32 = uint32(w.uintVals[name])
proc readUInt64*(w: RawWitness, name: string): uint64 =        w.uintVals[name]

proc readString*(w: RawWitness, name: string): string = w.strVals[name]

proc readSeqInt*(w: RawWitness, name: string): seq[int] =
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int(w.intVals[path])

proc readTableStrInt*(w: RawWitness, name: string): Table[string, int] =
  ## Phase 5 cycle 5: build a `Table[string, int]` populated with the
  ## key-value pairs the SUT accessed (static string literals).
  result = initTable[string, int]()
  if not w.tabKeys.hasKey(name):
    return
  for k in w.tabKeys[name]:
    let p = name & "." & k
    if w.intVals.hasKey(p):
      result[k] = int(w.intVals[p])

proc readSetInt*(w: RawWitness, name: string): HashSet[int] =
  ## Phase 5 cycle 8: build a `HashSet[int]` from collected members.
  result = initHashSet[int]()
  if not w.setMembers.hasKey(name): return
  for v in w.setMembers[name]:
    result.incl int(v)
