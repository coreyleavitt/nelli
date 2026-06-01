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

proc allocateSym(ty: IRType, baseName: string,
                 pcOut: var seq[Z3Bool]): SymVal =
  ## Recursively allocate a SymVal for `ty`. Init-side constraints
  ## (like `seqLen ≥ 0`) accumulate into `pcOut`.
  case ty.kind
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
  of iekIntLit, iekBoolLit:
    none(SymVal)

# ---- IR-expr → SymVal -------------------------------------------------------

proc lower(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal

proc mkZ3IntLit(v: int64): Z3Int {.inline.} =
  ## Build a Z3Int from an `int64`. `mkInt` truncates to `cint`
  ## (32 bits on Linux) — for values that don't fit, we route
  ## through `mkBigInt` which takes the decimal string.
  if v >= int64(low(int32)) and v <= int64(high(int32)):
    mkInt(int(v))
  else:
    mkBigInt($v)

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
  of svString, svSeq, svTable, svSet:
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
  of svBV8:  liftBV(mkBitVec[8](ival),  proto.signed)
  of svBV16: liftBV(mkBitVec[16](ival), proto.signed)
  of svBV32: liftBV(mkBitVec[32](ival), proto.signed)
  of svBV64: liftBV(mkBitVec[64](ival), proto.signed)
  of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(ival))
  of svBool:
    raise newException(ValueError,
      "coerceIntLit: bool prototype for integer literal")
  of svTuple, svArray, svString, svSeq, svTable, svSet:
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
  of iekBoolLit:
    ofBool(mkBool(e.bval))
  of iekVar:
    env[e.vname]
  of iekField:
    # Lower the receiver, then pick the field by index.
    let recv = lower(env, e.obj)
    doAssert recv.kind == svTuple,
      "iekField on non-tuple SymVal kind=" & $recv.kind
    recv.fields[e.fieldIx]
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
    w.intVals[path] = int64(m.evalInt(sv.zi))
  of svString:
    w.strVals[path] = m.evalStr(sv.str)
  of svTuple, svArray, svSeq, svTable, svSet:
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
  of isAssert:
    collectSetLitMembersExpr(s.acond, paramName, members)
  of isCall:
    for a in s.cargs: collectSetLitMembersExpr(a, paramName, members)
  of isIndex:
    collectSetLitMembersExpr(s.ixArr, paramName, members)
    collectSetLitMembersExpr(s.ixIdx, paramName, members)
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

proc trySolve(ctx: Z3Context,
              path: Path,
              params: seq[IRParam],
              tabKeys: Table[string, HashSet[string]] = initTable[string, HashSet[string]](),
              setMembers: Table[string, HashSet[int64]] = initTable[string, HashSet[int64]](),
              initialEnv: Env = initOrderedTable[string, SymVal]()
              ): tuple[status: SymexStatusKind, witness: RawWitness] =
  let s = newSolver(ctx)
  for c in path.pc:
    s.add(c)
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
  CallFrame = object
    ## A walker-level call frame. The runtime pushes one of these per
    ## active inline-call expansion; isReturn consults the top entry
    ## to wire the returned value into the caller's `retSym`.
    callee:        string
    retSym:        SymVal           ## the fresh symbol returned values bind to
    retName:       string           ## "" for void
    returnedPaths: seq[Path]        ## paths that hit `return` inside this call

  WalkCtx = object
    z3:        Z3Context
    target:    SymexTarget
    params:    seq[IRParam]
    found:     Option[RawResult]
    sawUnknown: bool
    settings:  SymexSettings
    procs:     Table[string, ProcSig]
    callStack: seq[CallFrame]
    callStats: Table[string, CallStat]
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
  w.found.isSome and w.found.get.status == sxSat

proc symValHash(sv: SymVal): uint =
  ## Hash of a SymVal's Z3 representation for use as a call-cache key.
  case sv.kind
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
            let (st, wit) = trySolve(w.z3, oobPath, w.params, w.tabKeys, w.setMembers, w.initialEnv)
            case st
            of sxSat:    w.found = some(RawResult(status: sxSat, witness: wit))
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
          let (st, wit) = trySolve(w.z3, oobPath, w.params, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found = some(RawResult(status: sxSat, witness: wit))
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
          let retConstraint =
            case w.callStack[frameIx].retSym.kind
            of svBool: w.callStack[frameIx].retSym.bo == retVal.bo
            of svInt:  w.callStack[frameIx].retSym.zi == retVal.zi
            of svBV8:  w.callStack[frameIx].retSym.bv8  == retVal.bv8
            of svBV16: w.callStack[frameIx].retSym.bv16 == retVal.bv16
            of svBV32: w.callStack[frameIx].retSym.bv32 == retVal.bv32
            of svBV64: w.callStack[frameIx].retSym.bv64 == retVal.bv64
            of svTuple, svArray, svString, svSeq, svTable, svSet:
              raise newException(ValueError,
                "composite-typed proc return not yet wired (Phase 4+)")
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
          let (st, wit) = trySolve(w.z3, violPath, w.params, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found = some(RawResult(status: sxSat, witness: wit))
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
          let (st, wit) = trySolve(w.z3, p, w.params, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found = some(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
    paths
  of isUnsupported:
    w.sawUnknown = true
    paths

# ---- Public driver ----------------------------------------------------------

proc runSymex*(prog: SymexProgram,
               target: SymexTarget,
               settings: SymexSettings = defaultSymexSettings()): RawResult =
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
  if settings.integerSemantics == isLoose:
    emitIsLooseBanner()
  for p in prog.params:
    case p.ty.kind
    of itTuple, itArray, itString, itSeq, itTable, itSet:
      env[p.name] = allocateSym(p.ty, p.name, initialPC)
    of itInt:
      let ivl = interval(p.rangeLo, p.rangeHi)
      # Three modes (ADR-0001):
      #   * isLoose      — all ints become Z3Int (UNSOUND; banner above).
      #   * isOptimised — promote when range-derived + window-fits +
      #                   not bit-twiddled.
      #   * isExact      — always BV[W].
      let promoteLoose = settings.integerSemantics == isLoose
      let promoteSound = settings.integerSemantics == isOptimised and
                         p.hasRange and
                         fitsBVWindow(ivl, p.ty) and
                         p.name notin banned
      let promote = promoteLoose or promoteSound
      if promote:
        env[p.name] = SymVal(kind: svInt, zi: mkIntVar(p.name))
        if promoteSound:
          # Range constraints in Z3Int form. Use mkZ3IntLit so values
          # outside `cint` range (e.g. `Natural`'s `int64.high` upper
          # bound) survive the conversion via mkBigInt.
          initialPC.add (env[p.name].zi >= mkZ3IntLit(p.rangeLo))
          initialPC.add (env[p.name].zi <= mkZ3IntLit(p.rangeHi))
          log.add AbstractionEntry(
            name: p.name,
            interval: ivl,
            evidence: aeTypeRange,
            derivation: "type-derived range " & $ivl & " fits " & $p.ty &
                        " BV window")
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
    found: none(RawResult), sawUnknown: false,
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
  if w.found.isSome:
    var r = w.found.get
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
