## proptest/symex — public-API entry for the symbolic-execution capability.
##
## See:
##   * docs/SYMEX_PLAN.md     — build plan + scope
##   * docs/symex/ADR-0001-integer-semantics.md
##   * docs/symex/ADR-0002-dsl-factoring.md
##
## Phase 1 supports a small Nim fragment: int/bool params + locals,
## arithmetic + comparison + boolean, `if` / `elif` / `else`, the
## three body markers below. Each later phase widens the fragment.
##
## Body markers — these are templates so that the same SUT is
## simultaneously walkable by symex AND runnable under random PBT
## without source duplication. Outside symex:
##
##   * `symexTarget(name)`  — no-op (it's a coverage label)
##   * `symexAssert(cond)`  — `doAssert cond` (it's a stated invariant)
##   * `symexAssume(cond)`  — early return if violated (filter the
##                            execution to satisfying inputs)

import std/macros
import ./smt/dsl
export dsl

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
    else:
      case ty.width
      of 8:  ("uint8",  "readUInt8")
      of 16: ("uint16", "readUInt16")
      of 32: ("uint32", "readUInt32")
      of 64: ("uint",   "readUInt")
      else: ("uint", "readUInt")
  else: ("", "")

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode) =
  ## Recursive: returns (Nim type AST, witness-construction expression).
  case ty.kind
  of itBool, itInt:
    let (tyName, readerName) = primTyAndReader(ty)
    (ident(tyName), newCall(ident(readerName), witId, newLit(path)))
  of itTuple:
    if ty.objectName.len > 0:
      # Nominal object: Type = ident(name); Value = ident(name)(field: …)
      let objTyId = ident(ty.objectName)
      var objVal = newTree(nnkObjConstr, objTyId)
      for i, fty in ty.fields:
        let suffix = "." & ty.fieldNames[i]
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
    let arrTy = newTree(nnkBracketExpr,
      ident("array"), newLit(ty.size), elemTyNode)
    var arrLit = newTree(nnkBracket)
    for i in 0 ..< ty.size:
      let (_, sv) = emitTyAndReader(ty.elemTy, path & "." & $i, witId)
      arrLit.add sv
    (arrTy, arrLit)
  of itString:
    (ident("string"), newCall(ident("readString"), witId, newLit(path)))
  of itSeq:
    # Phase 5 cycle 1: only seq[int] tested; specialised reader.
    if ty.seqElemTy.kind == itInt and ty.seqElemTy.signed and
       ty.seqElemTy.width == 64:
      (newTree(nnkBracketExpr, ident("seq"), ident("int")),
       newCall(ident("readSeqInt"), witId, newLit(path)))
    else:
      error("symex Phase 5: seq witness reader for " & $ty &
            " not yet implemented")
  of itTable, itSet:
    error("symex Phase 5: " & $ty.kind &
          " witness emission arrives with later cycles")

# ---- Body markers -----------------------------------------------------------

## Body markers are procs (not templates) so semcheck doesn't elide
## the call site before the symex parser sees it. The parser
## recognizes the call by callee name; outside symex these run as
## ordinary procs whose body provides the dual-mode semantics.

proc symexTarget*(name: string) {.inline.} =
  ## Marker: a coverage target for `symexFind(..., tLabel(name))`.
  ## Outside symex, calling this is a no-op — the SUT is unaffected.
  discard name

proc symexAssert*(cond: bool) {.inline.} =
  ## Marker: an invariant the user claims always holds. Outside
  ## symex, asserted at runtime via `doAssert` so random PBT also
  ## catches violations. Inside symex, the parser maps this to an
  ## IR node the walker treats as a fork point for
  ## `tAssertionViolation` searches.
  doAssert cond, "symexAssert violated"

proc symexAssume*(cond: bool) {.inline.} =
  ## Marker: a precondition restricting the input domain. Phase 1
  ## ships with no-op outside symex (the richer "early-return on
  ## violation" semantics is deferred until needed — `symexAssume`'s
  ## body markers in Phase 1 are recognized by the parser but don't
  ## yet affect the SUT's normal-run behavior). Inside symex, the
  ## walker conjoins `cond` into the path condition.
  discard cond

# ---- The driver macro -------------------------------------------------------

macro symexFind*(fn: typed,
                 target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): untyped =
  ## Symbolically execute `fn` searching for an input that reaches `target`.
  ## Returns `SymexResult[ParamTuple]` where `ParamTuple` is the proc's
  ## parameter list as a Nim tuple.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("symexFind: expected a `proc` symbol", fn)
  let parsed = parseProc(impl)

  # Build the tuple type and witness-construction tuple. We genSym a
  # local name for the RawWitness so the witness-constructor calls
  # share an identity-equal NimNode with the `let` that binds it.
  let witId = genSym(nskLet, "rawWit")
  var tupleTy = newTree(nnkTupleConstr)
  var witnessTup = newTree(nnkTupleConstr)
  for p in parsed.params:
    let (pTy, pVal) = emitTyAndReader(p.ty, p.name, witId)
    tupleTy.add pTy
    witnessTup.add pVal

  # `(int,)` is a syntactic 1-tuple; nnkTupleConstr with one child
  # renders correctly for both the type and the value.

  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode

  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      let raw = runSymex(prog, `target`, `settings`)
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats)
