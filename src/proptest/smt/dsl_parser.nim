## Layer 1 of the predicate DSL (ADR-0002): typed Nim AST → IR.
##
## This is the algorithmically subtle layer the ADR calls out as the
## one worth testing in isolation. It runs at macro time only.
##
## Supported fragment (cumulative across phases):
##
##   * Statements: `nnkStmtList`, `nnkBlockStmt`, `nnkIfStmt`,
##                 `nnkLetSection`/`nnkVarSection`, `nnkReturnStmt`,
##                 the body markers, and (Phase 3) user-defined proc
##                 calls.
##   * Expressions: int / bool / fixed-width-int literals + vars,
##                  `nnkInfix`/`nnkPrefix` arithmetic + comparison +
##                  boolean, `nnkHiddenStdConv`/`nnkConv` passthrough,
##                  and (Phase 3) calls to user procs — A-normalised
##                  into a preamble of `isCall` statements that bind
##                  fresh `__sym_<name>_<n>` temporaries.
##
## A-normalisation: each call expression `foo(args)` in expression
## position contributes:
##
##   1. An `isCall` stmt in the surrounding statement's *preamble*
##      that runs before the statement.
##   2. A fresh `mkVar(<synth>)` in place of the call.
##
## The walker only ever sees calls as statements.

import std/macros
import std/strformat
import std/strutils
import std/sets
import std/tables
import std/algorithm   ## Phase 15 G1a: sorted type-tuple in the inst key
import std/hashes      ## Phase 15 C1: lambda-site body-hash (lineInfo fallback)
import ./types
import ./dsl_typebridge
import ./stdlib_models
import ./exn_hierarchy   ## Phase 15 E4a: exnTypeTable (known-base sentinel)

# ---- emit: macro-time IR → runtime-construction NimNode -----------------------

proc emitBinop(op: IRBinop): NimNode =
  newDotExpr(bindSym"IRBinop", ident($op))

proc emitUnop(op: IRUnop): NimNode =
  newDotExpr(bindSym"IRUnop", ident($op))

proc emitIRType*(t: IRType): NimNode
proc emitStmt*(s: IRStmt): NimNode
proc emitParam(p: IRParam): NimNode     ## fwd: Phase 15 C1 (lambdaParams)

proc emitExpr*(e: IRExpr): NimNode =
  case e.kind
  of iekIntLit:
    newCall(bindSym"mkIntLit", newLit(e.ival))
  of iekFloatLit:
    newCall(bindSym"mkFloatLit", newLit(e.fval), newLit(e.fwidth))
  of iekConvIntToFloat:
    newCall(bindSym"mkConvIntToFloat", emitExpr(e.convOperand), newLit(e.convWidth))
  of iekConvFloatToInt:
    newCall(bindSym"mkConvFloatToInt", emitExpr(e.convOperand), newLit(e.convWidth))
  of iekMathCall:
    var argLit = newTree(nnkBracket)
    for a in e.mathArgs: argLit.add emitExpr(a)
    newCall(bindSym"mkMathCall", newLit(e.mathOp), prefix(argLit, "@"))
  of iekBoolLit:
    newCall(bindSym"mkBoolLit", newLit(e.bval))
  of iekVar:
    newCall(bindSym"mkVar", newLit(e.vname))
  of iekBinop:
    newCall(bindSym"mkBinop", emitBinop(e.bop), emitExpr(e.lhs), emitExpr(e.rhs))
  of iekUnop:
    newCall(bindSym"mkUnop", emitUnop(e.uop), emitExpr(e.operand))
  of iekBorrowOp:   ## Phase 15 G5
    newCall(bindSym"mkBorrowOp", emitBinop(e.borrowOp),
            emitExpr(e.borrowLhs), emitExpr(e.borrowRhs),
            newLit(e.borrowReturnsDistinct), newLit(e.borrowDistinctName))
  of iekField:
    newCall(bindSym"mkField", emitExpr(e.obj),
            newLit(e.fieldIx), newLit(e.fieldName))
  of iekIndex:
    newCall(bindSym"mkIndex", emitExpr(e.arr), emitExpr(e.idx))
  of iekArrayLit:
    var lit = newTree(nnkBracket)
    for c in e.lelems: lit.add emitExpr(c)
    newCall(bindSym"mkArrayLit", prefix(lit, "@"), emitIRType(e.lelemTy))
  of iekSeqLen:
    newCall(bindSym"mkSeqLen", emitExpr(e.lenObj))
  of iekStrLit:
    newCall(bindSym"mkStrLit", newLit(e.sval))
  of iekContains:
    newCall(bindSym"mkContains", emitExpr(e.container), emitExpr(e.key))
  of iekSeqAdd:
    newCall(bindSym"mkSeqAdd", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of iekSeqDel:
    newCall(bindSym"mkSeqDel", emitExpr(e.delSeq), emitExpr(e.delIdx))
  of iekSeqInsert:
    newCall(bindSym"mkSeqInsert", emitExpr(e.insSeq),
            emitExpr(e.insVal), emitExpr(e.insIdx))
  of iekSeqPop:
    newCall(bindSym"mkSeqPop", emitExpr(e.popSeq))
  of iekTableSet:
    newCall(bindSym"mkTableSet", emitExpr(e.tabRecv),
            emitExpr(e.tabKey), emitExpr(e.tabVal))
  of iekTableDel:
    newCall(bindSym"mkTableDel", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of iekSetIncl:
    newCall(bindSym"mkSetIncl", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of iekSetExcl:
    newCall(bindSym"mkSetExcl", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of StrOpKinds:
    # Phase 15 Cluster S (S1). Re-emit a runtime-reconstructible string-op node:
    # `mkStrOp(kind, op, @[args])`. The kind is emitted as its enum symbol.
    var argsLit = newTree(nnkBracket)
    for a in e.strArgs: argsLit.add emitExpr(a)
    newCall(bindSym"mkStrOp", ident($e.kind), newLit(e.strOp),
            prefix(argsLit, "@"))
  of iekGetCurrentExn:    newCall(bindSym"mkGetCurrentExn")      ## Phase 15 E8
  of iekGetCurrentExnMsg: newCall(bindSym"mkGetCurrentExnMsg")   ## Phase 15 E8
  of iekLambda:           ## Phase 15 C1
    var paramsLit = newTree(nnkBracket)
    for p in e.lambdaParams: paramsLit.add emitParam(p)
    var capsLit = newTree(nnkBracket)
    for c in e.lambdaCaptures: capsLit.add newLit(c)
    newCall(bindSym"mkLambda",
            newLit(e.lambdaSite.siteHash), newLit(e.lambdaSite.declOrder),
            prefix(paramsLit, "@"), emitStmt(e.lambdaBody),
            prefix(capsLit, "@"), emitIRType(e.lambdaRetTy))
  of iekClosureCall:      ## Phase 15 C1
    var argsLit = newTree(nnkBracket)
    for a in e.ccArgs: argsLit.add emitExpr(a)
    newCall(bindSym"mkClosureCall", newLit(e.ccCallee), prefix(argsLit, "@"))
  of iekSeqLit:           ## Phase 15 C4
    var elemsLit = newTree(nnkBracket)
    for c in e.seqLitElems: elemsLit.add emitExpr(c)
    newCall(bindSym"mkSeqLit", prefix(elemsLit, "@"), emitIRType(e.seqLitElemTy))
  of iekHofCall:          ## Phase 15 C4
    let initArg = if e.hofInit != nil: emitExpr(e.hofInit)
                  else: newNilLit()
    newCall(bindSym"mkHofCall", newLit(e.hofOp), emitExpr(e.hofSeq),
            emitExpr(e.hofClosure), emitIRType(e.hofRetElemTy), initArg)
  of iekNil:              ## Phase 15 R5
    newCall(bindSym"mkNil", emitIRType(e.nilPointee))

proc emitIRType*(t: IRType): NimNode =
  case t.kind
  of itBool:
    newCall(bindSym"tBool")
  of itString:
    newCall(bindSym"tString")
  of itUninterp:
    newCall(bindSym"tUninterp", newLit(t.uninterpName))
  of itFloat32: newCall(bindSym"tFloat32")
  of itFloat64: newCall(bindSym"tFloat64")
  of itDistinct:   ## Phase 15 G4: name + recursive base.
    newCall(bindSym"tDistinct", newLit(t.distinctName), emitIRType(t.distinctBase))
  of itRef:        ## Phase 15 R1a: ref + recursive pointee.
    newCall(bindSym"tRef", emitIRType(t.refPointeeTy))
  of itPtr:        ## Phase 15 R1a: ptr + recursive pointee.
    newCall(bindSym"tPtr", emitIRType(t.ptrPointeeTy))
  of itInt:
    newCall(bindSym"tInt", newLit(t.width), newLit(t.signed))
  of itTuple:
    var fieldsLit = newTree(nnkBracket)
    for f in t.fields:
      fieldsLit.add emitIRType(f)
    var namesLit = newTree(nnkBracket)
    for n in t.fieldNames:
      namesLit.add newLit(n)
    newCall(bindSym"tTuple", prefix(fieldsLit, "@"),
            prefix(namesLit, "@"), newLit(t.objectName))
  of itArray:
    newCall(bindSym"tArray", emitIRType(t.elemTy), newLit(t.size))
  of itSeq:
    newCall(bindSym"tSeq", emitIRType(t.seqElemTy))
  of itTable:
    newCall(bindSym"tTable", emitIRType(t.tabKeyTy), emitIRType(t.tabValTy))
  of itSet:
    newCall(bindSym"tSet", emitIRType(t.setElemTy))
  of itVariant:
    # Phase 11 cycle 3 + plain-field sharing — emit a runtime-
    # reconstructible IR literal for itVariant. Discriminator,
    # every arm's (tag ordinal + name + arm-specific fields),
    # plus the always-present plain field prefix.
    var armsLit = newTree(nnkBracket)
    for arm in t.vArms:
      var fieldNamesLit = newTree(nnkBracket)
      for n in arm.fieldNames: fieldNamesLit.add newLit(n)
      var fieldTypesLit = newTree(nnkBracket)
      for ft in arm.fieldTypes: fieldTypesLit.add emitIRType(ft)
      let armCons = nnkObjConstr.newTree(
        bindSym"VariantArm",
        nnkExprColonExpr.newTree(ident"tagOrdinal", newLit(arm.tagOrdinal)),
        nnkExprColonExpr.newTree(ident"tagName",    newLit(arm.tagName)),
        nnkExprColonExpr.newTree(ident"fieldNames", prefix(fieldNamesLit, "@")),
        nnkExprColonExpr.newTree(ident"fieldTypes", prefix(fieldTypesLit, "@")),
        nnkExprColonExpr.newTree(ident"isElse",     newLit(arm.isElse)))
      armsLit.add armCons
    var plainNamesLit = newTree(nnkBracket)
    for n in t.vPlainFieldNames: plainNamesLit.add newLit(n)
    var plainTypesLit = newTree(nnkBracket)
    for ft in t.vPlainFieldTypes: plainTypesLit.add emitIRType(ft)
    var discTagsLit = newTree(nnkBracket)
    for dt in t.vDiscTags:
      discTagsLit.add nnkTupleConstr.newTree(
        nnkExprColonExpr.newTree(ident"name", newLit(dt.name)),
        nnkExprColonExpr.newTree(ident"ord",  newLit(dt.ord)))
    newCall(bindSym"tVariant",
      newLit(t.vObjectName), newLit(t.vDiscName),
      emitIRType(t.vDiscTy),
      prefix(armsLit, "@"),
      prefix(plainNamesLit, "@"),
      prefix(plainTypesLit, "@"),
      prefix(discTagsLit, "@"))
  of itMultiVariant:
    # Phase 14 cycle A1a stub. Re-emit a runtime-reconstructible
    # `mkMultiVariant(…)` call. Full A1b (parser-side classification)
    # is what produces these IR values from Nim source; here we just
    # need round-trip emission of an already-built IR.
    var axesLit = newTree(nnkBracket)
    for ax in t.mvAxes:
      var armsLit = newTree(nnkBracket)
      for arm in ax.arms:
        var fieldNamesLit = newTree(nnkBracket)
        for n in arm.fieldNames: fieldNamesLit.add newLit(n)
        var fieldTypesLit = newTree(nnkBracket)
        for ft in arm.fieldTypes: fieldTypesLit.add emitIRType(ft)
        armsLit.add nnkObjConstr.newTree(
          bindSym"VariantArm",
          nnkExprColonExpr.newTree(ident"tagOrdinal", newLit(arm.tagOrdinal)),
          nnkExprColonExpr.newTree(ident"tagName",    newLit(arm.tagName)),
          nnkExprColonExpr.newTree(ident"fieldNames", prefix(fieldNamesLit, "@")),
          nnkExprColonExpr.newTree(ident"fieldTypes", prefix(fieldTypesLit, "@")),
          nnkExprColonExpr.newTree(ident"isElse",     newLit(arm.isElse)))
      var discTagsLit = newTree(nnkBracket)
      for dt in ax.discTags:
        discTagsLit.add nnkTupleConstr.newTree(
          nnkExprColonExpr.newTree(ident"name", newLit(dt.name)),
          nnkExprColonExpr.newTree(ident"ord",  newLit(dt.ord)))
      axesLit.add nnkObjConstr.newTree(
        bindSym"VariantAxis",
        nnkExprColonExpr.newTree(ident"discName", newLit(ax.discName)),
        nnkExprColonExpr.newTree(ident"discTy",   emitIRType(ax.discTy)),
        nnkExprColonExpr.newTree(ident"arms",     prefix(armsLit, "@")),
        nnkExprColonExpr.newTree(ident"discTags", prefix(discTagsLit, "@")))
    var plainNamesLit = newTree(nnkBracket)
    for n in t.mvPlainFieldNames: plainNamesLit.add newLit(n)
    var plainTypesLit = newTree(nnkBracket)
    for ft in t.mvPlainFieldTypes: plainTypesLit.add emitIRType(ft)
    newCall(bindSym"mkMultiVariant",
      newLit(t.mvObjectName),
      prefix(axesLit, "@"),
      prefix(plainNamesLit, "@"),
      prefix(plainTypesLit, "@"))

proc emitBranch(br: IRBranch): NimNode =
  newCall(bindSym"mkBranch", emitExpr(br.cond), emitStmt(br.body))

proc emitExprSeq(xs: seq[IRExpr]): NimNode =
  var lit = newTree(nnkBracket)
  for x in xs:
    lit.add emitExpr(x)
  prefix(lit, "@")

proc emitStmt*(s: IRStmt): NimNode =
  if s == nil:
    return newNilLit()
  case s.kind
  of isBlock:
    var seqLit = newTree(nnkBracket)
    for st in s.stmts:
      seqLit.add emitStmt(st)
    newCall(bindSym"mkBlock", prefix(seqLit, "@"))
  of isIf:
    var seqLit = newTree(nnkBracket)
    for br in s.branches:
      seqLit.add emitBranch(br)
    newCall(bindSym"mkIf", prefix(seqLit, "@"), emitStmt(s.elseBody))
  of isLet:
    newCall(bindSym"mkLet", newLit(s.lname), emitIRType(s.lty), emitExpr(s.lvalue))
  of isAssign:
    newCall(bindSym"mkAssign", newLit(s.aname), emitExpr(s.avalue))
  of isWhile:
    newCall(bindSym"mkWhile", emitExpr(s.wcond), emitStmt(s.wbody))
  of isBreak:
    newCall(bindSym"mkBreak")
  of isContinue:
    newCall(bindSym"mkContinue")
  of isReturn:
    if s.retExpr == nil:
      newCall(bindSym"mkReturn")
    else:
      newCall(bindSym"mkReturnVal", emitExpr(s.retExpr))
  of isCall:
    if s.opaque:
      newCall(bindSym"mkOpaqueCall",
              newLit(s.callee), newLit(s.retName),
              emitExprSeq(s.cargs), emitIRType(s.retTy))
    else:
      newCall(bindSym"mkCall",
              newLit(s.callee), newLit(s.retName),
              emitExprSeq(s.cargs), emitIRType(s.retTy))
  of isIndex:
    newCall(bindSym"mkIndexStmt",
            newLit(s.ixRetName), emitExpr(s.ixArr),
            emitExpr(s.ixIdx), emitIRType(s.ixElemTy))
  of isVariantField:
    var tagsLit = newTree(nnkBracket)
    for t in s.vfMatchingTags: tagsLit.add newLit(t)
    newCall(bindSym"mkVariantFieldStmt",
            newLit(s.vfRetName), emitExpr(s.vfRecv),
            newLit(s.vfFieldName), emitIRType(s.vfFieldTy),
            prefix(tagsLit, "@"))
  of isVariantReassign:
    newCall(bindSym"mkVariantReassign",
            newLit(s.vrObjName), newLit(s.vrNewTag), newLit(s.vrTagName))
  of isVariantReassignSymbolic:
    newCall(bindSym"mkVariantReassignSymbolic",
            newLit(s.vrsObjName), newLit(s.vrsDiscName),
            emitExpr(s.vrsRhs))
  of isAssert:
    newCall(bindSym"mkAssert", emitExpr(s.acond))
  of isTargetLabel:
    newCall(bindSym"mkTargetLabel", newLit(s.tname))
  of isRaise:
    if s.raiseIsReraise:
      newCall(bindSym"mkReraise")
    else:
      let msgNode = if s.raiseMsg == nil: newNilLit()
                    else: emitExpr(s.raiseMsg)
      newCall(bindSym"mkRaise", newLit(s.raiseTypeId), msgNode)
  of isTry:
    # Reconstruct the `seq[ExceptHandler]` literal, then the finally (nil-safe).
    var handlersLit = newTree(nnkBracket)
    for h in s.tryHandlers:
      var idsLit = newTree(nnkBracket)
      for tid in h.typeIds: idsLit.add newLit(tid)
      handlersLit.add nnkObjConstr.newTree(
        bindSym"ExceptHandler",
        nnkExprColonExpr.newTree(ident"typeIds", prefix(idsLit, "@")),
        nnkExprColonExpr.newTree(ident"body", emitStmt(h.body)))
    newCall(bindSym"mkTry", emitStmt(s.tryBody),
            prefix(handlersLit, "@"), emitStmt(s.tryFinally))
  of isDeref:   ## Phase 15 R1a: ref/ptr deref (ptr-family picks the ctor).
    if s.dField.len > 0:        ## Phase 15 R6: `p.field` field deref.
      newCall(bindSym"mkFieldDeref", newLit(s.dRetName), emitExpr(s.dPtr),
              emitIRType(s.dElemTy), emitIRType(s.dObjTy), newLit(s.dField),
              newLit(s.dPtrFamily))
    else:
      let ctor = if s.dPtrFamily: bindSym"mkPtrDeref" else: bindSym"mkDeref"
      newCall(ctor, newLit(s.dRetName), emitExpr(s.dPtr), emitIRType(s.dElemTy))
  of isNew:     ## Phase 15 R1a: allocation.
    newCall(bindSym"mkNewT", newLit(s.nRetName), emitIRType(s.nRefTy))
  of isDerefWrite:   ## Phase 15 R3: heap write `p[] = v` (walker no-ops at R3).
    if s.dwField.len > 0:       ## Phase 15 R6: `p.field = v` field write.
      newCall(bindSym"mkFieldDerefWrite", emitExpr(s.dwPtr), emitExpr(s.dwValue),
              emitIRType(s.dwElemTy), emitIRType(s.dwObjTy), newLit(s.dwField),
              newLit(s.dwPtrFamily))
    else:
      newCall(bindSym"mkDerefWrite", emitExpr(s.dwPtr), emitExpr(s.dwValue),
              emitIRType(s.dwElemTy), newLit(s.dwPtrFamily))
  of isUnsupported:
    newCall(bindSym"mkUnsupported", newLit(s.reason))
  of isUnsafeCast:
    newCall(bindSym"mkUnsafeCast", newLit(s.ucReason))

# ---- ParseCtx ----------------------------------------------------------------
#
# Threaded through the entire parse so that call discovery accumulates
# into a single `procs` table and synthesised temporaries get unique
# names.

type
  ParseCtx* = ref object
    procs*:      Table[string, ProcSig]
    parsing*:    HashSet[string]   ## currently-being-parsed callees
                                   ## (cycle break for mutual recursion)
    synthCounter*: int
    userExnHierarchy*: Table[string, string]
                                   ## Phase 15 E4a. child -> direct-parent
                                   ## links for USER-defined exception types,
                                   ## accumulated as raise/except type symbols
                                   ## are parsed. Threaded to WalkerStatics at
                                   ## parse completion.
    maxInstantiationsPerProc*: int
                                   ## Phase 15 G1c. Per-base-proc instantiation
                                   ## cap, threaded from the active
                                   ## `SymexSettings` at macro time. `0` =
                                   ## unlimited. Default 0 here; the macros set
                                   ## it from `settings.maxInstantiationsPerProc`.
    instCounts*: Table[string, int]
                                   ## Phase 15 G1c. Count of DISTINCT
                                   ## instantiations registered per BASE proc
                                   ## (keyed by the base identity — proc name +
                                   ## bodyHash — NOT the full instKey). Drives
                                   ## the per-proc cap check.
    parseErrors*: seq[SymexErrorInfo]
                                   ## Phase 15 G1c. Errors discovered during
                                   ## parse-time monomorphization (cap overflow
                                   ## → `geInstantiationCapped`). Emitted via
                                   ## `ParseResult` into `SymexProgram.parseErrors`
                                   ## and drained into the run's `errors`.
    lambdaCounter*: int
                                   ## Phase 15 Cluster C (C1, ADR-0009 D3). Monotone
                                   ## index of lambda declarations encountered
                                   ## during parse — the `declOrder` half of the
                                   ## lambda-site key, disambiguating two lambdas
                                   ## with identical bodies.

proc newParseCtx*(maxInstantiationsPerProc = 0): ParseCtx =
  ParseCtx(procs: initTable[string, ProcSig](),
           parsing: initHashSet[string](),
           synthCounter: 0,
           userExnHierarchy: initTable[string, string](),
           maxInstantiationsPerProc: maxInstantiationsPerProc,
           instCounts: initTable[string, int]())

proc collectUserExnAncestors(typeSym: NimNode, ctx: ParseCtx) =
  ## Phase 15 E4a. Walk `typeSym`'s inheritance chain via `getImpl`, recording
  ## each `child -> direct-parent` link into `ctx.userExnHierarchy`, until the
  ## chain reaches a type already in the static `exnTypeTable` (ValueError /
  ## IOError / Defect / …) or has no inherit clause (RootObj / non-object).
  ##
  ## Shape of `getImpl` for `type Child = object of Parent`:
  ##   TypeDef[ Sym "Child", Empty, ObjectTy[ Empty, OfInherit[ Sym "Parent" ],
  ##            <recList> ] ]  (RefTy/PtrTy may wrap the ObjectTy for `ref`).
  ##
  ## Only USER types are walked: a `typeSym` already known to the static table
  ## (a stdlib exn) needs no dynamic links. Cycles are guarded by a depth cap
  ## plus a "already recorded" check.
  if typeSym.kind notin {nnkSym, nnkIdent}:
    return
  var cur = typeSym
  var guard = 0
  while guard < 64:
    inc guard
    let childName = cur.strVal
    # A standard stdlib type terminates the walk (its static chain is known).
    if childName in exnTypeTable:
      return
    # Already captured this child: its chain is recorded — stop (cycle guard).
    if childName in ctx.userExnHierarchy:
      return
    let impl =
      try: cur.getImpl
      except CatchableError: return
    if impl.kind != nnkTypeDef or impl.len < 3:
      return
    # Locate the ObjectTy (possibly wrapped in Ref/PtrTy for `ref object`).
    var objTy = impl[2]
    while objTy.kind in {nnkRefTy, nnkPtrTy} and objTy.len > 0:
      objTy = objTy[0]
    if objTy.kind != nnkObjectTy or objTy.len < 1:
      return
    # The inherit clause is an `nnkOfInherit[ <parentSym> ]` child of the
    # ObjectTy (`ObjectTy[ <pragma|Empty>, OfInherit[Sym Parent], <recList> ]`).
    # A plain `nnkEmpty` in its place means no base (effectively `of RootObj`) —
    # end of chain. We scan the children for the OfInherit rather than assuming
    # a fixed index (the pragma slot shifts positions).
    var inheritNode: NimNode = nil
    for child in objTy:
      if child.kind == nnkOfInherit:
        inheritNode = child
        break
    if inheritNode == nil or inheritNode.len < 1:
      return
    var parent = inheritNode[0]
    while parent.kind in {nnkRefTy, nnkPtrTy, nnkBracketExpr} and parent.len > 0:
      parent = parent[0]
    if parent.kind notin {nnkSym, nnkIdent}:
      return
    let parentName = parent.strVal
    ctx.userExnHierarchy[childName] = parentName
    # If the parent is a known stdlib base, the static chain takes over.
    if parentName in exnTypeTable:
      return
    cur = parent

proc freshSynth(ctx: ParseCtx, prefixWord: string): string =
  inc ctx.synthCounter
  "__sym_" & prefixWord & "_" & $ctx.synthCounter

# ---- R16-2b: detect inline float→int conversions in RHS IR trees ------------

proc rhsHasInlineDefectFork(e: IRExpr): bool =
  ## Returns true iff `e` contains any node that produces an inline raise-fork
  ## when lowered, requiring the short-circuit guard even when rhsPreamble is empty.
  ## Covers:
  ##   iekConvFloatToInt — float→int conversion may raise RangeDefect (R16-2b).
  ##   iekBinop with op in {bDiv, bMod} — division/modulo may raise DivByZeroDefect
  ##     (R16-3). Only applies to the RHS of an `and`/`or` — a div in the LHS is
  ##     evaluated unconditionally, so its raise IS reachable without guarding.
  if e == nil: return false
  case e.kind
  of iekConvFloatToInt:
    result = true
  of iekConvIntToFloat:
    result = rhsHasInlineDefectFork(e.convOperand)
  of iekMathCall:
    for a in e.mathArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekBinop:
    if e.bop in {bDiv, bMod}: return true  ## R16-3: div/mod → DivByZeroDefect guard
    result = rhsHasInlineDefectFork(e.lhs) or rhsHasInlineDefectFork(e.rhs)
  of iekUnop:
    result = rhsHasInlineDefectFork(e.operand)
  of iekField:
    result = rhsHasInlineDefectFork(e.obj)
  of iekIndex:
    result = rhsHasInlineDefectFork(e.arr) or rhsHasInlineDefectFork(e.idx)
  of iekArrayLit:
    for a in e.lelems:
      if rhsHasInlineDefectFork(a): return true
  of iekSeqLen:
    result = rhsHasInlineDefectFork(e.lenObj)
  of iekContains:
    result = rhsHasInlineDefectFork(e.container) or rhsHasInlineDefectFork(e.key)
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    result = rhsHasInlineDefectFork(e.mutRecv) or rhsHasInlineDefectFork(e.mutArg)
  of iekSeqDel:
    result = rhsHasInlineDefectFork(e.delSeq) or rhsHasInlineDefectFork(e.delIdx)
  of iekSeqInsert:
    result = rhsHasInlineDefectFork(e.insSeq) or
             rhsHasInlineDefectFork(e.insVal) or
             rhsHasInlineDefectFork(e.insIdx)
  of iekSeqPop:
    result = rhsHasInlineDefectFork(e.popSeq)
  of iekTableSet:
    result = rhsHasInlineDefectFork(e.tabRecv) or
             rhsHasInlineDefectFork(e.tabKey) or
             rhsHasInlineDefectFork(e.tabVal)
  of iekStrLen, iekStrAt, iekStrSubstr, iekStrFind, iekStrContains,
     iekStrStartsWith, iekStrEndsWith, iekStrReplace, iekStrReplaceAll,
     iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe, iekStrReplaceRe,
     iekStrBytes, iekStrConcat, iekIntToStr, iekStrToInt, iekStrUnsupported:
    for a in e.strArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekBorrowOp:
    result = rhsHasInlineDefectFork(e.borrowLhs) or
             rhsHasInlineDefectFork(e.borrowRhs)
  of iekClosureCall:
    for a in e.ccArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekSeqLit:
    for a in e.seqLitElems:
      if rhsHasInlineDefectFork(a): return true
  of iekHofCall:
    if rhsHasInlineDefectFork(e.hofSeq): return true
    if rhsHasInlineDefectFork(e.hofClosure): return true
    if e.hofInit != nil and rhsHasInlineDefectFork(e.hofInit): return true
  of iekLambda:
    discard  # lambdaBody is IRStmt; don't recurse into lambdas
  of iekIntLit, iekFloatLit, iekBoolLit, iekVar, iekStrLit,
     iekGetCurrentExn, iekGetCurrentExnMsg, iekNil:
    discard  # no sub-exprs

# ---- Forward decls -----------------------------------------------------------

proc parseExpr*(n: NimNode, preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr
proc parseStmt*(n: NimNode, ctx: ParseCtx): IRStmt
proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode,
                          callSite: NimNode = nil): string
proc bodyHashPart(calleeSym, impl: NimNode): string  ## C3 site key (fwd)

# ---- Phase 15 Cluster C (C1): closure / lambda parsing ----------------------

proc collectBoundLocals(n: NimNode, into: var HashSet[string]) =
  ## Phase 15 C1. Collect names DEFINED inside a lambda body (the LHS of any
  ## `let`/`var`/`for`/nested-proc binding). These are NOT free variables —
  ## a reference to one is a body-local, not a capture from the enclosing scope.
  if n == nil: return
  case n.kind
  of nnkLetSection, nnkVarSection, nnkConstSection:
    for d in n:
      if d.kind == nnkIdentDefs or d.kind == nnkVarTuple:
        for i in 0 ..< d.len - 2:
          let nm = d[i]
          if nm.kind in {nnkSym, nnkIdent}: into.incl nm.strVal
  of nnkForStmt:
    for i in 0 ..< n.len - 2:
      if n[i].kind in {nnkSym, nnkIdent}: into.incl n[i].strVal
  else: discard
  for c in n: collectBoundLocals(c, into)

proc collectFreeVarRefs(n: NimNode, bound: HashSet[string],
                        order: var seq[string], seen: var HashSet[string]) =
  ## Phase 15 C1. Enumerate the FREE VARIABLES of a lambda body: every `nnkSym`
  ## reference whose symbol is a runtime VALUE binding (`nskParam`/`nskLet`/
  ## `nskVar`/`nskForVar`) and that is NOT bound inside the lambda (`bound`
  ## holds the lambda's own params ++ its body-locals). This excludes top-level
  ## procs/types/consts/enums (different `symKind`) — those are not captured.
  ## First-seen source order is preserved (deterministic capture list / key).
  if n == nil: return
  if n.kind == nnkSym:
    if symKind(n) in {nskParam, nskLet, nskVar, nskForVar}:
      let nm = n.strVal
      if nm notin bound and nm notin seen:
        seen.incl nm
        order.add nm
    return
  for c in n: collectFreeVarRefs(c, bound, order, seen)

proc lambdaBodyHash(lam: NimNode): string =
  ## Phase 15 C1 (ADR-0009 D3, reconciliation §F-C). `symBodyHash` is a
  ## `std/macros` builtin that hashes the SEMANTIC body of a *proc SYMBOL*; a
  ## lambda in expression position is an `nnkLambda`/`nnkProcDef` NODE with no
  ## name symbol, so `symBodyHash` does NOT apply to it directly (verified C1).
  ## We therefore use the ADR-0008 D2 lineInfo-style fallback: the body node's
  ## `file:line:col`, which is formatting-tolerant ENOUGH for C1's structural
  ## keying (declOrder disambiguates identical-position lambdas; D8's concrete
  ## param types disambiguate instantiations via the canonical key). C2a may
  ## refine if a stronger semantic hash proves necessary.
  let li = lam.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

proc parseRoutineToLambda(n: NimNode, ctx: ParseCtx,
                          site: tuple[siteHash: int64, declOrder: int],
                          forceNoCaptures = false): IRExpr =
  ## Phase 15 Cluster C. Shared core: turn a routine-def node (`nnkLambda` /
  ## expression-position `nnkProcDef`/`nnkFuncDef`, OR a top-level proc's
  ## `getImpl`) into an `iekLambda` under the supplied site key. Params/return
  ## come from the monomorphized formal-params (D8 — the typed AST is already at
  ## concrete types here). Free variables are enumerated by scope-stack diff
  ## (params ++ body-locals subtracted from the body's value-symbol references);
  ## `forceNoCaptures` short-circuits that to `@[]` for the C3 top-level-proc
  ## case (a module-scope proc has no enclosing runtime scope to capture from).
  ## PRAGMAS (`{.raises, gcsafe.}` etc.) are dropped — semchecker metadata only.
  let formal = n[3]
  formal.expectKind nnkFormalParams
  var params: seq[IRParam]
  var bound: HashSet[string]
  for i in 1 ..< formal.len:
    let id = formal[i]
    if id.kind != nnkIdentDefs: continue
    let tyNode = id[id.len - 2]
    let cls = classifyType(tyNode)
    let isVar = tyNode.kind == nnkVarTy
    for j in 0 ..< id.len - 2:
      params.add IRParam(name: id[j].strVal, ty: cls.ty,
                         rangeLo: cls.range.lo, rangeHi: cls.range.hi,
                         hasRange: cls.range.hasRange, isVar: isVar)
      bound.incl id[j].strVal
  var retTy = tBool()
  if formal[0].kind != nnkEmpty:
    retTy = classifyType(formal[0]).ty
  # The body of a routine def (lambda/proc/func) is at the fixed routine-body
  # index (`body(n)`); n.len-1 can be a trailing synthetic `result` symbol.
  let bodyNode = body(n)
  # Free variables = value-symbol refs not bound by the lambda. A top-level proc
  # (C3) has none by construction; skip the scan.
  var captures: seq[string]
  if not forceNoCaptures:
    # Body-local definitions are also bound (not captured).
    collectBoundLocals(bodyNode, bound)
    var seen: HashSet[string]
    collectFreeVarRefs(bodyNode, bound, captures, seen)
  let bodyIR = parseStmt(bodyNode, ctx)
  mkLambda(site.siteHash, site.declOrder, params, bodyIR, captures, retTy)

proc parseLambda(n: NimNode, ctx: ParseCtx): IRExpr =
  ## Phase 15 Cluster C (C1, ADR-0009). Parse an `nnkLambda` / expression-
  ## position `nnkProcDef` into an `iekLambda` keyed by `(lineInfo-hash,
  ## declOrder)` (D3 — a nameless lambda has no symbol for `symBodyHash`).
  let site = (siteHash: int64(hash(lambdaBodyHash(n))), declOrder: ctx.lambdaCounter)
  inc ctx.lambdaCounter
  parseRoutineToLambda(n, ctx, site)

proc parseProcAsValue(procSym, impl: NimNode, ctx: ParseCtx): IRExpr =
  ## Phase 15 C3 (ADR-0009, reconciliation §F-C). A TOP-LEVEL proc referenced in
  ## VALUE position (`let g = double`) → an `iekLambda` with `lambdaCaptures =
  ## @[]` (a unit-env closure: a module-scope proc has no free variables). The
  ## body comes from the proc's `getImpl` (`impl`, an `nnkProcDef`). The site key
  ## uses `symBodyHash` of the proc SYMBOL (which — unlike C1's nameless lambda —
  ## DOES apply: a top-level proc has a symbol), with the ADR-0008 D2 lineInfo
  ## fallback (`bodyHashPart`); `declOrder = 0` for a stable top-level name (D3).
  ## Calling it dispatches through the existing C2b `iekClosureCall` path; the
  ## walker materializes the zero-field unit-env via the C2a empty-capture path.
  let site = (siteHash: int64(hash(bodyHashPart(procSym, impl))), declOrder: 0)
  parseRoutineToLambda(impl, ctx, site, forceNoCaptures = true)

# ---- Binop / unop helpers ----------------------------------------------------

proc binopForInfix(op: string): IRBinop =
  case op
  of "+":   bAdd
  of "-":   bSub
  of "*":   bMul
  of "div": bDiv
  of "/":   bDiv   ## Phase 15 F3: float division (operands are float in typed AST)
  of "mod": bMod
  of "==":  bEq
  of "!=":  bNe
  of "<":   bLt
  of "<=":  bLe
  of ">":   bGt
  of ">=":  bGe
  of "and": bAnd
  of "or":  bOr
  of "xor": bXor
  of "shl": bShl
  of "shr": bShr
  else:
    error("symex: unsupported infix operator `" & op & "`")

proc hasSymexOpaquePragma(calleeSym: NimNode): bool =
  ## Phase 9 — the user-facing extension hook. A proc marked with
  ## `{.symexOpaque.}` is treated by symex as a black box: the
  ## walker does not enter its body, the return value becomes a
  ## fresh symbolic of the proc's return type, and the surviving
  ## path is marked uncertain (same machinery as the built-in
  ## OpaqueEffectfulProcs catalog for `echo`/`writeFile`/etc.).
  ##
  ## Use this to bring user-defined IO procs, FFI wrappers, or
  ## intentionally-uninterpreted primitives under symex without
  ## hand-extending the registry.
  if calleeSym.kind != nnkSym: return false
  let impl = calleeSym.getImpl
  if impl.kind != nnkProcDef: return false
  let prag = impl.pragma
  if prag.kind != nnkPragma: return false
  for p in prag:
    let name =
      case p.kind
      of nnkIdent, nnkSym: p.strVal
      of nnkExprColonExpr, nnkCall:
        if p[0].kind in {nnkIdent, nnkSym}: p[0].strVal else: ""
      else: ""
    if name == "symexOpaque":
      return true
  false

proc hasBorrowPragma(impl: NimNode): bool =
  ## Phase 15 G5. True when `impl` (an `nnkProcDef`) carries a `{.borrow.}`
  ## pragma — an `nnkPragma` child containing `ident"borrow"`. The borrow
  ## pragma's typed form is a bare `nnkIdent "borrow"` (confirmed by AST dump).
  if impl.kind != nnkProcDef: return false
  let prag = impl.pragma
  if prag.kind != nnkPragma: return false
  for p in prag:
    let name =
      case p.kind
      of nnkIdent, nnkSym: p.strVal
      of nnkExprColonExpr, nnkCall:
        if p[0].kind in {nnkIdent, nnkSym}: p[0].strVal else: ""
      else: ""
    if name == "borrow":
      return true
  false

type BorrowInfo = object
  ## Phase 15 G5. Classification of an operator symbol as a `{.borrow.}` shim.
  isBorrow*:        bool
  returnsDistinct*: bool     ## true → arithmetic (re-box result as distinct);
                             ## false → comparison (raw bool result).
  distinctName*:    string   ## the distinct return type to re-box into.

proc borrowInfoFor(calleeSym: NimNode): BorrowInfo =
  ## Phase 15 G5. Classify an operator symbol: is it a `{.borrow.}` proc, and
  ## does it return the distinct type (arithmetic) or bool (comparison)? A
  ## borrow proc has NO real body — its `getImpl` body is a bare `Sym` (the base
  ## operator) — so it must NOT be body-parsed; the call routes through the
  ## borrow path instead. The return type is `impl[3][0]` (the FormalParams'
  ## return node): an `itDistinct` classification → arithmetic re-box; anything
  ## else (itBool) → comparison.
  if calleeSym.kind != nnkSym: return BorrowInfo(isBorrow: false)
  let impl = calleeSym.getImpl
  if impl.kind != nnkProcDef or not hasBorrowPragma(impl):
    return BorrowInfo(isBorrow: false)
  let formal = impl[3]
  if formal.kind != nnkFormalParams or formal[0].kind == nnkEmpty:
    # A borrow with no return type would be a void operator — not a borrow we
    # model. Treat as non-borrow (falls through to the normal path).
    return BorrowInfo(isBorrow: false)
  let retCls = classifyType(formal[0])
  if retCls.ty.kind == itDistinct:
    BorrowInfo(isBorrow: true, returnsDistinct: true,
               distinctName: retCls.ty.distinctName)
  else:
    BorrowInfo(isBorrow: true, returnsDistinct: false, distinctName: "")

proc isMarkerCall(n: NimNode, name: string): bool =
  if n.kind != nnkCall:
    return false
  let callee = n[0]
  case callee.kind
  of nnkIdent, nnkSym:
    callee.strVal == name
  else:
    false

proc isMarkerCall(n: NimNode): bool =
  isMarkerCall(n, "symexTarget") or
  isMarkerCall(n, "symexAssert") or
  isMarkerCall(n, "symexAssume")

proc isNewCall(n: NimNode): bool =
  ## Phase 15 R2 (ADR-0010). True iff `n` is a `new T` allocation expression —
  ## either the command form `new int` (`nnkCommand[Sym "new", T]`) or the call
  ## form `new(int)` (`nnkCall[Sym "new", T]`). The `new` magic returns a fresh
  ## `ref T`; the let-section parser lowers such an RHS to an `isNew` stmt
  ## (binding the let-name to the fresh `Ref_T` const) rather than `parseExpr`,
  ## which has no expression-context model for allocation.
  if n.isNil: return false
  if n.kind notin {nnkCall, nnkCommand} or n.len < 1: return false
  let head = n[0]
  let nm =
    if head.kind in {nnkOpenSymChoice, nnkClosedSymChoice} and head.len > 0:
      head[0].strVal
    elif head.kind in {nnkSym, nnkIdent}:
      head.strVal
    else: return false
  nm == "new"

proc callsFailedAssertImpl(n: NimNode): bool =
  ## Phase 15 E6. A raw `assert cond, msg` / `doAssert cond` lowers (after
  ## semcheck) to a `Call` to the system template `failedAssertImpl` in the
  ## then-body of an `if not (cond): …`. Recursively detect such a call so the
  ## enclosing `if` can be recognised as an assert expansion.
  if n.isNil: return false
  if n.kind in {nnkCall, nnkCommand} and n.len >= 1 and
     n[0].kind in {nnkSym, nnkIdent, nnkOpenSymChoice, nnkClosedSymChoice}:
    let head = n[0]
    let nm =
      if head.kind in {nnkOpenSymChoice, nnkClosedSymChoice} and head.len > 0:
        head[0].strVal
      else: head.strVal
    if nm == "failedAssertImpl": return true
  for c in n:
    if callsFailedAssertImpl(c): return true
  false

proc findAssertFailsCond(n: NimNode): NimNode =
  ## Phase 15 E6. Scan a (typed) sub-AST for a raw-`assert` expansion and return
  ## the Nim node for the condition under which the assert FAILS (i.e. the
  ## `if`-arm condition `not (cond)` that guards the `failedAssertImpl` call) —
  ## or `nil` if `n` contains no assert. The walker lowers this to an implicit
  ## `raise AssertionDefect` guarded by that condition. (A SUT's explicit
  ## `symexAssert(...)` marker is handled separately and never reaches here.)
  if n.isNil: return nil
  if n.kind in {nnkIfStmt, nnkIfExpr}:
    for arm in n:
      if arm.kind in {nnkElifBranch, nnkElifExpr} and arm.len == 2 and
         callsFailedAssertImpl(arm[1]):
        return arm[0]
  for c in n:
    let r = findAssertFailsCond(c)
    if r != nil: return r
  nil

# ---- Expression parser -------------------------------------------------------

const fltTyNames = ["float", "float32", "float64"]
const intTyNames = ["int", "int8", "int16", "int32", "int64",
                    "uint", "uint8", "uint16", "uint32", "uint64"]

proc valueTypeName(node: NimNode): string =
  ## Phase 15 F5: resolved type name of a VALUE node (operand), via getTypeInst.
  ## (A bare `nnkSym` value resolves to its declared name, not its type, so we
  ## must always go through getTypeInst here.)
  let t = node.getTypeInst
  if t.kind in {nnkSym, nnkIdent}: t.strVal else: t.repr

proc typeNodeName(node: NimNode): string =
  ## Phase 15 F5: name of a TYPE node (the conversion target `n[0]`).
  if node.kind in {nnkSym, nnkIdent}: node.strVal else: node.repr

proc isStdMathProc(calleeSym: NimNode): bool =
  ## Phase 15 F6: is `calleeSym` a proc defined in the Nim standard library
  ## (`lib/pure/math` or `lib/system`)? Used to route otherwise-unmodeled
  ## float-receiver calls (e.g. `ln`, `sin`) to `iekMathCall` so the runtime
  ## emits `feUnsupportedOp`, instead of `ensureProcRegistered` raising a
  ## compile-time `getImpl` failure. Uses the defining file path of the
  ## symbol's implementation; user procs live outside the stdlib tree.
  if calleeSym.kind != nnkSym:
    return false
  let impl = calleeSym.getImpl
  if impl.kind notin {nnkProcDef, nnkFuncDef}:
    return false
  let fn = impl.lineInfoObj.filename.replace('\\', '/')
  result = ("/pure/math" in fn) or ("/lib/system" in fn) or
           fn.endsWith("system.nim") or ("/system/" in fn)

proc parseExpr*(n: NimNode, preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  case n.kind
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    mkIntLit(n.intVal)
  of nnkUIntLit .. nnkUInt64Lit:
    mkIntLit(n.intVal)
  of nnkCharLit:
    mkIntLit(n.intVal)   ## Phase 15 Z3c: char literal -> its ordinal (char = uint8)
  of nnkFloatLit, nnkFloat32Lit, nnkFloat64Lit:
    mkFloatLit(n.floatVal, if n.kind == nnkFloat32Lit: 32 else: 64)   ## Phase 15 F2
  of nnkIdent, nnkSym:
    let s = n.strVal
    if s == "true": mkBoolLit(true)
    elif s == "false": mkBoolLit(false)
    else:
      # #141: enum value — `getType` of the Sym yields nnkEnumTy
      # directly. Find the value's ord by scanning the enum body.
      if n.kind == nnkSym:
        let ty = n.getType
        var enumBody: NimNode = nil
        if ty.kind == nnkEnumTy: enumBody = ty
        elif ty.kind == nnkSym:
          let impl = ty.getImpl
          if impl.kind == nnkTypeDef and impl.len >= 3 and
             impl[2].kind == nnkEnumTy:
            enumBody = impl[2]
        if enumBody != nil:
          for i in 1 ..< enumBody.len:
            let field = enumBody[i]
            let fieldSym = if field.kind == nnkSym: field
                           elif field.kind == nnkEnumFieldDef: field[0]
                           else: continue
            if fieldSym.strVal == s:
              return mkIntLit(int64(i - 1))
        # Phase 15 C3 (reconciliation §F-C). A TOP-LEVEL proc referenced in
        # VALUE position (`let g = double`, or `double` as a proc-valued ARG) →
        # an `iekLambda` with empty captures (a unit-env closure). This branch
        # is the bare-`nnkSym` EXPRESSION path ONLY: a proc in CALLEE position is
        # `n[0]` of an `nnkCall` (parsed structurally, never via parseExpr) and a
        # call THROUGH a proc-valued local (`g(n)`) is the C2b `earlyClosure
        # CallDetect` — so neither reaches here. A `nnkParam`-kinded proc-valued
        # PARAMETER (symKind == nskParam) also does NOT match `nskProc`, so it
        # stays the proc-valued-param svClosure path (C2b), not C3. We require a
        # resolvable `nnkProcDef` impl (a real module-scope proc body to inline).
        if symKind(n) == nskProc:
          let impl = n.getImpl
          if impl.kind == nnkProcDef:
            return parseProcAsValue(n, impl, ctx)
      mkVar(s)
  of nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    mkStrLit(n.strVal)
  of nnkPar, nnkStmtListExpr:
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkLambda:
    # Phase 15 Cluster C (C1, ADR-0009). A lambda in expression position →
    # iekLambda (walker-stubbed `ceNotImplemented` in C1).
    parseLambda(n, ctx)
  of nnkProcDef, nnkFuncDef:
    # Phase 15 C1. A `proc(...) = ...` / `func(...) = ...` value lowered to an
    # expression-position proc/func def (vs the nnkLambda surface form) →
    # iekLambda. (ADR-0009: `func` is treated identically to `proc` here.)
    parseLambda(n, ctx)
  of nnkIteratorDef:
    # Phase 15 C1 (ADR-0009 Deferred). A closure iterator
    # (`iterator(): T {.closure.}`) in expression position is OUT OF SCOPE for
    # Cluster C → emit an iekLambda carrying an iterator marker so the walker
    # stub fires a classified `ceNotImplemented` (Invariant 3 — not a crash).
    # The detail string is surfaced at walk time via the stub message.
    var captures: seq[string]
    var seen: HashSet[string]
    var bound: HashSet[string]
    let bodyNode = body(n)
    collectBoundLocals(bodyNode, bound)
    collectFreeVarRefs(bodyNode, bound, captures, seen)
    let site = (siteHash: int64(hash("closure-iterator:" & lambdaBodyHash(n))),
                declOrder: ctx.lambdaCounter)
    inc ctx.lambdaCounter
    # Body is replaced with a sentinel unsupported stmt (closure iterators have
    # no symex-representable body); the walker never descends it (it stubs the
    # whole iekLambda first).
    mkLambda(site.siteHash, site.declOrder, @[],
             mkUnsupported("closure iterators not yet supported"),
             captures, tBool())
  of nnkConv:
    # Phase 15 F5: detect int<->float conversions; other explicit conversions
    # (int widening, etc.) fall through to pass-through unwrapping.
    let operand = n[n.len - 1]
    let tgt = typeNodeName(n[0])
    let src = valueTypeName(operand)
    if tgt in fltTyNames and src in intTyNames:
      mkConvIntToFloat(parseExpr(operand, preamble, ctx), if tgt == "float32": 32 else: 64)
    elif tgt in intTyNames and src in fltTyNames:
      mkConvFloatToInt(parseExpr(operand, preamble, ctx), if tgt == "int32": 32 else: 64)
    else:
      parseExpr(operand, preamble, ctx)
  of nnkHiddenStdConv, nnkHiddenAddr:
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkDerefExpr, nnkHiddenDeref:
    # Phase 15 R1 (ADR-0010). `p[]` — a ref/ptr dereference. The typed AST emits
    # an explicit `nnkDerefExpr` (or a compiler-inserted `nnkHiddenDeref`) whose
    # operand `n[0]` is the ref/ptr expression. When that operand classifies as a
    # genuine `ref T`/`ptr T`, A-normalise into an `isDeref` stmt (the walker
    # lowers it to a GROUND `select(path.heaps[typeId], p)`); a fresh let binds
    # the dereffed value. (Before R1 a `nnkHiddenDeref` was a no-op unwrap because
    # ref/ptr were unwrapped to the pointee at classify time; Cluster R restores
    # the real indirection, so we must materialise the heap read here.)
    # Phase 15 R8b (ADR-0010). For a `var ref T` / `var ptr T` PARAMETER, the
    # deref `p[]` presents as `nnkDerefExpr(nnkHiddenDeref(sym))` — the inner
    # `nnkHiddenDeref` is the lvalue (`var`-ness) indirection, NOT a real ref
    # deref. `classifyType` of that hidden-deref unwraps to the POINTEE (int),
    # which would defeat the itRef detection below and route to the value-unwrap
    # `else` arm (yielding a bogus deref-temp). Strip that ONE var-level
    # hidden-deref so `operand` is the ref/ptr symbol whose classify is itRef.
    var operand = n[0]
    if operand.kind == nnkHiddenDeref and operand.len == 1 and
       classifyType(operand[0]).ty.kind in {itRef, itPtr}:
      operand = operand[0]
    let opCls = classifyType(operand)
    case opCls.ty.kind
    of itRef, itPtr:
      let isPtr = opCls.ty.kind == itPtr
      let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
      let ptrIR = parseExpr(operand, preamble, ctx)
      let synth = freshSynth(ctx, "deref")
      let stmt = if isPtr: mkPtrDeref(synth, ptrIR, pointeeTy)
                 else:     mkDeref(synth, ptrIR, pointeeTy)
      preamble.add stmt
      mkVar(synth)
    else:
      # Not a ref/ptr operand (e.g. a compiler-inserted hidden deref over an
      # already-unwrapped value): preserve the pre-R unwrap behaviour.
      parseExpr(n[n.len - 1], preamble, ctx)
  of nnkCheckedFieldExpr:
    # `s.field` on a variant object — the runtime check is over the
    # discriminator; symex just lowers the inner dot-expr.
    parseExpr(n[0], preamble, ctx)
  of nnkInfix:
    # Phase 15 S8: `&` string concatenation. Intercept BEFORE binopForInfix
    # (which has no `&` case and would error). Only fire when BOTH operands
    # classify as `itString` — `s & t`, `s & "lit"`, `"lit" & s`. This guard
    # leaves the seq-concat / any-other-type `&` path untouched (those operands
    # are not itString, so they fall through to binopForInfix as before).
    # Chained `a & b & c` is left-associative: the typed AST nests it as
    # `(a & b) & c`, so each `&` is its own binary node and recursion on the
    # operands handles the chain naturally.
    if n[0].strVal == "&" and
       classifyType(n[1]).ty.kind == itString and
       classifyType(n[2]).ty.kind == itString:
      let lhs = parseExpr(n[1], preamble, ctx)
      let rhs = parseExpr(n[2], preamble, ctx)
      return mkStrOp(iekStrConcat, "&", @[lhs, rhs])
    # Phase 15 G5: a `{.borrow.}` operator on a `distinct T`. In the typed AST
    # `m1 + m2` (with `proc \`+\`(a,b: Meters): Meters {.borrow.}`) is an
    # `nnkInfix` whose `n[0]` is the borrow proc SYMBOL. Detect it and route
    # through the borrow path (eject operands to base, apply base op, re-box
    # arithmetic) rather than `binopForInfix` + `mkBinop`. The base operator is
    # `binopForInfix(operatorName)`. A borrow proc has no real body, so it must
    # NOT be body-parsed.
    block borrowIntercept:
      if n[0].kind == nnkSym:
        let bi = borrowInfoFor(n[0])
        if bi.isBorrow:
          let bop = binopForInfix(n[0].strVal)
          let l = parseExpr(n[1], preamble, ctx)
          let r = parseExpr(n[2], preamble, ctx)
          return mkBorrowOp(bop, l, r, bi.returnsDistinct, bi.distinctName)
    # Phase 15 R5 (Cluster R). A `nil` ref/ptr comparison `p == nil` / `nil == p`
    # (`==`/`!=`). One operand is an `nnkNilLit`; the OTHER is the ref/ptr whose
    # type supplies the pointee for the per-sort `nilConst`. Lower the nil side to
    # an `iekNil(pointee)` (built from the non-nil operand's classified `itRef`/
    # `itPtr` type) so the walker's `refEq` decides it as a ground `Ref_T`
    # equality. Intercept BEFORE `binopForInfix`+`parseExpr`, which has no
    # nnkNilLit arm.
    # Phase 16 D1a (CR-22 fix): Two-level classifier for nil comparisons so that
    # BOTH `p: ref int` / `p: ref Point` (inline ref params, itRef from
    # classifyType) AND `n.next` (a DotExpr that returns a ref-typed field value —
    # classifyType UNWRAPS `Node = ref object` to itTuple) are handled correctly.
    #
    # Level 1: `classifyType(refNode)` — the original classifier. Correctly returns
    # itRef/itPtr for INLINE ref params (`p: ref int`, `q: ref Point`). For a
    # NAMED `ref object` type (e.g. `type Node = ref object`), `classifyType`
    # UNWRAPS the alias to the object body, returning itTuple — not itRef.
    #
    # Level 2 (fallback, NON-bare-symbol only): `classifyFieldType(refNode.getTypeInst)`
    # — the ref-aware field classifier. Recognizes named `ref object` aliases and
    # returns itRef. Applied ONLY when the expression is NOT a bare symbol (i.e. a
    # derived expression like `n.next`). A bare symbol `n: Node` is VALUE-MODELLED
    # by the engine (classifyType returns itTuple deliberately — the walker allocates
    # it as svTuple, not svRef), so a nil comparison on a bare value-modelled param
    # is unsupported and must NOT generate a nil IR (it would crash at walk time when
    # comparing svTuple ≠ svRef). Non-symbol derived expressions (`n.next`, a
    # field-split heap lookup) are always svRef-typed and ARE safely comparable to nil.
    if n[0].strVal in ["==", "!="] and
       (n[1].kind == nnkNilLit or n[2].kind == nnkNilLit):
      let op = binopForInfix(n[0].strVal)
      let nilIsLhs = n[1].kind == nnkNilLit
      let refNode  = if nilIsLhs: n[2] else: n[1]
      # Level 1: classifyType — correct for inline ref params; unwraps named ref objects.
      var refCls = classifyType(refNode)
      # Level 2 fallback: only for derived (non-bare-symbol) expressions.
      # A bare nnkSym/nnkIdent that classifies as itTuple is value-modelled — skip.
      if refCls.ty.kind notin {itRef, itPtr} and
         refNode.kind notin {nnkSym, nnkIdent}:
        refCls = classifyFieldType(refNode.getTypeInst)
      if refCls.ty.kind in {itRef, itPtr}:
        let refIR = parseExpr(refNode, preamble, ctx)
        let nilIR = mkNil(refCls.ty)
        return (if nilIsLhs: mkBinop(op, nilIR, refIR)
                else:        mkBinop(op, refIR, nilIR))
    let op = binopForInfix(n[0].strVal)
    # Phase 16 D1c: model `and`/`or` short-circuit evaluation.
    # The LHS is always evaluated (hoisted into the outer preamble as usual).
    # The RHS is parsed into a SEPARATE scratch preamble; if that preamble is
    # non-empty (i.e. it contains defect-fork stmts — isVariantField, isIndex,
    # isDeref, …), we wrap the whole RHS block in a boolean-temp guard so the
    # RHS preamble only executes when the LHS value demands it:
    #   and: guard  = `if __sc:   …rhsPreamble…; __sc = rhsIR`
    #   or:  guard  = `if not __sc: …rhsPreamble…; __sc = rhsIR`
    # Fast path (rhsPreamble empty): zero IR overhead — emits the same
    # `mkBinop(bAnd/bOr, lhsIR, rhsIR)` as before D1c.
    if op in {bAnd, bOr}:
      let lhsIR = parseExpr(n[1], preamble, ctx)
      var rhsPreamble: seq[IRStmt]
      let rhsIR = parseExpr(n[2], rhsPreamble, ctx)
      if rhsPreamble.len == 0 and not rhsHasInlineDefectFork(rhsIR):
        # Fast path: no hoisted stmts in RHS AND no inline defect-fork operation.
        # R16-2b: iekConvFloatToInt is lowered inline — rhsPreamble.len==0 alone
        # is insufficient. R16-3: iekBinop(bDiv/bMod) also lowers inline and must
        # force the guarded path so the b==0 fork only fires under the LHS guard.
        mkBinop(op, lhsIR, rhsIR)
      else:
        # Guarded path: bind LHS result into a fresh bool temp, then
        # conditionally evaluate the RHS preamble + assign back.
        let sc = freshSynth(ctx, "sc")
        preamble.add mkLet(sc, tBool(), lhsIR)
        let scGuard =
          if op == bAnd:
            mkVar(sc)                      # and: run RHS only when LHS is true
          else:
            mkUnop(uNot, mkVar(sc))        # or:  run RHS only when LHS is false
        let rhsBody = mkBlock(rhsPreamble & @[mkAssign(sc, rhsIR)])
        preamble.add mkIf(@[mkBranch(scGuard, rhsBody)], nil)
        mkVar(sc)
    else:
      let l = parseExpr(n[1], preamble, ctx)
      let r = parseExpr(n[2], preamble, ctx)
      mkBinop(op, l, r)
  of nnkPrefix:
    let op = n[0].strVal
    case op
    of "not": mkUnop(uNot, parseExpr(n[1], preamble, ctx))
    of "$":
      # Phase 15 S10a: `$n` (system.`$`) on an `itInt` operand → `iekIntToStr`
      # (Z3 `Z3_mk_int_to_str`). In the typed AST `$n` is an `nnkPrefix` (NOT an
      # nnkCall), so it is intercepted here. Only an int operand routes to the
      # conversion — `$float`/`$bool`/etc. are deferred (S10b / future).
      let opndTy = classifyType(n[1]).ty.kind
      if opndTy == itInt:
        mkStrOp(iekIntToStr, "$", @[parseExpr(n[1], preamble, ctx)])
      elif opndTy in {itFloat32, itFloat64}:
        # Phase 15 S10b: Z3 String theory has NO float↔string conversion, so
        # `$f` (a float stringified) routes to a classified `seUnsupportedStringOp`
        # → `sxUnknown` (reusing the S9 `iekStrUnsupported` mechanism with opName
        # "$float"; Invariant 3 — never a crash/silent UNSAT). The operand is
        # dropped (the residual `lower` arm raises the classified error).
        mkStrOp(iekStrUnsupported, "$float", @[])
      else:
        error("symex: `$` is only modeled for int operands (S10a); `$" &
              $classifyType(n[1]).ty & "` is deferred", n)
    of "-":
      # Phase 15 F2: fold `-<float-literal>` into a negated float literal at
      # parse time (covers -0.0 / -Inf) so the walker sees a literal, not uNeg.
      if n[1].kind in {nnkFloatLit, nnkFloat32Lit, nnkFloat64Lit}:
        mkFloatLit(-n[1].floatVal, if n[1].kind == nnkFloat32Lit: 32 else: 64)
      else:
        mkUnop(uNeg, parseExpr(n[1], preamble, ctx))
    of "@":
      # Phase 15 C4: a seq literal `@[a, b, c]` (incl. empty `@[]`). The typed
      # form is `Prefix(Sym "@", Bracket)`. Lower to a CONCRETE-length `svSeq`
      # so a downstream HOF can take the bounded inline path. The element type
      # comes from the whole expression's `seq[T]` type (works for `@[]` too).
      if n[1].kind != nnkBracket:
        error("symex: unsupported `@` operand (expected a seq literal `@[..]`)", n)
      var elems: seq[IRExpr]
      for c in n[1]: elems.add parseExpr(c, preamble, ctx)
      # Recover the element IRType. Prefer the seq's own type; fall back to the
      # first element's classified type for a non-empty literal.
      let seqCls = classifyType(n)
      if seqCls.ty.kind != itSeq and n[1].len == 0:
        error("symex: cannot infer element type of empty `@[]`", n)
      let elemTy = if seqCls.ty.kind == itSeq: seqCls.ty.seqElemTy
                   else: classifyType(n[1][0]).ty
      mkSeqLit(elems, elemTy)
    else:
      error("symex: unsupported prefix operator `" & op & "`", n)
  of nnkBracket:
    # Static array literal `[a, b, c]`. The element type comes from
    # the first element; uniform homogeneity is enforced by Nim.
    var elems: seq[IRExpr]
    for c in n: elems.add parseExpr(c, preamble, ctx)
    let elemCls = classifyType(n[0])
    mkArrayLit(elems, elemCls.ty)
  of nnkBracketExpr:
    # Tuple positional access (`t[0]`) or array index (`arr[i]`).
    # Decide via the LHS's classified type.
    let lhsCls = classifyType(n[0])
    let objIR = parseExpr(n[0], preamble, ctx)
    case lhsCls.ty.kind
    of itTuple:
      # Index must be a static int literal at the AST level.
      let ixNode = n[1]
      if ixNode.kind notin {nnkIntLit, nnkInt8Lit, nnkInt16Lit,
                             nnkInt32Lit, nnkInt64Lit}:
        error("symex (Phase 4): tuple index must be a literal", ixNode)
      let ix = int(ixNode.intVal)
      let fname = if lhsCls.ty.fieldNames.len > ix:
                    lhsCls.ty.fieldNames[ix]
                  else: ""
      mkField(objIR, ix, fname)
    of itArray:
      let idxIR = parseExpr(n[1], preamble, ctx)
      let synth = freshSynth(ctx, "idx")
      preamble.add mkIndexStmt(synth, objIR, idxIR, lhsCls.ty.elemTy)
      mkVar(synth)
    of itSeq:
      # `s[i]` on a seq — same A-normalised isIndex stmt; the runtime
      # walker dispatches on the receiver's SVKind.
      let idxIR = parseExpr(n[1], preamble, ctx)
      let synth = freshSynth(ctx, "idx")
      preamble.add mkIndexStmt(synth, objIR, idxIR, lhsCls.ty.seqElemTy)
      mkVar(synth)
    of itString:
      # Phase 15 S3. `s[i]` (index read) / `s[a..b]` (slice) in bracket-expr
      # form. The slice index is an `nnkInfix(.., a, b)` / `nnkInfix(..<, a, b)`;
      # everything else is a single-byte index. Mirrors the `[]`-call handling
      # in the string-call guard (typed AST emits either shape depending on
      # context). Byte-faithful (ADR-0006): position == Nim byte index.
      let idxNode = n[1]
      if idxNode.kind == nnkInfix and idxNode.len == 3 and
         idxNode[0].kind in {nnkSym, nnkIdent} and
         idxNode[0].strVal in ["..", "..<"]:
        let loIR = parseExpr(idxNode[1], preamble, ctx)
        var hiIR = parseExpr(idxNode[2], preamble, ctx)
        if idxNode[0].strVal == "..<":
          hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
        mkStrOp(iekStrSubstr, "[]", @[objIR, loIR, hiIR])
      else:
        let idxIR = parseExpr(idxNode, preamble, ctx)
        mkStrOp(iekStrAt, "[]", @[objIR, idxIR])
    else:
      error(&"symex: `[]` on unsupported type {lhsCls.ty}", n)
  of nnkDotExpr:
    # Phase 15 R6 (ADR-0010). `p.field` field READ through a `ref object` /
    # `ptr object`. The typed AST is `nnkDotExpr(nnkHiddenDeref(p), field)` (or
    # an explicit `nnkDerefExpr`). When the dereffed operand classifies as a
    # genuine `ref T` / `ptr T` whose pointee is an OBJECT (`itTuple`), lower to a
    # FIELD deref: `select(heap_<objTid>__<field>, p)` over the field-split heap.
    # This MUST run before the `classifyType(n[0])`-based tuple/variant routing
    # below (which would classify the hidden-deref's tuple value and lose the
    # ref address). Inherited fields fall out for free — the field-split heap is
    # keyed by field NAME (unique across the flat layout), and the field TYPE
    # comes from `classifyType(n)` on the whole access node (resolves base + own
    # fields), so no flat-offset arithmetic is needed.
    if n[0].kind in {nnkHiddenDeref, nnkDerefExpr} and n[0].len >= 1:
      let operand = n[0][0]
      var opCls = classifyType(operand)
      # Phase 15 R9 (ADR-0010). RECURSIVE ref-object field access. When the
      # operand is a DERIVED ref-valued expression (a nested `n.next` returning a
      # `Node` ref — NOT a bare top-level param sym), `classifyType` UNWRAPS the
      # named `ref object` to its value (path 2, preserved so a value-modelled ref
      # PARAM like `rectify_refs`'s `c: Counter` is NOT regressed). But the value
      # here IS an `svRef` (the recursive `next` field's heap address), so we must
      # route the deeper `.field` through the field-split HEAP. Re-classify a
      # NON-symbol operand via `classifyFieldType` (the ref-aware field classifier)
      # to recover the `itRef`/`itPtr`. A bare param sym keeps the value-unwrap.
      if opCls.ty.kind notin {itRef, itPtr} and operand.kind notin {nnkSym, nnkIdent}:
        let fieldCls = classifyFieldType(operand)
        if fieldCls.ty.kind in {itRef, itPtr}:
          opCls = fieldCls
      if opCls.ty.kind in {itRef, itPtr}:
        let isPtr = opCls.ty.kind == itPtr
        let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
        # `itTuple` → field-split heap deref. `itVariant`/`itMultiVariant` →
        # routed through the SAME field-deref IR (the field type is still
        # well-defined), but the WALKER detects the variant `dObjTy` and raises
        # the classified `heRefVariantUnsupported` (Feas-MED-4 / M17 negative DoD)
        # — a field-split heap has no flat positional layout to split a variant
        # on, so it is honestly out of scope (sxUnknown, never a Defect on
        # svTuple dispatch).
        if pointeeTy.kind in {itTuple, itVariant, itMultiVariant}:
          let fieldName = n[1].strVal
          # The field's type: ref-aware (`classifyFieldType`) so a RECURSIVE
          # `next: Node` field resolves to `tRef(placeholder)` (a `Ref_T`-valued
          # field-split heap entry, R9), while a plain scalar field (e.g. `val`)
          # resolves to its value type as before.
          let fieldTy = classifyFieldType(n).ty
          let ptrIR = parseExpr(operand, preamble, ctx)
          let synth = freshSynth(ctx, "fderef")
          preamble.add mkFieldDeref(synth, ptrIR, fieldTy, pointeeTy,
                                    fieldName, isPtr)
          return mkVar(synth)
    let lhsCls = classifyType(n[0])
    let fieldName = n[1].strVal
    case lhsCls.ty.kind
    of itTuple:
      var ix = -1
      for i, fn in lhsCls.ty.fieldNames:
        if fn == fieldName:
          ix = i; break
      if ix < 0:
        error(&"symex: field `{fieldName}` not in type {lhsCls.ty}", n)
      let objIR = parseExpr(n[0], preamble, ctx)
      mkField(objIR, ix, fieldName)
    of itSeq:
      if fieldName == "len":
        let objIR = parseExpr(n[0], preamble, ctx)
        mkSeqLen(objIR)
      else:
        error(&"symex (Phase 5): unsupported seq accessor `.{fieldName}`", n)
    of itVariant:
      # Phase 11. Three field-access shapes:
      #   * discriminator (cycle 3) → expression-level iekField
      #   * plain shared field (post-cycle-12) → expression-level
      #     iekField; the walker reads from the single shared
      #     SymVal — no fork, no FieldDefect risk.
      #   * arm-specific field (cycle 5) → A-normalised into an
      #     `isVariantField` statement so the walker can fork and
      #     `tFieldDefect` lands on the out-of-arm branch.
      let objIR = parseExpr(n[0], preamble, ctx)
      if fieldName == lhsCls.ty.vDiscName:
        mkField(objIR, 0, fieldName)
      elif fieldName in lhsCls.ty.vPlainFieldNames:
        mkField(objIR, 0, fieldName)
      else:
        var matchingTags: seq[int]
        var fieldTy: IRType = nil
        for arm in lhsCls.ty.vArms:
          let ix = arm.fieldNames.find(fieldName)
          if ix >= 0:
            matchingTags.add arm.tagOrdinal
            if fieldTy == nil:
              fieldTy = arm.fieldTypes[ix]
        if matchingTags.len == 0:
          error(&"symex Phase 11: field `{fieldName}` not present " &
                &"in any arm of `{lhsCls.ty}`", n)
        let synth = freshSynth(ctx, "vf")
        preamble.add mkVariantFieldStmt(
          synth, objIR, fieldName, fieldTy, matchingTags)
        mkVar(synth)
    of itMultiVariant:
      # Phase 14 cycle A1c slice 2. Axis-aware field access on an
      # itMultiVariant value. Three shapes:
      #   1. Plain shared field → expression-level iekField (no fork).
      #   2. Axis discriminator (matching a vDiscName) → iekField.
      #   3. Arm-specific field → walk each axis's arms, find the
      #      owning axis, emit `isVariantField` with that axis's tags
      #      as matchingTags. The walker resolves the axis at
      #      lowering time via `recv`'s svMultiVariant.
      let objIR = parseExpr(n[0], preamble, ctx)
      var isDiscOrPlain = fieldName in lhsCls.ty.mvPlainFieldNames
      if not isDiscOrPlain:
        for ax in lhsCls.ty.mvAxes:
          if fieldName == ax.discName: isDiscOrPlain = true; break
      if isDiscOrPlain:
        mkField(objIR, 0, fieldName)
      else:
        # Arm-specific: find the owning axis.
        var matchingTags: seq[int]
        var fieldTy: IRType = nil
        for ax in lhsCls.ty.mvAxes:
          for arm in ax.arms:
            let ix = arm.fieldNames.find(fieldName)
            if ix >= 0:
              matchingTags.add arm.tagOrdinal
              if fieldTy == nil:
                fieldTy = arm.fieldTypes[ix]
          if matchingTags.len > 0: break
        if matchingTags.len == 0:
          error("symex Phase 14: field `" & fieldName & "` not " &
                "present in any axis of `" & $lhsCls.ty & "`", n)
        let synth = freshSynth(ctx, "vf")
        preamble.add mkVariantFieldStmt(
          synth, objIR, fieldName, fieldTy, matchingTags)
        mkVar(synth)
    else:
      error(&"symex: `.` on unsupported type {lhsCls.ty}", n)
  of nnkCall:
    if isMarkerCall(n):
      error("symex: marker call `" & n[0].repr & "` used in expression " &
            "position; markers are statements only", n)
    let calleeSym = n[0]
    if calleeSym.kind != nnkSym:
      error(&"symex: cannot resolve callee `{n[0].repr}` in untyped " &
            "context; expression-position calls require the full macro flow.",
            n)
    # Phase 15 E8: the two no-arg exception-query magic intrinsics. Recognised
    # by callee symbol name and intercepted BEFORE the user-proc fall-through
    # (`ensureProcRegistered`), which would otherwise try to parse their stdlib
    # bodies (`if currException == nil: ...`) and choke. They lower at walk time
    # against `w.frame.inFlightExn`, so no operands are carried here.
    if n.len == 1:
      case calleeSym.strVal
      of "getCurrentException":    return mkGetCurrentExn()
      of "getCurrentExceptionMsg": return mkGetCurrentExnMsg()
      else: discard
    # Phase 15 Cluster C (C2b). Detect a CLOSURE CALL through a proc-valued
    # variable/param (`f(...)` where `f`'s impl is NOT a routine def AND its
    # type is `nnkProcTy`) BEFORE the string-builtin / seq routing below. Those
    # routings call `classifyType(n[1])`, and a closure-call ARG that is itself a
    # closure call (`f(f(v))`) carries no resolvable `getTypeInst`, so classify
    # would raise a non-catchable "node has no type". Routing the closure call
    # here keeps that classify off the closure-arg path entirely. (Mirrors the
    # `closureCallDetect` block below, which now only catches statement-position
    # forms the expression path did not reach.)
    block earlyClosureCallDetect:
      let impl = calleeSym.getImpl
      if impl.kind notin {nnkProcDef, nnkFuncDef, nnkIteratorDef,
                          nnkMethodDef, nnkConverterDef, nnkTemplateDef,
                          nnkMacroDef}:
        let ti = calleeSym.getTypeInst
        if ti.kind == nnkProcTy:
          var argIRs: seq[IRExpr]
          for i in 1 ..< n.len:
            argIRs.add parseExpr(n[i], preamble, ctx)
          return mkClosureCall(calleeSym.strVal, argIRs)
    # Phase 15 C4 (Des-LOW-L3). DSL higher-order calls — `filter`/`map`/`fold`
    # over `seq[T]` taking a CLOSURE arg, dispatched to the walker's HOF
    # handlers (inline / axiom), NOT the generic isCall descent. The interception
    # is GUARDED on the callee's ORIGIN being `std/sequtils` (`owner.strVal ==
    # "sequtils"`): a user-defined same-named proc (e.g. a local `filter[T]`)
    # owns to ITS module and falls through to the normal isCall descent — the
    # regression guard. `foldl`/`foldr` are sequtils TEMPLATES expanded to a loop
    # before this point, so only `filter`/`map` (real procs) reach here in
    # practice; the `fold` op name is handled for a hypothetical closure-fold.
    block hofDispatch:
      if calleeSym.strVal in ["filter", "map", "fold"] and
         calleeSym.kind == nnkSym:
        let owner = calleeSym.owner
        if owner.kind == nnkSym and owner.strVal == "sequtils" and n.len >= 3:
          let seqIR = parseExpr(n[1], preamble, ctx)
          let closureIR = parseExpr(n[2], preamble, ctx)
          # Only a genuine closure arg (an iekLambda) drives the HOF path; a
          # non-lambda 2nd arg means an unexpected shape — fall through.
          if closureIR != nil and closureIR.kind == iekLambda:
            # Result element type: `map` → mapper return; `filter`/`fold` →
            # the input element type (filter preserves; fold accumulates).
            let retCls = classifyType(n)   ## the HOF result type
            let retElemTy =
              if retCls.ty.kind == itSeq: retCls.ty.seqElemTy
              else: retCls.ty   ## fold returns the accumulator scalar
            let initIR = if calleeSym.strVal == "fold" and n.len >= 4:
                           parseExpr(n[3], preamble, ctx)
                         else: nil
            return mkHofCall(calleeSym.strVal, seqIR, closureIR,
                             retElemTy, initIR)
    # Phase 15 Cluster S (S1): `itString`-receiver call routing. This guard
    # runs BEFORE the seq/Table/HashSet builtins so `s.len` on a `string` is
    # NOT mis-routed to `iekSeqLen` (which would lower a Z3String operand into
    # the seq-length path → sort-mismatch crash), and BEFORE the user-proc
    # fall-through (which crashes resolving `getImpl` on a built-in like `len`).
    # In S1 every recognised string op routes to a STUBBED `iekStr*` node that
    # lowers to a classified `seUnsupportedStringOp` (sxUnknown); S2–S11 give
    # each its real Z3 String/Seq/Regex lowering. An UNRECOGNISED string call
    # routes to `iekStrUnsupported` (same clean diagnostic) — never a crash.
    # Phase 15 S5: `xs.join(sep)` where `xs` is a `seq[string]` (e.g. the result
    # of `split`). The receiver type is `seq[string]`/`openArray[string]`, which
    # `classifyType` below rejects, so route `join` to `iekStrJoin` BEFORE the
    # itString-receiver classify. The receiver expr is parsed through the normal
    # path (a `split` receiver lowers to an svSeq[string]); the runtime asserts
    # the receiver is an svSeq[string] and concats with `sep` interleaved.
    if calleeSym.strVal == "join" and n.len == 3:
      let recvIR = parseExpr(n[1], preamble, ctx)
      let sepIR  = parseExpr(n[2], preamble, ctx)
      return mkStrOp(iekStrJoin, "join", @[recvIR, sepIR])
    # Phase 15 S10a: int↔string conversion. `$n` (system.`$`) on an `itInt`
    # operand → `iekIntToStr` (Z3 `Z3_mk_int_to_str`); `parseInt(s)` on an
    # `itString` operand → `iekStrToInt` (digits-path, Z3 `Z3_mk_str_to_int`).
    # Both intercept BEFORE the itString-receiver classify (their operand/result
    # types straddle int and string). `$` only routes here for an int operand —
    # `$float`/`$bool`/etc. fall through unchanged (deferred to S10b / future).
    if calleeSym.strVal == "$" and n.len == 2 and
       classifyType(n[1]).ty.kind == itInt:
      return mkStrOp(iekIntToStr, "$", @[parseExpr(n[1], preamble, ctx)])
    if calleeSym.strVal == "parseInt" and n.len == 2 and
       classifyType(n[1]).ty.kind == itString:
      return mkStrOp(iekStrToInt, "parseInt", @[parseExpr(n[1], preamble, ctx)])
    if calleeSym.strVal == "parseFloat" and n.len == 2 and
       classifyType(n[1]).ty.kind == itString:
      # Phase 15 S10b: Z3 String theory has NO float↔string conversion (only the
      # int `str.to_int`/`int.to_str` pair). `parseFloat(s)` routes to a
      # classified `seUnsupportedStringOp` → `sxUnknown` (S9 `iekStrUnsupported`
      # mechanism, opName "parseFloat"; Invariant 3 — never a crash/silent UNSAT).
      return mkStrOp(iekStrUnsupported, "parseFloat", @[])
    # Phase 15 C2b: the receiver of a string-builtin must be type-classifiable.
    # A nested CLOSURE CALL (`f(f(v))` — `n[1]` is `f(v)`) carries NO semantic
    # type (`typeKind == ntyNone`), so `classifyType`'s `getTypeInst` would raise
    # a non-catchable "node has no type" compile error. Gate the string-receiver
    # classify on the node actually HAVING a type; an untyped receiver is not a
    # string op — fall through to the normal/closure-call dispatch below.
    if n.len >= 2 and n[1].typeKind != ntyNone:
      let recvCls0 = classifyType(n[1])
      if recvCls0.ty.kind == itString:
        # Phase 15 S6b: regex calls. `s.match(re"…")` / `s.find(re"…")` /
        # `s.contains(re"…")` / `s.replace(re"…", repl)` from Nim's `std/re`.
        # In the typed AST a `re"…"` literal is an `nnkCallStrLit` whose callee
        # is `re`/`rex` and whose `[1]` is the raw pattern string-literal; the
        # surrounding call also carries a trailing default `start` int arg
        # (match/find/contains) which we drop. We must intercept BEFORE the
        # uniform `sArgs` parse below, which would choke on `nnkCallStrLit`.
        # Only a COMPILE-TIME literal pattern is extractable; a symbolic Regex
        # value can't be parsed at walk time → routes to `iekStrUnsupported`.
        block regexCall:
          if calleeSym.strVal notin ["match", "find", "contains", "replace"]:
            break regexCall
          # locate the `re"…"` arg (nnkCallStrLit with callee re/rex).
          var rePat = ""
          var reIdx = -1
          for i in 2 ..< n.len:
            let a = n[i]
            if a.kind == nnkCallStrLit and a.len >= 2 and
               a[0].kind in {nnkSym, nnkIdent} and
               a[0].strVal in ["re", "rex"] and
               a[1].kind in {nnkRStrLit, nnkStrLit, nnkTripleStrLit}:
              rePat = a[1].strVal
              reIdx = i
              break
          if reIdx < 0:
            break regexCall   # not a regex call (string-arg overload) — fall through
          let recvIR = parseExpr(n[1], preamble, ctx)
          case calleeSym.strVal
          of "match", "contains":
            # membership predicate → svBool. Pattern in strOp; strArgs = [recv].
            return mkStrOp(iekStrMatch, rePat, @[recvIR])
          of "find":
            # DEFERRED: nim-z3 has no indexOf-on-regex API → classified
            # seUnsupportedRegex at walk time. Pattern in strOp; strArgs = [recv].
            return mkStrOp(iekStrFindRe, rePat, @[recvIR])
          of "replace":
            # regex global replace → version-gated (z3WithSeqReplaceRe). The
            # replacement is the OTHER (non-regex) string arg. strArgs =
            # [recv, replacement]; pattern in strOp.
            var replIR: IRExpr = mkStrLit("")
            for i in 2 ..< n.len:
              if i != reIdx and n[i].kind != nnkIntLit:
                replIR = parseExpr(n[i], preamble, ctx)
                break
            return mkStrOp(iekStrReplaceRe, rePat, @[recvIR, replIR])
          else: discard
        # Phase 15 S3: `s[i]` (index read) and `s[a..b]` (slice) arrive as a
        # `[]` call on the string. The slice argument is an `nnkInfix(.., a, b)`
        # / `nnkInfix(..<, a, b)` which is NOT a scalar IR expr — handle both
        # shapes before the uniform arg parse below.
        if calleeSym.strVal == "[]" and n.len == 3:
          let recvIR = parseExpr(n[1], preamble, ctx)
          let idxNode = n[2]
          if idxNode.kind == nnkInfix and idxNode.len == 3 and
             idxNode[0].kind in {nnkSym, nnkIdent} and
             idxNode[0].strVal in ["..", "..<"]:
            # `s[a..b]` (inclusive) / `s[a..<b]` (exclusive). Lower to
            # `iekStrSubstr` carrying [recv, lo, hi] — the runtime computes the
            # Z3 (seq.extract recv lo (hi-lo+1)) length-arg form, with hi being
            # `b` for `..` and `b-1` for `..<`.
            let loIR = parseExpr(idxNode[1], preamble, ctx)
            var hiIR = parseExpr(idxNode[2], preamble, ctx)
            if idxNode[0].strVal == "..<":
              hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
            return mkStrOp(iekStrSubstr, "[]", @[recvIR, loIR, hiIR])
          else:
            # `s[i]` single-byte index read → char via at->toCode->BV8 bridge.
            let idxIR = parseExpr(idxNode, preamble, ctx)
            return mkStrOp(iekStrAt, "[]", @[recvIR, idxIR])
        # Phase 15 S3: `s.high` is byte-faithfully `len(s) - 1` (ADR-0006) —
        # NOT unsupported. Build it directly from `iekStrLen`.
        if calleeSym.strVal == "high" and n.len == 2:
          let recvIR = parseExpr(n[1], preamble, ctx)
          let lenIR = mkStrOp(iekStrLen, "len", @[recvIR])
          return mkBinop(bSub, lenIR, mkIntLit(1))
        # Phase 15 S9: case-folding ops — `toLower`/`toUpper` (std/unicode) and
        # the ASCII-only `toLowerAscii`/`toUpperAscii` (std/strutils). Z3 has NO
        # native case-folding primitive (ADR-0006; a regex-range approximation is
        # deferred to Phase 16), so these route EXPLICITLY to `iekStrUnsupported`
        # → classified `seUnsupportedStringOp` (sxUnknown, Invariant 3 — never a
        # silent UNSAT, never a crash). An explicit guard (rather than relying on
        # the `getStdlibModelFor` else-fallthrough) keeps the classification
        # intentional and carries the real surface op name into the diagnostic.
        if calleeSym.strVal in
             ["toLower", "toUpper", "toLowerAscii", "toUpperAscii"] and
           n.len >= 2:
          var caseArgs: seq[IRExpr]
          for i in 1 ..< n.len:
            caseArgs.add parseExpr(n[i], preamble, ctx)
          return mkStrOp(iekStrUnsupported, calleeSym.strVal, caseArgs)
        let sm = getStdlibModelFor(calleeSym.strVal, itString)
        # Phase 15 G8: a call whose FIRST arg is an `itString` is NOT necessarily
        # a string OPERATION — it may be an ordinary USER PROC whose first
        # parameter happens to be `string` (`proc foo(a: string, …)`). The
        # string-op guard must only claim calls it actually models; an
        # `smkUnregistered` name that resolves to a real user `nnkProcDef` falls
        # THROUGH to the user-proc call path below (without this, e.g.
        # `solo(s)` was mis-classified `seUnsupportedStringOp` → sxUnknown). A
        # genuinely-unsupported stdlib string call (no user impl) still routes to
        # `iekStrUnsupported` (Invariant 3 — never a silent UNSAT).
        if sm.kind == smkUnregistered and
           calleeSym.kind == nnkSym and calleeSym.getImpl.kind == nnkProcDef:
          discard   ## user proc — fall through to the user-proc call path
        else:
          var sArgs: seq[IRExpr]
          for i in 1 ..< n.len:
            sArgs.add parseExpr(n[i], preamble, ctx)
          let irKind = case sm.kind
            of smkStrLen:        iekStrLen
            of smkStrIndex:      iekStrAt
            of smkStrAt:         iekStrAt
            of smkStrSubstr:     iekStrSubstr
            of smkStrFind:       iekStrFind
            of smkStrContains:   iekStrContains
            of smkStrStartsWith: iekStrStartsWith
            of smkStrEndsWith:   iekStrEndsWith
            of smkStrReplace:    iekStrReplace
            of smkStrReplaceAll: iekStrReplaceAll
            of smkStrSplit:      iekStrSplit
            of smkStrJoin:       iekStrJoin
            of smkStrMatch:      iekStrMatch
            of smkStrBytes:      iekStrBytes
            else:                iekStrUnsupported
          return mkStrOp(irKind, calleeSym.strVal, sArgs)
    # Stdlib builtins recognised by name (Phase 5+):
    # `len(c)` on seq/Table/HashSet → iekSeqLen (semantic: "container
    # cardinality", lowered against the right counter at runtime).
    if calleeSym.strVal in ["len", "card"] and n.len == 2:
      let argCls = classifyType(n[1])
      if argCls.ty.kind in {itSeq, itTable, itSet}:
        return mkSeqLen(parseExpr(n[1], preamble, ctx))
    # `contains(c, k)` and `hasKey(c, k)` on a Table/HashSet → iekContains.
    if (calleeSym.strVal == "contains" or calleeSym.strVal == "hasKey") and
       n.len == 3:
      let recvCls = classifyType(n[1])
      if recvCls.ty.kind in {itTable, itSet}:
        let recvIR = parseExpr(n[1], preamble, ctx)
        let keyIR  = parseExpr(n[2], preamble, ctx)
        return mkContains(recvIR, keyIR)
    # `[](t, k)` on a Table → A-normalised isIndex (runtime dispatches
    # on receiver kind for select-from-tabData semantics).
    if calleeSym.strVal == "[]" and n.len == 3:
      let recvCls = classifyType(n[1])
      if recvCls.ty.kind == itTable:
        let recvIR = parseExpr(n[1], preamble, ctx)
        let keyIR  = parseExpr(n[2], preamble, ctx)
        let synth = freshSynth(ctx, "tget")
        preamble.add mkIndexStmt(synth, recvIR, keyIR, recvCls.ty.tabValTy)
        return mkVar(synth)
      if recvCls.ty.kind == itSeq:
        let recvIR = parseExpr(n[1], preamble, ctx)
        let keyIR  = parseExpr(n[2], preamble, ctx)
        let synth = freshSynth(ctx, "sget")
        preamble.add mkIndexStmt(synth, recvIR, keyIR, recvCls.ty.seqElemTy)
        return mkVar(synth)
    # Phase 15 F6: std/math float ops + FP predicates. The modeled and the
    # deferred names are both routed to iekMathCall — the runtime lowers the
    # modeled ones to Z3-FP-native asts and the deferred ones to a classified
    # `feUnsupportedOp` error (Invariant 3 — never a silent UNSAT). We only
    # intercept when the FIRST argument is float-typed, so e.g. integer `abs`
    # or `min`/`max` on ints fall through to their existing handling.
    block mathInterception:
      let cn = calleeSym.strVal
      if n.len >= 2:
        let firstCls = classifyType(n[1])
        if firstCls.ty.kind in {itFloat32, itFloat64}:
          # Known modeled/deferred names always route to iekMathCall. Any
          # OTHER float-receiver call into the Nim stdlib (e.g. `ln`, `sin`)
          # is an unmodeled std/math op — also route it so the runtime emits
          # `feUnsupportedOp` rather than failing `getImpl` resolution or
          # walking a transcendental's body (Invariant 3 — never silent UNSAT).
          if cn in mathFpModeledOps or cn in mathFpDeferredOps or
             isStdMathProc(calleeSym):
            var mArgs: seq[IRExpr]
            for i in 1 ..< n.len:
              mArgs.add parseExpr(n[i], preamble, ctx)
            return mkMathCall(cn, mArgs)
    # Opaque effectful proc (#137 + Phase 9 user extension via
    # `{.symexOpaque.}` pragma) — fresh-symbolic return, no body walk.
    let calleeName = calleeSym.strVal
    let opaModel = getStdlibModelFor(calleeName, itBool)
    if opaModel.kind == smkOpaqueEffectful or hasSymexOpaquePragma(calleeSym):
      var argIRs: seq[IRExpr]
      for i in 1 ..< n.len:
        argIRs.add parseExpr(n[i], preamble, ctx)
      let retCls = classifyType(n)
      let synth = freshSynth(ctx, calleeName)
      preamble.add mkOpaqueCall(calleeName, synth, argIRs, retCls.ty)
      return mkVar(synth)
    # Phase 15 Cluster C (C1, ADR-0009 D6). A call THROUGH a proc-valued
    # VARIABLE (a local/param of proc type), distinct from a normal named-proc
    # call. The discriminator: `calleeSym`'s `getImpl` is NOT a proc/func DEF
    # (a top-level proc resolves to `nnkProcDef`; a proc-valued variable's impl
    # is the `nnkIdentDefs` of its let/var/param binding) AND its instantiated
    # type is a proc type (`nnkProcTy`). Top-level procs-as-VALUES are C3; C1
    # handles only the proc-valued-variable CALL shape → `iekClosureCall`
    # (walker-stubbed `ceNotImplemented` in C1; C2b adds application).
    block closureCallDetect:
      if calleeSym.kind == nnkSym:
        let impl = calleeSym.getImpl
        if impl.kind notin {nnkProcDef, nnkFuncDef, nnkIteratorDef,
                            nnkMethodDef, nnkConverterDef, nnkTemplateDef,
                            nnkMacroDef}:
          let ti = calleeSym.getTypeInst
          if ti.kind == nnkProcTy:
            var argIRs: seq[IRExpr]
            for i in 1 ..< n.len:
              argIRs.add parseExpr(n[i], preamble, ctx)
            return mkClosureCall(calleeName, argIRs)
    # User-proc call in expression position. A-normalise. The instantiation
    # key returned by `ensureProcRegistered` (G1a) is the dispatch key the
    # walker looks up — it MUST be the `mkCall` callee name (not the bare name).
    let callKey = ensureProcRegistered(ctx, calleeSym, n)
    var argIRs: seq[IRExpr]
    for i in 1 ..< n.len:
      argIRs.add parseExpr(n[i], preamble, ctx)
    let retCls = classifyType(n)
    let synth = freshSynth(ctx, calleeName)
    preamble.add mkCall(callKey, synth, argIRs, retCls.ty)
    mkVar(synth)
  else:
    error(&"symex: unsupported expression kind {n.kind} in `{n.repr}`", n)

# ---- Statement parser --------------------------------------------------------

proc unsafeCastReason(n: NimNode): string =
  ## Phase 15 R11 (ADR-0010, RFC §R11 — Open Question 7 CLOSED). Classify an RHS
  ## expression as an unsafe POINTER MATERIALISATION when it is unmodelable in
  ## the logical-heap model (the heap is keyed by an abstract `Ref_T` value, not
  ## a raw machine address). Returns a non-empty `ucReason` string when `n` is
  ## such a pattern, "" otherwise. The detection is CONSERVATIVE — it keys ONLY
  ## on the two unambiguous pointer-materialisation node shapes:
  ##
  ##   * `nnkCast` whose TARGET type node is a `ptr T` (`cast[ptr T](...)`).
  ##     `nnkPtrTy` is the typed-AST node for a `ptr` cast target. A `cast`
  ##     between non-pointer VALUE types (if ever reached) is NOT matched here.
  ##   * `nnkAddr` (`addr x` / `unsafeAddr x` — both lower to `nnkAddr` in the
  ##     typed AST) — taking the address of a local materialises a raw pointer.
  ##
  ## Anything else returns "" and parses as before (the guard never fires on
  ## ordinary value expressions, so a no-cast SUT is unaffected — Invariant: no
  ## over-trigger).
  case n.kind
  of nnkCast:
    if n.len >= 1 and n[0].kind == nnkPtrTy:
      "cast[ptr T]"
    else:
      ""
  of nnkAddr:
    # `addr x` and `unsafeAddr x` are indistinguishable in the typed AST (both
    # `nnkAddr`); the reason string names the pointer-taking operation.
    "addr"
  else:
    ""

proc parseStmtInner(n: NimNode,
                    preamble: var seq[IRStmt],
                    ctx: ParseCtx): IRStmt =
  ## The `preamble` accumulates A-normalised calls from any expression
  ## the surrounding statement contains; callers wrap the resulting
  ## stmt with the preamble before returning.
  case n.kind
  # Phase 15 E6. A raw `assert cond, msg` / `doAssert cond` lowers (after
  # semcheck) to gensym scaffolding (`const loc…`, `bind`, `mixin`) plus a
  # `PragmaBlock[Pragma, IfStmt[ElifBranch[not (cond), Call failedAssertImpl]]]`.
  # The scaffolding statements are not in the supported fragment and the
  # `failedAssertImpl` call would land `isUnsupported`; instead, recognise the
  # whole expansion and lower it to an implicit `AssertionDefect` raise guarded
  # by the assert-FAILS condition (`not cond`), so a reachable assert violation
  # surfaces as `sxRaised{isDefect: true}` rather than silently. This is the
  # raw-`assert` path; the `symexAssert(...)` MARKER (→ `mkAssert`/`isAssert`)
  # and its `tAssertionViolation` semantics are UNCHANGED.
  # CR-22 fix: the detection is SCOPED to the nnkPragmaBlock node that IS the
  # assert expansion — NOT applied greedily to any enclosing StmtList that
  # merely CONTAINS an assert.  Sibling statements (e.g. symexTarget labels)
  # are parsed normally in their original order by the StmtList arm below.
  of nnkPragmaBlock:
    let failsCond = findAssertFailsCond(n)
    if failsCond != nil:
      let condIR = parseExpr(failsCond, preamble, ctx)
      return mkIf(@[mkBranch(condIR, mkRaise("AssertionDefect", nil))])
    # Fallthrough: a PragmaBlock that is NOT an assert expansion — treat as
    # a transparent wrapper around its body (the last child).
    parseStmt(n[n.len - 1], ctx)
  of nnkStmtList, nnkStmtListExpr, nnkBlockStmt:
    let inner = if n.kind == nnkBlockStmt: n[1] else: n
    var stmts: seq[IRStmt]
    for c in inner:
      stmts.add parseStmt(c, ctx)
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkIfStmt, nnkIfExpr:
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        # Each branch's condition gets its own preamble; we surface it
        # into the outer preamble so the call runs *before* the if.
        var condPreamble: seq[IRStmt]
        let condIR = parseExpr(arm[0], condPreamble, ctx)
        # The condition's preamble must run before the if for the
        # branch's then-body to see the bindings. For Phase 3 a
        # single if's preamble flows into the enclosing block.
        for cs in condPreamble: preamble.add cs
        branches.add mkBranch(condIR, parseStmt(arm[1], ctx))
      of nnkElse, nnkElseExpr:
        elseBody = parseStmt(arm[0], ctx)
      else:
        error(&"symex: unexpected if-arm kind {arm.kind}", arm)
    mkIf(branches, elseBody)
  of nnkAsgn:
    # Shapes after semcheck (some forms get re-wrapped):
    #   * `name = expr`                 — simple env reassignment
    #   * `t[k] = v`                    — Table set
    # Var receivers may carry HiddenDeref/HiddenAddr — unwrap.
    proc unwrap(x: NimNode): NimNode =
      var r = x
      while r.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv}:
        r = r[r.len - 1]
      r
    # Phase 15 R8b (ADR-0010). `p = new T` REBIND of a `var ref T` / `var ptr T`
    # parameter. Because the param is a `var`, the typed LHS is a compiler-
    # inserted `nnkHiddenDeref(sym)` (the lvalue indirection) — NOT an explicit
    # `nnkDerefExpr` (which is the `p[] = v` heap-write shape). So `p = new int`
    # presents as `Asgn[HiddenDeref[Sym p], Command[new, int]]`, whereas
    # `p[] = v` is `Asgn[DerefExpr[HiddenDeref[Sym p]], v]`. Distinguish on the
    # bare `nnkHiddenDeref` (var-ness) + a `new T` RHS: this is a VARIABLE rebind
    # to a freshly allocated cell, lowered to `isNew` under the var name (the R2
    # `freshRef` mints a new `Ref_T` const), NOT a heap store at the old address.
    # The fresh binding flows back to the caller via the #140 `isVar` write-back
    # (R8b extends it to svRef/svPtr in the walker's `isCall` return arm). Checked
    # BEFORE the `nnkDerefExpr|nnkHiddenDeref` deref-write arm (which would treat
    # this as `p[] = new int` and `parseExpr` the unsupported `new` command).
    if n[0].kind == nnkHiddenDeref and n[0].len == 1 and
       n[0][0].kind == nnkSym and isNewCall(n[1]):
      let sym = n[0][0]
      let symCls = classifyType(sym)
      if symCls.ty.kind in {itRef, itPtr}:
        return mkNewT(sym.strVal, symCls.ty)
    # Phase 15 R3 (ADR-0010). `p[] = v` — a heap WRITE through a ref/ptr deref.
    # The LHS is an explicit `nnkDerefExpr` (or a compiler-inserted
    # `nnkHiddenDeref`) whose operand classifies as a genuine `ref T`/`ptr T`.
    # Lower it to an `isDerefWrite` stmt (the walker no-ops it at R3; the real
    # `store` lands R4). This MUST be checked BEFORE `unwrap` (which strips a
    # hidden deref down to the pointee and would lose the indirection). A
    # hidden-deref over a NON-ref operand keeps the pre-R unwrap path below.
    if n[0].kind in {nnkDerefExpr, nnkHiddenDeref} and n[0].len >= 1:
      # Phase 15 R8b: a `var ref T` param's `p[] = v` is
      # `Asgn[DerefExpr[HiddenDeref[Sym p]], v]` — the inner `HiddenDeref` is the
      # `var`-ness lvalue indirection, which `classifyType` unwraps to the
      # pointee (defeating the itRef detection). Strip that ONE var-level
      # hidden-deref so the operand is the ref/ptr symbol (matching the deref-READ
      # arm). For a plain `ref T` param `p[] = v` is `Asgn[DerefExpr[Sym p], v]`
      # (no inner HiddenDeref) and this strip is a no-op.
      var operand = n[0][0]
      if operand.kind == nnkHiddenDeref and operand.len == 1 and
         classifyType(operand[0]).ty.kind in {itRef, itPtr}:
        operand = operand[0]
      let opCls = classifyType(operand)
      if opCls.ty.kind in {itRef, itPtr}:
        let isPtr = opCls.ty.kind == itPtr
        let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
        let ptrIR = parseExpr(operand, preamble, ctx)
        let valIR = parseExpr(n[1], preamble, ctx)
        return mkDerefWrite(ptrIR, valIR, pointeeTy, isPtr)
    # Phase 15 R6 (ADR-0010). `p.field = v` — a FIELD WRITE through a
    # `ref object` / `ptr object`. LHS is `nnkDotExpr(nnkHiddenDeref(p), field)`.
    # Lower to a field-split `isDerefWrite` (`store(heap_<objTid>__<field>, p, v)`
    # — only that field's array changes; an aliased read of the same field sees
    # the write). Checked BEFORE `unwrap` (which would strip the indirection).
    if n[0].kind == nnkDotExpr and n[0].len == 2 and
       n[0][0].kind in {nnkHiddenDeref, nnkDerefExpr} and n[0][0].len >= 1:
      let operand = n[0][0][0]
      let opCls = classifyType(operand)
      if opCls.ty.kind in {itRef, itPtr}:
        let isPtr = opCls.ty.kind == itPtr
        let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
        if pointeeTy.kind in {itTuple, itVariant, itMultiVariant}:
          let fieldName = n[0][1].strVal
          let fieldTy   = classifyType(n[0]).ty   ## the field's type
          let ptrIR = parseExpr(operand, preamble, ctx)
          let valIR = parseExpr(n[1], preamble, ctx)
          return mkFieldDerefWrite(ptrIR, valIR, fieldTy, pointeeTy,
                                   fieldName, isPtr)
    let lhs = unwrap(n[0])
    if lhs.kind == nnkBracketExpr and lhs.len == 2:
      let recv = unwrap(lhs[0])
      if recv.kind == nnkSym:
        let recvCls = classifyType(recv)
        if recvCls.ty.kind == itTable:
          let key = parseExpr(lhs[1], preamble, ctx)
          let val = parseExpr(n[1], preamble, ctx)
          return mkAssign(recv.strVal,
            mkTableSet(mkVar(recv.strVal), key, val))
        # Phase 15 S11: `s[i] = c` — string index ASSIGNMENT on an `itString`
        # receiver. Z3 String theory strings are IMMUTABLE (ADR-0006), so this
        # mutation has no sound symbolic encoding and is honestly classified
        # `seUnsupportedStringOp` → `sxUnknown` (Invariant 3 — never a silent
        # UNSAT, never a crash). The reason is immutability, NOT a byte/codepoint
        # mismatch (the model is byte-faithful). Reuse the S9/S3 idiom: bind the
        # receiver to an `iekStrUnsupported` op (carrying the surface op name);
        # the residual `lower` arm raises `SymexUnsupportedStringOpError`, which
        # the `runSymex` boundary maps to `seUnsupportedStringOp`.
        if recvCls.ty.kind == itString:
          let recvIR = mkVar(recv.strVal)
          let idxIR  = parseExpr(lhs[1], preamble, ctx)
          let valIR  = parseExpr(n[1], preamble, ctx)
          return mkAssign(recv.strVal,
            mkStrOp(iekStrUnsupported, "string mutation",
                    @[recvIR, idxIR, valIR]))
    if lhs.kind == nnkSym:
      let nm = lhs.strVal
      # Phase 15 R8b (ADR-0010): a `new T` RHS REBINDS the var to a freshly
      # allocated cell (`p = new int`). Lower it to an `isNew` stmt under the
      # LHS name — `freshRef` mints a fresh `Ref_T` const and binds it for `nm`,
      # exactly as the let-section `new T` arm does (R2). The classified type
      # comes from the LHS sym (a `var ref T` param classifies to `itRef`, the
      # `var` stripped). Without this the assign would `parseExpr(new int)` and
      # halt on the unsupported `nnkCommand`. The fresh binding flows back to the
      # caller via the #140 `isVar` write-back (R8b extends it to svRef/svPtr).
      if isNewCall(n[1]):
        let classified = classifyType(lhs)
        if classified.ty.kind in {itRef, itPtr}:
          return mkNewT(nm, classified.ty)
      let val = parseExpr(n[1], preamble, ctx)
      return mkAssign(nm, val)
    # Phase 11 cycle 6: `obj.kind = tagLiteral` — discriminator
    # reassignment. Requires (a) the object to be a Sym in env,
    # (b) the field to be the variant's discriminator name, and
    # (c) the RHS to resolve to a static enum constant of the
    # discriminator's enum. Symbolic RHS is a future cycle.
    if lhs.kind == nnkDotExpr and lhs.len == 2:
      let recv = unwrap(lhs[0])
      let fieldNode = lhs[1]
      if recv.kind == nnkSym and fieldNode.kind in {nnkIdent, nnkSym}:
        let recvCls = classifyType(recv)
        # Phase 11 + Phase 14 A4. Three cases:
        #   1. itVariant disc reassign with a static enum-constant RHS
        #      → mkVariantReassign (Phase 11 cycle 6 path).
        #   2. itVariant disc reassign with a symbolic RHS → A4's
        #      mkVariantReassignSymbolic (walker forks).
        #   3. itMultiVariant axis-disc reassign → same A4 IR with
        #      vrsDiscName = axis name. Static-tag path on multi-
        #      variant is a future cycle.
        if recvCls.ty.kind == itVariant and
           fieldNode.strVal == recvCls.ty.vDiscName:
          let rhs = unwrap(n[1])
          # Try the static-tag path first.
          let tagIR = parseExpr(rhs, preamble, ctx)
          if tagIR.kind == iekIntLit:
            var tagName = if rhs.kind == nnkSym: rhs.strVal else: ""
            for arm in recvCls.ty.vArms:
              if arm.tagOrdinal == int(tagIR.ival):
                tagName = arm.tagName; break
            return mkVariantReassign(recv.strVal, int(tagIR.ival), tagName)
          # Symbolic RHS: A4 fork path.
          return mkVariantReassignSymbolic(recv.strVal, "", tagIR)
        if recvCls.ty.kind == itMultiVariant:
          # Identify which axis owns `fieldNode.strVal` as discName.
          for ax in recvCls.ty.mvAxes:
            if ax.discName == fieldNode.strVal:
              let rhs = unwrap(n[1])
              let tagIR = parseExpr(rhs, preamble, ctx)
              # Multi-axis disc reassign — static or symbolic, both
              # go through the A4 symbolic IR for now (no Phase 11
              # static path was ever implemented for multi-axis).
              return mkVariantReassignSymbolic(
                recv.strVal, ax.discName, tagIR)
    mkUnsupported(&"unsupported nnkAsgn shape: {n.repr}")
  of nnkWhileStmt:
    var preamble2: seq[IRStmt]
    let cond = parseExpr(n[0], preamble2, ctx)
    let body = parseStmt(n[1], ctx)
    if preamble2.len == 0:
      mkWhile(cond, body)
    else:
      var both = preamble2
      both.add mkWhile(cond, body)
      mkBlock(both)
  of nnkCaseStmt:
    # Lower to if-elif chain: each `of label: body` becomes
    # `elif scrutinee == label: body`, with multiple labels chained via OR.
    var preamble3: seq[IRStmt]
    let scrutinee = parseExpr(n[0], preamble3, ctx)
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for i in 1 ..< n.len:
      let arm = n[i]
      case arm.kind
      of nnkOfBranch:
        # arm[0..arm.len-2] = labels; arm[arm.len-1] = body
        var cond: IRExpr = nil
        for j in 0 ..< arm.len - 1:
          let labelIR = parseExpr(arm[j], preamble3, ctx)
          let eq = mkBinop(bEq, scrutinee, labelIR)
          if cond == nil: cond = eq
          else: cond = mkBinop(bOr, cond, eq)
        branches.add mkBranch(cond, parseStmt(arm[arm.len - 1], ctx))
      of nnkElse, nnkElseExpr:
        elseBody = parseStmt(arm[0], ctx)
      else:
        error(&"unexpected case-arm kind {arm.kind}", arm)
    let ifNode = mkIf(branches, elseBody)
    if preamble3.len == 0: ifNode
    else:
      var all = preamble3
      all.add ifNode
      mkBlock(all)
  of nnkForStmt:
    # Phase 6: desugar common shapes to while loops.
    # Common cases (after semcheck):
    #   * `for i in a..b: body`  → Infix(.., a, b) — inclusive
    #   * `for i in a..<b: body` → Infix(..<, a, b) — exclusive
    #   * `for x in arr: body`   → Sym arr — static-N array
    #   * `for x in s: body`     → Sym s — seq[T]
    let iterVar = n[0]
    let iterExpr = n[^2]
    let bodyNode = n[^1]
    iterVar.expectKind nnkSym
    let iterName = iterVar.strVal
    if iterExpr.kind == nnkInfix and iterExpr[0].kind == nnkSym and
       iterExpr[0].strVal in [".." , "..<"]:
      let inclusive = iterExpr[0].strVal == ".."
      var preamble3: seq[IRStmt]
      let loIR = parseExpr(iterExpr[1], preamble3, ctx)
      let hiIR = parseExpr(iterExpr[2], preamble3, ctx)
      let body = parseStmt(bodyNode, ctx)
      # Build: { var __iv = lo; while __iv <op> hi: { let i = __iv; body; __iv = __iv + 1 } }
      let ivName = freshSynth(ctx, "iv")
      let intTy = tInt(64, signed = true)
      let initStmt = mkLet(ivName, intTy, loIR)
      let cmpOp = if inclusive: bLe else: bLt
      let cond = mkBinop(cmpOp, mkVar(ivName), hiIR)
      # Wrap body with: let i = __iv; <body>; __iv = __iv + 1
      let bindIter = mkLet(iterName, intTy, mkVar(ivName))
      let incIv = mkAssign(ivName,
        mkBinop(bAdd, mkVar(ivName), mkIntLit(1)))
      let loopBody = mkBlock(@[bindIter, body, incIv])
      let whileSt = mkWhile(cond, loopBody)
      var allStmts = preamble3
      allStmts.add initStmt
      allStmts.add whileSt
      mkBlock(allStmts)
    elif iterExpr.kind == nnkCall and iterExpr.len == 2 and
         iterExpr[0].kind == nnkSym and iterExpr[0].strVal in ["items", "pairs"]:
      # `for x in container` semchecks to `for x in items(container)`.
      let container = iterExpr[1]
      let recvCls = classifyType(container)
      if recvCls.ty.kind == itString:
        # Phase 15 S3 (ADR-0006): `for c in s` over a *symbolic* string is
        # unsupported — NOT for a byte/codepoint reason (byte-faithful makes
        # iteration positional and well-defined), but because the iteration
        # count is the string's unknown symbolic length: there is no sound
        # bounded encoding of an unbounded-length positional walk. We classify
        # it here (BEFORE parsing the body — the body may itself reference the
        # loop var in ways that only typecheck inside the loop) so the walker
        # marks the path uncertain (sxUnknown), never a silent UNSAT
        # (Invariant 3).
        return mkUnsupported("symex Phase 15 S3: `for c in s` over a symbolic " &
          "string is unsupported (unbounded symbolic iteration length, " &
          "not a byte/codepoint mismatch — ADR-0006)")
      let body = parseStmt(bodyNode, ctx)
      let intTy = tInt(64, signed = true)
      case recvCls.ty.kind
      of itArray:
        # Static unroll: N iterations, each with `let i = arr[k]; body`.
        var preamble3: seq[IRStmt]
        let arrIR = parseExpr(container, preamble3, ctx)
        var stmts = preamble3
        for k in 0 ..< recvCls.ty.size:
          # bind `iterName = arr[k]`
          let synth = freshSynth(ctx, "fa")
          stmts.add mkIndexStmt(synth, arrIR, mkIntLit(int64(k)),
                                recvCls.ty.elemTy)
          stmts.add mkLet(iterName, recvCls.ty.elemTy, mkVar(synth))
          stmts.add body
        mkBlock(stmts)
      of itSeq:
        # Desugar: var __iv = 0; while __iv < s.len: let x = s[__iv]; body; __iv += 1
        var preamble3: seq[IRStmt]
        let seqIR = parseExpr(container, preamble3, ctx)
        let ivName = freshSynth(ctx, "iv")
        let initStmt = mkLet(ivName, intTy, mkIntLit(0))
        let lenExpr = mkSeqLen(seqIR)
        let cond = mkBinop(bLt, mkVar(ivName), lenExpr)
        let synth = freshSynth(ctx, "fs")
        # A-normalised index: isIndex stmt + bind via let
        let idxStmt = mkIndexStmt(synth, seqIR, mkVar(ivName),
                                  recvCls.ty.seqElemTy)
        let bindIter = mkLet(iterName, recvCls.ty.seqElemTy, mkVar(synth))
        let incIv = mkAssign(ivName,
          mkBinop(bAdd, mkVar(ivName), mkIntLit(1)))
        let loopBody = mkBlock(@[idxStmt, bindIter, body, incIv])
        let whileSt = mkWhile(cond, loopBody)
        var allStmts = preamble3
        allStmts.add initStmt
        allStmts.add whileSt
        mkBlock(allStmts)
      else:
        # itString is handled by the early return above (before body parse).
        mkUnsupported(&"unsupported for-loop container kind: {recvCls.ty.kind}")
    else:
      mkUnsupported(&"unsupported for-loop iterable shape: {iterExpr.kind}")
  of nnkBreakStmt:
    mkBreak()
  of nnkContinueStmt:
    mkContinue()
  of nnkReturnStmt:
    # Semchecked AST forms for `return EXPR`:
    #   * `return EXPR` directly (untyped)         → ReturnStmt[EXPR]
    #   * `return EXPR` in a value-returning proc  → ReturnStmt[Asgn(result, EXPR)]
    # Phase 3 handles both.
    let inner = n[0]
    if inner.kind == nnkEmpty:
      mkReturn()
    elif inner.kind == nnkAsgn and inner[0].kind == nnkSym and
         inner[0].strVal == "result":
      mkReturnVal(parseExpr(inner[1], preamble, ctx))
    else:
      mkReturnVal(parseExpr(inner, preamble, ctx))
  of nnkLetSection, nnkVarSection:
    var stmts: seq[IRStmt]
    for id in n:
      id.expectKind nnkIdentDefs
      let valNode = id[id.len - 1]
      # Phase 15 R11 (ADR-0010, RFC §R11). An unsafe POINTER MATERIALISATION RHS
      # (`cast[ptr T](...)`, `addr x`, `unsafeAddr x`) is unmodelable in the
      # logical-heap model — classify `heUnsafeCast` (sevError) so the verdict
      # degrades to `sxUnknown` (Invariant 3 — never a silent sat/unsat) and emit
      # `isUnsafeCast`. We do NOT model the address. The guard keys strictly on
      # the pointer-materialisation node shapes (`nnkCast` to `ptr T`, `nnkAddr`),
      # so a no-cast binding is unaffected. Without this, the cast/addr node would
      # hit parseExpr's hard `error()` (a compile-time failure, not a classified
      # halt); R11 converts it to the classified-error path.
      block:
        let ucReason = unsafeCastReason(valNode)
        if ucReason.len > 0:
          ctx.parseErrors.add SymexErrorInfo(
            kind: heUnsafeCast,
            severity: sevError,
            msg: "unsafe pointer materialisation (" & ucReason & ") not modeled")
          stmts.add mkUnsafeCast(ucReason)
          continue
      # Phase 15 R2 (ADR-0010): a `new T` RHS is an ALLOCATION, not an ordinary
      # expression. Lower it to an `isNew` stmt per bound name — `freshRef` mints
      # a fresh `Ref_T` const for the let-name in the walker. The binding's
      # classified type is the `ref T` itself (`itRef(pointee)`), which is exactly
      # `mkNewT`'s `nRefTy` (the walker extracts the pointee for the ref sort).
      if isNewCall(valNode):
        for j in 0 ..< id.len - 2:
          let classified = classifyType(id[j])
          stmts.add mkNewT(id[j].strVal, classified.ty)
        continue
      let valIR = parseExpr(valNode, preamble, ctx)
      # Phase 15 Cluster C (C1): a proc-valued binding (`let f = proc(...) = …`)
      # has no scalar IRType — `classifyType` would reject the proc type. The
      # binding's value IR is an `iekLambda`; bind it under a placeholder type
      # (the walker stubs the `iekLambda` rvalue with `ceNotImplemented` before
      # the binding's type is ever consumed). C2a gives it a real closure type.
      if valIR != nil and valIR.kind in {iekLambda, iekClosureCall}:
        for j in 0 ..< id.len - 2:
          stmts.add mkLet(id[j].strVal, tBool(), valIR)
      else:
        for j in 0 ..< id.len - 2:
          let classified = classifyType(id[j])
          stmts.add mkLet(id[j].strVal, classified.ty, valIR)
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkCall, nnkCommand:
    # nnkCommand is the command-syntax form of a call (e.g.
    # `echo "x"` vs `echo("x")`). Same shape, same dispatch.
    if isMarkerCall(n, "symexTarget"):
      let argNode = n[1]
      if argNode.kind notin {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
        error("symex: `symexTarget` requires a string literal", argNode)
      mkTargetLabel(argNode.strVal)
    elif isMarkerCall(n, "symexAssert"):
      mkAssert(parseExpr(n[1], preamble, ctx))
    elif isMarkerCall(n, "symexAssume"):
      mkAssert(parseExpr(n[1], preamble, ctx))
    elif n.len >= 2 and n[0].kind == nnkSym and n[0].strVal in ["inc", "dec"] and
         (block:
            # Phase 15 R8 (ADR-0010). `inc`/`dec` are the `{.magic: Inc/Dec.}`
            # ordinal mutators. The GUARD keys on the RECEIVER's type so the
            # normal INT case is UNAFFECTED (it falls through to the int-mutator
            # arm below); ONLY a `ptr`-typed operand is pointer arithmetic. The
            # receiver may carry a semcheck `nnkHiddenAddr`/`nnkHiddenDeref`
            # (the `var T` formal) — unwrap before classifying.
            var recv = n[1]
            while recv.kind in {nnkHiddenAddr, nnkHiddenDeref, nnkHiddenStdConv} and
                  recv.len >= 1:
              recv = recv[recv.len - 1]
            classifyType(recv).ty.kind == itPtr):
      # Pointer arithmetic (`inc(p)`/`dec(p)` on a `ptr T`). The resulting
      # address is UNMODELABLE in the logical-heap model (the heap is keyed by
      # an abstract `Ref_T` address, not a numeric offset). Classify
      # `hePtrArith` (sevError) so the verdict degrades to `sxUnknown`
      # (Invariant 3 — never a silent sat/unsat) and emit `isUnsupported`. We do
      # NOT model the arithmetic.
      ctx.parseErrors.add SymexErrorInfo(
        kind: hePtrArith,
        severity: sevError,
        msg: "pointer arithmetic (inc/dec) not modeled")
      mkUnsupported("pointer arithmetic `" & n[0].strVal &
                    "` on a ptr operand is unsupported (Cluster R R8)")
    elif n.len >= 2 and n[0].kind == nnkSym and n[0].strVal in ["inc", "dec"] and
         (block:
            var recv = n[1]
            while recv.kind in {nnkHiddenAddr, nnkHiddenDeref, nnkHiddenStdConv} and
                  recv.len >= 1:
              recv = recv[recv.len - 1]
            recv.kind == nnkSym and classifyType(recv).ty.kind == itInt):
      # Phase 15 R8. `inc(i)`/`dec(i)` on an INT receiver — the normal ordinal
      # mutation. Lower to the equivalent env rebind `i = i ± y` (`y` defaults to
      # 1) so the int case symexes natively (the `{.magic.}` body is not walked).
      # This keeps inc/dec on int working `as before` while the ptr-operand guard
      # above peels off pointer arithmetic.
      var recv = n[1]
      while recv.kind in {nnkHiddenAddr, nnkHiddenDeref, nnkHiddenStdConv} and
            recv.len >= 1:
        recv = recv[recv.len - 1]
      let nm = recv.strVal
      let stepIR = if n.len >= 3: parseExpr(n[2], preamble, ctx) else: mkIntLit(1)
      let bop = if n[0].strVal == "inc": bAdd else: bSub
      mkAssign(nm, mkBinop(bop, mkVar(nm), stepIR))
    else:
      # User-proc call as a statement (void-return). Only resolvable
      # against typed AST — isolation-mode falls to `isUnsupported`.
      let calleeSym = n[0]
      if calleeSym.kind != nnkSym:
        mkUnsupported(&"call to `{n[0].repr}` not in supported fragment")
      # Phase 15 R13 (sub-track A). A CLOSURE CALL through a proc-valued
      # variable/param in STATEMENT position (e.g. `capture()` — a `let`-bound
      # closure called for its effect, with NO args). The expression-position
      # `earlyClosureCallDetect` only fires through `parseExpr`; a void-return
      # closure call reaches here. Detect it structurally (callee's impl is NOT
      # a routine def AND its type is `nnkProcTy`) and route to `iekClosureCall`
      # — the same C2b dispatch — so a captured ref/closure call symexes BEFORE
      # the `ensureProcRegistered` proc-call fall-through (which would
      # `getImpl`-fail on the variable's `nnkIdentDefs`).
      elif (block:
              let impl = calleeSym.getImpl
              impl.kind notin {nnkProcDef, nnkFuncDef, nnkIteratorDef,
                               nnkMethodDef, nnkConverterDef, nnkTemplateDef,
                               nnkMacroDef} and
                calleeSym.getTypeInst.kind == nnkProcTy):
        var argIRs: seq[IRExpr]
        for i in 1 ..< n.len:
          argIRs.add parseExpr(n[i], preamble, ctx)
        # The closure call is value-producing IR; in statement position its
        # EFFECTS (a `symexTarget`/write inside the lowered body) are what matter,
        # so bind it to a synthetic sink `let` (the `discardExn` idiom) — the
        # walker descends the closure body and the binding's value is dropped.
        mkLet(freshSynth(ctx, "closureCallSink"), tBool(),
              mkClosureCall(calleeSym.strVal, argIRs))
      else:
        let calleeName = calleeSym.strVal
        # Unwrap semcheck-inserted HiddenDeref / HiddenAddr / HiddenStdConv
        # on the first argument (receiver position for method-call syntax
        # like `s.add(v)`).
        proc unwrapHidden(x: NimNode): NimNode =
          var r = x
          while r.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv}:
            r = r[r.len - 1]
          r
        let recv1 = if n.len > 1: unwrapHidden(n[1]) else: nil
        let m = getStdlibModelFor(calleeName, itBool)  ## kind ignored
        if m.kind == smkOpaqueEffectful or hasSymexOpaquePragma(calleeSym):
          var argIRs: seq[IRExpr]
          for i in 1 ..< n.len:
            argIRs.add parseExpr(n[i], preamble, ctx)
          mkOpaqueCall(calleeName, "", argIRs, tBool())
        # #145 mutations recognised by name + receiver kind.
        elif recv1 != nil and recv1.kind == nnkSym:
          let recvName = recv1.strVal
          let recvCls = classifyType(recv1)
          # Phase 15 S11: `s.add(c)` / `s.add(otherStr)` — string APPEND on an
          # `itString` receiver. Z3 String theory strings are IMMUTABLE
          # (ADR-0006), so this mutation has no sound symbolic encoding and is
          # honestly classified `seUnsupportedStringOp` → `sxUnknown` (Invariant
          # 3 — never a silent UNSAT, never a crash). The reason is immutability,
          # NOT a byte/codepoint mismatch. Reuse the S9/S3 idiom (bind the
          # receiver to an `iekStrUnsupported` op whose residual `lower` arm
          # raises `SymexUnsupportedStringOpError`). This arm must precede the
          # `itSeq` `add` arm below (a string is NOT an itSeq, but the explicit
          # guard keeps the classification intentional and self-documenting).
          if calleeName == "add" and recvCls.ty.kind == itString and n.len == 3:
            let argIR = parseExpr(n[2], preamble, ctx)
            return mkAssign(recvName,
              mkStrOp(iekStrUnsupported, "string add",
                      @[mkVar(recvName), argIR]))
          # `s.add(v)` on a seq
          if calleeName == "add" and recvCls.ty.kind == itSeq and n.len == 3:
            let val = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSeqAdd(mkVar(recvName), val))
          # `s.del(i)` on a seq (Nim's swap-with-last)
          elif calleeName == "del" and recvCls.ty.kind == itSeq and n.len == 3:
            let idx = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSeqDel(mkVar(recvName), idx))
          # `s.insert(v, i)` on a seq
          elif calleeName == "insert" and recvCls.ty.kind == itSeq and n.len == 4:
            let val = parseExpr(n[2], preamble, ctx)
            let idx = parseExpr(n[3], preamble, ctx)
            mkAssign(recvName, mkSeqInsert(mkVar(recvName), val, idx))
          # `t.del(k)` on a Table
          elif calleeName == "del" and recvCls.ty.kind == itTable and n.len == 3:
            let key = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkTableDel(mkVar(recvName), key))
          # `s.incl(x)` on a HashSet
          elif calleeName == "incl" and recvCls.ty.kind == itSet and n.len == 3:
            let v = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSetIncl(mkVar(recvName), v))
          # `s.excl(x)` on a HashSet
          elif calleeName == "excl" and recvCls.ty.kind == itSet and n.len == 3:
            let v = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSetExcl(mkVar(recvName), v))
          # `[]=(t, k, v)` on a Table
          elif calleeName == "[]=" and recvCls.ty.kind == itTable and n.len == 4:
            let key = parseExpr(n[2], preamble, ctx)
            let val = parseExpr(n[3], preamble, ctx)
            mkAssign(recvName, mkTableSet(mkVar(recvName), key, val))
          else:
            let callKey = ensureProcRegistered(ctx, calleeSym, n)
            var argIRs: seq[IRExpr]
            for i in 1 ..< n.len:
              argIRs.add parseExpr(n[i], preamble, ctx)
            mkCall(callKey, "", argIRs, tBool())
        else:
          let callKey = ensureProcRegistered(ctx, calleeSym, n)
          var argIRs: seq[IRExpr]
          for i in 1 ..< n.len:
            argIRs.add parseExpr(n[i], preamble, ctx)
          mkCall(callKey, "", argIRs, tBool())
  of nnkDiscardStmt:
    # Phase 15 E8. A bare `discard <expr>` normally drops the value. But the
    # two exception-query magic intrinsics are EFFECTFUL in the symex model
    # (they validate the in-flight-handler context — out of a handler is a
    # classified `eeNotInHandler` — and `getCurrentException()` records its
    # opaque ref tag). So a `discard getCurrentException()` /
    # `discard getCurrentExceptionMsg()` must still be lowered. We bind the
    # discarded intrinsic to a synthetic sink `let` so the walker lowers it.
    # Any OTHER discarded expression is dropped (unchanged behaviour).
    if n.len == 1 and n[0].kind == nnkCall and n[0].len == 1 and
       n[0][0].kind == nnkSym and
       n[0][0].strVal in ["getCurrentException", "getCurrentExceptionMsg"]:
      let exprIR = parseExpr(n[0], preamble, ctx)
      let sinkTy = if n[0][0].strVal == "getCurrentExceptionMsg": tString()
                   else: tUninterp("")
      mkLet(freshSynth(ctx, "discardExn"), sinkTy, exprIR)
    else:
      mkBlock(@[])
  of nnkEmpty, nnkCommentStmt:
    mkBlock(@[])
  of nnkRaiseStmt:
    # Phase 15 E1. `raise newException(T, msg)` or bare `raise` (re-raise).
    # Typed-AST shape of `raise newException(ValueError, "x")`:
    #   RaiseStmt[ StmtListExpr[ Empty, ObjConstr[ Par[RefTy[Sym "T"]],
    #              ExprColonExpr[msg, <msgExpr>], ExprColonExpr[parent, nil] ]]]
    # Bare `raise`: RaiseStmt[Empty].
    if n.len == 0 or n[0].kind == nnkEmpty:
      mkReraise()
    else:
      var oc = n[0]
      while oc.kind in {nnkStmtListExpr, nnkStmtList} and oc.len > 0:
        oc = oc[oc.len - 1]
      if oc.kind == nnkObjConstr:
        var tn = oc[0]
        while tn.kind in {nnkPar, nnkRefTy, nnkPtrTy} and tn.len > 0:
          tn = tn[0]
        let typeId =
          if tn.kind in {nnkSym, nnkIdent}: tn.strVal else: tn.repr
        # Phase 15 E4a. Capture the RAISED type's inheritance chain (beyond the
        # RFC's nnkExceptBranch-only wording): a SUT may raise a user subtype
        # `MyError` here yet catch its stdlib base `ValueError` — the link only
        # appears at this raise site, so we must walk getImpl on `tn`.
        collectUserExnAncestors(tn, ctx)
        var msgIR: IRExpr = nil
        for k in 1 ..< oc.len:
          if oc[k].kind == nnkExprColonExpr and oc[k][0].repr == "msg":
            msgIR = parseExpr(oc[k][1], preamble, ctx)
        mkRaise(typeId, msgIR)
      else:
        # `raise <existing exception value>` (not the newException form) —
        # E1 has no value-tracking; classify so the walker stubs it.
        mkRaise(oc.repr, nil)
  of nnkTryStmt:
    # Phase 15 E1. `try: body  (except [T,…]: h)*  [finally: f]`.
    # Typed-AST shape: TryStmt[ <body>, ExceptBranch[<Type>* , <handlerBody>]*,
    #                  [Finally[<finallyBody>]] ]. A bare `except:` ExceptBranch
    # has no leading Type nodes (typeIds empty = catch-all).
    let tBody = parseStmt(n[0], ctx)
    var handlers: seq[ExceptHandler]
    var finallyBody: IRStmt = nil
    for k in 1 ..< n.len:
      let arm = n[k]
      case arm.kind
      of nnkExceptBranch:
        var typeIds: seq[string]
        for j in 0 ..< arm.len - 1:
          let tnode = arm[j]
          typeIds.add (if tnode.kind in {nnkSym, nnkIdent}: tnode.strVal
                       else: tnode.repr)
          # Phase 15 E4a. Capture the HANDLER type's inheritance chain too
          # (RFC §E4a's stated source) — e.g. a SUT catching a user base that
          # is itself a subtype of a stdlib exn.
          collectUserExnAncestors(tnode, ctx)
        handlers.add ExceptHandler(typeIds: typeIds,
                                   body: parseStmt(arm[arm.len - 1], ctx))
      of nnkFinally:
        finallyBody = parseStmt(arm[0], ctx)
      else:
        discard
    mkTry(tBody, handlers, finallyBody)
  else:
    mkUnsupported(&"statement kind {n.kind} not in supported fragment")

proc scanForHiddenMarkers(n: NimNode): seq[tuple[kind: string, name: string]] =
  ## Phase 14 cycle B67. Recursively scan a Nim sub-AST for
  ## `symexTarget(...)` / `symexAssert(...)` / `symexAssume(...)`
  ## calls so the parse-time diagnostic can list them when the
  ## statement they live in lands as `isUnsupported`. The IR scan
  ## can't see past `isUnsupported` (the body wasn't parsed), so
  ## this lives on the raw Nim AST.
  if n.isNil: return
  if n.kind in {nnkCall, nnkCommand}:
    if n.len >= 1 and n[0].kind in {nnkIdent, nnkSym}:
      let nm = n[0].strVal
      if nm in ["symexTarget", "symexAssert", "symexAssume"]:
        var arg = ""
        if n.len >= 2 and n[1].kind in {nnkStrLit..nnkTripleStrLit}:
          arg = n[1].strVal
        result.add (kind: nm, name: arg)
  for child in n: result.add scanForHiddenMarkers(child)

proc parseStmt*(n: NimNode, ctx: ParseCtx): IRStmt =
  var preamble: seq[IRStmt]
  let inner = parseStmtInner(n, preamble, ctx)
  # Phase 14 B67. If a parse landed on `isUnsupported`, scan the
  # raw Nim sub-AST for symex markers and emit a {.hint.} for each
  # so the user knows their target/assert is invisible to the
  # analysis. Does NOT close Phase 12 deferral #3 — semantics are
  # unchanged; markers are still ignored — but observability is up.
  if inner != nil and inner.kind == isUnsupported:
    for m in scanForHiddenMarkers(n):
      let arg = if m.name.len > 0: "(\"" & m.name & "\")" else: "(...)"
      hint("symex: `" & m.kind & arg & "` is inside an unsupported " &
           "statement (" & inner.reason & ") and will NOT be " &
           "discovered by symex analysis", n)
  if preamble.len == 0:
    inner
  else:
    mkBlock(preamble & @[inner])

# ---- Untyped-friendly wrappers for the DSL isolation tests -------------------
#
# Phase 1's tsymex_phase1_dsl tests call `parseExpr(node)` / `parseStmt(node)`
# with no ctx. We preserve those signatures by creating a throwaway ctx.

proc parseExpr*(n: NimNode): IRExpr =
  var preamble: seq[IRStmt]
  let ctx = newParseCtx()
  let e = parseExpr(n, preamble, ctx)
  if preamble.len > 0:
    error("symex: isolation parseExpr cannot lift A-normalised calls; " &
          "the input contains a user-proc call which only the full " &
          "parseProc/parseStmt entry points handle.", n)
  e

proc parseStmt*(n: NimNode): IRStmt =
  parseStmt(n, newParseCtx())

# ---- Callee resolution -------------------------------------------------------

proc parseCalleeImpl(impl: NimNode, ctx: ParseCtx,
                     typeSubst: Table[string, NimNode] =
                       initTable[string, NimNode]()): ProcSig

# ---- Phase 15 G6: stdlib concept membership (trust boundary) ---------------
#
# Nim's standard type-class concepts are closed, statically-known sets of
# concrete types. We mirror them as a compile-time membership table so a
# concept-constrained generic instantiated at a NON-conforming concrete type
# emits `geConceptViolation` at parse time (Invariant 3 — never silent).
#
# TRUST BOUNDARY: this table covers ONLY the stdlib concepts below. A
# USER-DEFINED concept name is NOT in the table; `conformsToStdlibConcept`
# returns `true` (= "no violation to assert") for it, so the parse-time
# validator SKIPS it and TRUSTS the Nim semchecker, which already enforced the
# constraint at the call site before the macro saw the typed AST. From REAL
# Nim source the semchecker likewise guarantees stdlib-concept conformance, so
# the stdlib check here is belt-and-suspenders — it is the test-injectable
# Invariant-3 guard, and never fires on real source.

const
  someUnsignedIntTypes = ["uint", "uint8", "uint16", "uint32", "uint64"]
  someSignedIntTypes   = ["int", "int8", "int16", "int32", "int64"]
  someFloatTypes       = ["float", "float32", "float64"]
  # `SomeOrdinal` = signed ints + unsigned ints + char + bool + enums. We list
  # the closed scalar members; enum types are recognised structurally below.
  someOrdinalExtra     = ["char", "bool"]

proc stdlibConceptMembers(conceptName: string): seq[string] =
  ## The concrete type names that satisfy a stdlib type-class concept.
  ## Empty seq ⇒ `conceptName` is NOT a known stdlib concept (→ user-defined,
  ## trusted to the semchecker).
  case conceptName
  of "SomeUnsignedInt": @someUnsignedIntTypes
  of "SomeSignedInt":   @someSignedIntTypes
  of "SomeInteger":     @someSignedIntTypes & @someUnsignedIntTypes
  of "SomeFloat":       @someFloatTypes
  of "SomeNumber":      @someSignedIntTypes & @someUnsignedIntTypes &
                        @someFloatTypes
  of "SomeOrdinal":     @someSignedIntTypes & @someUnsignedIntTypes &
                        @someOrdinalExtra
  else:                 @[]

proc isStdlibConcept*(conceptName: string): bool =
  ## True iff `conceptName` is one of the stdlib type-class concepts G6
  ## validates. A `false` here means "trust the semchecker" (user concept).
  stdlibConceptMembers(conceptName).len > 0

proc isEnumTypeNode*(node: NimNode): bool =
  ## CR-15: structural recognition of user enum types. Returns true iff `node`
  ## is a typed AST node whose `getImpl` is an nnkTypeDef over an nnkEnumTy (and
  ## is not `bool`, which is enum-shaped but handled separately). Used by
  ## `conformsToStdlibConcept` to allow user enums for `SomeOrdinal` — Nim's
  ## semchecker already guarantees a `T: SomeOrdinal` call site is valid, and
  ## user enums ARE ordinal types (Nim's definition of SomeOrdinal explicitly
  ## includes enum types). This is purely a TRUST check (the semchecker already
  ## validated the constraint at the call site); adding structural detection just
  ## prevents a spurious `geConceptViolation` in the Invariant-3 guard.
  if node == nil: return false
  let sym = try:
    if node.kind in {nnkSym, nnkIdent}: node
    else: node.getTypeInst
  except: return false
  if sym.kind notin {nnkSym, nnkIdent}: return false
  let impl = try: sym.getImpl except: return false
  if impl.kind != nnkTypeDef or impl.len < 3: return false
  if impl[2].kind != nnkEnumTy: return false
  # Exclude `bool` — it is enum-shaped in the typed AST but is already in
  # someOrdinalExtra as an explicit member, so no special case needed for it.
  let nm = if sym.kind in {nnkSym, nnkIdent}: sym.strVal else: sym.repr
  nm != "bool"

proc conformsToStdlibConcept*(conceptName, resolvedTypeName: string): bool =
  ## The single conformance-check entry point used both by the parse-time
  ## validator (`parseCalleeImpl`) AND by the G6 negative test (which injects a
  ## non-conforming pair directly — there is NO `isGenericCall` IR node to
  ## malform, so this helper IS the real, test-reachable check).
  ##
  ## Returns:
  ##   * for a STDLIB concept: `true` iff `resolvedTypeName` is a member;
  ##   * for a USER-DEFINED (non-stdlib) concept: ALWAYS `true` — there is no
  ##     violation to assert (the semchecker already validated it). This is the
  ##     trust boundary made explicit.
  ##
  ## NOTE: for `SomeOrdinal` with a user enum type, see the call site in
  ## `parseCalleeImpl` — structural enum detection via `isEnumTypeNode` runs
  ## BEFORE this helper and short-circuits to `true` (no violation) when the
  ## resolved node is a user enum. This string-based overload thus never sees
  ## user enum names; the Invariant-3 guard remains intact for non-enum types.
  let members = stdlibConceptMembers(conceptName)
  if members.len == 0:
    return true   ## user-defined concept → trust the semchecker
  resolvedTypeName in members

proc monomorphize(node: NimNode, subst: Table[string, NimNode]): NimNode =
  ## Walk `node`, replacing `Ident "T"` references with the concrete
  ## type node when `T` is in the substitution map. Used to lower a
  ## generic proc body to its monomorphic form before parsing.
  if node.kind in {nnkIdent, nnkSym} and node.strVal in subst:
    return subst[node.strVal]
  if node.kind in {nnkEmpty} or node.len == 0:
    return node
  result = newTree(node.kind)
  if node.kind == nnkSym:
    return node
  for c in node:
    result.add monomorphize(c, subst)

proc hasGenericParams(impl: NimNode): bool =
  ## True when `impl` (an `nnkProcDef`) carries generic params. In the typed
  ## AST these live either in `impl[2]` (untyped form) or nested in
  ## `impl[5][1]` (typed form). Shared by `gatherTypeSubst`,
  ## `ensureProcRegistered`, and `instKeyFor` so the three agree on what
  ## "generic" means.
  if impl.kind != nnkProcDef: return false
  (impl[2].kind == nnkGenericParams) or
    (impl[5].kind == nnkBracket and impl[5].len >= 2 and
     impl[5][1].kind == nnkGenericParams)

proc genericParamsNode(impl: NimNode): NimNode =
  ## The `nnkGenericParams` node of a generic `impl`, or `nil`. Shared so
  ## `gatherTypeSubst` and `staticParamNames` read the same location.
  if impl.kind != nnkProcDef: return nil
  if impl[2].kind == nnkGenericParams: return impl[2]
  if impl[5].kind == nnkBracket and impl[5].len >= 2 and
     impl[5][1].kind == nnkGenericParams: return impl[5][1]
  nil

proc staticParamNames(impl: NimNode): HashSet[string] =
  ## Phase 15 G7. The names of generic params whose CONSTRAINT is `static[T]`.
  ## In the typed generic-params AST the constraint surfaces as an
  ## `nnkCommand[Ident "static", <T>]` (probed on the typed AST — NOT the
  ## `nnkStaticTy` the RFC §G7 GREEN guessed; `nnkStaticTy` is the untyped /
  ## `static[int]`-bracket form, which we also accept defensively).
  result = initHashSet[string]()
  let gp = genericParamsNode(impl)
  if gp == nil: return
  for idDefs in gp:
    if idDefs.kind != nnkIdentDefs: continue
    let constraint = idDefs[idDefs.len - 2]
    let isStatic =
      (constraint.kind == nnkStaticTy) or
      (constraint.kind == nnkCommand and constraint.len == 2 and
       constraint[0].kind in {nnkIdent, nnkSym} and
       constraint[0].strVal == "static")
    if isStatic:
      for i in 0 ..< idDefs.len - 2:
        result.incl idDefs[i].strVal

proc gatherTypeSubst(callSite: NimNode, impl: NimNode): Table[string, NimNode] =
  result = initTable[string, NimNode]()
  if impl.kind != nnkProcDef: return
  # Generic params live in impl[2] (untyped) or impl[5][1] (typed).
  var genericNames: HashSet[string]
  var gpNode: NimNode = nil
  if impl[2].kind == nnkGenericParams:
    gpNode = impl[2]
  elif impl[5].kind == nnkBracket and impl[5].len >= 2 and
       impl[5][1].kind == nnkGenericParams:
    gpNode = impl[5][1]
  if gpNode != nil:
    for gp in gpNode:
      if gp.kind == nnkIdentDefs:
        for i in 0 ..< gp.len - 2:
          genericNames.incl gp[i].strVal
  if genericNames.len == 0: return
  # Phase 15 G7: `static[T]` params (e.g. `N` in `proc foo[N: static int]`).
  # Their VALUE is a compile-time constant; Nim's semchecker has already baked
  # it into the proc BODY (`x[N-1]` → `x[2]`), so the body needs no further
  # substitution. The one un-substituted spot is a FORMAL param TYPE that names
  # the static param as an array DIMENSION (`array[N, int]`), which
  # `classifyType` cannot size until `N` resolves to a literal. We recover the
  # literal from the matching ARRAY ARG's range type below.
  let staticNames = staticParamNames(impl)
  proc staticValFromArrayArg(formalTy, argTy: NimNode, sname: string): NimNode =
    ## If `formalTy` is `array[<sname>, _]`, read the concrete dimension from
    ## `argTy` (`array[range[lo..hi], _]` after `getType`) and return it as an
    ## `nnkIntLit`; else nil.
    if formalTy.kind != nnkBracketExpr or formalTy.len != 3: return nil
    if not (formalTy[0].kind in {nnkIdent, nnkSym} and
            formalTy[0].strVal == "array"): return nil
    if not (formalTy[1].kind in {nnkIdent, nnkSym} and
            formalTy[1].strVal == sname): return nil
    if argTy.kind != nnkBracketExpr or argTy.len != 3: return nil
    let idx = argTy[1]
    # `getType` renders the index as `range[lo .. hi]` (a BracketExpr) or, in
    # some forms, a bare `lo .. hi` Infix.
    var lo, hi: NimNode = nil
    if idx.kind == nnkBracketExpr and idx.len == 3 and
       idx[0].kind in {nnkIdent, nnkSym} and idx[0].strVal == "range":
      lo = idx[1]; hi = idx[2]
    elif idx.kind == nnkInfix and idx.len == 3 and idx[0].strVal == "..":
      lo = idx[1]; hi = idx[2]
    if lo != nil and hi != nil and
       lo.kind in nnkIntLit..nnkInt64Lit and hi.kind in nnkIntLit..nnkInt64Lit:
      return newLit(int(hi.intVal - lo.intVal + 1))
    nil
  # Phase 15 G3: a formal type may WRAP the generic param in an ownership /
  # lvalue annotation — `var T`, `sink T`, `lent T`. The typed AST presents
  # these as `nnkVarTy[T]` or (for sink/lent) `nnkBracketExpr[sink|lent, T]`.
  # Unwrap them so the BARE generic name is recovered and `T` actually binds
  # (without this, `proc foo[T](x: sink T)` never records `T` and the body's
  # `T` references stay un-monomorphised → `classifyType` errors on `T`).
  proc unwrapGenericTy(n: NimNode): NimNode =
    if n.kind == nnkVarTy and n.len == 1:
      return unwrapGenericTy(n[0])
    # `sink T` / `lent T` present in the typed generic AST as an
    # `nnkCommand[sink|lent, T]` (NOT a bracket — see G3 AST dump); a
    # post-substitution form may also surface as `nnkBracketExpr`.
    if n.kind in {nnkBracketExpr, nnkCommand} and n.len == 2 and
       n[0].kind in {nnkIdent, nnkSym} and n[0].strVal in ["sink", "lent"]:
      return unwrapGenericTy(n[1])
    n
  let formal = impl[3]
  # Walk formal params, matching to call args
  var argIx = 1   ## skip n[0] = callee
  for i in 1 ..< formal.len:
    let id = formal[i]
    let rawTy = id[id.len - 2]
    let tyNode = unwrapGenericTy(rawTy)
    for j in 0 ..< id.len - 2:
      if argIx < callSite.len:
        let argTy = callSite[argIx].getType
        if tyNode.kind in {nnkIdent, nnkSym} and tyNode.strVal in genericNames:
          result[tyNode.strVal] = argTy
        else:
          # Phase 15 G7: a STATIC param used as an array dimension
          # (`array[N, int]`). Bind `N` to its concrete literal so
          # `monomorphize` rewrites the formal to `array[3, int]` (which
          # `classifyType` can size) and any residual body `N` to the literal.
          for sname in staticNames:
            let v = staticValFromArrayArg(rawTy, argTy, sname)
            if v != nil:
              result[sname] = v
      inc argIx

proc bodyHashPart(calleeSym, impl: NimNode): string =
  ## Module-disambiguating stable identity for a proc body (ADR-0008 D2).
  ## `symBodyHash` encodes the full module path + body identity, so two
  ## same-named procs in different modules hash differently. The `lineInfo`
  ## fallback (file path + proc name) preserves module disambiguation when
  ## `symBodyHash` is unavailable/empty; it is NOT `repr.hash` (structurally
  ## ambiguous across modules — ADR-0008 Alt 2).
  if calleeSym.kind == nnkSym:
    let h = symBodyHash(calleeSym)
    if h.len > 0: return h
  impl.lineInfoObj.filename & ":" & calleeSym.strVal

proc instKeyFor(calleeSym: NimNode, typeSubst: Table[string, NimNode],
                impl: NimNode): string =
  ## The instantiation key under which a (callee, concrete-type-tuple) pair is
  ## registered in `ctx.procs` AND dispatched by the walker (`mkCall` callee
  ## name). Registration and dispatch MUST compute this identically, so both
  ## go through THIS one proc.
  ##
  ## Non-generic procs (empty `typeSubst`) → bare proc name, preserving the
  ## pre-G1a behavior exactly. Generic procs → `name#<bodyHash>#<typeTuple>`
  ## where the type tuple is sorted by formal-param name (ADR-0008 D2/D6:
  ## order-independent canonical identity) so two instantiations at the same
  ## types share one entry, and two instantiations at DIFFERENT types do not
  ## collide on the bare name (the G1a bug).
  ##
  ## Phase 15 G7: a `static[T]` param's VALUE is part of the instantiation
  ## identity, so two static instantiations (`foo[3]`/`foo[5]`) must NOT share
  ## a key. When the static value is bound as an array dimension it is already
  ## in `typeSubst` (`N=3` vs `N=5` → distinct type tuples). When it is a
  ## SCALAR static param (`bar[N: static int](x:int)` / `gate[B: static bool]`)
  ## it appears in NO formal-type position, so `typeSubst` stays EMPTY — but
  ## Nim instantiates each value as a DISTINCT symbol whose `symBodyHash`
  ## differs (the literal is baked into the body), so we discriminate on that
  ## bodyHash. RECONCILIATION NOTE: the RFC §G7 asserts the exact key string
  ## `"foo#int;static=3"`; the REAL key carries a per-instantiation `bodyHash`
  ## (`name#<bodyHash>#<tuple>` or `name#<bodyHash>#static`), so the test asserts
  ## BEHAVIOR (distinct dispatch + per-instantiation literal), not that string.
  let name = calleeSym.strVal
  if typeSubst.len == 0:
    if staticParamNames(impl).len > 0:
      # Scalar static param: force a per-instantiation-distinct, non-bare key.
      return name & "#" & bodyHashPart(calleeSym, impl) & "#static"
    return name
  var keys: seq[string]
  for k in typeSubst.keys: keys.add k
  keys.sort()
  var parts: seq[string]
  for k in keys:
    parts.add k & "=" & typeSubst[k].repr
  name & "#" & bodyHashPart(calleeSym, impl) & "#" & parts.join(";")

proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode,
                          callSite: NimNode = nil): string =
  ## Registers the (monomorphized) callee under its instantiation key and
  ## returns that key. The CALLER must use the returned key as the `mkCall`
  ## callee name so the walker's `w.procs[stmt.callee]` dispatch lands on the
  ## exact `ProcSig` registered here (G1a: registration and dispatch share one
  ## key).
  if calleeSym.kind notin {nnkSym, nnkIdent}:
    error("symex Phase 3: callee position is not a symbol — got " &
          $calleeSym.kind & " in `" & calleeSym.repr & "`", calleeSym)
  let name = calleeSym.strVal
  let impl = calleeSym.getImpl
  if impl.kind != nnkProcDef:
    error("symex Phase 3: cannot resolve `getImpl` for callee `" & name &
          "` — generic / private cross-module / built-in?", calleeSym)
  # Phase 15 G5. `geDistinctBarrier` (Invariant 3 — never a silent fallback). A
  # NON-borrowed proc taking a `distinct T` param whose body is NOT parseable
  # (`impl[6] == nnkEmpty`, e.g. an `{.importc.}` / magic on a distinct type)
  # cannot be walked: the type wall forbids silently treating the distinct value
  # as its base. (A `{.borrow.}` op IS routed through the borrow path at parse
  # time and never reaches `ensureProcRegistered`, so this fires only for the
  # genuine no-borrow, no-body case.) Emit `geDistinctBarrier` (sevError) and do
  # NOT register — the call's `mkCall` key is absent from `w.procs`, so the
  # walker's missing-callee arm degrades the path to sxUnknown, and the sevError
  # forces the verdict to sxUnknown (never silent).
  if impl[6].kind == nnkEmpty and not hasBorrowPragma(impl):
    let formal = impl[3]
    var distinctParam = ""
    if formal.kind == nnkFormalParams:
      for i in 1 ..< formal.len:
        let id = formal[i]
        if id.kind == nnkIdentDefs:
          let pc = classifyType(id[id.len - 2])
          if pc.ty.kind == itDistinct:
            distinctParam = pc.ty.distinctName
            break
    if distinctParam.len > 0:
      ctx.parseErrors.add SymexErrorInfo(
        kind: geDistinctBarrier,
        severity: sevError,
        msg: "proc `" & name & "` operates on distinct type `" & distinctParam &
             "` with no parseable body and no `{.borrow.}` pragma — the " &
             "distinct type wall forbids walking it (Invariant 3); result is " &
             "sxUnknown")
      return instKeyFor(calleeSym, initTable[string, NimNode](), impl)
  # Detect generic procs. In typed AST, the generic-params live in
  # impl[2] (untyped) or nested in impl[5] (typed). Either way, we
  # use the call's `getType` reads to derive the substitution.
  var typeSubst: Table[string, NimNode]
  if hasGenericParams(impl) and callSite != nil:
    typeSubst = gatherTypeSubst(callSite, impl)
  let key = instKeyFor(calleeSym, typeSubst, impl)
  if key in ctx.procs or key in ctx.parsing:
    return key  ## already known, or actively being parsed (mutual-recursion)
  # Phase 15 G1c (ADR-0008 D7 / OQ5): per-BASE-proc instantiation cap. Every
  # DISTINCT instantiation of ONE generic proc shares a counter (keyed by the
  # generic's definition site, below) while different generic procs count
  # independently. A non-generic proc has exactly one instKey (empty typeSubst)
  # and trivially never exceeds the cap.
  let cap = ctx.maxInstantiationsPerProc
  if cap > 0:
    # Base-proc identity must be STABLE across instantiations of the SAME
    # generic, so the per-proc counter actually accumulates. `symBodyHash`
    # (used by `bodyHashPart` for the instKey) is per-INSTANTIATION (each
    # monomorphized `szof[int8]`/`szof[int16]` symbol hashes differently), so
    # it CANNOT key the base count. The generic's DEFINITION site —
    # `lineInfoObj` (file:line:column) — is invariant across instantiations
    # (verified: all three `szof` calls report the one `szof[T]` def line) and
    # is module-disambiguating (the file path differs across modules), so it is
    # the correct base identity. Proc name is included for readability.
    let li = impl.lineInfoObj
    let baseId = name & "#" & li.filename & ":" & $li.line & ":" & $li.column
    let prior = ctx.instCounts.getOrDefault(baseId, 0)
    if prior >= cap:
      # Over-cap: do NOT register this instantiation. The call site still emits
      # `mkCall` with `key`, which is absent from `w.procs`, so the walker's
      # missing-callee arm sets `w.sawUnknown = true` → sxUnknown. We attach a
      # `geInstantiationCapped` (sevError) so the unknown is never silent
      # (Invariant 3). `observedCount`/`procSym` live in `msg` (the
      # `SymexErrorInfo` record carries no dedicated fields for them).
      ctx.parseErrors.add SymexErrorInfo(
        kind: geInstantiationCapped,
        severity: sevError,
        msg: "generic proc `" & name & "` exceeded maxInstantiationsPerProc=" &
             $cap & " (observedCount=" & $(prior + 1) & "); instantiation `" &
             key & "` not registered — result is sxUnknown")
      return key
    ctx.instCounts[baseId] = prior + 1
  ctx.parsing.incl key
  let sig = parseCalleeImpl(impl, ctx, typeSubst)
  ctx.procs[key] = sig
  ctx.parsing.excl key
  key

proc parseCalleeImpl(impl: NimNode, ctx: ParseCtx,
                     typeSubst: Table[string, NimNode] =
                       initTable[string, NimNode]()): ProcSig =
  ## Build a `ProcSig` from a callee's `nnkProcDef`. Recursively parses
  ## the body; the parsing-set in `ctx` short-circuits mutual recursion.
  ## For generic procs, `typeSubst` carries `T → concreteTypeNode`
  ## bindings; types and the body are monomorphised before parsing.
  impl.expectKind nnkProcDef
  let monoImpl = if typeSubst.len > 0: monomorphize(impl, typeSubst)
                 else: impl
  # Phase 15 G6: capture concept constraints + validate stdlib conformance.
  # Generic params live in `impl[2]` (untyped) or `impl[5][1]` (typed) on the
  # ORIGINAL (pre-monomorphize) impl. For each `nnkIdentDefs` whose constraint
  # node (`gp[gp.len-2]`) is NOT `nnkEmpty` (i.e. `T: SomeConcept`), record the
  # constraint sym name; then, for STDLIB concepts, validate the RESOLVED
  # concrete type bound to that param (from `typeSubst`) against the membership
  # table. A non-conforming binding → `geConceptViolation` (sevError) into
  # `ctx.parseErrors` (G1c/G5 plumbing → sxUnknown). USER-DEFINED concepts are
  # trusted to the semchecker (`conformsToStdlibConcept` returns true for them).
  var conceptConstraints: seq[string]
  block captureConstraints:
    var gpNode: NimNode = nil
    if impl[2].kind == nnkGenericParams:
      gpNode = impl[2]
    elif impl[5].kind == nnkBracket and impl[5].len >= 2 and
         impl[5][1].kind == nnkGenericParams:
      gpNode = impl[5][1]
    if gpNode == nil: break captureConstraints
    for gp in gpNode:
      if gp.kind != nnkIdentDefs: continue
      let constraintNode = gp[gp.len - 2]
      if constraintNode.kind == nnkEmpty: continue   ## bare `T` — no constraint
      # The constraint may be a single sym (`SomeNumber`) or a compound the
      # semchecker already elaborated (`A and B` → nnkInfix). We capture the
      # constraint's textual form and, for a single stdlib-concept sym, validate.
      let constraintName =
        if constraintNode.kind in {nnkIdent, nnkSym}: constraintNode.strVal
        else: constraintNode.repr
      # Each generic param name carried by this IdentDefs.
      for i in 0 ..< gp.len - 2:
        let paramName =
          if gp[i].kind in {nnkIdent, nnkSym}: gp[i].strVal else: gp[i].repr
        conceptConstraints.add constraintName
        # Validate stdlib conformance of the resolved concrete type, if known.
        if paramName in typeSubst and isStdlibConcept(constraintName):
          # The resolved type's leaf name. `monomorphize` substituted a typed
          # type node; its `repr` is the concrete type name (e.g. "int").
          let resolvedNode = typeSubst[paramName]
          let resolved = resolvedNode.repr
          # CR-15: user enum types satisfy `SomeOrdinal` structurally (Nim's
          # semchecker already validated the constraint at the call site). Detect
          # an enum type via `isEnumTypeNode` and skip the violation guard for
          # `SomeOrdinal` — a user enum IS an ordinal type; emitting a spurious
          # `geConceptViolation` here is over-conservative (safe direction, but
          # incorrect: valid programs yielding sxUnknown instead of sxSat).
          let isOrdinalEnum = constraintName == "SomeOrdinal" and
                              isEnumTypeNode(resolvedNode)
          if not isOrdinalEnum and not conformsToStdlibConcept(constraintName, resolved):
            ctx.parseErrors.add SymexErrorInfo(
              kind: geConceptViolation,
              severity: sevError,
              msg: "generic param `" & paramName & "` of proc `" &
                   impl.name.strVal & "` is constrained by stdlib concept `" &
                   constraintName & "` but was instantiated at non-conforming " &
                   "type `" & resolved & "` — result is sxUnknown (Invariant 3)")
  let formal = monoImpl[3]
  formal.expectKind nnkFormalParams
  # Params
  var params: seq[IRParam]
  for i in 1 ..< formal.len:
    let id = formal[i]
    id.expectKind nnkIdentDefs
    let tyNode = id[id.len - 2]
    let cls = classifyType(tyNode)
    let isVar = tyNode.kind == nnkVarTy
    for j in 0 ..< id.len - 2:
      params.add IRParam(name: id[j].strVal, ty: cls.ty,
                         rangeLo: cls.range.lo,
                         rangeHi: cls.range.hi,
                         hasRange: cls.range.hasRange,
                         isVar: isVar)
  # Return type
  var retTy = tBool()
  var isVoid = true
  if formal[0].kind != nnkEmpty:
    let cls = classifyType(formal[0])
    retTy = cls.ty
    isVoid = false
  else:
    # Phase 15 G3 auto-return guard. A monomorphised proc whose return node is
    # `nnkEmpty` is ordinarily a genuine `void` proc. But if the ORIGINAL impl
    # DECLARED a (generic / `auto`) return type that vanished to `nnkEmpty`
    # under substitution, that is a type-substitution FAILURE — Nim's
    # semchecker resolves `auto` to a concrete type before `getImpl`, so a
    # surviving `nnkEmpty` means the resolution did not happen and a default
    # would be unsound (Invariant 3 — never silently fall back). Error cleanly
    # instead of treating it as `void`. (Defensive: not expected to fire under
    # the current semcheck-then-getImpl pipeline.)
    if impl[3].kind == nnkFormalParams and impl[3][0].kind != nnkEmpty:
      error("symex G3: type-substitution produced nnkEmpty retTy for proc `" &
            impl[0].repr & "` (declared return `" & impl[3][0].repr &
            "` did not resolve to a concrete type under monomorphization)",
            impl)
  # Body. Value-returning Nim procs of the form
  #
  #     proc f(...): T = expr
  #
  # semcheck to `result = expr`. We detect this single-assignment-to-
  # result shape and rewrite as `return expr` so the runtime walker
  # doesn't need to model `result` as a mutable local for cycle 1.
  # Procs with conditional / multi-step result-assignment land via
  # the general parser path (parseStmt below) — those cases need
  # cycle-2 work to model `result` as a mutable binding.
  let bodyNode = monoImpl[6]
  proc resultRhs(n: NimNode): NimNode =
    ## If `n` is a single `result = expr` assignment (possibly wrapped
    ## in a one-element nnkStmtList), return the expr; else nil.
    let inner = if n.kind == nnkStmtList and n.len == 1: n[0] else: n
    if inner.kind == nnkAsgn and
       inner[0].kind == nnkSym and inner[0].strVal == "result":
      inner[1]
    else:
      nil
  let rhs = if isVoid: nil else: resultRhs(bodyNode)
  let body =
    if rhs != nil:
      # `proc f(...): T = expr` shape: rewrite as `return expr`.
      var preamble: seq[IRStmt]
      let valIR = parseExpr(rhs, preamble, ctx)
      if preamble.len == 0:
        mkReturnVal(valIR)
      else:
        # Phase 15 G7: the single-expr RHS A-normalised into preamble
        # statements (e.g. an array index `x[N-1]` lifts a bounds-checked
        # element read). Emit the preamble before the return rather than
        # asserting it away — the value is still `valIR`.
        mkBlock(preamble & @[mkReturnVal(valIR)])
    else:
      parseStmt(bodyNode, ctx)
  let nameStr = monoImpl.name.strVal
  ProcSig(name: nameStr, params: params, body: body,
          retTy: retTy, isVoid: isVoid,
          conceptConstraints: conceptConstraints)   ## Phase 15 G6

# ---- Top-level: procDef → SymexProgram-emitting NimNode ----------------------

type
  ParseResult* = object
    params*: seq[IRParam]
    bodyNimNode*: NimNode
    paramsNimNode*: NimNode
    procsNimNode*: NimNode    ## emit-time AST: yields `Table[string, ProcSig]`
                              ## with all transitively-reachable callees
    body*: IRStmt             ## Phase 12 cycle 7: parsed IR body, kept
                              ## as a Nim value at macro time so the
                              ## `irHasAssert` / `irHasIndex` /
                              ## `irHasVariantField` / `irCollectLabels`
                              ## scan helpers can inspect it directly
                              ## without re-parsing.
    procs*: Table[string, ProcSig]
                              ## Macro-time copy of the callee table so
                              ## the cycle-4 scan helpers can recurse
                              ## through `isCall` bodies. Mirrors the
                              ## emit-time AST in `procsNimNode`.
    userExnHierarchyNimNode*: NimNode
                              ## Phase 15 E4a. Emit-time AST yielding a
                              ## `Table[string, string]` of captured
                              ## child -> parent user-exn links.
    parseErrorsNimNode*: NimNode
                              ## Phase 15 G1c. Emit-time AST yielding a
                              ## `seq[SymexErrorInfo]` of parse-time errors
                              ## (generic instantiation-cap overflow). Threaded
                              ## into `SymexProgram.parseErrors`.

proc emitParam(p: IRParam): NimNode =
  newTree(nnkObjConstr,
    bindSym"IRParam",
    newColonExpr(ident"name",     newLit(p.name)),
    newColonExpr(ident"ty",       emitIRType(p.ty)),
    newColonExpr(ident"rangeLo",  newLit(p.rangeLo)),
    newColonExpr(ident"rangeHi",  newLit(p.rangeHi)),
    newColonExpr(ident"hasRange", newLit(p.hasRange)),
    newColonExpr(ident"isVar",    newLit(p.isVar)))

proc emitParamSeq(ps: seq[IRParam]): NimNode =
  var lit = newTree(nnkBracket)
  for p in ps:
    lit.add emitParam(p)
  prefix(lit, "@")

proc emitProcSig(sig: ProcSig): NimNode =
  newTree(nnkObjConstr,
    bindSym"ProcSig",
    newColonExpr(ident"name",    newLit(sig.name)),
    newColonExpr(ident"params",  emitParamSeq(sig.params)),
    newColonExpr(ident"body",    emitStmt(sig.body)),
    newColonExpr(ident"retTy",   emitIRType(sig.retTy)),
    newColonExpr(ident"isVoid",  newLit(sig.isVoid)))

proc emitProcs(procs: Table[string, ProcSig]): NimNode =
  ## Emit a Table[string, ProcSig] builder. Uses a `block:` with an
  ## explicit assignment per entry — the Nim literal syntax for Table
  ## values via `{ … }.toTable` is brittle for object-rich payloads.
  let tableId = genSym(nskVar, "tbl")
  result = newStmtList()
  result.add newVarStmt(tableId,
    newCall(newTree(nnkBracketExpr, bindSym"initTable",
                                     ident"string", bindSym"ProcSig")))
  for name, sig in procs:
    result.add newAssignment(
      newTree(nnkBracketExpr, tableId, newLit(name)),
      emitProcSig(sig))
  result.add tableId
  result = newTree(nnkBlockStmt, newEmptyNode(), result)

proc emitStrStrTable(t: Table[string, string]): NimNode =
  ## Phase 15 E4a. Emit a `Table[string, string]` builder (child -> parent
  ## user-exn links). Same `block:` + per-entry assignment shape as
  ## `emitProcs`, which is robust for object-rich payloads.
  let tableId = genSym(nskVar, "uxh")
  result = newStmtList()
  result.add newVarStmt(tableId,
    newCall(newTree(nnkBracketExpr, bindSym"initTable",
                                     ident"string", ident"string")))
  for child, parent in t:
    result.add newAssignment(
      newTree(nnkBracketExpr, tableId, newLit(child)),
      newLit(parent))
  result.add tableId
  result = newTree(nnkBlockStmt, newEmptyNode(), result)

proc emitErrorSeq(errs: seq[SymexErrorInfo]): NimNode =
  ## Phase 15 G1c. Emit a `seq[SymexErrorInfo]` literal of parse-time errors
  ## (generic instantiation-cap overflow). `kind`/`severity` are enum members
  ## (emitted by name via `ident`); `msg` is a string literal.
  var br = newTree(nnkBracket)
  for e in errs:
    br.add nnkObjConstr.newTree(
      bindSym"SymexErrorInfo",
      newColonExpr(ident"kind", ident($e.kind)),
      newColonExpr(ident"severity", ident($e.severity)),
      newColonExpr(ident"msg", newLit(e.msg)))
  prefix(br, "@")

proc parseProc*(procDef: NimNode, maxInstantiationsPerProc = 0): ParseResult =
  procDef.expectKind nnkProcDef
  let formalParams = procDef[3]
  formalParams.expectKind nnkFormalParams
  let ctx = newParseCtx(maxInstantiationsPerProc)
  var params: seq[IRParam]
  var paramsNimSeq = newTree(nnkBracket)
  for i in 1 ..< formalParams.len:
    let id = formalParams[i]
    id.expectKind nnkIdentDefs
    let tyNode = id[id.len - 2]
    # Phase 14 A7a: detect `var T` at the SUT parameter level so
    # `isVar = true` is consistently set for top-level params, not
    # just for callees (parseCalleeImpl already does this). The
    # witness still extracts the INITIAL value via `initialEnv` —
    # mutations are walker-internal symbolic operations.
    let isVarParam = tyNode.kind == nnkVarTy
    let classified = classifyType(tyNode)
    for j in 0 ..< id.len - 2:
      let name = id[j].strVal
      var p = IRParam(name: name, ty: classified.ty,
                      rangeLo: classified.range.lo,
                      rangeHi: classified.range.hi,
                      hasRange: classified.range.hasRange,
                      isVar: isVarParam)
      params.add p
      paramsNimSeq.add emitParam(p)
  # Phase 14 cycle C3: always wrap the proc body in `isBlock` so the
  # walker's frontier-prune (which lives in `walkBlock`) sees the
  # top-level statement stream. Without this, single-statement
  # bodies (e.g. one outer `if`) dispatch straight to `walk(isIf)`
  # and bypass the prune entirely.
  let parsed = parseStmt(procDef[6], ctx)
  let bodyIR = if parsed != nil and parsed.kind == isBlock: parsed
               else: mkBlock(@[parsed])
  result.params = params
  result.bodyNimNode = emitStmt(bodyIR)
  result.paramsNimNode = prefix(paramsNimSeq, "@")
  result.procsNimNode = emitProcs(ctx.procs)
  result.body = bodyIR
  result.procs = ctx.procs
  result.userExnHierarchyNimNode = emitStrStrTable(ctx.userExnHierarchy)
  result.parseErrorsNimNode = emitErrorSeq(ctx.parseErrors)   ## Phase 15 G1c
