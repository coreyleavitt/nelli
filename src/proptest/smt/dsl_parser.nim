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
import std/options    ## RFC-chapulin-hardening Q1: tryRecognizeScanIdiom's Option[IRStmt]
import std/strformat
import std/strutils
import std/sets
import std/tables
import std/algorithm   ## Phase 15 G1a: sorted type-tuple in the inst key
import std/hashes      ## Phase 15 C1: lambda-site body-hash (lineInfo fallback)
import std/unicode     ## Phase 16 A7-S3: toRunes/runeLen for literal decode at parse time
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
  of iekTupleLit:
    var lit = newTree(nnkBracket)
    for c in e.telems: lit.add emitExpr(c)
    newCall(bindSym"mkTupleLit", prefix(lit, "@"), emitIRType(e.ttupleTy))
  of iekSeqLen:
    newCall(bindSym"mkSeqLen", emitExpr(e.lenObj))
  of iekSeqSlice:
    newCall(bindSym"mkSeqSlice", emitExpr(e.ssBase),
            emitExpr(e.ssLo), emitExpr(e.ssHi))
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
    # Cluster H Step C fix: `nominalId` MUST round-trip through the runtime
    # reconstruction call — `refPointeeTypeId` (runtime_heap.nim) reads
    # `IRType.nominalId` at WALK time, and the walker only ever sees IRTypes
    # rebuilt via THIS emitted call tree (never the macro-time originals
    # directly). Before this fix `nominalId` silently defaulted to "" at
    # runtime regardless of what the macro-time classify computed, so
    # `refPointeeTypeId` ALWAYS fell back to the structural `$pointeeTy`
    # rendering — which differs between a bare ref's FULL-fielded pointee and
    # a recursive field's EMPTY-fielded placeholder (`namedRefPlaceholder`),
    # minting two DIFFERENT `Ref_<id>`/`nil_<id>` sorts for the same nominal
    # type (a same-type nil-comparison silently comparing against the WRONG
    # sort's nil const — the bug this fix closes).
    #
    # Cluster H H_witness fix: `isPlaceholder` NOW ALSO round-trips. The
    # comment here used to say `isPlaceholder`/`nameIsRefAlias` are consumed
    # ONLY by witness CODEGEN (`symex.nim`'s `emitTyAndReader`), which reads
    # the macro-time IRType directly and never needs the runtime
    # reconstruction — true for every consumer BEFORE H_witness.
    # `buildHeapSnapshot`'s recursive descent (`resolveObjectFields`,
    # runtime.nim) is the FIRST consumer that inspects `isPlaceholder` on a
    # WALK-TIME (runtime-reconstructed) `IRType` — a ref-typed FIELD's
    # pointee, reached via `heapSelect`/`liftHeapValue` at witness-extraction
    # time, is exactly one of these reconstructed nodes. Without this fix
    # every runtime-reconstructed `itTuple` silently defaulted
    # `isPlaceholder = false` (Nim's zero-value), so `resolveObjectFields`
    # could never tell a genuine empty-fielded placeholder apart from a
    # PROVEN-EMPTY value type — it always took the "already full, don't
    # substitute" branch, permanently rendering a placeholder's `{}` empty
    # body instead of resolving the real nominal type. `nameIsRefAlias` stays
    # NOT threaded — still genuinely codegen-only, no walk-time reader needs it.
    newCall(bindSym"tTuple", prefix(fieldsLit, "@"),
            prefix(namesLit, "@"), newLit(t.objectName), newLit(t.nominalId),
            newLit(t.isPlaceholder))
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
  of isAssume:
    newCall(bindSym"mkAssume", emitExpr(s.acond))
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
    activeIterators*: HashSet[string]
                                   ## A3 (ADR-0014 D2-0d). Iterator sym names
                                   ## currently being inlined. Guards against
                                   ## recursive/mutually-recursive iterators that
                                   ## would otherwise cause infinite compile-time
                                   ## recursion via getImpl re-entrancy (CRIT-3).

proc newParseCtx*(maxInstantiationsPerProc = 0): ParseCtx =
  ParseCtx(procs: initTable[string, ProcSig](),
           parsing: initHashSet[string](),
           synthCounter: 0,
           userExnHierarchy: initTable[string, string](),
           maxInstantiationsPerProc: maxInstantiationsPerProc,
           instCounts: initTable[string, int](),
           activeIterators: initHashSet[string]())

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
    if e.bop in {bAdd, bSub, bMul, bDiv, bMod}: return true  ## R16-3/R16-4: arith → DivByZeroDefect/OverflowDefect guard
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
  of iekTupleLit:
    for a in e.telems:
      if rhsHasInlineDefectFork(a): return true
  of iekSeqLen:
    result = rhsHasInlineDefectFork(e.lenObj)
  of iekSeqSlice:
    # v67: a seq slice carries its own IndexDefect fork (the SND-4 OOB
    # deposit in its lowering) — always guard-worthy on an and/or RHS.
    result = true
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
  of iekStrAt, iekStrToInt:
    ## R1B (short-circuit OOB-guard fix): `iekStrAt` (SND-4, ADR-0024) deposits
    ## an inline OOB-defect fork into `strIndexOobConds` EVERY time it lowers
    ## (runtime_strings.nim `iekStrAt` arm), and `iekStrToInt` (S10b) likewise
    ## deposits an inline `ValueError` raise fork into `parseIntRaiseConds`
    ## (runtime_strings.nim `iekStrToInt` arm) every time it lowers. Both must
    ## SELF-REPORT true unconditionally — unlike the pure string ops below,
    ## these two nodes are themselves inline defect forks, not just carriers
    ## of forks in their sub-expressions. Without this, `A and s[i]==c` took
    ## D1c's FAST path (flat `mkBinop`), so the OOB fork fired UNGUARDED even
    ## when `A` (e.g. `i < s.len`) was false — a false `sxRaised(IndexDefect)`
    ## that real Nim's short-circuit evaluation never produces.
    result = true
  of iekStrLen, iekStrSubstr, iekStrFind, iekStrRfind, iekStrContains,
     iekStrStartsWith, iekStrEndsWith, iekStrReplace, iekStrReplaceAll,
     iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe, iekStrReplaceRe,
     iekStrBytes, iekStrConcat, iekIntToStr, iekRadixFmt,
     iekStrUnsupported, iekStrToLower, iekStrToUpper, iekRuneToStr,
     iekStrStrip:
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
proc zeroValueForType(ty: IRType): IRExpr  ## CR-2a fwd decl (defined below):
                                            ## parseExpr's expression-kind
                                            ## catch-all needs this to build a
                                            ## type-correct dummy.
proc unsupportedFieldPlaceholder(ty: IRType): IRExpr  ## R8 fwd decl (defined
                                            ## below, beside `zeroValueForType`):
                                            ## P2a's `nnkObjConstr` arm needs
                                            ## this to build a KIND-correct
                                            ## placeholder for an omitted field
                                            ## whose type has no clean zero.
proc refExprClassify(n: NimNode): ClassifiedType  ## P2b fwd decl (defined
                                            ## below): classify whether a VALUE
                                            ## expression genuinely carries a
                                            ## ref/ptr ADDRESS (itRef/itPtr) as
                                            ## opposed to a bare NAMED
                                            ## ref-object-alias symbol, which
                                            ## D1a value-models as itTuple.
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

proc isRuneTyped(node: NimNode): bool =
  ## True iff `node`'s Nim type is `std/unicode.Rune` (= `distinct int32` via
  ## RuneImpl). Mirrors the name-pair check in dsl_typebridge.classifyType (A7-S1
  ## intercept) so the two sites always agree. A user-defined `Rune` whose base
  ## type is NOT `RuneImpl` does NOT match (Invariant 3 — no accidental coercion).
  ## Used by the `$` interception sites in A7-S2 to route `$r` to `iekRuneToStr`
  ## BEFORE the `itInt` check (Rune classifies to itInt post-S1, so checking the
  ## classified kind alone would conflate Rune with a plain int).
  var ty = node.getTypeInst
  if ty.isNil: return false
  if ty.kind == nnkVarTy and ty.len == 1: ty = ty[0]
  if ty.kind != nnkSym or ty.strVal != "Rune": return false
  let impl = ty.getImpl
  result = impl.kind == nnkTypeDef and impl.len >= 3 and
           impl[2].kind == nnkDistinctTy and impl[2].len == 1 and
           impl[2][0].strVal == "RuneImpl"

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
        # v69 (chapulin "&-concat sxUnknown" root cause — which was never
        # about concat): a CONST symbol referenced in value position
        # (`s & SidecarExt`) emitted `iekVar("SidecarExt")`, but module-level
        # consts are never bound in any env — a guaranteed KeyError →
        # weInternalWalkerFault → sxUnknown, in whatever expression happened
        # to reference the const (hence the reported shape-sensitivity:
        # spellings where the const folded to a literal proved fine). Fold
        # the const to its VALUE at parse time: `getImpl` of an nskConst sym
        # is the nnkConstDef `[name, ty, value]`; recursing into the value
        # node reuses every literal/expression arm the parser already has.
        # Unresolvable shapes fall through to mkVar (prior behavior).
        if symKind(n) == nskConst:
          let cImpl = n.getImpl
          if cImpl.kind == nnkConstDef and cImpl.len >= 3 and
             cImpl[2].kind != nnkEmpty:
            return parseExpr(cImpl[2], preamble, ctx)
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
    # CR-1b (RFC-chapulin-hardening, Cluster 2 — crash-totality). A
    # `nnkStmtListExpr` with more than one child is how semcheck presents a
    # value-returning proc's `result = (let hi = ...; hi + 1)` RHS — the
    # implicit tail return of a multi-statement body. Taking only the LAST
    # child (as this arm used to) silently dropped every LEADING statement,
    # including a `let` the tail expression reads — the walker would later
    # crash with an uncaught KeyError on `lower(iekVar)` because the local's
    # binding never made it into `env`. Parse each leading child as an
    # ordinary statement (mirroring `parseStmtInner`'s `nnkLetSection` arm)
    # into `preamble`, the same A-normalisation channel every other
    # expression-position side-effect in this file already uses — callers
    # (`parseCalleeImpl`'s `resultRhs` path, `isLet`/`isAssign` RHS parsing,
    # …) already thread `preamble` ahead of the expression's consumer, so
    # the binding flows into the tail expression's environment at walk time.
    for i in 0 ..< n.len - 1:
      preamble.add parseStmt(n[i], ctx)
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
    elif tgt in intTyNames and src == "bool":
      # v69 (sello #3): `int32(b)` — previously the pass-through below, which
      # left an svBool flowing where an int-kinded SymVal is required
      # (`-int32(b)`, the ref10 mask idiom, then died in negBV's non-BV arm).
      # A-normalise via the M5 if-expression idiom: a fresh temp bound to
      # 1/0 at the conversion's classified width (the v69 isLet proto shapes
      # the literals), read back as the expression value.
      let convTy = classifyType(n).ty
      let tmp = freshSynth(ctx, "boolConv")
      let condIR = parseExpr(operand, preamble, ctx)
      preamble.add mkIf(
        @[mkBranch(condIR, mkLet(tmp, convTy, mkIntLit(1)))],
        mkLet(tmp, convTy, mkIntLit(0)))
      mkVar(tmp)
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
    # v64 (§0 clause (b), chapulin round-3 natural-form probe): an infix the
    # DSL does not model — e.g. `a .. b` building an HSlice VALUE in a call-
    # argument position, which the bracket-slice interceptors never see —
    # used to fall into `binopForInfix`'s macro-time `error()`, aborting the
    # whole file's compilation (observed on the real `parseTftpUri`).
    # Degrade CR-2a-style instead: classified parse error (sevError forces
    # the whole-run verdict to sxUnknown via `capForcedUnknown`), an
    # `mkUnsupported` stmt for the SND-1 walker taint, and a typed zero
    # dummy so parsing continues.
    if n[0].strVal notin ["+", "-", "*", "div", "/", "mod", "==", "!=",
                          "<", "<=", ">", ">=", "and", "or", "xor",
                          "shl", "shr"]:
      let dummyTy = classifyType(n).ty
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedOp,
        severity: sevError,
        msg: "unsupported infix operator `" & n[0].strVal & "` in `" &
             n.repr & "` — degraded to sxUnknown (feUnsupportedOp)")
      preamble.add mkUnsupported("unsupported infix operator `" &
                                 n[0].strVal & "` (feUnsupportedOp)")
      let dummy = zeroValueForType(dummyTy)
      return (if dummy != nil: dummy else: mkIntLit(0))
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
      # v64 (chapulin catalog #3 residual): Nim spells the BOOLEAN `and`/`or`
      # and the BITWISE `and`/`or` with the SAME identifiers, so `op in
      # {bAnd, bOr}` alone also matches an INT-typed infix (e.g.
      # `(hi shl 8) or lo` on uint16). The D1c short-circuit machinery below
      # is only correct — and only type-sound — for the boolean form: the
      # guarded path binds the LHS into a `tBool()` temp and emits
      # `uNot(temp)` as the or-guard, which for a BV-valued LHS walked
      # straight into `runtime.nim`'s `doAssert inner.kind == svBool`
      # (an uncaught AssertionDefect — a native crash, not a classified
      # degrade). A bitwise `and`/`or` has NO short-circuit semantics in Nim
      # (the RHS always evaluates), so its hoisted defect-fork stmts belong
      # unconditionally in the outer preamble and the plain binop is the
      # faithful lowering.
      if classifyType(n).ty.kind != itBool:
        preamble.add rhsPreamble
        mkBinop(op, lhsIR, rhsIR)
      elif rhsPreamble.len == 0 and not rhsHasInlineDefectFork(rhsIR):
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
      # Phase 16 A7-S2: `$r` where r: Rune → `iekRuneToStr` (UTF-8 byte string
      # via runeToUtf8Sym). Must intercept BEFORE the itInt check: after S1, Rune
      # classifies to itInt, so `classifyType(n[1]).ty.kind == itInt` is true for
      # BOTH a plain int and a Rune — the Rune case must be caught first by
      # checking the ACTUAL Nim type via isRuneTyped. A non-Rune distinct int
      # falls through to the itInt branch (decimal), never the Rune UTF-8 branch.
      if isRuneTyped(n[1]):
        return mkStrOp(iekRuneToStr, "$rune", @[parseExpr(n[1], preamble, ctx)])
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
      # v67 (dev item 1): a seq SLICE in bracket form — `data[a..b]` /
      # `data[a ..< b]` — is a VALUE (array-lambda view, `iekSeqSlice`),
      # dispatched with the same unwrap-then-TYPE discipline as the v66
      # string path (the `..<` template expansion wraps the index in
      # `nnkStmtListExpr(…, Infix("..", lo, pred(hi, 1)))`). Single int
      # index keeps the A-normalised isIndex stmt.
      var idxNode = n[1]
      while idxNode.kind in {nnkHiddenDeref, nnkHiddenAddr,
                             nnkHiddenStdConv,
                             nnkStmtListExpr} and idxNode.len >= 1:
        idxNode = idxNode[idxNode.len - 1]
      if idxNode.kind == nnkInfix and idxNode.len == 3 and
         idxNode[0].kind in {nnkSym, nnkIdent} and
         idxNode[0].strVal in ["..", "..<"]:
        let loIR = parseExpr(idxNode[1], preamble, ctx)
        # `^k` stays a `BackwardsIndex(k)` conversion for seqs — rewrite to
        # `len(base) - k` (mirrors the call-form intercept).
        var hiNode = idxNode[2]
        while hiNode.kind in {nnkHiddenStdConv, nnkStmtListExpr} and
              hiNode.len >= 1:
          hiNode = hiNode[hiNode.len - 1]
        var hiIR: IRExpr
        if hiNode.kind in {nnkCall, nnkConv, nnkCommand, nnkPrefix} and
           hiNode.len == 2 and hiNode[0].kind in {nnkSym, nnkIdent} and
           hiNode[0].strVal in ["BackwardsIndex", "^"]:
          hiIR = mkBinop(bSub, mkSeqLen(objIR),
                         parseExpr(hiNode[1], preamble, ctx))
        else:
          hiIR = parseExpr(idxNode[2], preamble, ctx)
        if idxNode[0].strVal == "..<":
          hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
        mkSeqSlice(objIR, loIR, hiIR)
      elif idxNode.typeKind != ntyNone and
           classifyType(idxNode).ty.kind == itInt:
        # `s[i]` on a seq — same A-normalised isIndex stmt; the runtime
        # walker dispatches on the receiver's SVKind.
        let idxIR = parseExpr(idxNode, preamble, ctx)
        let synth = freshSynth(ctx, "idx")
        preamble.add mkIndexStmt(synth, objIR, idxIR, lhsCls.ty.seqElemTy)
        mkVar(synth)
      else:
        ctx.parseErrors.add SymexErrorInfo(
          kind: feUnsupportedExprKind, severity: sevError,
          msg: "seq `[]` index is neither int-typed nor a recognizable " &
               "range literal (kind " & $idxNode.kind & ") in `" & n.repr &
               "` — degraded to sxUnknown (feUnsupportedExprKind)")
        preamble.add mkUnsupported(
          "seq `[]` with unrecognized index (feUnsupportedExprKind)")
        let dummy = zeroValueForType(classifyType(n).ty)
        (if dummy != nil: dummy else: mkIntLit(0))
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
      # v65 (§0 clause (b)): `[]` on an unclassified/unmodeled receiver type
      # used to macro-`error()`, aborting the whole file. CR-2a-style
      # classified degrade instead (parse error + SND-1 taint + typed zero
      # dummy).
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedExprKind, severity: sevError,
        msg: "`[]` on unsupported type " & $lhsCls.ty & " in `" & n.repr &
             "` — degraded to sxUnknown (feUnsupportedExprKind)")
      preamble.add mkUnsupported("`[]` on unsupported type " & $lhsCls.ty &
                                 " (feUnsupportedExprKind)")
      let dummy = zeroValueForType(classifyType(n).ty)
      return (if dummy != nil: dummy else: mkIntLit(0))
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
      # `Node` ref), `classifyType(n.next)` UNWRAPS to the recursive field's
      # placeholder VALUE type (it does not re-derive "this came from a ref
      # field" from a dot-expr node) — so we must re-classify via
      # `classifyFieldType` (the ref-aware field classifier) to recover the
      # `itRef`/`itPtr`.
      #
      # Cluster H Step C (ADR-0022) KEEPS the `operand.kind notin {nnkSym,
      # nnkIdent}` exclusion — NOT one of the carve-outs actually deleted.
      # Deleting it was considered (per the original H1 brief) but rejected:
      # `classifyType` now correctly classifies a BARE named-ref symbol at
      # Level 1 (itRef for a plain ref-object, itVariant — deliberately, ADR
      # sub-decision #1 — for a ref-VARIANT object), so this fallback is
      # already dead-but-harmless for that case (the `opCls.ty.kind notin
      # {itRef,itPtr}` half of the guard alone would skip it). But
      # `classifyFieldType`/`namedRefPlaceholder` is variant-BLIND (it
      # ref-wraps ANY object pointee, by design — a FIELD pointing to a
      # variant is a legitimate heap address the field-split heap already
      # supports for disc/plain-field reads, ADR-0013). Deleting the bare-sym
      # exclusion would let a bare `p: TreeRef` (`TreeRef = ref object; case
      # kind: …`) — value-modelled to `itVariant` by design — get
      # MISCLASSIFIED to `itRef` here, diverting `p.field` off the
      # already-correct value-modelled `itVariant` field-access arm below and
      # onto the field-split-heap path with an `svVariant` env value where an
      # `svRef` is expected (a Z3-sort-mismatch / walker-crash risk). A bare
      # symbol's classification is `classifyType`'s job alone; keeping this
      # exclusion is what preserves that authority.
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
      # v65 (§0 clause (b)): `.field` on an unclassified/unmodeled type —
      # e.g. an HSlice VALUE flowing into the inlined `system.[]` (`x.a`) on
      # a slice-as-value shape — used to macro-`error()`, aborting the
      # whole file (the "`.` on unsupported type uninterp[HSlice[int,int]]"
      # class). CR-2a-style classified degrade instead.
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedExprKind, severity: sevError,
        msg: "`.` on unsupported type " & $lhsCls.ty & " in `" & n.repr &
             "` — degraded to sxUnknown (feUnsupportedExprKind)")
      preamble.add mkUnsupported("`.` on unsupported type " & $lhsCls.ty &
                                 " (feUnsupportedExprKind)")
      let dummy = zeroValueForType(classifyType(n).ty)
      return (if dummy != nil: dummy else: mkIntLit(0))
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
    # Phase 16 A7-S2: `$r` where r: Rune (call form: `` `$`(r) ``). Intercept
    # BEFORE the itInt check for the same reason as the nnkPrefix site above.
    if calleeSym.strVal == "$" and n.len == 2 and isRuneTyped(n[1]):
      return mkStrOp(iekRuneToStr, "$rune", @[parseExpr(n[1], preamble, ctx)])
    if calleeSym.strVal == "$" and n.len == 2 and
       classifyType(n[1]).ty.kind == itInt:
      return mkStrOp(iekIntToStr, "$", @[parseExpr(n[1], preamble, ctx)])
    # RFC-chapulin-hardening M2: `parseBiggestInt(s)` (std/strutils) is routed to
    # the SAME `iekStrToInt` IR as `parseInt(s)`. On this platform `BiggestInt` is
    # a 64-bit int — identical to `parseInt`'s result type — so the two are
    # semantically identical here; no new IR kind, no new runtime lowering. The
    # `strOp` label passes the REAL callee name (not hardcoded "parseInt") so
    # diagnostics/pretty-printing stay accurate; `iekStrToInt`'s runtime lowering
    # dispatches purely on `e.kind` (never reads `e.strOp`), so this is a pure
    # label change with zero effect on modeling. `canonicalize`'s cache key does
    # include `strOp`, so a `parseBiggestInt` SUT gets its OWN cache key distinct
    # from an otherwise-identical `parseInt` SUT — correct (they are different
    # source expressions), not a collision risk.
    if calleeSym.strVal in ["parseInt", "parseBiggestInt"] and n.len == 2 and
       classifyType(n[1]).ty.kind == itString:
      return mkStrOp(iekStrToInt, calleeSym.strVal, @[parseExpr(n[1], preamble, ctx)])
    if calleeSym.strVal == "parseFloat" and n.len == 2 and
       classifyType(n[1]).ty.kind == itString:
      # Phase 15 S10b: Z3 String theory has NO float↔string conversion (only the
      # int `str.to_int`/`int.to_str` pair). `parseFloat(s)` routes to a
      # classified `seUnsupportedStringOp` → `sxUnknown` (S9 `iekStrUnsupported`
      # mechanism, opName "parseFloat"; Invariant 3 — never a crash/silent UNSAT).
      return mkStrOp(iekStrUnsupported, "parseFloat", @[])
    # Phase 16 A8: radix formatting — toHex, toBin, toOct.
    # `toHex(x)` full-width and `toHex(x, len)` / `toBin(x, len)` with a
    # COMPILE-TIME LITERAL len. Only fixed-width int operands (int8/16/32/64,
    # uint8/16/32/64 — all map to Z3 BVs under ADR-0001) are supported.
    # `strOp` encodes `"<name>:<base>:<numDigits>"` so distinct combinations
    # content-address distinctly in the cache key.
    # DEGRADE → iekStrUnsupported for: toOct, symbolic len, non-int operand.
    if calleeSym.strVal == "toOct" and n.len >= 2:
      return mkStrOp(iekStrUnsupported, "toOct", @[])
    if calleeSym.strVal in ["toHex", "toBin"] and n.len in [2, 3]:
      let operandTy = classifyType(n[1]).ty
      if operandTy.kind == itInt:
        let bvWidth     = operandTy.width   ## 8, 16, 32, or 64
        let base        = if calleeSym.strVal == "toHex": 16 else: 2
        let bitsPerDigit = if base == 16: 4 else: 1
        var numDigits: int
        if n.len == 2:
          # Full-width form: numDigits = total bits / bits-per-digit.
          # `toBin` without a len is ambiguous (Nim requires len) → degrade.
          if calleeSym.strVal != "toHex":
            return mkStrOp(iekStrUnsupported, "toBin_no_len", @[])
          numDigits = bvWidth div bitsPerDigit
        else:
          # Has a len arg — must be a compile-time integer literal.
          # Unwrap any hidden conversion inserted by Nim's semantic analysis
          # when the formal type differs from int (e.g. toBin's len is Positive,
          # so `toBin(x, 8)` may have n[2] = nnkHiddenStdConv(Positive, 8)).
          var lenNode = n[2]
          if lenNode.kind in {nnkConv, nnkHiddenStdConv, nnkHiddenSubConv}:
            lenNode = lenNode[^1]
          if lenNode.kind notin {nnkIntLit, nnkInt8Lit, nnkInt16Lit,
                                  nnkInt32Lit, nnkInt64Lit,
                                  nnkUIntLit, nnkUInt8Lit, nnkUInt16Lit,
                                  nnkUInt32Lit, nnkUInt64Lit}:
            # Symbolic/non-literal len → sound degrade (Invariant 3).
            return mkStrOp(iekStrUnsupported,
                           calleeSym.strVal & "_dynamic_len", @[])
          numDigits = int(lenNode.intVal)
        let operandIR = parseExpr(n[1], preamble, ctx)
        # Encode base+numDigits in strOp so distinct configurations get distinct
        # cache keys (canonicalize already folds strOp in for StrOpKinds).
        let opStr = calleeSym.strVal & ":" & $base & ":" & $numDigits
        return mkStrOp(iekRadixFmt, opStr, @[operandIR])
      else:
        # Non-int operand (float, bool, …) → sound degrade.
        return mkStrOp(iekStrUnsupported, calleeSym.strVal & "_non_int", @[])
    # Phase 16 A7-S3: `runeLen(s)` / `s.runeLen` — UFCS or direct call.
    # Intercept BEFORE the string-receiver guard so the std/unicode body is never
    # walked. Origin guard (owner == "unicode") prevents hijacking a user-defined
    # proc of the same name (regression guard, mirrors the C4-4 sequtils guard).
    # Literal arg → concrete rune count (decoded in Nim at parse time).
    # Symbolic arg → seZ3StringIncomplete (sxUnknown, Invariant 3 — never a crash,
    # never a hang, never a silent wrong verdict).
    if calleeSym.strVal == "runeLen" and n.len == 2:
      let runeOwner = calleeSym.owner
      if runeOwner.kind == nnkSym and runeOwner.strVal == "unicode":
        let argNode = n[1]
        if argNode.kind in {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
          # Concrete literal: call Nim's own runeLen at parse time → numeral.
          # Trivially exact vs Nim (we ARE calling Nim — Invariant 3).
          let rLen = unicode.runeLen(argNode.strVal)
          return mkIntLit(int64(rLen))
        else:
          # Symbolic string: UTF-8 grouping over an unknown byte stream has no
          # quantifier-free Z3 encoding → classified seZ3StringIncomplete (ADR-0017).
          # We are inside `parseExpr` (returns IRExpr): add the classify-error to
          # ctx.parseErrors (drained to r.errors at runSymex boundary), emit an
          # mkUnsupported stmt into the preamble (sets sawUnknown=true in walker),
          # and return a dummy IRExpr so the enclosing expression is well-typed.
          # The dummy value is never reached (walker sees sawUnknown first).
          ctx.parseErrors.add SymexErrorInfo(
            kind: seZ3StringIncomplete,
            severity: sevError,
            msg: "A7-S3: runeLen(symbolic) — UTF-8 grouping over unknown byte " &
                 "stream; no quantifier-free Z3 encoding (ADR-0017)")
          preamble.add mkUnsupported("symex A7-S3: runeLen(symbolic) unsupported " &
                                     "(seZ3StringIncomplete)")
          return mkIntLit(0)   # unreachable: walker halts on sawUnknown from above
    # Phase 15 C2b: the receiver of a string-builtin must be type-classifiable.
    # A nested CLOSURE CALL (`f(f(v))` — `n[1]` is `f(v)`) carries NO semantic
    # type (`typeKind == ntyNone`), so `classifyType`'s `getTypeInst` would raise
    # a non-catchable "node has no type" compile error. Gate the string-receiver
    # classify on the node actually HAVING a type; an untyped receiver is not a
    # string op — fall through to the normal/closure-call dispatch below.
    if n.len >= 2 and n[1].typeKind != ntyNone:
      # v65 (char-needle family): `s.contains('@')` has NO strutils
      # (string, char) overload — Nim resolves it to system.contains(
      # openArray[T], T) through the string→openArray[char] implicit
      # conversion, so the receiver arrives as nnkHiddenStdConv(
      # openArray[char], s). That classifies non-string and used to fall
      # through to user-proc INLINING of the generic system.contains,
      # whose openArray formal aborts macro expansion ("node has no
      # type"). Unwrap the hidden conversion when the node BENEATH is a
      # string — element membership over a string's openArray[char] view
      # IS char containment, i.e. exactly `iekStrContains`.
      var recvNode = n[1]
      var recvCls0 = classifyType(recvNode)
      if recvCls0.ty.kind != itString and
         recvNode.kind == nnkHiddenStdConv and recvNode.len >= 1:
        let inner = recvNode[recvNode.len - 1]
        if inner.typeKind != ntyNone and classifyType(inner).ty.kind == itString:
          recvNode = inner
          recvCls0 = classifyType(inner)
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
          # v66 (round-4 Slice A, soundness): the slice argument can arrive
          # WRAPPED — a let/var-RHS `s[0 ..< i]` reaches here as
          # `nnkHiddenStdConv(HSlice[int, int], infix)` — and the former
          # shape-only `nnkInfix` test fell through to the CHAR path for it:
          # the binding mis-lowered as the `s[lowered-dummy]` BV8 char, every
          # downstream string op degraded (requireStr), and TWO such
          # mis-lowered slices would have compared as first-char equality —
          # a wrong-verdict hazard. Unwrap hidden wrappers first (inline
          # `unwrapHidden` — that helper is declared later in this file),
          # then dispatch on the unwrapped node's TYPE, never on shape alone.
          # `nnkStmtListExpr` included: the `..<` TEMPLATE expansion arrives
          # as `StmtListExpr(Empty, Infix("..", lo, pred(hi, 1)))` — the same
          # wrapper shape Q1 documented for the `!=` desugar; `pred(hi, 1)`
          # then lowers via the v64 pred/succ arithmetic passthrough.
          var idxNode = n[2]
          while idxNode.kind in {nnkHiddenDeref, nnkHiddenAddr,
                                 nnkHiddenStdConv,
                                 nnkStmtListExpr} and idxNode.len >= 1:
            idxNode = idxNode[idxNode.len - 1]
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
          elif idxNode.typeKind != ntyNone and
               classifyType(idxNode).ty.kind == itInt:
            # `s[i]` single-byte index read → char via at->toCode->BV8 bridge.
            # The int-type gate (not an else-fallthrough) is what makes the
            # char path UNREACHABLE for any slice-shaped index.
            let idxIR = parseExpr(idxNode, preamble, ctx)
            return mkStrOp(iekStrAt, "[]", @[recvIR, idxIR])
          else:
            # Non-int, non-recognizable-range index (e.g. an HSlice VALUE
            # bound to a name — bounds not statically extractable). CR-2a
            # classified degrade; never a char mis-read (§0 clause (b)/(c)).
            ctx.parseErrors.add SymexErrorInfo(
              kind: feUnsupportedExprKind, severity: sevError,
              msg: "string `[]` index is neither int-typed nor a " &
                   "recognizable range literal (kind " & $idxNode.kind &
                   ") in `" & n.repr &
                   "` — degraded to sxUnknown (feUnsupportedExprKind)")
            preamble.add mkUnsupported(
              "string `[]` with unrecognized index (feUnsupportedExprKind)")
            let dummy = zeroValueForType(classifyType(n).ty)
            return (if dummy != nil: dummy else: mkStrLit(""))
        # Phase 15 S3: `s.high` is byte-faithfully `len(s) - 1` (ADR-0006) —
        # NOT unsupported. Build it directly from `iekStrLen`.
        if calleeSym.strVal == "high" and n.len == 2:
          let recvIR = parseExpr(n[1], preamble, ctx)
          let lenIR = mkStrOp(iekStrLen, "len", @[recvIR])
          return mkBinop(bSub, lenIR, mkIntLit(1))
        # Phase 15 S9 / Phase 16 A9: case-folding ops.
        # `toLower`/`toUpper` (std/unicode) — no Z3 native full-Unicode fold
        # primitive — stay `iekStrUnsupported` → classified `seUnsupportedStringOp`
        # (sxUnknown, Invariant 3 — never a silent UNSAT, never a crash).
        # `toLowerAscii`/`toUpperAscii` (std/strutils) are now modeled via a
        # quantifier-free BV18-ITE seqMap (ADR-0015, A9) and route to the new
        # `iekStrToLower`/`iekStrToUpper` IR kinds. An explicit guard (rather than
        # relying on the `getStdlibModelFor` else-fallthrough) keeps the
        # classification intentional and carries the real surface op name.
        if calleeSym.strVal in
             ["toLower", "toUpper", "toLowerAscii", "toUpperAscii"] and
           n.len >= 2:
          var caseArgs: seq[IRExpr]
          for i in 1 ..< n.len:
            caseArgs.add parseExpr(n[i], preamble, ctx)
          case calleeSym.strVal
          of "toLowerAscii": return mkStrOp(iekStrToLower, calleeSym.strVal, caseArgs)
          of "toUpperAscii": return mkStrOp(iekStrToUpper, calleeSym.strVal, caseArgs)
          else:              return mkStrOp(iekStrUnsupported, calleeSym.strVal, caseArgs)
        # Round-4 Slice B (ADR-0026): `strutils.strip(s[, leading[,
        # trailing[, chars]]])` with LITERAL flags and a LITERAL char set →
        # `iekStrStrip` (decomposition constraints, runtime_strings.nim).
        # Everything must be compile-time extractable — the flags select the
        # decomposition SHAPE and the chars build the finite regex union; a
        # non-literal spec degrades CLASSIFIED here rather than falling into
        # `getImpl` inlining of strip's while-loop body (exactly the Q2
        # unprovable shape this slice replaces). The typed AST materializes
        # defaulted args, so all arities land here.
        if calleeSym.strVal == "strip" and n.len >= 2:
          let recvIR = parseExpr(n[1], preamble, ctx)
          var leading = true
          var trailing = true
          var chars = " \t\v\r\n\f"     # strutils.Whitespace (the default)
          var literalOk = true
          proc boolLit(b: NimNode, into: var bool): bool =
            case b.kind
            of nnkIntLit:
              into = b.intVal != 0
              true
            of nnkSym, nnkIdent:
              if b.strVal == "true": into = true; true
              elif b.strVal == "false": into = false; true
              else: false
            else: false
          if n.len >= 3 and not boolLit(n[2], leading): literalOk = false
          if n.len >= 4 and not boolLit(n[3], trailing): literalOk = false
          if literalOk and n.len >= 5:
            var curly = n[4]
            while curly.kind in {nnkHiddenStdConv, nnkStmtListExpr} and
                  curly.len >= 1:
              curly = curly[curly.len - 1]
            if curly.kind == nnkCurly:
              chars = ""
              for el in curly:
                if el.kind == nnkCharLit:
                  chars.add char(el.intVal and 0xFF)
                elif (el.kind == nnkRange and el.len == 2 and
                      el[0].kind == nnkCharLit and el[1].kind == nnkCharLit):
                  for code in el[0].intVal .. el[1].intVal:
                    chars.add char(code and 0xFF)
                elif (el.kind == nnkInfix and el.len == 3 and
                      el[0].kind in {nnkSym, nnkIdent} and
                      el[0].strVal == ".." and
                      el[1].kind == nnkCharLit and el[2].kind == nnkCharLit):
                  for code in el[1].intVal .. el[2].intVal:
                    chars.add char(code and 0xFF)
                else:
                  literalOk = false
            else:
              literalOk = false
          if literalOk:
            let flags = (if leading and trailing: "LT"
                         elif leading: "L"
                         elif trailing: "T"
                         else: "-")
            return mkStrOp(iekStrStrip, flags & ":" & chars, @[recvIR])
          ctx.parseErrors.add SymexErrorInfo(
            kind: seUnsupportedStringOp, severity: sevError,
            msg: "strip with a non-literal flag/char-set spec in `" &
                 n.repr & "` is not modeled (ADR-0026 covers literal " &
                 "specs) — degraded to sxUnknown (seUnsupportedStringOp)")
          preamble.add mkUnsupported(
            "strip with non-literal spec (seUnsupportedStringOp)")
          return mkStrLit("")
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
          # v65: parse the (possibly conversion-unwrapped) receiver node —
          # `recvNode`, not `n[1]` — so the openArray-conv contains shape
          # lowers its actual string receiver.
          sArgs.add parseExpr(recvNode, preamble, ctx)
          for i in 2 ..< n.len:
            sArgs.add parseExpr(n[i], preamble, ctx)
          let irKind = case sm.kind
            of smkStrLen:        iekStrLen
            of smkStrIndex:      iekStrAt
            of smkStrAt:         iekStrAt
            of smkStrSubstr:     iekStrSubstr
            of smkStrFind:       iekStrFind
            of smkStrRfind:      iekStrRfind
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
      # v67 (dev item 1): system's slice `[]` overload takes an OPENARRAY
      # receiver — `data[a..b]` therefore arrives as
      # `[]`(nnkHiddenStdConv(openArray[T], data), HSlice…) and the bare
      # receiver classify sees openArray, not itSeq. Unwrap the hidden
      # conversion when a seq sits beneath (the `contains`-via-openArray
      # precedent, v65).
      var sliceRecvNode = n[1]
      var sliceRecvCls = recvCls
      if sliceRecvCls.ty.kind != itSeq and
         sliceRecvNode.kind == nnkHiddenStdConv and sliceRecvNode.len >= 1:
        let inner = sliceRecvNode[sliceRecvNode.len - 1]
        if inner.typeKind != ntyNone and classifyType(inner).ty.kind == itSeq:
          sliceRecvNode = inner
          sliceRecvCls = classifyType(inner)
      if sliceRecvCls.ty.kind == itSeq:
        let recvIR = parseExpr(sliceRecvNode, preamble, ctx)
        # v67 (dev item 1): the call-form seq slice — `[]`(data, HSlice…) —
        # previously fell through to `getImpl` INLINING of system's `[]`
        # (whose body macro-aborted on `len`). Same unwrap-then-TYPE
        # dispatch as the bracket arm: range → `iekSeqSlice` view; int →
        # isIndex; anything else → classified degrade.
        var idxNode = n[2]
        while idxNode.kind in {nnkHiddenDeref, nnkHiddenAddr,
                               nnkHiddenStdConv,
                               nnkStmtListExpr} and idxNode.len >= 1:
          idxNode = idxNode[idxNode.len - 1]
        if idxNode.kind == nnkInfix and idxNode.len == 3 and
           idxNode[0].kind in {nnkSym, nnkIdent} and
           idxNode[0].strVal in ["..", "..<"]:
          let loIR = parseExpr(idxNode[1], preamble, ctx)
          # `data[4 .. ^1]`: for seqs `^k` does NOT pre-expand (it stays a
          # `BackwardsIndex(k)` conversion in the typed AST — strings have
          # their own overload that expands to `len - k`). Rewrite it to
          # `len(base) - k` here.
          var hiNode = idxNode[2]
          while hiNode.kind in {nnkHiddenStdConv, nnkStmtListExpr} and
                hiNode.len >= 1:
            hiNode = hiNode[hiNode.len - 1]
          var hiIR: IRExpr
          if hiNode.kind in {nnkCall, nnkConv, nnkCommand, nnkPrefix} and
             hiNode.len == 2 and hiNode[0].kind in {nnkSym, nnkIdent} and
             hiNode[0].strVal in ["BackwardsIndex", "^"]:
            hiIR = mkBinop(bSub, mkSeqLen(recvIR),
                           parseExpr(hiNode[1], preamble, ctx))
          else:
            hiIR = parseExpr(idxNode[2], preamble, ctx)
          if idxNode[0].strVal == "..<":
            hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
          return mkSeqSlice(recvIR, loIR, hiIR)
        elif idxNode.typeKind != ntyNone and
             classifyType(idxNode).ty.kind == itInt:
          let keyIR  = parseExpr(idxNode, preamble, ctx)
          let synth = freshSynth(ctx, "sget")
          preamble.add mkIndexStmt(synth, recvIR, keyIR,
                                   sliceRecvCls.ty.seqElemTy)
          return mkVar(synth)
        else:
          ctx.parseErrors.add SymexErrorInfo(
            kind: feUnsupportedExprKind, severity: sevError,
            msg: "seq `[]` index is neither int-typed nor a recognizable " &
                 "range literal (kind " & $idxNode.kind & ") in `" & n.repr &
                 "` — degraded to sxUnknown (feUnsupportedExprKind)")
          preamble.add mkUnsupported(
            "seq `[]` with unrecognized index (feUnsupportedExprKind)")
          let dummy = zeroValueForType(classifyType(n).ty)
          return (if dummy != nil: dummy else: mkIntLit(0))
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
    # A7 (ADR-0017 Path B): `ord(r)` where `r` classifies as tInt (Rune → tInt).
    # `ord` is a magic intrinsic with no parseable body; for a type already
    # classified to tInt (e.g. Rune after A7 intercept), `ord` is the identity.
    if calleeSym.strVal == "ord" and n.len == 2 and
       n[1].typeKind != ntyNone and
       classifyType(n[1]).ty.kind == itInt:
      return parseExpr(n[1], preamble, ctx)
    # v64 (chapulin catalog #pred): `pred(x[, k])` / `succ(x[, k])` are magic
    # intrinsics with no parseable body, and `a ..< b` lowers via a template
    # to `a .. pred(b)` — so `pred` sits on the hot path of every `..<`
    # slice/range a SUT writes (chapulin: `rest[1 ..< closeBracket]` failed
    # to compile with "unsupported infix operator `..`" precisely because
    # the pred-rewritten bound had no case here; the literal-infix `..<`
    # match stays the fast path for shapes the compiler leaves unexpanded).
    # For an int-classified operand they are plain arithmetic: pred → `-`,
    # succ → `+`, with the default step 1 when the typed AST omits it.
    if calleeSym.strVal in ["pred", "succ"] and n.len in [2, 3] and
       n[1].typeKind != ntyNone and
       classifyType(n[1]).ty.kind == itInt:
      let base = parseExpr(n[1], preamble, ctx)
      let step = if n.len == 3: parseExpr(n[2], preamble, ctx)
                 else: mkIntLit(1)
      return mkBinop(if calleeSym.strVal == "pred": bSub else: bAdd,
                     base, step)
    # A7 (ADR-0017 Path B): borrow comparison ops (==, !=, <, <=, >, >=) on
    # types that classify as tInt (e.g. Rune → tInt) arriving as nnkCall.
    # The nnkInfix borrowIntercept already handles infix-form writes; this block
    # covers the nnkCall form that the compiler may emit for borrow shims.
    block runeCompareIntercept:
      if calleeSym.strVal notin ["==", "!=", "<", "<=", ">", ">="]: break runeCompareIntercept
      if n.len != 3: break runeCompareIntercept
      if n[1].typeKind == ntyNone: break runeCompareIntercept
      if classifyType(n[1]).ty.kind != itInt: break runeCompareIntercept
      let ci = calleeSym.getImpl
      if ci.kind != nnkProcDef or not hasBorrowPragma(ci): break runeCompareIntercept
      let lhs = parseExpr(n[1], preamble, ctx)
      let rhs = parseExpr(n[2], preamble, ctx)
      return mkBinop(binopForInfix(calleeSym.strVal), lhs, rhs)
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
  of nnkIfExpr:
    # RFC-chapulin-hardening M5 (walker v50->51): an if-EXPRESSION used as a
    # SUB-EXPRESSION (e.g. `(if c: 1 else: 2) + 1`, or the direct RHS of a
    # `let`) previously fell through to the CR-2a catch-all below. Model it
    # via synthetic let+read A-normalisation (the same idiom CR-1b/M4 use):
    # hoist a fresh temp, emit the if AS A STATEMENT into `preamble` whose
    # each arm's tail expression is bound to that temp via `mkLet` (each
    # branch only ever executes on its OWN forked path — runtime.nim's
    # `isIf` walker forks `paths` per-arm before running the arm body, so
    # rebinding the same name in sibling arms cannot collide), then return a
    # read of the temp. Nim only accepts an if-EXPRESSION when every arm's
    # type unifies (and requires an `else`), so `classifyType(n).ty` yields
    # one common type shared by all arms.
    #
    # This also — with NO further code — makes `min`/`max` on ints work:
    # `system.min`/`system.max`'s int overloads have a real (non-empty) body
    # `if x <= y: x else: y` despite the `{.magic.}` pragma, so `getImpl`
    # resolves it; `parseCalleeImpl`'s single-`result = expr` rewrite (the
    # `resultRhs` helper) detects the whole body as one expression and calls
    # `parseExpr` directly on its `nnkIfExpr` — routing straight through this
    # arm via ordinary proc-inlining (confirmed against `system/comparisons.nim`
    # in the toolchain image; the float overloads are intercepted earlier, by
    # `mathInterception`, and never reach here).
    let resultTy = classifyType(n).ty
    let tmp = freshSynth(ctx, "ifexpr")
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        var condPre: seq[IRStmt]
        let condIR = parseExpr(arm[0], condPre, ctx)
        for cs in condPre: preamble.add cs
        var bodyPre: seq[IRStmt]
        let bodyIR = parseExpr(arm[1], bodyPre, ctx)
        bodyPre.add mkLet(tmp, resultTy, bodyIR)
        branches.add mkBranch(condIR,
          if bodyPre.len == 1: bodyPre[0] else: mkBlock(bodyPre))
      of nnkElse, nnkElseExpr:
        var bodyPre: seq[IRStmt]
        let bodyIR = parseExpr(arm[0], bodyPre, ctx)
        bodyPre.add mkLet(tmp, resultTy, bodyIR)
        elseBody = if bodyPre.len == 1: bodyPre[0] else: mkBlock(bodyPre)
      else:
        error(&"symex M5: unexpected if-expr arm kind {arm.kind}", arm)
    preamble.add mkIf(branches, elseBody)
    mkVar(tmp)
  of nnkTupleConstr:
    # RFC-chapulin-hardening P1 (walker v51->52): a general N-ary tuple
    # constructor `(a, b, c)` / named `(x: a, y: b)` used as an EXPRESSION
    # (e.g. `let t = (a, b)`, `return (a, b, c)`) — previously only the
    # narrow `yield (e1,e2)` special-case (`parseIterBodyStmt` above) handled
    # `nnkTupleConstr`; any OTHER occurrence fell through to the CR-2a
    # catch-all below, degrading the whole run to `sxUnknown` (SND-1 taint on
    # the dummy). Build an `iekTupleLit` node, reusing the ALREADY-BUILT
    # itTuple/svTuple witness/runtime machinery (used today for
    # variant/object values) — this slice is purely the CONSTRUCTION path.
    #
    # `classifyType(n)` resolves via `n.getTypeInst` (dsl_typebridge.nim:89),
    # which for a tuple-constructor EXPRESSION node yields the tuple's TYPE
    # node — `nnkTupleConstr` for an anonymous tuple, `nnkTupleTy` for a named
    # one — and dsl_typebridge's existing structural-match arms (lines
    # 129-146) already turn either into a correctly-shaped
    # `tTuple(fields, names)` (field names populated for the named-tuple
    # case, all-"" for the anonymous case). So the type side needs no new
    # code; only the runtime `iekTupleLit` construction is net-new.
    #
    # Each element is parsed via the ORDINARY `parseExpr` recursion — no
    # special-casing per element. A still-unsupported field expression
    # (`cast`, `objConstr`, …) independently hits the CR-2a catch-all below,
    # which emits `mkUnsupported` into `preamble`; SND-1's taint on
    # `isUnsupported` demotes `Path.uncertain` regardless of where in the
    # tuple construction it originates, so a tuple with one unsupported field
    # degrades the WHOLE run to `sxUnknown` — it can never manufacture a
    # false `sxSat` from the unsupported field's dummy zero-value
    # (Invariant 3).
    #
    # A named tuple constructor `(x: a, y: b)` presents each field as an
    # `nnkExprColonExpr[name, valueExpr]` child; unwrap to the value.
    let tupleTy = classifyType(n).ty
    var elems: seq[IRExpr]
    for child in n:
      let elemNode = if child.kind == nnkExprColonExpr: child[1] else: child
      elems.add parseExpr(elemNode, preamble, ctx)
    mkTupleLit(elems, tupleTy)
  of nnkObjConstr:
    # RFC-chapulin-hardening P2a (walker v52->53): a value-object (non-ref)
    # constructor `Point(x: a, y: b)` used as an EXPRESSION (`let p =
    # Point(x: a, y: b)`, an object `return`). Previously `nnkObjConstr` was
    # recognised ONLY inside `nnkRaiseStmt`'s `newException(T, msg)` shape
    # (above); any OTHER value-object construction fell through to the CR-2a
    # catch-all below, tainting the whole run to `sxUnknown` (SND-1).
    #
    # A value object's `IRType` is `itTuple`-shaped: `classifyType`
    # (`dsl_typebridge.nim`'s nominal-object plain-record path, already
    # exercised today by object-typed SUT PARAMETERS — see
    # `tsymex_phase4_tuple.nim`'s `Point` case) resolves an `nnkObjConstr`
    # EXPRESSION node's `getTypeInst` to the object's type symbol, yielding
    # `tTuple(fields, fieldNames, objectName = "Point")` — the SAME shape
    # `nnkTupleConstr` (P1, just above) produces, just with `objectName`
    # populated. So this slice REUSES `iekTupleLit`/`mkTupleLit`/
    # `lowerTupleLit` wholesale (no new IR kind): the itTuple/svTuple
    # witness/runtime machinery already renders objects correctly (they
    # appear as SUT params today) and every existing `iekTupleLit` dispatch
    # site (emitExpr, abstraction.nim, probeProto, canonicalize, …)
    # transfers for free. Reading a field (`p.x`) was ALREADY supported
    # (`nnkDotExpr`'s `itTuple` arm above) — the gap was only construction.
    #
    # Unlike a tuple, `nnkObjConstr` fields may be (a) in ANY order and (b)
    # OMITTED, so we cannot just walk `n`'s children positionally. Build a
    # name -> value-node map from the present fields (skip `n[0]`, the type
    # symbol — fields start at index 1, each an `nnkExprColonExpr[name,
    # valueExpr]`; Nim's object-constructor syntax has no positional form),
    # then walk `objTy.fieldNames` — the TYPE's declared order — filling in
    # each element in that order. A present field parses via the ORDINARY
    # `parseExpr` recursion (same soundness argument as P1: an individually-
    # unsupported field, e.g. `cast[int32](x)`, independently hits the CR-2a
    # catch-all and taints the whole run via SND-1 — Invariant 3, never a
    # false `sxSat`).
    #
    # An OMITTED field is genuinely, soundly zero-initialised by Nim (this is
    # NOT a degrade-to-dummy — it is the real value a running program would
    # observe), so we synthesise it via CR-2a's `zeroValueForType` on the
    # field's OWN `IRType` (mirrors the catch-all's dummy-construction idiom
    # just below, reused here for a genuinely-sound purpose rather than an
    # unsupported-shape fallback). If a field's declared type has NO clean
    # zero-value encoding (`zeroValueForType` returns `nil` — e.g. a nested
    # seq/tuple/variant/ref-typed field), guessing would be UNSOUND, so this
    # degrades that one field the same way the CR-2a catch-all degrades an
    # unsupported node: register a classified `feUnsupportedExprKind` error
    # and emit `mkUnsupported` into the preamble, which taints the whole run
    # to `sxUnknown` via SND-1 — never a false `sxSat` from a guessed zero.
    #
    # RFC-chapulin-hardening P2b (walker v53->54, ADR-0021): `ref object`
    # construction as an expression (`let p = Node(val: x, next: nil)`,
    # `Node = ref object`). `classifyType` UNWRAPS a NAMED `ref object` alias
    # to its VALUE shape EXACTLY like a plain value object (both build the
    # SAME `tTuple(fields, fieldNames, objectName)` — see `dsl_typebridge.nim`
    # "#136: unwrap ref T / ptr T" ~195-205), so this arm is UNCONDITIONALLY
    # reached for ref-object constructors too, already, with NO branch needed
    # to detect "is this a ref object" — P2a's shipped code silently already
    # took this path for `Node(...)`. Empirically confirmed (RFC investigation
    # 2026-07-22): a synthesised `isNew` + field-split-heap-write preamble (the
    # RFC's original sketch) is NOT viable here and was rejected — `let p =
    # new(Node)` for a NAMED ref-object alias crashes TODAY at walk time
    # (`field 'refPointeeTy' is not accessible for type 'IRType' using 'kind =
    # itTuple'`) because Phase 16 D1a deliberately VALUE-MODELS every BARE
    # symbol of a named ref-object-alias type (`classifyType` doesn't unwrap
    # based on how the symbol was bound — a `let`-bound temp is classified
    # IDENTICALLY to a formal param). Any `svRef` a heap-based construction
    # minted would be invisible to every later BARE read of `p.field`
    # elsewhere in the SUT (those reads independently re-derive `p`'s type
    # from the AST, always landing `itTuple`) — see ADR-0021 for the full
    # writeup. So P2b's real (and narrower-than-sketched) new capability is:
    # teach THIS existing value-tuple construction arm to handle ref/ptr-typed
    # FIELDS soundly — `nil` literals, omitted-field nil-init, and a safe
    # degrade for a field value that doesn't resolve to a genuine ref/ptr
    # address. This applies uniformly to value-object AND ref-object
    # constructors alike (a plain `object` can also declare a `next: Node`
    # field), so there is deliberately no ref-vs-value branch here.
    #
    # GUARD (P2b): a VARIANT object constructor (`itVariant`/`itMultiVariant`
    # — `case` fields) reaching this arm would otherwise CRASH — the code
    # below unconditionally reads `objTy.fieldNames`/`.fields`, fields that
    # simply do not exist on those `IRType` kinds (a Nim object-variant
    # `FieldDefect`, empirically confirmed as a hard MACRO-EXPANSION error:
    # `VNode(kind: true, a: x)` for a `case`-fielded `VNode` fails to compile
    # the SUT at all today — a P2a gap this retroactively hardens). Variant
    # ref-object construction is explicitly EXCLUDED (round-2 decision): the
    # field-split heap already declines variant READS (`heRefVariantUnsupported`,
    # ~1299-1305 above); variant construction needs its own ADR revisiting
    # that read gap. Degrade soundly: register the classified error and
    # return a reference to a FRESH, DELIBERATELY-UNBOUND synthetic var name
    # (never `mkLet`/`mkAssign`-bound). This is the SAFE degrade shape — env
    # is `OrderedTable[string, SymVal]`, so any consumer's later `env[name]`
    # lookup (whether via a `let`-bound witness, a nested field access, …)
    # raises `KeyError` (`CatchableError`), caught by the CR-1c safety net
    # (`weInternalWalkerFault` → `sxUnknown`). A type-MISMATCHED dummy (e.g.
    # `mkIntLit(0)` bound under a name whose declared type is `itVariant`)
    # would be UNSAFE instead: a later variant-field access on a
    # wrongly-kinded-but-PRESENT `SymVal` hits `isVariantField`'s
    # `doAssert false` — an uncatchable `Defect`, a genuine process crash, not
    # merely an unmodeled construct.
    #
    # Cluster H Step C (ADR-0022 Round-2) FOLDS IN H4's core here: once
    # `classifyType` flips a NAMED ref-object alias to `itRef`/`itPtr(full
    # pointee)` (dsl_typebridge.nim), THIS constructor node classifies to
    # `itRef`/`itPtr` too — so the P2b value-tuple arm below is superseded by
    # REAL heap construction (`mkNewT` + per-PRESENT-field
    # `mkFieldDerefWrite`) for a ref-object constructor, while a plain
    # (non-ref) `object` constructor keeps the ORIGINAL P2a/P2b value-tuple
    # path unchanged. This MUST land in the SAME change as the classifyType
    # flip (field-read routing has no runtime fallback — see the H1 handoff:
    # leaving construction on `mkTupleLit` would regress P2b-1..8 to
    # `sxUnknown` the instant `classifyType` flips).
    let objTyFull = classifyType(n).ty
    case objTyFull.kind
    of itVariant, itMultiVariant:
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedExprKind,
        severity: sevError,
        msg: "P2b: variant object constructor `" & n.repr & "` (" &
             $objTyFull.kind & ") is out of scope — the field-split heap " &
             "declines variant reads today (heRefVariantUnsupported); " &
             "variant construction needs its own ADR")
      preamble.add mkUnsupported("P2b: variant object constructor " &
                                  "unmodeled (feUnsupportedExprKind)")
      return mkVar(freshSynth(ctx, "p2bVariantUnsupported"))
    of itTuple, itRef, itPtr:
      discard   ## handled below
    else:
      # Defensive: an `nnkObjConstr` node should only ever classify to one of
      # the shapes above. Degrade soundly rather than crash on an unforeseen
      # shape (never reached today — belt-and-suspenders).
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedExprKind, severity: sevError,
        msg: "P2b: object constructor `" & n.repr & "` classified to an " &
             "unexpected shape " & $objTyFull.kind)
      preamble.add mkUnsupported("P2b: unexpected object-constructor shape " &
                                  "(feUnsupportedExprKind)")
      return mkVar(freshSynth(ctx, "p2bUnexpectedShapeUnsupported"))

    let isRefCtor = objTyFull.kind in {itRef, itPtr}
    let isPtrCtor = objTyFull.kind == itPtr
    # `objTy` is always the FULL-fielded object shape: for a ref/ptr
    # constructor it's the pointee (`objTyFull.refPointeeTy`/`.ptrPointeeTy`,
    # built by `classifyObjectRecordFields`); for a plain value object it's
    # `objTyFull` itself (unchanged from pre-H1).
    let objTy = if isRefCtor:
                  (if isPtrCtor: objTyFull.ptrPointeeTy else: objTyFull.refPointeeTy)
                else: objTyFull

    var byName = initTable[string, NimNode]()
    for k in 1 ..< n.len:
      let child = n[k]
      if child.kind == nnkExprColonExpr:
        byName[child[0].strVal] = child[1]

    if isRefCtor:
      # H1 (folds in H4's core): REAL heap construction. `mkNewT` allocates a
      # fresh `Ref_T`; each PRESENT field is written via `mkFieldDerefWrite`.
      # Omitted fields are NOT written here — the universal `isNew`
      # zero-write (`runtime_heap.nim`) zero-initialises EVERY field of a
      # freshly allocated object, so a separate omitted-field zero-write here
      # would be redundant (ADR-0022 Round-2: "H4's separate omitted-field
      # zero-write is DROPPED").
      let tmp = freshSynth(ctx, "p2bNew")
      preamble.add mkNewT(tmp, objTyFull)
      for i, fieldName in objTy.fieldNames:
        if not byName.hasKey(fieldName): continue
        let fty = objTy.fields[i]
        let isRefField = fty.kind in {itRef, itPtr}
        let valNode = byName[fieldName]
        var valIR: IRExpr
        if isRefField and valNode.kind == nnkNilLit:
          # `next: nil` — bare `parseExpr` has no general `nnkNilLit` arm
          # (only the `==`/`!=` comparison special-case above) — lower
          # directly via `mkNil` using the FIELD's OWN declared type.
          valIR = mkNil(fty)
        elif isRefField and refExprClassify(valNode).ty.kind notin {itRef, itPtr}:
          # A ref-typed field initialised from an expression that does NOT
          # resolve to a genuine ref/ptr address (e.g. an unsupported
          # sub-expression). Under H1 a bare named-ref symbol (`next:
          # otherNode`) DOES resolve to `itRef` here (classifyType no longer
          # value-unwraps it) and takes the `else` arm below — real aliasing.
          # This branch is now the narrower genuinely-unresolvable case.
          # Degrade THIS FIELD ONLY (SND-1 taints the whole run to
          # `sxUnknown`) and fill with a type-COMPATIBLE `nil` — never a
          # shape-mismatched value.
          ctx.parseErrors.add SymexErrorInfo(
            kind: feUnsupportedExprKind,
            severity: sevError,
            msg: "P2b: ref-typed field `" & fieldName & "` initialised from `" &
                 valNode.repr & "`, which does not resolve to a genuine " &
                 "ref/ptr address — this expression shape is out of scope")
          preamble.add mkUnsupported("P2b: recursive ref-field construction " &
                                      "from an unresolvable expression " &
                                      "(feUnsupportedExprKind)")
          valIR = mkNil(fty)
        else:
          valIR = parseExpr(valNode, preamble, ctx)
        preamble.add mkFieldDerefWrite(mkVar(tmp), valIR, fty, objTy,
                                       fieldName, isPtrCtor)
      return mkVar(tmp)

    # P2a / P2b (pre-H1 shape, UNCHANGED): a plain (non-ref) value-object
    # constructor still builds a positional `itTuple` literal.
    var elems: seq[IRExpr]
    for i, fieldName in objTy.fieldNames:
      let fty = objTy.fields[i]
      let isRefField = fty.kind in {itRef, itPtr}
      if byName.hasKey(fieldName):
        let valNode = byName[fieldName]
        if isRefField and valNode.kind == nnkNilLit:
          # P2b: `next: nil` — bare `parseExpr` has no general `nnkNilLit` arm
          # (only the `==`/`!=` comparison special-case, ~1104-1146 above) —
          # lower directly via `mkNil` using the FIELD's OWN declared type,
          # matching Nim's real "next is genuinely nil" semantics.
          elems.add mkNil(fty)
        elif isRefField and refExprClassify(valNode).ty.kind notin {itRef, itPtr}:
          # P2b: a ref-typed field initialised from an expression that does
          # NOT resolve to a genuine ref/ptr address. Degrade THIS FIELD ONLY
          # (SND-1 taints the whole run to `sxUnknown`) and fill with a
          # type-COMPATIBLE `nil` — never a shape-mismatched value.
          ctx.parseErrors.add SymexErrorInfo(
            kind: feUnsupportedExprKind,
            severity: sevError,
            msg: "P2b: ref-typed field `" & fieldName & "` initialised from `" &
                 valNode.repr & "`, which does not resolve to a genuine " &
                 "ref/ptr address — this expression shape is out of scope")
          preamble.add mkUnsupported("P2b: recursive ref-field construction " &
                                      "from an unresolvable expression " &
                                      "(feUnsupportedExprKind)")
          elems.add mkNil(fty)
        else:
          elems.add parseExpr(valNode, preamble, ctx)
      elif isRefField:
        # P2b: an OMITTED ref-typed field is genuinely, soundly nil-initialised
        # by Nim — `zeroValueForType` returns `nil` (no encoding) for
        # `itRef`/`itPtr` (its `else: nil` catch-all), so special-case ref/ptr
        # fields to the REAL zero (`mkNil`) before falling to the scalar path.
        elems.add mkNil(fty)
      else:
        let zv = zeroValueForType(fty)
        if zv != nil:
          elems.add zv
        else:
          ctx.parseErrors.add SymexErrorInfo(
            kind: feUnsupportedExprKind,
            severity: sevError,
            msg: "P2a: omitted field `" & fieldName & "` of type " &
                 $fty.kind & " in `" & n.repr &
                 "` has no clean zero-value encoding")
          preamble.add mkUnsupported("P2a: omitted field `" & fieldName &
                                      "` zero-value unmodeled " &
                                      "(feUnsupportedExprKind)")
          # R8 (deferred LOW finding): a KIND-correct placeholder, never a
          # bare `mkIntLit(0)` that would mistype a non-scalar field and
          # crash downstream with an unclassified `weInternalWalkerFault`
          # (see `unsupportedFieldPlaceholder`'s doc comment). The taint
          # emitted just above already forces `sxUnknown` regardless of this
          # placeholder's content.
          elems.add unsupportedFieldPlaceholder(fty)
    mkTupleLit(elems, objTy)
  else:
    # RFC-chapulin-hardening CR-2a (walker v44): expression-position catch-all
    # safety net. Previously `error()`ed at MACRO-EXPANSION time on any
    # NimNode `kind` not covered by the arms above, aborting compilation
    # outright — strictly worse than `sxUnknown` (the SUT couldn't be
    # analysed at all). Convert to the established mkUnsupported degrade
    # idiom (precedent above: A7-S3 `runeLen(symbolic)`): register a
    # classified `sevError` parseError, emit `mkUnsupported` into the
    # preamble, and return a type-correct dummy resolved from the typed AST
    # via `classifyType(n).ty` — resolvable regardless of `n.kind`.
    # Soundness: `of isUnsupported` taints `Path.uncertain` (SND-1), so any
    # witness produced downstream of this dummy is demoted to `sxUnknown` at
    # the chokepoints — the dummy can NEVER produce a false witness. Because
    # this also registers a `sevError`, it is Class-A and `capForcedUnknown`
    # backstops it independently (belt-and-suspenders). This is the
    # catch-all for the whole expression-position macro-error class
    # (M2/M5/P1/P2a shapes).
    let dummyTy = classifyType(n).ty
    ctx.parseErrors.add SymexErrorInfo(
      kind: feUnsupportedExprKind,
      severity: sevError,
      msg: "CR-2a: unsupported expression kind " & $n.kind & " in `" &
           n.repr & "` — not in the supported expression fragment")
    preamble.add mkUnsupported("CR-2a: unsupported expression kind " &
                                $n.kind & " (feUnsupportedExprKind)")
    let dummy = zeroValueForType(dummyTy)
    if dummy != nil: dummy
    else: mkIntLit(0)  # unreachable: SND-1 taint halts the walker before
                        # this value is ever read (dummyTy has no clean
                        # zero-value encoding, e.g. seq/tuple/variant/ref)

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

# ---- A3 (ADR-0014): closure/inline iterator inlining -------------------------
#
# A `for x in it(args):` whose iterable is a direct call to a user-defined
# iterator is desugared at parse time by INLINING the iterator body — exactly
# as the Nim compiler expands an inline iterator. The transform produces only
# existing IR (isWhile/isIf/isLet/…), reuses the whole walker (including the
# `isWhile` bounded-unroll), and needs no new IR node.
#
# Only direct calls qualify in A3-S1. First-class resumable iterators (stored
# in a var, passed as a param) remain sxUnknown (D6, out of A3-S1 scope).
#
# Pre-scans (D2 step 0) mechanize all degradation promises so no unsound path
# is ever silently mis-modeled (Invariant 3).

proc hasYieldShallow(n: NimNode): bool =
  ## True iff `n` contains ≥1 `nnkYieldStmt` outside nested routine
  ## definitions. Used for pre-scan 0(a): require at least one surface yield
  ## so a post-transf state-machine lowering (which removes yield leaves) is
  ## caught and degraded (ADR-0014 D2-0a, CRIT-4).
  case n.kind
  of nnkYieldStmt: return true
  of nnkProcDef, nnkFuncDef, nnkIteratorDef, nnkLambda,
     nnkTemplateDef, nnkMacroDef: return false  ## don't cross routine boundary
  else:
    for c in n:
      if hasYieldShallow(c): return true
    false

proc hasReturnShallow(n: NimNode): bool =
  ## True iff `n` contains a `nnkReturnStmt` outside nested routines.
  ## Pre-scan 0(b): a bare iterator `return` (early-finish) inlines to a
  ## proc-`return` which either drops the path or leaves a caller `retSym`
  ## unconstrained → false positive (CRIT-1, ADR-0014 D4-3).
  case n.kind
  of nnkReturnStmt: return true
  of nnkProcDef, nnkFuncDef, nnkIteratorDef, nnkLambda,
     nnkTemplateDef, nnkMacroDef: return false
  else:
    for c in n:
      if hasReturnShallow(c): return true
    false

proc hasKindShallow(n: NimNode, kinds: set[NimNodeKind]): bool =
  ## Shared walk behind `hasBreakContinueShallow`/`hasContinueShallow`: true
  ## iff `n` contains a node whose kind is in `kinds`, outside nested loops
  ## or routines (both stop the descent at the same boundary kinds — only
  ## the matched-kind set differs between the two callers).
  if n.kind in kinds: return true
  case n.kind
  of nnkWhileStmt, nnkForStmt: return false     ## nested loop owns break/continue
  of nnkProcDef, nnkFuncDef, nnkIteratorDef, nnkLambda,
     nnkTemplateDef, nnkMacroDef: return false
  else:
    for c in n:
      if hasKindShallow(c, kinds): return true
    false

proc hasBreakContinueShallow(n: NimNode): bool =
  ## True iff `n` (the raw for-body) contains `break`/`continue` outside
  ## nested loops or routines. Pre-scan 0(c): for a finite (straight-yield)
  ## iterator the inlined body has no enclosing while, so `break` hits
  ## loopStack.len==0 → path dropped while later inlined yields still run →
  ## wrong surviving state → false positive (CRIT-2/SF-1, ADR-0014 D4-2).
  hasKindShallow(n, {nnkBreakStmt, nnkContinueStmt})

proc substIteratorParams(n: NimNode,
                         paramSubst: Table[string, string]): NimNode =
  ## Deep-copy `n`, replacing every `nnkSym`/`nnkIdent` whose `strVal` is
  ## a key in `paramSubst` with a fresh `nnkIdent` of the mapped gensym'd
  ## name. Only USE sites are affected: formal params never appear as
  ## declaration-site `nnkSym` inside the body (they are the routine's own
  ## formals, not body-declared locals), so `classifyType` on declaration-
  ## site identifiers is unaffected. Does NOT descend into nested routines
  ## to avoid capturing their params (different scope).
  if n.kind in {nnkSym, nnkIdent}:
    let s = n.strVal
    if s in paramSubst:
      return ident(paramSubst[s])
    return n
  if n.kind in {nnkProcDef, nnkFuncDef, nnkIteratorDef, nnkLambda,
                nnkTemplateDef, nnkMacroDef}:
    return n   ## own scope — do not substitute inside
  result = n.copyNimNode()
  for c in n:
    result.add substIteratorParams(c, paramSubst)

proc sameSym(a, b: NimNode): bool =
  ## RFC-chapulin-hardening R6 (ADR-0025 hardening). True iff `a` and `b` are
  ## BOTH `nnkSym` nodes denoting the SAME BINDING (true symbol identity), not
  ## merely the same printed name. Two distinct symbols that happen to share a
  ## base name (e.g. a gensym'd template-injected `i` shadowing an outer loop
  ## `i`) must compare false here.
  ##
  ## Empirically confirmed (probe against this Nim version, 2.2.10): the
  ## stdlib `macros.==(a, b: NimNode): bool` (magic `EqNimrodNode`) compares
  ## SYMBOL IDENTITY for `nnkSym` nodes — two references to the same binding
  ## compare `true`; two distinct same-named bindings in disjoint scopes
  ## compare `false`. This is exactly the semantics needed here, so `==` is
  ## used directly rather than a hand-rolled key (e.g. `.strVal` comparison,
  ## which the R6 finding identified as unsound — it matches on the printed
  ## name only).
  a.kind == nnkSym and b.kind == nnkSym and a == b

proc refersToSym(n: NimNode, sym: NimNode): bool =
  ## RFC-chapulin-hardening R2 (ADR-0025). True iff `n`'s subtree contains any
  ## `nnkSym` reference to the SAME BINDING as `sym` (via `sameSym`, i.e. true
  ## symbol identity — R6). Used to reject a scan-idiom match whose `bound`
  ## expression is NOT loop-invariant (reads the loop counter itself, e.g.
  ## `while i < (n - i) and ...: inc i`) — the closed-form rewrite evaluates
  ## `bound` ONCE at loop entry, so a bound that depends on `i` would silently
  ## change the program's semantics (a false-SAT/false-witness class bug).
  if sameSym(n, sym): return true
  for c in n:
    if refersToSym(c, sym): return true
  false

proc unwrapHidden(n: NimNode): NimNode =
  ## Strips compiler-inserted PASSTHROUGH wrapper nodes — `nnkHiddenAddr`,
  ## `nnkHiddenDeref`, `nnkHiddenStdConv` — to reach the underlying semantic
  ## operand, e.g. to see past a `var`/`sink` formal's lvalue wrapping or an
  ## auto-converted argument when what's needed is the RAW node shape or
  ## symbol identity (bracket-expr recognition, `sameSym` receiver matching,
  ## augmented-assignment LHS extraction, and similar).
  ##
  ## This is a BLIND, unconditional peel: unlike the dedicated one-level
  ## unwraps beside the `nnkDerefExpr`/`nnkHiddenDeref` arms of `parseExpr`
  ## and the `nnkAsgn`/`nnkDotExpr` write arms (Phase 15 R1/R3/R6/R8b,
  ## ADR-0010), it does NOT distinguish a REAL ref/ptr dereference from the
  ## `var`-ness lvalue indirection the compiler wraps around a by-ref formal
  ## — collapsing that distinction there would defeat the itRef/itPtr
  ## detection those sites depend on. Only use this helper where the result
  ## feeds a NAME/SHAPE match and any residual ref/ptr semantics of the
  ## innermost `nnkHiddenDeref` are irrelevant to that match.
  result = n
  while result.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv} and
        result.len >= 1:
    result = result[result.len - 1]

proc tryRecognizeScanIdiom(n: NimNode, preamble: var seq[IRStmt],
                            ctx: ParseCtx): Option[IRStmt] =
  ## RFC-chapulin-hardening Q1 (ADR-0025, walker v60). Recognizes ONLY the
  ## canonical bounded forward scan-to-literal-delimiter idiom:
  ##   while <i> < <bound> and <s>[<i>] != <lit>: inc <i>
  ## (body may also be the equivalent `<i> = <i> + 1`) and rewrites it to the
  ## closed form
  ##   <i> = (let p = <s>.find($<lit>, <i>);
  ##          if p == -1 or p >= <bound>: <bound> else: p)
  ## eliminating the loop — a finite k-unroll cannot decide a SYMBOLIC trip
  ## count, but Sequence-theory `indexOf` can. `<i>`'s CURRENT value (read
  ## as-is, whatever it was bound/rebound to) is used as the find start, so a
  ## LATER scan whose `var j = i + 1` binding derives from an EARLIER scan's
  ## result composes for free — no special-casing needed for dependent
  ## chains (RFC's finding #6, Q1's headline capability).
  ##
  ## Deliberately NARROW (a decidability-boundary recognizer, not a general
  ## loop solver): `==`-guards (skip-while), char-class/predicate scans
  ## (`s[i] in {'0'..'9'}`, `isDigit(s[i])`), backward scans, non-`inc`
  ## bodies, bodies with extra statements, and non-char delimiters are all
  ## OUT of scope and must fall through UNRECOGNIZED to the caller's
  ## unchanged `mkWhile` k-unroll path. When in doubt this returns `none` —
  ## a false-positive recognition would be UNSOUND (silently changes the
  ## program's semantics), which is strictly worse than leaving the loop as
  ## a clean `sxUnknown` degrade.
  ##
  ## `n` is the raw (untouched) `nnkWhileStmt` node, inspected BEFORE any
  ## `parseExpr`/`parseStmt` call on its `cond`/`body` children — both call
  ## sites (this proc's own `nnkWhileStmt` handling below, and
  ## `parseStmtInner`'s) invoke this FIRST. On a match, any synthetic
  ## lets/ifs the closed form needs are appended to `preamble` (caller-owned,
  ## merged exactly like any other preamble contribution) and the final
  ## `i = ...`-equivalent statement is returned as the whole loop's
  ## replacement; on `none`, the caller falls through to `mkWhile` untouched.
  if n.kind != nnkWhileStmt or n.len != 2: return none(IRStmt)
  let cond = n[0]
  let body = n[1]

  # ---- guard shape: `<i> < <bound> and <s>[<i>] != <lit>` (and-shaped,
  # short-circuit order: the bound check FIRST) ----
  if cond.kind != nnkInfix or cond.len != 3 or cond[0].strVal != "and":
    return none(IRStmt)
  let ltPart = cond[1]
  if ltPart.kind != nnkInfix or ltPart.len != 3 or ltPart[0].strVal != "<":
    return none(IRStmt)
  # `!=` desugars (via a template) to
  # `StmtListExpr(Empty, Prefix("not", Infix("==", lhs, rhs)))` in the typed
  # AST (confirmed empirically via a `treeRepr` dump) — NOT a plain
  # `nnkInfix "!="`. Unwrap the StmtListExpr wrapper, then match the
  # not(==) shape; also accept a literal `nnkInfix "!="` defensively in case
  # a different desugaring reaches here (e.g. a future compiler version).
  var nePart = cond[2]
  while nePart.kind == nnkStmtListExpr and nePart.len >= 1:
    nePart = nePart[nePart.len - 1]
  var idxExprRaw: NimNode
  var litNodeRaw: NimNode
  if nePart.kind == nnkInfix and nePart.len == 3 and nePart[0].strVal == "!=":
    idxExprRaw = nePart[1]
    litNodeRaw = nePart[2]
  elif nePart.kind == nnkPrefix and nePart.len == 2 and nePart[0].strVal == "not" and
       nePart[1].kind == nnkInfix and nePart[1].len == 3 and nePart[1][0].strVal == "==":
    idxExprRaw = nePart[1][1]
    litNodeRaw = nePart[1][2]
  else:
    return none(IRStmt)

  let iNode = ltPart[1]
  let boundNode = ltPart[2]
  if iNode.kind != nnkSym or classifyType(iNode).ty.kind != itInt:
    return none(IRStmt)
  if classifyType(boundNode).ty.kind != itInt:
    return none(IRStmt)
  # R2 (CRITICAL soundness fix): the closed form evaluates `bound` ONCE at
  # loop entry, so it is only a valid rewrite of the guard when `bound` is
  # LOOP-INVARIANT. The body shape checked below constrains the loop's ONLY
  # mutated variable to be `i` itself, so `bound` is loop-invariant iff it
  # does not reference `i` at all (e.g. `while i < (n - i) and ...: inc i`
  # has a REAL guard of `2*i < n`, not the fixed `bound = n` the closed form
  # would fabricate — a false witness / wrong verdict, not just imprecision).
  if refersToSym(boundNode, iNode):
    return none(IRStmt)

  let idxExpr = unwrapHidden(idxExprRaw)
  if idxExpr.kind != nnkBracketExpr or idxExpr.len != 2:
    return none(IRStmt)
  let sNode = idxExpr[0]
  let idxInBracket = idxExpr[1]
  if sNode.kind != nnkSym or classifyType(sNode).ty.kind != itString:
    return none(IRStmt)
  if not sameSym(idxInBracket, iNode):
    return none(IRStmt)

  let litNode = unwrapHidden(litNodeRaw)
  if litNode.kind != nnkCharLit:
    return none(IRStmt)

  # ---- body shape: EXACTLY `inc <i>` (default step) or `<i> = <i> + 1` ----
  # The typed AST materialises `inc i`'s default step explicitly as a 3rd
  # child (`Command(Sym "inc", Sym "i", IntLit 1)`), not an implicit 2-child
  # form — confirmed empirically via a treeRepr dump. Accept either arity, but a
  # 3rd child MUST be the literal `1` (an explicit non-1 step, e.g. `inc(i,
  # 2)`, is scope-narrowing: NOT the canonical idiom).
  # A single-statement while body is NOT always wrapped in `nnkStmtList` —
  # for a bare `inc i` the typed AST's `n[1]` IS the `Command` node directly
  # (confirmed empirically). Accept both shapes; a genuine
  # multi-statement body (`nnkStmtList` with len != 1) is out of scope.
  let stmt =
    if body.kind == nnkStmtList:
      if body.len != 1: return none(IRStmt)
      body[0]
    else:
      body
  var bodyMatched = false
  if stmt.kind in {nnkCall, nnkCommand} and stmt.len in {2, 3} and
     stmt[0].kind == nnkSym and stmt[0].strVal == "inc":
    let recv = unwrapHidden(stmt[1])
    let stepOk = stmt.len == 2 or
                 (stmt[2].kind == nnkIntLit and stmt[2].intVal == 1)
    bodyMatched = stepOk and sameSym(recv, iNode)
  elif stmt.kind == nnkAsgn and stmt.len == 2:
    let lhs = unwrapHidden(stmt[0])
    let rhs = stmt[1]
    bodyMatched = sameSym(lhs, iNode) and
                  rhs.kind == nnkInfix and rhs.len == 3 and rhs[0].strVal == "+" and
                  sameSym(rhs[1], iNode) and
                  rhs[2].kind == nnkIntLit and rhs[2].intVal == 1
  if not bodyMatched:
    return none(IRStmt)

  # ---- shape matched: emit the closed form ----
  # `sIR`/`boundIR` are pure (a string param/local and an int expression with
  # no side effects reachable through this restricted symex fragment), so
  # reusing them twice below (once in the `p>=bound` comparison, once in the
  # `bound`-clamp branch) is semantically exact — identical to the original
  # loop guard re-evaluating `<bound>` on every iteration check.
  let sIR = parseExpr(sNode, preamble, ctx)
  let iIR = parseExpr(iNode, preamble, ctx)
  let boundIR = parseExpr(boundNode, preamble, ctx)
  let litChar = char(litNode.intVal and 0xFF)
  let litIR = mkStrLit($litChar)
  let findIR = mkStrOp(iekStrFind, "find", @[sIR, litIR, iIR])
  let p = freshSynth(ctx, "scanFind")
  preamble.add mkLet(p, tInt(64), findIR)
  let noMatchCond = mkBinop(bOr,
    mkBinop(bEq, mkVar(p), mkIntLit(-1)),
    mkBinop(bGe, mkVar(p), boundIR))
  some(mkIf(
    @[mkBranch(noMatchCond, mkAssign(iNode.strVal, boundIR))],
    mkAssign(iNode.strVal, mkVar(p))))

proc hasContinueShallow(n: NimNode): bool =
  ## True iff `n` contains a `nnkContinueStmt` outside a nested loop/routine
  ## boundary (mirrors `hasBreakContinueShallow`'s nesting rules, but
  ## continue-only — R14: only `continue` can skip a trailing guard-refresh
  ## statement; `break` exits the loop outright, so a stale post-break guard
  ## is never checked again and is harmless).
  hasKindShallow(n, {nnkContinueStmt})

proc mkRotatedGuardWhile(cond: IRExpr, body: IRStmt, guardPre: seq[IRStmt]): IRStmt =
  ## The pre-R14 do-while rotation (former `mkGuardedWhile`'s guarded path),
  ## RETAINED for the narrow case where it is PROVABLY safe: `guardPre` must
  ## re-run every real iteration for some reason other than a clean and-split
  ## (a plain guard's ordinary hoisting — e.g. a nested `let`, or even a
  ## no-op structural artifact of the typed AST — or a nested and-chain), AND
  ## the loop body contains no `continue` that could ever skip the trailing
  ## refresh. Callers MUST have already established `not
  ## hasContinueShallow(rawBodyNode)` before calling this. See
  ## `mkShortCircuitWhile`'s doc comment for why a bare non-empty preamble is
  ## NOT itself evidence of a short-circuit fault needing the and-split or a
  ## degrade.
  if guardPre.len == 0:
    mkWhile(cond, body)
  else:
    let rotatedBody = mkBlock(@[body] & guardPre)
    mkBlock(guardPre & @[mkWhile(cond, rotatedBody)])

proc mkShortCircuitWhile(guardNode: NimNode, rawBodyNode: NimNode,
                         body: IRStmt, ctx: ParseCtx): IRStmt =
  ## RFC-chapulin-hardening R14 (CRITICAL soundness fix). REPLACES the old
  ## `mkGuardedWhile` do-while rotation as the DEFAULT: that rotation
  ## re-evaluated a short-circuit guard's hoisted preamble as a TRAILING
  ## statement in the loop body (`<body>; <guardPre>`). `walkBlock`
  ## (runtime.nim) stops processing a block's remaining statements once a
  ## statement returns zero paths — which is exactly what `continue` does
  ## (siphons the path into `continuePaths`, returns `@[]`). So a `continue`
  ## skipped the trailing guard-refresh, the guard temp went stale, and the
  ## NEXT guard check ran against old loop-variable state — a false verdict
  ## (confirmed repro: a `continue` in a `while i < s.len and s[i] != 'z':
  ## inc i; continue` body).
  ##
  ## THE FIX (preferred): desugar a short-circuit `and` at the LOOP level
  ## instead of hoisting a guard temp. `while (A and B): body` (B carrying an
  ## inline defect fork, e.g. `s[i]`) becomes
  ##   while A:                 # A is the REAL loop guard
  ##     <B's preamble>         # B's hoisted stmts (re-run every real iter)
  ##     if not B: break        # short-circuit exit when B is false
  ##     body
  ## B is lowered INSIDE the body, which the walker only enters when guard A
  ## holds — so the path entering the body already has A in its path
  ## condition, and B's inline fault forks guarded FOR FREE by loop semantics
  ## (no `sc` temp, no rotation, no deposit rewriting). `continue` jumps to
  ## the top of `while A`, re-evaluating A and re-running B's preamble at the
  ## body top — exactly Nim's re-evaluation, so it is continue-safe BY
  ## CONSTRUCTION regardless of what the body does. A is a REAL SAT-able
  ## guard (not `while true`), so Z3 prunes cleanly — no path-frontier
  ## blowup under nesting.
  ##
  ## THE SUBTLETY (why this is NOT simply "non-empty preamble ⇒ split-or-
  ## degrade"): a while guard's parse can hoist a non-empty preamble for
  ## reasons that have NOTHING to do with short-circuit `and`/`or` fault
  ## guarding — e.g. `(a div b) > i` semchecks to a trivial
  ## `nnkStmtListExpr(Empty, Infix("<", i, Infix("div", a, b)))` (the `>`
  ## operator's own desugaring artifact), whose lone leading `Empty` child
  ## still parses to one (no-op) preamble statement (CR-1b's
  ## `nnkStmtListExpr` handling, unconditionally used for the "value-
  ## returning multi-statement body" shape). Treating ANY non-empty preamble
  ## as "must be a fault guard, therefore split-or-degrade" over-degrades
  ## these ordinary shapes to `sxUnknown` — a real regression (caught by
  ## `tsymex_r1_draingap.nim`'s `whileDivZero`, whose `(a div b) > i` guard
  ## has no `and`/`or` at all). The actual hazard is narrower: a preamble
  ## that must re-run every real iteration is UNSAFE to hoist via the old
  ## rotation ONLY when the body contains a `continue` that could skip the
  ## refresh. So: whenever the clean and-split (above) is not available, fall
  ## back to the pre-R14 rotation (`mkRotatedGuardWhile`) IF AND ONLY IF the
  ## raw body provably contains no `continue` (`hasContinueShallow`) —
  ## otherwise sound-degrade (Invariant 3: never a false verdict).
  ##
  ## Outcomes, decided by inspecting the RAW (untouched) guard node:
  ##  1. Top-level `A and B`, A a simple (non-hoisting) guard, B carrying the
  ##     fault (inline defect-fork op, or its own hoisted preamble) → the
  ##     faithful split above. Continue-safe unconditionally — does not even
  ##     consult `hasContinueShallow`.
  ##  1b. Top-level `A and B`, NEITHER side carries a fault → no special
  ##     handling needed at all; reconstruct the plain flat guard
  ##     `mkBinop(bAnd, condA, condB)`.
  ##  2. A top-level `and` whose LHS `A` itself required hoisting (a nested
  ##     short-circuit buried in `A`, e.g. `(X and Y) and B`) — splitting only
  ##     the outer `and` would leave `A`'s own guard temp exactly as stale as
  ##     the bug this proc fixes, so the clean split doesn't apply. Falls
  ##     back to the rotation (body continue-free) or sound-degrades
  ##     (body has continue). Rare.
  ##  3. Anything else (a plain non-and/or guard whose parse hoists a
  ##     preamble for any reason, or a top-level `or` with a fault) — same
  ##     fallback: rotation (continue-free) or sound-degrade (has continue).
  ##  4. No preamble at all needed for the guard — PLAIN `mkWhile(cond,
  ##     body)`, byte-identical to the pre-R1B fast path. This also covers an
  ##     UNBOUNDED single-expr guard with a genuinely-reachable fault (e.g.
  ##     `while s[i] != 'z'`) — R1's drain correctly keeps forking the real
  ##     IndexDefect; do NOT degrade it.
  ##
  ## Shared by BOTH `nnkWhileStmt` arms (`parseStmtInner` and the
  ## `parseIterBodyStmt` for/iterator-body context) so they stay consistent.
  let bodyHasContinue = hasContinueShallow(rawBodyNode)
  if guardNode.kind == nnkInfix and guardNode.len == 3 and
     guardNode[0].strVal == "and":
    let aNode = guardNode[1]
    let bNode = guardNode[2]
    var preA: seq[IRStmt]
    let condA = parseExpr(aNode, preA, ctx)
    var preB: seq[IRStmt]
    let condB = parseExpr(bNode, preB, ctx)
    let bHasFault = rhsHasInlineDefectFork(condB) or preB.len > 0
    if preA.len == 0 and bHasFault:
      # Case 1: faithful and-split. Continue-safe by construction.
      let breakIfNotB = mkIf(@[mkBranch(mkUnop(uNot, condB), mkBreak())], nil)
      let loopBody = mkBlock(preB & @[breakIfNotB, body])
      mkWhile(condA, loopBody)
    elif preA.len == 0 and not bHasFault:
      # Case 1b: no fault anywhere in this and-guard — plain flat guard
      # (identical to D1c's own fast path for the same node).
      mkWhile(mkBinop(bAnd, condA, condB), body)
    elif not bodyHasContinue:
      # Case 2, continue-free: A itself needed hoisting (nested
      # short-circuit) — safe to fall back to the pre-R14 rotation since
      # there is no `continue` to ever skip the refresh.
      mkRotatedGuardWhile(mkBinop(bAnd, condA, condB), body, preA & preB)
    else:
      # Case 2, continue present: no safe re-run mechanism for this rare
      # nested shape — sound-degrade (Invariant 3: never a false verdict).
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedOp, severity: sevError,
        msg: "R14: short-circuit while-guard shape unmodeled (nested " &
             "and-chain with a fault on the guard's LHS, body contains " &
             "continue) — sound degrade")
      mkUnsupported("R14: short-circuit while-guard shape unmodeled " &
        "(nested and-chain with a fault on the guard's LHS, body contains " &
        "continue) — sound degrade")
  else:
    var tmpPre: seq[IRStmt]
    let cond = parseExpr(guardNode, tmpPre, ctx)
    if tmpPre.len == 0:
      # Case 4: no preamble needed at all — plain fast path.
      mkWhile(cond, body)
    elif not bodyHasContinue:
      # Case 3, continue-free: whatever the preamble is for (ordinary
      # hoisting, an `or`-guard's fault, a nested fault — it does not matter
      # WHY), it is safe to re-run via the pre-R14 rotation since there is no
      # `continue` to ever skip the refresh.
      mkRotatedGuardWhile(cond, body, tmpPre)
    else:
      # Case 3, continue present: no clean and-split is available (an
      # `or`-guard with a fault, or a fault nested deeper) and the rotation
      # is unsafe here — sound-degrade (Invariant 3: never a false verdict).
      ctx.parseErrors.add SymexErrorInfo(
        kind: feUnsupportedOp, severity: sevError,
        msg: "R14: short-circuit while-guard shape unmodeled (or-with-fault " &
             "/ nested, body contains continue) — sound degrade")
      mkUnsupported("R14: short-circuit while-guard shape unmodeled " &
        "(or-with-fault / nested, body contains continue) — sound degrade")

proc parseIterBodyStmt(n: NimNode,
                       iterVarBindings: seq[(string, IRType)],
                       forBodyNode: NimNode,
                       ctx: ParseCtx): IRStmt =
  ## Parse an iterator body node (after param-subst), transforming each
  ## `nnkYieldStmt(e)` into bound let(s) followed by the for-body.
  ##
  ## Single loop variable (iterVarBindings.len == 1, A3-S1):
  ##   block: let <iterVar> = e; <forBody>
  ##
  ## Multiple loop variables (A3-S2a tuple-yield):
  ##   e MUST be an explicit tuple constructor `(e1, e2, …)` (after peeling any
  ##   `nnkHiddenSubConv` wrapper that semcheck inserts for typed tuple returns).
  ##   Emits one `let` per loop variable:
  ##     block: let a = e1; let b = e2; …; <forBody>
  ##   A non-constructor yield (e.g. `yield myTupleVar`) degrades to
  ##   mkUnsupported (sound — Invariant 3; indirect tuple var out of scope).
  ##
  ## `iterVarBindings[k]` carries the k-th loop var name and its IRType from
  ## the iterator's declared formal return type (not derived from the yield
  ## expression — avoids classifyType failures on untyped literal AST nodes
  ## in pre-transf `getImpl` output, ADR-0014).
  ##
  ## Compound control-flow nodes (StmtList, While, If) are recursed into;
  ## all other nodes delegate to the normal parseStmt.
  ## The existing `isWhile` bounded-unroll (maxLoopUnwind) applies unchanged
  ## to any `while` in the inlined body (ADR-0014 D3).
  case n.kind
  of nnkYieldStmt:
    if iterVarBindings.len == 1:
      # D2 step 3 (single-var, A3-S1): yield rewrite → let <iterVar> = <e>; <forBody>
      # This path is byte-identical to the original A3-S1 implementation.
      var yp: seq[IRStmt]
      let yieldIR = parseExpr(n[0], yp, ctx)
      let bindStmt = mkLet(iterVarBindings[0][0], iterVarBindings[0][1], yieldIR)
      let bodyIR = parseStmt(forBodyNode, ctx)
      var stmts = yp
      stmts.add bindStmt
      stmts.add bodyIR
      if stmts.len == 1: stmts[0] else: mkBlock(stmts)
    else:
      # D2 step 3 (multi-var, A3-S2a): require explicit tuple constructor.
      # Semcheck wraps `yield (e1, e2)` as nnkHiddenSubConv[nnkEmpty, nnkTupleConstr].
      let yieldExprRaw = n[0]
      let tupleConstr =
        if yieldExprRaw.kind == nnkTupleConstr: yieldExprRaw
        elif yieldExprRaw.kind == nnkHiddenSubConv and yieldExprRaw.len >= 2 and
             yieldExprRaw[1].kind == nnkTupleConstr: yieldExprRaw[1]
        else: nil
      if tupleConstr == nil:
        return mkUnsupported("A3-S2a: multi-var for-loop requires explicit tuple " &
          "constructor in yield (got " & $yieldExprRaw.kind &
          " — indirect tuple variable not supported; ADR-0014 S2, Invariant 3)")
      if tupleConstr.len != iterVarBindings.len:
        return mkUnsupported("A3-S2a: arity mismatch — yield tuple has " &
          $tupleConstr.len & " elements, for-loop has " &
          $iterVarBindings.len & " vars (ADR-0014 S2, Invariant 3)")
      # Emit one `let varK = elemK` per loop variable, in order.
      var stmts: seq[IRStmt]
      for k in 0 ..< iterVarBindings.len:
        var elemPre: seq[IRStmt]
        let elemIR = parseExpr(tupleConstr[k], elemPre, ctx)
        for s in elemPre: stmts.add s
        stmts.add mkLet(iterVarBindings[k][0], iterVarBindings[k][1], elemIR)
      let bodyIR = parseStmt(forBodyNode, ctx)
      stmts.add bodyIR
      if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkStmtList, nnkStmtListExpr:
    var stmts: seq[IRStmt]
    for c in n:
      stmts.add parseIterBodyStmt(c, iterVarBindings, forBodyNode, ctx)
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkBlockStmt:
    parseIterBodyStmt(n[n.len - 1], iterVarBindings, forBodyNode, ctx)
  of nnkWhileStmt:
    var wp: seq[IRStmt]
    # RFC-chapulin-hardening Q1 (ADR-0025): try the bounded scan-idiom lift
    # BEFORE building the ordinary k-unrolled `mkWhile` — see
    # `tryRecognizeScanIdiom`'s doc comment for the exact recognized shape.
    let scanLift = tryRecognizeScanIdiom(n, wp, ctx)
    if scanLift.isSome:
      # Closed-form replacement for the whole loop (no loop to re-run) — its
      # preamble `wp` (the hoisted `find` call) runs once, hoisted as before.
      if wp.len > 0:
        var all = wp
        all.add scanLift.get
        mkBlock(all)
      else:
        scanLift.get
    else:
      # `wp` is still empty here (tryRecognizeScanIdiom only appends on the
      # `some(...)` path) and unused below — R14 routes through the shared
      # `mkShortCircuitWhile` helper so a `while i<s.len and s[i]==c` NESTED
      # INSIDE a for/iterator body desugars to the loop-level and-split
      # (guard A re-evaluated by real `while` semantics, B's fault forked
      # inside the body), exactly like the top-level `parseStmtInner` arm —
      # and stays continue-safe by construction (see `mkShortCircuitWhile`).
      let whileBody = parseIterBodyStmt(n[1], iterVarBindings, forBodyNode, ctx)
      mkShortCircuitWhile(n[0], n[1], whileBody, ctx)
  of nnkIfStmt, nnkIfExpr:
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    var allPre: seq[IRStmt]
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        var cp: seq[IRStmt]
        let condIR = parseExpr(arm[0], cp, ctx)
        for cs in cp: allPre.add cs
        let branchBody = parseIterBodyStmt(arm[1], iterVarBindings, forBodyNode, ctx)
        branches.add mkBranch(condIR, branchBody)
      of nnkElse, nnkElseExpr:
        elseBody = parseIterBodyStmt(arm[0], iterVarBindings, forBodyNode, ctx)
      else: discard
    let ifNode = mkIf(branches, elseBody)
    if allPre.len > 0:
      var all = allPre
      all.add ifNode
      mkBlock(all)
    else:
      ifNode
  else:
    # No yield in this subtree — delegate to the normal statement parser.
    # (nnkYieldStmt in an unrecognised context becomes mkUnsupported via
    # parseStmt's default arm — sound degradation, never a false positive.)
    parseStmt(n, ctx)

proc zeroValueForType(ty: IRType): IRExpr =
  ## An uninitialized `var x: T` is zero-initialized by Nim. Return the IR for
  ## T's ZERO value where it is cleanly expressible; `nil` for types whose
  ## default is not modeled in this cycle (the caller then degrades to a
  ## classified `sxUnknown` — sound, never a wrong verdict). Zero-init (NOT a
  ## fresh free symbol) is the sound model: a read-before-write must observe
  ## Nim's guaranteed default, not an arbitrary value (Invariant 3).
  case ty.kind
  of itInt: mkIntLit(0)               ## int (and char, modeled as itInt): 0 / '\0'
  of itBool: mkBoolLit(false)
  of itFloat32: mkFloatLit(0.0, 32)
  of itFloat64: mkFloatLit(0.0, 64)
  of itString: mkStrLit("")           ## Nim `string` default is the empty string
  else: nil                            ## seq/table/set/tuple/variant/ref/… — defer

proc unsupportedFieldPlaceholder(ty: IRType): IRExpr =
  ## RFC-chapulin-hardening R8 (deferred LOW finding, telemetry hygiene). A
  ## KIND-COMPATIBLE placeholder for an omitted `nnkObjConstr` field whose
  ## type `zeroValueForType` declines (no clean zero this cycle). Used
  ## EXCLUSIVELY by the P2a construction-time DEGRADE path, always alongside
  ## a classified `feUnsupportedExprKind` parse-error + `mkUnsupported`
  ## SND-1 taint stmt emitted by the caller — the taint alone already forces
  ## the reported verdict to `sxUnknown` regardless of this placeholder's
  ## content (`isTargetLabel`'s `if p.uncertain: w.sawUnknown = true`
  ## chokepoint never even calls `trySolve`), so this is NEVER real modeling
  ## and NEVER influences the verdict.
  ##
  ## What this DOES fix: before R8, the degrade path filled the field with a
  ## bare `mkIntLit(0)` regardless of the field's actual declared type. For a
  ## NON-scalar field (seq/tuple/…) that is a KIND MISMATCH — `lowerTupleLit`
  ## only assigns a proto for `itInt`/`itBool` fields (see `runtime.nim`), so
  ## the mismatched element silently becomes a wrongly-kinded `SymVal`
  ## sitting where (say) an `svSeq` belongs. If the SUT later performs any
  ## type-appropriate operation on that field (`.len`, indexing, …), the
  ## walker raises a plain `ValueError` (e.g. `iekSeqLen`'s "on non-container
  ## kind=..." arm) — an exception NONE of `runSymexImpl`'s specific carriers
  ## match, so it falls through to the generic `CatchableError` catch-all and
  ## gets reported as `weInternalWalkerFault`, clobbering the
  ## already-registered `feUnsupportedExprKind` classification before
  ## `prog.parseErrors` is ever drained (that only happens if the walk
  ## completes without raising). Building a KIND-matching placeholder here
  ## means ordinary type-appropriate operations succeed structurally (with
  ## meaningless content — irrelevant, since the taint already owns the
  ## verdict), so the walk completes and the classified error surfaces.
  ##
  ## Mirrors the existing ref-field precedent just above in the P2a arm
  ## (`mkNil(fty)` for an unresolved ref-typed field) and Cluster H's
  ## `zeroIRExprForType` sibling (heap-field zero-init): `itRef`/`itPtr` →
  ## `mkNil`; `itTuple` → recurse field-by-field (bounded — Nim forbids
  ## cyclic VALUE nesting). For `itSeq`, an EMPTY seq literal is
  ## kind-correct without attempting to claim it is a REAL modeled zero (this
  ## proc is reached ONLY from the degrade branch, never the sound
  ## `zeroValueForType`-succeeds branch, so it can never promote a field from
  ## "unmodeled" to "real"). The residual `itTable`/`itSet`/`itArray`/
  ## `itVariant`/`itMultiVariant`/`itDistinct`/`itUninterp` kinds have no
  ## literal IR constructor at all today (same set `zeroIRExprForType`
  ## declines) — a same-kind placeholder isn't buildable without new IR
  ## machinery, out of scope for this telemetry-only fix; `mkIntLit(0)`
  ## remains the fallback there, same residual risk as before R8.
  let realZero = zeroValueForType(ty)
  if realZero != nil: return realZero
  case ty.kind
  of itRef, itPtr: mkNil(ty)
  of itSeq: mkSeqLit(@[], ty.seqElemTy)
  of itTuple:
    var elems: seq[IRExpr]
    for f in ty.fields: elems.add unsupportedFieldPlaceholder(f)
    mkTupleLit(elems, ty)
  else: mkIntLit(0)   ## table/set/array/variant/multiVariant/distinct/
                       ## uninterp: no literal constructor exists (residual).

proc refExprClassify(n: NimNode): ClassifiedType =
  ## RFC-chapulin-hardening P2b. Classify whether VALUE expression `n`
  ## genuinely carries a ref/ptr ADDRESS (`itRef`/`itPtr`), reusing the SAME
  ## two-level classify already established for `nil` comparisons
  ## (`nnkInfix`'s `==`/`!=` arm) and recursive ref-object field reads
  ## (`nnkDotExpr`'s R9 extension): `classifyType` handles a BARE symbol
  ## directly (post-Cluster-H-Step-C: `itRef` for a plain named-ref-object
  ## alias, `itVariant` — deliberately, ADR-0022 sub-decision #1 — for a
  ## ref-VARIANT alias); a DERIVED (non-bare) expression re-classifies via
  ## `classifyFieldType` to recover `itRef`/`itPtr` (`classifyType` on a
  ## derived dot-expr node resolves the FIELD's placeholder value shape, not
  ## "this came from a ref field"). Used by the P2b `nnkObjConstr` arm to
  ## decide whether a ref-typed field's VALUE can be soundly stored as-is (an
  ## address) or must be degraded (an expression with no address to store).
  ##
  ## Cluster H Step C (ADR-0022): the `n.kind notin {nnkSym, nnkIdent}`
  ## exclusion below was FLAGGED for deletion by the original H1 brief (as
  ## one of "3 bare-symbol carve-outs suppressing itRef") but is KEPT after
  ## reasoning through the variant interaction (see the twin comment at the
  ## `nnkDotExpr` field-read site, ~1328, for the full argument). Short
  ## version: it is already dead-but-harmless for the new capability (a bare
  ## named-ref symbol now classifies `itRef` at Level 1, so the fallback below
  ## never fires for it), and deleting it would let a bare ref-VARIANT symbol
  ## (value-modelled to `itVariant` on purpose) get mis-recovered to `itRef`
  ## by `classifyFieldType` (which is deliberately variant-BLIND — correct
  ## for genuine FIELD declarations, wrong for a bare top-level symbol).
  var cls = classifyType(n)
  if cls.ty.kind notin {itRef, itPtr} and n.kind notin {nnkSym, nnkIdent}:
    let fc = classifyFieldType(n)
    if fc.ty.kind in {itRef, itPtr}: cls = fc
  cls

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
    # Var receivers may carry HiddenDeref/HiddenAddr — unwrap (unwrapHidden).
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
    # Phase 15 R6 (ADR-0010) + ADR-0013 S3. `p.field = v` — a FIELD WRITE through
    # a `ref object` / `ptr object`. LHS is `nnkDotExpr(nnkHiddenDeref(p), field)`,
    # OR — for a variant ARM field — semcheck wraps that dot-expr in a
    # `nnkCheckedFieldExpr(<dotExpr>, <disc check call>)` (the runtime
    # discriminant guard). Unwrap to the inner dot-expr — the runtime check is
    # modeled symbolically by the walker's arm-field FieldDefect fork (ADR-0013
    # D3), exactly as the READ side does (`of nnkCheckedFieldExpr: parseExpr(n[0])`).
    # Lower to a field-split `isDerefWrite` (`store(heap_<objTid>__<field>, p, v)`
    # — only that field's array changes; an aliased read of the same field sees
    # the write). Checked BEFORE `unwrap` (which would strip the indirection).
    let lhsFW = if n[0].kind == nnkCheckedFieldExpr and n[0].len >= 1: n[0][0]
                else: n[0]
    if lhsFW.kind == nnkDotExpr and lhsFW.len == 2 and
       lhsFW[0].kind in {nnkHiddenDeref, nnkDerefExpr} and lhsFW[0].len >= 1:
      let operand = lhsFW[0][0]
      let opCls = classifyType(operand)
      if opCls.ty.kind in {itRef, itPtr}:
        let isPtr = opCls.ty.kind == itPtr
        let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
        if pointeeTy.kind in {itTuple, itVariant, itMultiVariant}:
          let fieldName = lhsFW[1].strVal
          let fieldTy   = classifyType(lhsFW).ty   ## the field's type
          let ptrIR = parseExpr(operand, preamble, ctx)
          let valIR = parseExpr(n[1], preamble, ctx)
          return mkFieldDerefWrite(ptrIR, valIR, fieldTy, pointeeTy,
                                   fieldName, isPtr)
    let lhs = unwrapHidden(n[0])
    if lhs.kind == nnkBracketExpr and lhs.len == 2:
      let recv = unwrapHidden(lhs[0])
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
      let recv = unwrapHidden(lhs[0])
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
          let rhs = unwrapHidden(n[1])
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
              let rhs = unwrapHidden(n[1])
              let tagIR = parseExpr(rhs, preamble, ctx)
              # Multi-axis disc reassign — static or symbolic, both
              # go through the A4 symbolic IR for now (no Phase 11
              # static path was ever implemented for multi-axis).
              return mkVariantReassignSymbolic(
                recv.strVal, ax.discName, tagIR)
    mkUnsupported(&"unsupported nnkAsgn shape: {n.repr}")
  of nnkWhileStmt:
    var preamble2: seq[IRStmt]
    # RFC-chapulin-hardening Q1 (ADR-0025): try the bounded scan-idiom lift
    # BEFORE building the ordinary k-unrolled `mkWhile` — see
    # `tryRecognizeScanIdiom`'s doc comment for the exact recognized shape.
    let scanLift = tryRecognizeScanIdiom(n, preamble2, ctx)
    if scanLift.isSome:
      # Closed-form replacement for the whole loop (not a `while` at all) —
      # any preamble it needs (e.g. the hoisted `find` call) runs once,
      # exactly as before.
      let whileSt = scanLift.get
      if preamble2.len == 0:
        whileSt
      else:
        var both = preamble2
        both.add whileSt
        mkBlock(both)
    else:
      # `preamble2` is still empty here (tryRecognizeScanIdiom only appends
      # to it on the `some(...)` path above) and unused below — R14 routes
      # through the shared `mkShortCircuitWhile` helper — when the RAW guard
      # is a top-level `A and B` with the fault in `B`, it desugars to `while
      # A: <B's preamble>; if not B: break; body` so guard `A` (a real,
      # SAT-able loop guard) and B's preamble both re-run on every real
      # iteration — including after `continue`, by construction; otherwise it
      # emits the plain `mkWhile(cond, body)` fast path, or a sound
      # `mkUnsupported` degrade for the rare or-with-fault / nested-fault
      # shapes it cannot cleanly split. Identical helper used by the
      # `parseIterBodyStmt` for/iterator-body arm above.
      let body = parseStmt(n[1], ctx)
      mkShortCircuitWhile(n[0], n[1], body, ctx)
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
        # Phase 16 INV: wire to structured seByteIterUnsupported — the parse-time
        # error is added to ctx.parseErrors (drained into prog.parseErrors →
        # r.errors at runtime), then mkUnsupported yields w.sawUnknown = true in
        # the walker, together producing sxUnknown + classified kind (Invariant 3).
        ctx.parseErrors.add SymexErrorInfo(
          kind: seByteIterUnsupported,
          severity: sevError,
          msg: "Phase 15 S3: `for c in s` over a symbolic string — unbounded " &
               "iteration length has no sound bounded encoding (ADR-0006, " &
               "seByteIterUnsupported)")
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
    elif iterExpr.kind == nnkCall and iterExpr.len >= 1 and
         iterExpr[0].kind == nnkSym:
      # Phase 16 A7-S3: intercept `for r in s.runes` / `for r in lit.runes`
      # BEFORE A3 attempts to getImpl/inline the std/unicode `runes` iterator.
      # Origin guard (owner == "unicode") ensures a user-defined `runes` iterator
      # falls through to A3 (or degrades) unchanged — regression-safe.
      # This block uses `return` to exit early; the A3 code below runs only if
      # `break runesA7s3` fires (non-unicode origin → fall through).
      block runesA7s3:
        if iterExpr.len == 2 and iterExpr[0].strVal == "runes":
          let runeIterSym = iterExpr[0]
          let runeIterOwner = runeIterSym.owner
          if runeIterOwner.kind == nnkSym and runeIterOwner.strVal == "unicode":
            let container = iterExpr[1]
            if container.kind in {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
              # Concrete literal: decode runes in Nim at parse time → static unroll.
              # Each rune is bound to iterName as an svInt (Rune → tInt(64), A7-S1).
              # Exact vs Nim: we call Nim's own toRunes (Invariant 3 §Soundness).
              let runeSeq = unicode.toRunes(container.strVal)
              let runeTy = tInt(64, signed = true)
              let body = parseStmt(bodyNode, ctx)
              var stmts: seq[IRStmt]
              for rune in runeSeq:
                stmts.add mkLet(iterName, runeTy,
                                mkIntLit(int64(rune.ord)))
                stmts.add body
              return mkBlock(stmts)
            else:
              # Symbolic string: UTF-8 grouping over an unknown byte stream has
              # no quantifier-free Z3 encoding → seZ3StringIncomplete (ADR-0017).
              # Must NEVER reach the A3 inline path (avoid body parse → possible hang).
              ctx.parseErrors.add SymexErrorInfo(
                kind: seZ3StringIncomplete,
                severity: sevError,
                msg: "A7-S3: `for r in s.runes` over symbolic string — UTF-8 " &
                     "grouping over unknown byte stream; no quantifier-free Z3 " &
                     "encoding (ADR-0017)")
              return mkUnsupported("symex A7-S3: `for r in s.runes` over " &
                                   "symbolic string unsupported (seZ3StringIncomplete)")
          # Non-unicode origin: break to fall through to A3 path below.
      # ---- A3-S1/S2a (ADR-0014): inline direct-call closure/inline iterator ------
      # Placed AFTER the items/pairs arm (which already claimed those iterator
      # syms optimally); fires only for unrecognised direct iterator calls.
      # Collect all loop-variable names. Single-var (S1): n.len == 3, [iterName].
      # Multi-var tuple-yield (S2a): n.len > 3, each n[vi] nnkSym for vi in 0..n.len-3.
      var loopVarNames: seq[string]
      for vi in 0 ..< n.len - 2:
        if n[vi].kind != nnkSym:
          return mkUnsupported("A3-S2a: loop variable at index " & $vi &
            " is " & $n[vi].kind & " (expected nnkSym; ADR-0014 S2)")
        loopVarNames.add n[vi].strVal
      let itSym = iterExpr[0]
      # Try to resolve the callee's implementation. A builtin/magic/unresolvable
      # sym causes getImpl to raise; catch and fall through (→ sxUnknown, sound).
      var impl: NimNode = nil
      try: impl = itSym.getImpl
      except CatchableError: discard
      if impl != nil and impl.kind == nnkIteratorDef:
        let implBody = body(impl)
        # ---- Step 0: soundness pre-scans — ALL must pass; any failure → degrade
        # (a) Require ≥1 surface yield (catches post-transf state-machine lowering)
        if not hasYieldShallow(implBody):
          return mkUnsupported("iterator " & itSym.strVal & " has no surface " &
            "nnkYieldStmt — may be post-transf lowered; cannot inline " &
            "(ADR-0014 D2-0a, CRIT-4)")
        # (b) No bare `return` in body — early-finish mis-modeled by proc-return
        if hasReturnShallow(implBody):
          return mkUnsupported("iterator " & itSym.strVal & " contains `return` " &
            "— early-finish not yet modeled in A3-S1 (ADR-0014 D2-0b, CRIT-1)")
        # (c) No break/continue in the raw for-body (unsound for finite iterators)
        if hasBreakContinueShallow(bodyNode):
          return mkUnsupported("for-body contains `break`/`continue` — unsound " &
            "for finite iterators in A3-S1; lifted in S2 (ADR-0014 D2-0c, CRIT-2)")
        # (d) Recursion guard: if this iterator is already being inlined, degrade
        let itSymName = itSym.strVal
        if itSymName in ctx.activeIterators:
          return mkUnsupported("recursive iterator " & itSymName &
            " — cannot inline (ADR-0014 D2-0d, CRIT-3)")
        # (e) Non-trivial default params that can't safely be evaluated out-of-scope
        let formal = impl[3]  # nnkFormalParams: [retTy, IdentDefs…]
        block checkDefaults:
          var argIdx = 0  # tracks supplied call arg index
          for fi in 1 ..< formal.len:
            let paramDef = formal[fi]
            if paramDef.kind != nnkIdentDefs: continue
            let defaultNode = paramDef[paramDef.len - 1]
            for pj in 0 ..< paramDef.len - 2:
              if argIdx >= iterExpr.len - 1:
                # This param is absent from the call — check its default
                let isLit = defaultNode.kind in
                  {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit,
                   nnkUIntLit, nnkUInt8Lit, nnkUInt16Lit, nnkUInt32Lit, nnkUInt64Lit,
                   nnkFloat32Lit, nnkFloat64Lit, nnkStrLit, nnkRStrLit,
                   nnkTripleStrLit, nnkCharLit, nnkNilLit}
                let isConst = defaultNode.kind == nnkSym and
                              symKind(defaultNode) in {nskConst, nskEnumField}
                if not isLit and not isConst:
                  return mkUnsupported("iterator " & itSymName & " param " &
                    paramDef[pj].strVal & " has non-trivial default — cannot " &
                    "safely evaluate out-of-scope (ADR-0014 D2-0e, N-2)")
              inc argIdx
        # ---- Steps 1-4: inline transform ----
        # D2 step 2: bind each formal param to a gensym'd let.
        ctx.activeIterators.incl itSymName
        var paramSubst = initTable[string, string]()  # param name → gensym'd name
        var preambleStmts: seq[IRStmt]
        var argIdx2 = 0
        for fi in 1 ..< formal.len:
          let paramDef = formal[fi]
          if paramDef.kind != nnkIdentDefs: continue
          let tyNode = paramDef[paramDef.len - 2]
          let cls = classifyType(tyNode)
          let defaultNode = paramDef[paramDef.len - 1]
          for pj in 0 ..< paramDef.len - 2:
            let paramName = paramDef[pj].strVal
            let synthName = freshSynth(ctx, "itp")
            paramSubst[paramName] = synthName
            let argNode =
              if argIdx2 < iterExpr.len - 1: iterExpr[argIdx2 + 1]
              else: defaultNode  # use the pre-checked literal/const default
            var argPre: seq[IRStmt]
            let argIR = parseExpr(argNode, argPre, ctx)
            for s in argPre: preambleStmts.add s
            preambleStmts.add mkLet(synthName, cls.ty, argIR)
            inc argIdx2
        # D2 step 3+4: substitute params in body, rewrite yields, parse.
        # Compute the iterator element type from its DECLARED return type in
        # nnkFormalParams[0]. Using classifyType on the yield EXPRESSION itself
        # (n[0] inside the body) fails for literal yields (e.g. `yield 1`) whose
        # pre-transf AST nodes do not carry runtime type annotations (ADR-0014).
        let yieldElemTyTop = classifyType(formal[0]).ty
        # Build per-variable bindings. Single-var (S1) uses the whole type.
        # Multi-var (A3-S2a) destructures the itTuple fields positionally.
        # Both arity-mismatch and non-itTuple degrade soundly (Invariant 3).
        var iterVarBindings: seq[(string, IRType)]
        if loopVarNames.len == 1:
          iterVarBindings.add (loopVarNames[0], yieldElemTyTop)
        else:
          # Require itTuple return type with matching arity — degrade otherwise.
          if yieldElemTyTop.kind != itTuple:
            ctx.activeIterators.excl itSymName
            return mkUnsupported("A3-S2a: multi-var for requires itTuple iterator " &
              "return type; got " & $yieldElemTyTop.kind &
              " (ADR-0014 S2, Invariant 3)")
          if yieldElemTyTop.fields.len != loopVarNames.len:
            ctx.activeIterators.excl itSymName
            return mkUnsupported("A3-S2a: arity mismatch — iterator tuple has " &
              $yieldElemTyTop.fields.len & " fields, for-loop has " &
              $loopVarNames.len & " vars (ADR-0014 S2, Invariant 3)")
          for k, name in loopVarNames:
            iterVarBindings.add (name, yieldElemTyTop.fields[k])
        let substBody = substIteratorParams(implBody, paramSubst)
        let bodyIR = parseIterBodyStmt(substBody, iterVarBindings, bodyNode, ctx)
        ctx.activeIterators.excl itSymName
        # Combine preamble + inlined body
        if preambleStmts.len > 0:
          preambleStmts.add bodyIR
          mkBlock(preambleStmts)
        else:
          bodyIR
      else:
        mkUnsupported(&"unsupported for-loop iterable: {itSym.strVal} is not a " &
          "resolvable direct iterator call (ADR-0014 D1)")
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
      # ADR-0014 D6: a bare iterator sym in VALUE position (`let it = someIter`)
      # has no supported IR scalar type — `classifyType` would hard-error on the
      # `iterator(...): T` type. Emit an mkUnsupported to set sawUnknown and skip
      # the binding entirely. The subsequent `for x in it(…)` also degrades:
      # D1 uses getImpl at AST level (not the IR env), so the missing env entry
      # is irrelevant; getImpl on a nskLet sym returns IdentDefs, not nnkIteratorDef,
      # so D1 emits mkUnsupported too → sxUnknown (CRIT-5, D6 deferred).
      if valNode.kind == nnkSym and symKind(valNode) == nskIterator:
        stmts.add mkUnsupported("iterator value binding `" & valNode.strVal &
          "` not supported (ADR-0014 D6 deferred)")
        continue
      # Uninitialized `var x: T` (no initializer): the value node is nnkEmpty.
      # Nim zero-initializes, so bind each name to its type's ZERO value rather
      # than reaching parseExpr's hard `error()` on nnkEmpty (which aborts macro
      # expansion — strictly worse than a classified halt). Unmodeled defaults
      # degrade to mkUnsupported → sxUnknown (sound, Invariant 3).
      if valNode.kind == nnkEmpty:
        for j in 0 ..< id.len - 2:
          let classified = classifyType(id[j])
          let zero = zeroValueForType(classified.ty)
          if zero != nil:
            stmts.add mkLet(id[j].strVal, classified.ty, zero)
          else:
            stmts.add mkUnsupported("uninitialized `var` of unmodeled type " &
              $classified.ty.kind & " (zero-init not modeled this cycle)")
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
      ## Phase 16 SND-2: `symexAssume` is filter/prune, NOT assert — it must
      ## NOT fork an `AssertionDefect`. Previously byte-identical to
      ## `symexAssert` (`mkAssert`), which masked `sxUnsat` with a false
      ## `sxRaised(AssertionDefect)` for a violatable assume ahead of a
      ## genuinely-unreachable target. Distinct IR kind: `mkAssume`.
      mkAssume(parseExpr(n[1], preamble, ctx))
    elif n.len >= 2 and n[0].kind == nnkSym and n[0].strVal in ["inc", "dec"] and
         (block:
            # Phase 15 R8 (ADR-0010). `inc`/`dec` are the `{.magic: Inc/Dec.}`
            # ordinal mutators. The GUARD keys on the RECEIVER's type so the
            # normal INT case is UNAFFECTED (it falls through to the int-mutator
            # arm below); ONLY a `ptr`-typed operand is pointer arithmetic. The
            # receiver may carry a semcheck `nnkHiddenAddr`/`nnkHiddenDeref`
            # (the `var T` formal) — unwrap before classifying.
            let recv = unwrapHidden(n[1])
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
            let recv = unwrapHidden(n[1])
            recv.kind == nnkSym and classifyType(recv).ty.kind == itInt):
      # Phase 15 R8. `inc(i)`/`dec(i)` on an INT receiver — the normal ordinal
      # mutation. Lower to the equivalent env rebind `i = i ± y` (`y` defaults to
      # 1) so the int case symexes natively (the `{.magic.}` body is not walked).
      # This keeps inc/dec on int working `as before` while the ptr-operand guard
      # above peels off pointer arithmetic.
      let recv = unwrapHidden(n[1])
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
          # Phase 16 M4 (RFC-chapulin-hardening, Cluster 3): `s.add(x)` — string
          # APPEND on an `itString` receiver — is modeled as the in-place
          # concat-assign `s := s & x`, reusing the EXISTING `iekStrConcat` IR
          # (the same ctor the binary `s & x` expression arm builds, above)
          # rather than inventing a new IR kind. Z3 String theory strings are
          # immutable (ADR-0006), but the MUTATION is soundly modeled by
          # rebinding the receiver's env slot to the concatenation result — no
          # new encoding is needed beyond what `&` already has.
          #
          # Type-classify the ARGUMENT too: `iekStrConcat`'s runtime lowering
          # (`runtime_strings.nim`) `doAssert`s BOTH operands are `svString`.
          # `s.add('c')` (a char arg) classifies to `itInt` (Phase 15 Z3c: char
          # = uint8) — there is no char→1-char-string conversion IR in this
          # engine, so promoting a char arg to `iekStrConcat` would either
          # under-constrain or crash. Out of scope per RFC round-2 note; keep
          # the prior clean `iekStrUnsupported` degrade for a non-string arg
          # (still sound — Invariant 3 — and preserves S11's `addChar` pin).
          # This arm must precede the `itSeq` `add` arm below (a string is NOT
          # an itSeq, but the explicit guard keeps the classification
          # intentional and self-documenting).
          if calleeName == "add" and recvCls.ty.kind == itString and n.len == 3:
            if classifyType(n[2]).ty.kind == itString:
              let argIR = parseExpr(n[2], preamble, ctx)
              return mkAssign(recvName,
                mkStrOp(iekStrConcat, "&", @[mkVar(recvName), argIR]))
            else:
              let argIR = parseExpr(n[2], preamble, ctx)
              return mkAssign(recvName,
                mkStrOp(iekStrUnsupported, "string add (non-string arg)",
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
    # v68 (round 5, chapulin CRITICAL finding): a discarded expression is
    # WALKED, not dropped. Every `discard <expr>` is lowered to a synthetic
    # sink `let`, so its raise/defect forks are searched exactly as a bound
    # use would be. Previously this arm dropped everything except an
    # allowlisted handful (E8's exception intrinsics, then M2's parseInt/
    # parseBiggestInt) to `mkBlock(@[])` — `discard f(x)` never walked `f`,
    # leaving the surrounding verdict vacuously narrow (Invariant 3
    # unsoundness for the call-and-discard idiom). The parseInt allowlist
    # entry is subsumed by the general path (same iekStrToInt via parseExpr,
    # same tInt(64) via classifyType); the exception-intrinsic entry is kept
    # because its sink types are bespoke (`getCurrentException()` binds under
    # `tUninterp("")`, not the ref classification).
    if n.len == 1 and n[0].kind == nnkCall and n[0].len == 1 and
       n[0][0].kind == nnkSym and
       n[0][0].strVal in ["getCurrentException", "getCurrentExceptionMsg"]:
      let exprIR = parseExpr(n[0], preamble, ctx)
      let sinkTy = if n[0][0].strVal == "getCurrentExceptionMsg": tString()
                   else: tUninterp("")
      mkLet(freshSynth(ctx, "discardExn"), sinkTy, exprIR)
    elif n.len == 1 and n[0].kind != nnkEmpty:
      # The sink's type follows the let-section discipline (`classifyType`
      # on the value node; unmodeled types map to the classified
      # `__unsupported` placeholder, not a macro error). A no-scalar-type
      # value IR (lambda/closure) binds under the let-section arm's
      # placeholder-type precedent. `discard` of a `void` expression cannot
      # occur (Nim rejects it), so the node has a type.
      let sinkIR = parseExpr(n[0], preamble, ctx)
      if sinkIR == nil:
        mkBlock(@[])
      elif sinkIR.kind in {iekLambda, iekClosureCall}:
        mkLet(freshSynth(ctx, "discardSink"), tBool(), sinkIR)
      else:
        mkLet(freshSynth(ctx, "discardSink"), classifyType(n[0]).ty, sinkIR)
    else:
      # Bare `discard` (empty child) — genuinely a no-op.
      mkBlock(@[])
  of nnkEmpty, nnkCommentStmt:
    mkBlock(@[])
  of nnkConstSection, nnkBindStmt, nnkMixinStmt:
    # SND-1 (RFC-chapulin-hardening Cluster 1) fallout fix. These three node
    # kinds are ALWAYS pure compile-time hygiene with zero runtime footprint —
    # `bind`/`mixin` only affect identifier resolution inside templates/
    # generics (never emit code), and a proc-local `const` is fully erased by
    # Nim's semantic pass (every reference is constant-folded to a literal at
    # its use site; the `ConstDef` itself binds nothing at runtime). Before
    # SND-1 these fell through to the generic `mkUnsupported` catch-all below,
    # which was harmless because `isUnsupported` was a no-op continuation. But
    # every `assert`/`doAssert` expansion's typed AST is
    # `StmtList[ConstSection(loc, ploc), BindStmt(instantiationInfo),
    # MixinStmt(failedAssertImpl), PragmaBlock[...]]` (verified via
    # `getImpl.treeRepr`) — i.e. EVERY assert unconditionally carries these
    # three siblings immediately before the real `PragmaBlock` the
    # `nnkPragmaBlock` arm above lowers to the `AssertionDefect` raise. Once
    # `isUnsupported` taints `Path.uncertain` (SND-1), those three inert
    # scaffolding statements would poison every subsequent statement on the
    # path — including the assert's own raise, via the `routeRaise`
    # chokepoint — silently demoting every `doAssert`/`assert` to `sxUnknown`.
    # These are genuinely SUPPORTED (safe to skip), not unsupported: treat
    # them as the same no-op as `nnkEmpty`/`nnkCommentStmt` above.
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
  of nnkInfix:
    # Augmented-assignment statement: `<simpleVar> <op>= <rhs>`.
    # After semcheck, `s += x` presents as `nnkInfix(Sym "+=", <lhs>, <rhs>)`.
    # This is the ONLY `nnkInfix` shape that reaches statement-level dispatch —
    # expression-position infixes go through parseExpr, not parseStmtInner.
    #
    # Supported subset: `+=` | `-=` | `*=` with a plain `nnkSym` LHS (after
    # unwrapping hidden var/deref wrappers). Desugars to the same IR that
    # `<var> = <var> <op> <rhs>` would produce, so the walker sees
    # byte-identical IR for both forms (Invariant: same verdict/witness).
    #
    # Phase 16 M4 (RFC-chapulin-hardening, Cluster 3; closes SND-1's Class-B
    # `&=` case): `s &= x` on a STRING LHS is modeled as the in-place
    # concat-assign `s := s & x`, reusing the EXISTING `iekStrConcat` IR (the
    # same ctor the binary `s & x` expression arm builds, ~line 1081) —
    # string concat is a DIFFERENT IR family (`mkStrOp`, not `IRBinop`), so
    # this is a type-classify branch, NOT an addition to `binopForInfix`
    # (which has no `"&"` case and must stay that way — adding one would
    # wrongly imply `&` composes with the numeric-binop family). The branch
    # is taken BEFORE `binopForInfix` is ever called with `"&"`, so its
    # `error()` catch-all is never reached for this op.
    #
    # A non-string LHS (or non-string RHS — `iekStrConcat`'s runtime lowering
    # `doAssert`s both operands `svString`; a char RHS classifies `itInt` and
    # has no char→1-char-string IR, out of scope per M4's round-2 note) keeps
    # the prior clean `mkUnsupported` degrade rather than routing through
    # `binopForInfix("&")`, which would macro-time `error()` (a hard compile
    # abort, NOT a sound sxUnknown degrade — would be a regression).
    #
    # ALL other shapes degrade to mkUnsupported (sound — Invariant 3):
    #   * field LHS (`obj.f += y`) — non-nnkSym after unwrap
    #   * index LHS (`a[i] += y`) — non-nnkSym after unwrap
    #   * any other `<op>=` not in {+=, -=, *=, &=}
    #   * user-defined `op=` proc calls (land as nnkCall, not nnkInfix)
    let augOp = n[0]
    if n.len == 3 and augOp.kind == nnkSym and
       augOp.strVal in ["+=", "-=", "*=", "&="]:
      let lhs = unwrapHidden(n[1])
      if lhs.kind == nnkSym:
        let nm       = lhs.strVal
        let baseOpStr = augOp.strVal[0 .. ^2]  # strip trailing "=": "+=" → "+"
        if baseOpStr == "&":
          let lhsCls = classifyType(lhs)
          if lhsCls.ty.kind == itString and classifyType(n[2]).ty.kind == itString:
            let rhsIR = parseExpr(n[2], preamble, ctx)
            return mkAssign(nm,
              mkStrOp(iekStrConcat, "&", @[mkVar(nm), rhsIR]))
          else:
            return mkUnsupported(
              &"augmented assign: `&=` with non-string LHS/RHS " &
              &"(lhs kind={lhsCls.ty.kind}) not modeled; degrade to " &
              &"sxUnknown (sound, Invariant 3)")
        let bop      = binopForInfix(baseOpStr)
        let rhsIR    = parseExpr(n[2], preamble, ctx)
        return mkAssign(nm, mkBinop(bop, mkVar(nm), rhsIR))
      else:
        return mkUnsupported(
          &"augmented assign: LHS `{n[1].repr}` is not a simple variable " &
          &"(kind={n[1].kind}); degrade to sxUnknown (sound, Invariant 3)")
    mkUnsupported(
      &"augmented assign: operator `{n[0].repr}` not in supported set " &
      &"{{+=,-=,*=,&=}} or wrong AST shape (len={n.len}); " &
      &"degrade to sxUnknown (sound, Invariant 3)")
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
    # v67 (§0 clause (b), dev item 1): this was a macro-time `error()` —
    # the LAST compile wall on the natural seq-slice value path
    # (`getImpl`-inlining system's `[]` died here on its `len` callee).
    # CR-2a-style classified degrade instead: record the parse error
    # (sevError → whole-run sxUnknown via `capForcedUnknown`) and return a
    # synthetic key that is never registered, so the walker's
    # missing-callee arm degrades the path (exactly the geDistinctBarrier
    # / over-cap-instantiation precedent above and below).
    ctx.parseErrors.add SymexErrorInfo(
      kind: feUnsupportedOp, severity: sevError,
      msg: "cannot resolve `getImpl` for callee `" & name &
           "` (generic / private cross-module / built-in / func) — call " &
           "degraded to sxUnknown (feUnsupportedOp)")
    return "__unresolved:" & name
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

proc demoteUnrenderableWitnessTy(ty: IRType): IRType =
  ## RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality). `classifyType`
  ## is a SHARED, widely-reused classifier — it also runs on purely-internal
  ## (non-witness) types, e.g. the return type of an in-body helper call like
  ## `bytes(s): seq[byte]`, which legitimately classifies to `itSeq` even
  ## though `byte`-element seqs have no witness reader. Degrading THOSE would
  ## be over-triggering: it would corrupt internal type modeling for values
  ## that are never rendered as a witness at all (confirmed by a regression:
  ## gating `classifyType` itself broke `.len`/indexing on such internal
  ## values). The renderability gate must therefore apply ONLY at the true
  ## choke point — here, where `parseProc*` classifies a TOP-LEVEL SUT
  ## PARAMETER type, the exact value `emitTyAndReader` (`symex.nim`) will
  ## later be asked to build a witness reader for.
  ##
  ## Only a fixed sub-fragment of `seq`/`Table`/`HashSet` element/key/value
  ## shapes has a witness reader. `isRenderableWitnessTy` (`smt/types.nim`)
  ## is the RECURSIVE renderability predicate over the WHOLE witness type-tree
  ## — it mirrors EXACTLY the type-tree `emitTyAndReader` walks (recursing into
  ## tuple/object fields, array elements, variant arms, distinct bases and ref
  ## pointees), reusing the `isRenderableSeqElemTy`/`isRenderableTableTy`/
  ## `isRenderableSetElemTy` leaf checks so predicate and reader never drift.
  ## This closes the nested-aggregate completeness gap: a parameter that NESTS
  ## an unrenderable `seq[Widget]`/`Table[string,string]`/`HashSet[string]`
  ## inside a tuple / object / array / variant / distinct / ref pointee (not
  ## just a bare top-level `seq`/`Table`/`HashSet`) is demoted to the
  ## `itUninterp("__unsupported_witness:" & s)` placeholder INSTEAD of the real
  ## aggregate type — mirroring CR-2b's `__unsupported:` idiom under a distinct
  ## marker — so `allocateSym` (`smt/runtime.nim`) raises the classified
  ## `SymexClassifiedDegradeError` (`feUnsupportedWitnessType`) at PARAMETER-
  ## ALLOCATION time, before the body is walked and before witness codegen is
  ## ever reached, forcing a WHOLE-RUN `sxUnknown` instead of
  ## `emitTyAndReader`'s `error()` aborting compilation. The DEMOTED unit is
  ## always the WHOLE top-level parameter (sound: the run degrades to
  ## `sxUnknown` regardless of the body, and no dummy is ever rendered as a
  ## false `sxSat`).
  if isRenderableWitnessTy(ty): ty
  else: tUninterp("__unsupported_witness:" & $ty)

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
    var classified = classifyType(tyNode)
    classified.ty = demoteUnrenderableWitnessTy(classified.ty)   ## CR-2c
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
