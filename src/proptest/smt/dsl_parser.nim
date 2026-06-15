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
import std/sets
import ./types
import ./dsl_typebridge
import ./stdlib_models

# ---- emit: macro-time IR → runtime-construction NimNode -----------------------

proc emitBinop(op: IRBinop): NimNode =
  newDotExpr(bindSym"IRBinop", ident($op))

proc emitUnop(op: IRUnop): NimNode =
  newDotExpr(bindSym"IRUnop", ident($op))

proc emitIRType*(t: IRType): NimNode

proc emitExpr*(e: IRExpr): NimNode =
  case e.kind
  of iekIntLit:
    newCall(bindSym"mkIntLit", newLit(e.ival))
  of iekFloatLit:
    newCall(bindSym"mkFloatLit", newLit(e.fval), newLit(e.fwidth))
  of iekBoolLit:
    newCall(bindSym"mkBoolLit", newLit(e.bval))
  of iekVar:
    newCall(bindSym"mkVar", newLit(e.vname))
  of iekBinop:
    newCall(bindSym"mkBinop", emitBinop(e.bop), emitExpr(e.lhs), emitExpr(e.rhs))
  of iekUnop:
    newCall(bindSym"mkUnop", emitUnop(e.uop), emitExpr(e.operand))
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

proc emitStmt*(s: IRStmt): NimNode

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
  of isUnsupported:
    newCall(bindSym"mkUnsupported", newLit(s.reason))

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

proc newParseCtx*(): ParseCtx =
  ParseCtx(procs: initTable[string, ProcSig](),
           parsing: initHashSet[string](),
           synthCounter: 0)

proc freshSynth(ctx: ParseCtx, prefixWord: string): string =
  inc ctx.synthCounter
  "__sym_" & prefixWord & "_" & $ctx.synthCounter

# ---- Forward decls -----------------------------------------------------------

proc parseExpr*(n: NimNode, preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr
proc parseStmt*(n: NimNode, ctx: ParseCtx): IRStmt
proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode,
                          callSite: NimNode = nil)

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

# ---- Expression parser -------------------------------------------------------

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
      mkVar(s)
  of nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    mkStrLit(n.strVal)
  of nnkPar, nnkStmtListExpr:
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkHiddenStdConv, nnkConv, nnkHiddenDeref, nnkHiddenAddr:
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkCheckedFieldExpr:
    # `s.field` on a variant object — the runtime check is over the
    # discriminator; symex just lowers the inner dot-expr.
    parseExpr(n[0], preamble, ctx)
  of nnkInfix:
    let op = binopForInfix(n[0].strVal)
    let l = parseExpr(n[1], preamble, ctx)
    let r = parseExpr(n[2], preamble, ctx)
    mkBinop(op, l, r)
  of nnkPrefix:
    let op = n[0].strVal
    case op
    of "not": mkUnop(uNot, parseExpr(n[1], preamble, ctx))
    of "-":
      # Phase 15 F2: fold `-<float-literal>` into a negated float literal at
      # parse time (covers -0.0 / -Inf) so the walker sees a literal, not uNeg.
      if n[1].kind in {nnkFloatLit, nnkFloat32Lit, nnkFloat64Lit}:
        mkFloatLit(-n[1].floatVal, if n[1].kind == nnkFloat32Lit: 32 else: 64)
      else:
        mkUnop(uNeg, parseExpr(n[1], preamble, ctx))
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
    else:
      error(&"symex: `[]` on unsupported type {lhsCls.ty}", n)
  of nnkDotExpr:
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
    # User-proc call in expression position. A-normalise.
    ensureProcRegistered(ctx, calleeSym, n)
    var argIRs: seq[IRExpr]
    for i in 1 ..< n.len:
      argIRs.add parseExpr(n[i], preamble, ctx)
    let retCls = classifyType(n)
    let synth = freshSynth(ctx, calleeName)
    preamble.add mkCall(calleeName, synth, argIRs, retCls.ty)
    mkVar(synth)
  else:
    error(&"symex: unsupported expression kind {n.kind} in `{n.repr}`", n)

# ---- Statement parser --------------------------------------------------------

proc parseStmtInner(n: NimNode,
                    preamble: var seq[IRStmt],
                    ctx: ParseCtx): IRStmt =
  ## The `preamble` accumulates A-normalised calls from any expression
  ## the surrounding statement contains; callers wrap the resulting
  ## stmt with the preamble before returning.
  case n.kind
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
    if lhs.kind == nnkSym:
      let nm = lhs.strVal
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
      let valIR = parseExpr(valNode, preamble, ctx)
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
    else:
      # User-proc call as a statement (void-return). Only resolvable
      # against typed AST — isolation-mode falls to `isUnsupported`.
      let calleeSym = n[0]
      if calleeSym.kind != nnkSym:
        mkUnsupported(&"call to `{n[0].repr}` not in supported fragment")
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
            ensureProcRegistered(ctx, calleeSym, n)
            var argIRs: seq[IRExpr]
            for i in 1 ..< n.len:
              argIRs.add parseExpr(n[i], preamble, ctx)
            mkCall(calleeName, "", argIRs, tBool())
        else:
          ensureProcRegistered(ctx, calleeSym, n)
          var argIRs: seq[IRExpr]
          for i in 1 ..< n.len:
            argIRs.add parseExpr(n[i], preamble, ctx)
          mkCall(calleeName, "", argIRs, tBool())
  of nnkDiscardStmt, nnkEmpty, nnkCommentStmt:
    mkBlock(@[])
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
  let formal = impl[3]
  # Walk formal params, matching to call args
  var argIx = 1   ## skip n[0] = callee
  for i in 1 ..< formal.len:
    let id = formal[i]
    let tyNode = id[id.len - 2]
    for j in 0 ..< id.len - 2:
      if argIx < callSite.len:
        let argTy = callSite[argIx].getType
        if tyNode.kind == nnkIdent and tyNode.strVal in genericNames:
          result[tyNode.strVal] = argTy
      inc argIx

proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode,
                          callSite: NimNode = nil) =
  if calleeSym.kind notin {nnkSym, nnkIdent}:
    error("symex Phase 3: callee position is not a symbol — got " &
          $calleeSym.kind & " in `" & calleeSym.repr & "`", calleeSym)
  let name = calleeSym.strVal
  if name in ctx.procs or name in ctx.parsing:
    return  ## already known, or actively being parsed (mutual-recursion break)
  let impl = calleeSym.getImpl
  if impl.kind != nnkProcDef:
    error("symex Phase 3: cannot resolve `getImpl` for callee `" & name &
          "` — generic / private cross-module / built-in?", calleeSym)
  ctx.parsing.incl name
  # Detect generic procs. In typed AST, the generic-params live in
  # impl[2] (untyped) or nested in impl[5] (typed). Either way, we
  # use the call's `getType` reads to derive the substitution.
  var typeSubst: Table[string, NimNode]
  let hasGenerics =
    (impl[2].kind == nnkGenericParams) or
    (impl[5].kind == nnkBracket and impl[5].len >= 2 and
     impl[5][1].kind == nnkGenericParams)
  if hasGenerics and callSite != nil:
    typeSubst = gatherTypeSubst(callSite, impl)
  let sig = parseCalleeImpl(impl, ctx, typeSubst)
  ctx.procs[name] = sig
  ctx.parsing.excl name

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
      doAssert preamble.len == 0,
        "single-expr proc body with embedded call — cycle 2 work"
      mkReturnVal(valIR)
    else:
      parseStmt(bodyNode, ctx)
  let nameStr = monoImpl.name.strVal
  ProcSig(name: nameStr, params: params, body: body,
          retTy: retTy, isVoid: isVoid)

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

proc parseProc*(procDef: NimNode): ParseResult =
  procDef.expectKind nnkProcDef
  let formalParams = procDef[3]
  formalParams.expectKind nnkFormalParams
  let ctx = newParseCtx()
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
