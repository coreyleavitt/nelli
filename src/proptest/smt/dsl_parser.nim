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
proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode)

# ---- Binop / unop helpers ----------------------------------------------------

proc binopForInfix(op: string): IRBinop =
  case op
  of "+":   bAdd
  of "-":   bSub
  of "*":   bMul
  of "div": bDiv
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
  of nnkIdent, nnkSym:
    let s = n.strVal
    if s == "true": mkBoolLit(true)
    elif s == "false": mkBoolLit(false)
    else: mkVar(s)
  of nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    mkStrLit(n.strVal)
  of nnkPar, nnkStmtListExpr:
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkHiddenStdConv, nnkConv, nnkHiddenDeref, nnkHiddenAddr:
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkInfix:
    let op = binopForInfix(n[0].strVal)
    let l = parseExpr(n[1], preamble, ctx)
    let r = parseExpr(n[2], preamble, ctx)
    mkBinop(op, l, r)
  of nnkPrefix:
    let op = n[0].strVal
    case op
    of "not": mkUnop(uNot, parseExpr(n[1], preamble, ctx))
    of "-":   mkUnop(uNeg, parseExpr(n[1], preamble, ctx))
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
    # Opaque effectful proc (#137) — fresh-symbolic return, no body walk.
    let calleeName = calleeSym.strVal
    let opaModel = getStdlibModelFor(calleeName, itBool)
    if opaModel.kind == smkOpaqueEffectful:
      var argIRs: seq[IRExpr]
      for i in 1 ..< n.len:
        argIRs.add parseExpr(n[i], preamble, ctx)
      let retCls = classifyType(n)
      let synth = freshSynth(ctx, calleeName)
      preamble.add mkOpaqueCall(calleeName, synth, argIRs, retCls.ty)
      return mkVar(synth)
    # User-proc call in expression position. A-normalise.
    ensureProcRegistered(ctx, calleeSym)
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
    mkUnsupported(&"unsupported nnkAsgn shape: {n.repr}")
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
        if m.kind == smkOpaqueEffectful:
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
            ensureProcRegistered(ctx, calleeSym)
            var argIRs: seq[IRExpr]
            for i in 1 ..< n.len:
              argIRs.add parseExpr(n[i], preamble, ctx)
            mkCall(calleeName, "", argIRs, tBool())
        else:
          ensureProcRegistered(ctx, calleeSym)
          var argIRs: seq[IRExpr]
          for i in 1 ..< n.len:
            argIRs.add parseExpr(n[i], preamble, ctx)
          mkCall(calleeName, "", argIRs, tBool())
  of nnkDiscardStmt, nnkEmpty, nnkCommentStmt:
    mkBlock(@[])
  else:
    mkUnsupported(&"statement kind {n.kind} not in supported fragment")

proc parseStmt*(n: NimNode, ctx: ParseCtx): IRStmt =
  var preamble: seq[IRStmt]
  let inner = parseStmtInner(n, preamble, ctx)
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

proc parseCalleeImpl(impl: NimNode, ctx: ParseCtx): ProcSig

proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode) =
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
  let sig = parseCalleeImpl(impl, ctx)
  ctx.procs[name] = sig
  ctx.parsing.excl name

proc parseCalleeImpl(impl: NimNode, ctx: ParseCtx): ProcSig =
  ## Build a `ProcSig` from a callee's `nnkProcDef`. Recursively parses
  ## the body; the parsing-set in `ctx` short-circuits mutual recursion.
  impl.expectKind nnkProcDef
  let formal = impl[3]
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
  let bodyNode = impl[6]
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
  let nameStr = impl.name.strVal
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
    let classified = classifyType(tyNode)
    for j in 0 ..< id.len - 2:
      let name = id[j].strVal
      var p = IRParam(name: name, ty: classified.ty,
                      rangeLo: classified.range.lo,
                      rangeHi: classified.range.hi,
                      hasRange: classified.range.hasRange)
      params.add p
      paramsNimSeq.add emitParam(p)
  let bodyIR = parseStmt(procDef[6], ctx)
  result.params = params
  result.bodyNimNode = emitStmt(bodyIR)
  result.paramsNimNode = prefix(paramsNimSeq, "@")
  result.procsNimNode = emitProcs(ctx.procs)
