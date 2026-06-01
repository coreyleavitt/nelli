## Layer 1 of the predicate DSL (ADR-0002): typed Nim AST → IR.
##
## This is the algorithmically subtle layer the ADR calls out as the
## one worth testing in isolation. It runs at macro time only: it
## consumes a `NimNode` (typed, post-semcheck) and produces a Phase-1
## IR value plus the equivalent emit-time NimNode tree that
## reconstructs the IR at runtime.
##
## Supported fragment in Phase 1:
##
##   * Statements: `nnkStmtList`, `nnkBlockStmt`, `nnkIfStmt`
##                 (`nnkElifBranch` / `nnkElseBranch`), the call
##                 `symexTarget("…")`.
##   * Expressions: `nnkIntLit`, `nnkInfix` for arithmetic +
##                  comparison + boolean, `nnkPrefix` for `not` / `-`,
##                  `nnkSym` (var reference), `nnkPar` (passthrough).
##
## Any node outside the fragment lowers to `IRStmt(kind: isUnsupported)`
## or — for expressions — raises a macro-time error (Phase 1 has no
## "unsupported expression" sentinel; the supported expressions cover
## the supported statements).
##
## Each lowering returns a tuple `(ir, nimNode)`:
##   * `ir`    — the macro-time IR ref object (used so we can pattern-
##               match further during parsing if needed)
##   * `nimNode` — the AST that, when emitted into the macro result,
##               constructs the equivalent IR at runtime.

import std/macros
import std/strformat
import ./types
import ./dsl_typebridge

# ---- emit: macro-time IR → runtime-construction NimNode -----------------------

proc emitBinop(op: IRBinop): NimNode =
  ## Emit `IRBinop.bGt` as the dotted-access NimNode.
  newDotExpr(bindSym"IRBinop", ident($op))

proc emitUnop(op: IRUnop): NimNode =
  newDotExpr(bindSym"IRUnop", ident($op))

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

proc emitStmt*(s: IRStmt): NimNode

proc emitIRType*(t: IRType): NimNode =
  ## Emit a NimNode that, when expanded, constructs the same IRType
  ## at runtime via `tBool()` / `tInt(width, signed)`.
  case t.kind
  of itBool:
    newCall(bindSym"tBool")
  of itInt:
    newCall(bindSym"tInt", newLit(t.width), newLit(t.signed))

proc emitBranch(br: IRBranch): NimNode =
  newCall(bindSym"mkBranch", emitExpr(br.cond), emitStmt(br.body))

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
  of isReturn:
    newCall(bindSym"mkReturn")
  of isAssert:
    newCall(bindSym"mkAssert", emitExpr(s.acond))
  of isTargetLabel:
    newCall(bindSym"mkTargetLabel", newLit(s.tname))
  of isUnsupported:
    newCall(bindSym"mkUnsupported", newLit(s.reason))

# `emitBranch` recurses through `emitStmt`; declare-and-define order
# requires `emitStmt` to forward-declare. Nim allows the recursive call
# above only because both procs share a compilation unit; if mutual
# recursion ever becomes a problem add an explicit forward decl.

# ---- parse: typed Nim AST → macro-time IR ------------------------------------

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
    error("symex (Phase 1): unsupported infix operator `" & op & "`")

proc parseExpr*(n: NimNode): IRExpr =
  case n.kind
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    mkIntLit(n.intVal)
  of nnkUIntLit .. nnkUInt64Lit:
    mkIntLit(n.intVal)
  of nnkIdent, nnkSym:
    # Booleans `true` / `false` come through as nnkSym after semcheck.
    let s = n.strVal
    if s == "true": mkBoolLit(true)
    elif s == "false": mkBoolLit(false)
    else: mkVar(s)
  of nnkPar, nnkStmtListExpr:
    parseExpr(n[n.len - 1])
  of nnkHiddenStdConv, nnkConv:
    # Semcheck inserts these for widening/narrowing literal coercions
    # (e.g. `x < 0` with x: int8 → x < int8(0)). The inner expression
    # is the value; the target type comes from context, so we just
    # pass the value through.
    parseExpr(n[n.len - 1])
  of nnkInfix:
    # Standard shape:  Infix [op, lhs, rhs]
    let op = binopForInfix(n[0].strVal)
    mkBinop(op, parseExpr(n[1]), parseExpr(n[2]))
  of nnkPrefix:
    let op = n[0].strVal
    case op
    of "not": mkUnop(uNot, parseExpr(n[1]))
    of "-":   mkUnop(uNeg, parseExpr(n[1]))
    else:
      error("symex (Phase 1): unsupported prefix operator `" & op & "`", n)
  else:
    error(&"symex (Phase 1): unsupported expression kind {n.kind} in `{n.repr}`", n)

proc isMarkerCall(n: NimNode, name: string): bool =
  ## True iff `n` is a call to the body-marker template named `name`.
  ## We compare by leading identifier strVal; the marker templates live
  ## in `proptest/symex` and `dsl.nim` re-exports them.
  if n.kind != nnkCall:
    return false
  let callee = n[0]
  case callee.kind
  of nnkIdent, nnkSym:
    callee.strVal == name
  else:
    false

proc parseStmt*(n: NimNode): IRStmt =
  case n.kind
  of nnkStmtList, nnkStmtListExpr, nnkBlockStmt:
    let inner = if n.kind == nnkBlockStmt: n[1] else: n
    var stmts: seq[IRStmt]
    for c in inner:
      stmts.add parseStmt(c)
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkIfStmt, nnkIfExpr:
    # In macro-argument position the same syntactic `if` is parsed as
    # `nnkIfExpr` with `nnkElifExpr` / `nnkElseExpr` arms; in
    # statement position it's `nnkIfStmt` / `nnkElifBranch` /
    # `nnkElse`. Treat both forms uniformly — the IR doesn't care.
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        branches.add mkBranch(parseExpr(arm[0]), parseStmt(arm[1]))
      of nnkElse, nnkElseExpr:
        elseBody = parseStmt(arm[0])
      else:
        error(&"symex (Phase 1): unexpected if-arm kind {arm.kind}", arm)
    mkIf(branches, elseBody)
  of nnkReturnStmt:
    # Phase 1: `return` with or without a value — we ignore the value
    # (the proc's return value is not part of the witness). The path
    # terminates here.
    mkReturn()
  of nnkLetSection, nnkVarSection:
    # IdentDefs may carry multiple names per group (`let a, b = 0`);
    # we split into one IR `isLet` per name. Var sections in Phase 1
    # are treated identically to let — Phase 1 has no `assign` IR yet,
    # so a `var` whose body never rebinds collapses to `let`. An
    # assignment to a `var` later would currently lower to
    # `isUnsupported` until Phase 1 cycle for assignment exists.
    var stmts: seq[IRStmt]
    for id in n:
      id.expectKind nnkIdentDefs
      # nnkIdentDefs: [name1, name2, ..., type, value]
      # In `let y = x * 2` with inferred type the type slot may be
      # nnkEmpty; the resolved type lives on the name symbol post-
      # semcheck, so we read from id[j].
      let valNode = id[id.len - 1]
      let valIR = parseExpr(valNode)
      for j in 0 ..< id.len - 2:
        # `let` ignores any type-derived range info for Phase 2 —
        # range plumbing for locals lands when needed (cycle 7+'s
        # composition tests use param ranges only).
        let classified = classifyType(id[j])
        stmts.add mkLet(id[j].strVal, classified.ty, valIR)
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkCall:
    if isMarkerCall(n, "symexTarget"):
      # symexTarget("name") — expect a single string-literal arg.
      let argNode = n[1]
      if argNode.kind notin {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
        error("symex (Phase 1): `symexTarget` requires a string literal", argNode)
      mkTargetLabel(argNode.strVal)
    elif isMarkerCall(n, "symexAssert"):
      mkAssert(parseExpr(n[1]))
    elif isMarkerCall(n, "symexAssume"):
      # Phase 1 treats `symexAssume` identically to `symexAssert`'s
      # path-tightening behavior, minus the tAssertionViolation hook.
      # Both are recognized by the parser; the runtime distinguishes
      # via the IR kind.
      mkAssert(parseExpr(n[1]))
    else:
      mkUnsupported(&"call to `{n[0].repr}` not in Phase 1 fragment")
  of nnkDiscardStmt, nnkEmpty, nnkCommentStmt:
    mkBlock(@[])   ## treated as no-op
  else:
    mkUnsupported(&"statement kind {n.kind} not in Phase 1 fragment")

# ---- Top-level: procDef → SymexProgram-emitting NimNode ----------------------

type
  ParseResult* = object
    params*: seq[IRParam]
    bodyNimNode*: NimNode   ## emit-time AST: builds the IR `body` at runtime
    paramsNimNode*: NimNode ## emit-time AST: builds the IR `params` at runtime

proc emitParam(p: IRParam): NimNode =
  newTree(nnkObjConstr,
    bindSym"IRParam",
    newColonExpr(ident"name",     newLit(p.name)),
    newColonExpr(ident"ty",       emitIRType(p.ty)),
    newColonExpr(ident"rangeLo",  newLit(p.rangeLo)),
    newColonExpr(ident"rangeHi",  newLit(p.rangeHi)),
    newColonExpr(ident"hasRange", newLit(p.hasRange)))

proc parseProc*(procDef: NimNode): ParseResult =
  ## Consume an `nnkProcDef` (typed) and produce:
  ##   * the macro-time param descriptor list
  ##   * an emit-time NimNode that, when evaluated, yields a
  ##     `seq[IRParam]` matching that list
  ##   * an emit-time NimNode that, when evaluated, yields the IR body
  procDef.expectKind nnkProcDef
  let formalParams = procDef[3]
  formalParams.expectKind nnkFormalParams
  # formalParams[0] is the return type; we ignore it (procs are
  # interpreted symbolically — their return value isn't part of the
  # witness in Phase 1).
  var params: seq[IRParam]
  var paramsNimSeq = newTree(nnkBracket)
  for i in 1 ..< formalParams.len:
    let id = formalParams[i]
    id.expectKind nnkIdentDefs
    # nnkIdentDefs: [name1, name2, ..., type, default]
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
  let bodyIR = parseStmt(procDef[6])
  result.params = params
  result.bodyNimNode = emitStmt(bodyIR)
  result.paramsNimNode = prefix(paramsNimSeq, "@")
