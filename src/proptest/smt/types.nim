## Symex IR + public result/target/settings types.
##
## The architecture (per [docs/SYMEX_PLAN.md](../../../docs/SYMEX_PLAN.md))
## is a classic front-end / back-end split:
##
##   typed Nim AST  ─[dsl_parser]→  SymexProgram (this file)
##                                       │
##                                       └─[runtime]→  SymexResult
##
## The IR is intentionally small. Each phase widens it; this file
## carries only the Phase-1 fragment (int/bool, arithmetic +
## comparison, `if` / `block` / target labels). Later phases extend
## with `let`, `assign`, `return`, composite types, function calls,
## loops, etc.
##
## `ref object` is used for the variant nodes so the parser can
## construct them with ordinary heap allocation; the runtime walks
## them without ever needing to mutate the structure (it's an
## immutable view).

type
  IRBinop* = enum
    bAdd, bSub, bMul, bDiv, bMod
    bAnd, bOr, bXor              ## boolean (bool×bool→bool) for Phase 1;
                                 ## also bitwise on integers in later phases
    bEq, bNe                     ## polymorphic equality
    bLt, bLe, bGt, bGe           ## signed comparison on integers

  IRUnop* = enum
    uNot                         ## boolean negation
    uNeg                         ## arithmetic negation

  IRTypeKind* = enum
    itInt   ## Nim `int` (Phase 1: encoded as Z3BitVec[sizeof(int)*8])
    itBool

  IRExprKind* = enum
    iekIntLit, iekBoolLit, iekVar, iekBinop, iekUnop

  IRExpr* = ref object
    case kind*: IRExprKind
    of iekIntLit:
      ival*: int64
    of iekBoolLit:
      bval*: bool
    of iekVar:
      vname*: string
    of iekBinop:
      bop*: IRBinop
      lhs*, rhs*: IRExpr
    of iekUnop:
      uop*: IRUnop
      operand*: IRExpr

  IRStmtKind* = enum
    isBlock           ## sequence of statements
    isIf              ## branches[*] tried in order; first SAT cond wins;
                      ## elseBody runs if all guards fail (nil = no else)
    isLet             ## `let name = value` — bind one symbolic value;
                      ## immutable for the remainder of the path
    isReturn          ## `return` — terminate this path; subsequent stmts
                      ## in the enclosing block are not walked
    isAssert          ## `symexAssert(cond)` — under a label target,
                      ## tighten path condition with cond; under
                      ## `tAssertionViolation`, fork to search for
                      ## `not cond` reachability
    isTargetLabel     ## `symexTarget("name")`
    isUnsupported     ## any AST kind the Phase-1 parser doesn't model

  IRBranch* = object
    cond*: IRExpr     ## guard for this arm (already negation-folded for elif)
    body*: IRStmt

  IRStmt* = ref object
    case kind*: IRStmtKind
    of isBlock:
      stmts*: seq[IRStmt]
    of isIf:
      branches*: seq[IRBranch]
      elseBody*: IRStmt          ## nil if no `else:` clause
    of isLet:
      lname*: string
      lty*: IRTypeKind
      lvalue*: IRExpr
    of isReturn:
      discard
    of isAssert:
      acond*: IRExpr
    of isTargetLabel:
      tname*: string
    of isUnsupported:
      reason*: string            ## human-readable diagnostic

  IRParam* = object
    name*: string
    ty*: IRTypeKind

  SymexProgram* = object
    params*: seq[IRParam]
    body*: IRStmt

# ---- Public symex-level types -----------------------------------------------

type
  SymexTargetKind* = enum
    stkLabel               ## reach a `symexTarget("name")`
    stkAssertionViolation  ## falsify any `symexAssert(cond)` on any path
                           ## (Cycle 9 — body markers shipped, target wired)

  SymexTarget* = object
    case kind*: SymexTargetKind
    of stkLabel:
      label*: string
    of stkAssertionViolation:
      discard

  SymexStatusKind* = enum
    sxSat       ## witness found
    sxUnsat     ## target proved unreachable / no violation possible
    sxUnknown   ## solver gave up, or every path hit an `isUnsupported` node

  SymexResult*[T] = object
    case status*: SymexStatusKind
    of sxSat:
      witness*: T
    of sxUnsat, sxUnknown:
      discard

  IntegerSemantics* = enum
    isExact      ## BV[W] always. Phase 1 default.
    isOptimised  ## BV[W] + selective Z3Int abstraction (Phase 2 lands this).
    isLoose      ## Z3Int everywhere, unsound. Research-only.

  SymexSettings* = object
    integerSemantics*: IntegerSemantics
    queryTimeoutMs*: uint  ## per-Z3-query timeout; 0 = no limit
    maxFrontierSize*: int  ## paranoid concurrent-path cap; 0 = no limit

# ---- Constructors -----------------------------------------------------------
#
# Plain constructor procs over the variant types. The parser builds the
# IR at macro time using these (or the generated NimNode equivalent);
# the runtime consumes the IR built by the emitted code at runtime.

proc mkIntLit*(v: int64): IRExpr =
  IRExpr(kind: iekIntLit, ival: v)

proc mkBoolLit*(v: bool): IRExpr =
  IRExpr(kind: iekBoolLit, bval: v)

proc mkVar*(name: string): IRExpr =
  IRExpr(kind: iekVar, vname: name)

proc mkBinop*(op: IRBinop, lhs, rhs: IRExpr): IRExpr =
  IRExpr(kind: iekBinop, bop: op, lhs: lhs, rhs: rhs)

proc mkUnop*(op: IRUnop, operand: IRExpr): IRExpr =
  IRExpr(kind: iekUnop, uop: op, operand: operand)

proc mkBlock*(stmts: seq[IRStmt]): IRStmt =
  IRStmt(kind: isBlock, stmts: stmts)

proc mkIf*(branches: seq[IRBranch], elseBody: IRStmt = nil): IRStmt =
  IRStmt(kind: isIf, branches: branches, elseBody: elseBody)

proc mkLet*(name: string, ty: IRTypeKind, value: IRExpr): IRStmt =
  IRStmt(kind: isLet, lname: name, lty: ty, lvalue: value)

proc mkReturn*(): IRStmt =
  IRStmt(kind: isReturn)

proc mkAssert*(cond: IRExpr): IRStmt =
  IRStmt(kind: isAssert, acond: cond)

proc mkBranch*(cond: IRExpr, body: IRStmt): IRBranch =
  IRBranch(cond: cond, body: body)

proc mkTargetLabel*(name: string): IRStmt =
  IRStmt(kind: isTargetLabel, tname: name)

proc mkUnsupported*(reason: string): IRStmt =
  IRStmt(kind: isUnsupported, reason: reason)

# ---- Defaults ---------------------------------------------------------------

proc defaultSymexSettings*(): SymexSettings =
  SymexSettings(
    integerSemantics: isExact,
    queryTimeoutMs: 0,
    maxFrontierSize: 0,
  )

proc tLabel*(name: string): SymexTarget =
  SymexTarget(kind: stkLabel, label: name)

proc tAssertionViolation*(): SymexTarget =
  SymexTarget(kind: stkAssertionViolation)

# ---- Rendering --------------------------------------------------------------
#
# Canonical S-expression form for the IR. Used by Layer-1 isolation
# tests (per ADR-0002) to assert on the parser's output without going
# through the runtime — the renderer is the test-side oracle.

import std/sequtils
import std/strutils

proc render*(e: IRExpr): string =
  if e == nil: return "nil"
  case e.kind
  of iekIntLit:  $e.ival
  of iekBoolLit: $e.bval
  of iekVar:     e.vname
  of iekBinop:   "(" & $e.bop & " " & render(e.lhs) & " " & render(e.rhs) & ")"
  of iekUnop:    "(" & $e.uop & " " & render(e.operand) & ")"

proc render*(s: IRStmt): string =
  if s == nil: return "nil"
  case s.kind
  of isBlock:
    "{" & s.stmts.mapIt(render(it)).join(";") & "}"
  of isIf:
    var arms = ""
    for br in s.branches:
      arms.add "[" & render(br.cond) & "=>" & render(br.body) & "]"
    if s.elseBody != nil:
      arms.add "[else=>" & render(s.elseBody) & "]"
    "if(" & arms & ")"
  of isLet:
    "let(" & s.lname & ":" & $s.lty & "=" & render(s.lvalue) & ")"
  of isReturn:       "return"
  of isAssert:       "assert(" & render(s.acond) & ")"
  of isTargetLabel:  "target(" & s.tname & ")"
  of isUnsupported:  "unsupported(" & s.reason & ")"
