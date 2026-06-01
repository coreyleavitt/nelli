## Symex IR + public result/target/settings types.
##
## NB: imports of std/tables / std/sequtils / std/strutils live near
## the bottom of the file (right above the rendering helpers); the
## rest of this module is type definitions only.

import std/tables
export tables
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
    bAnd, bOr, bXor              ## bool×bool→bool, or bitwise on integers —
                                 ## the runtime dispatches by operand type
    bShl, bShr                   ## bit-shifts on integers; sign-aware shr
                                 ## maps to ashr (signed) / lshr (unsigned)
    bEq, bNe                     ## polymorphic equality
    bLt, bLe, bGt, bGe           ## comparison; signed vs unsigned by IRType

  IRUnop* = enum
    uNot                         ## boolean negation
    uNeg                         ## arithmetic negation

  IRTypeKind* = enum
    itInt   ## Any fixed-width Nim integer (`int{8,16,32,64}`/`uint{8,16,32,64}`/
            ## `int`/`uint`). Width + signedness on the wrapping `IRType`.
    itBool

  IRType* = object
    case kind*: IRTypeKind
    of itInt:
      width*: int    ## bits: 8 | 16 | 32 | 64
      signed*: bool  ## Nim `int*` are signed; `uint*` are unsigned.
    of itBool:
      discard

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
    isReturn          ## `return [expr]` — terminate this path; in callees
                      ## the optional value binds the call's return symbol
    isAssert          ## `symexAssert(cond)` — under a label target,
                      ## tighten path condition with cond; under
                      ## `tAssertionViolation`, fork to search for
                      ## `not cond` reachability
    isCall            ## A-normalised call to a user-defined proc; lookup
                      ## via `SymexProgram.procs[callee]`, walk the body
                      ## under arg bindings, bind retval to the named
                      ## fresh symbol if non-void
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
      lty*: IRType
      lvalue*: IRExpr
    of isReturn:
      retExpr*: IRExpr   ## nil for void returns; callees use this to
                         ## carry the value back to the caller
    of isCall:
      callee*: string
      cargs*: seq[IRExpr]
      retName*: string   ## "" for void; else the fresh let-name the
                         ## return value binds to
      retTy*: IRType     ## return type; tBool() sentinel when void
    of isAssert:
      acond*: IRExpr
    of isTargetLabel:
      tname*: string
    of isUnsupported:
      reason*: string            ## human-readable diagnostic

  IRParam* = object
    name*: string
    ty*: IRType
    rangeLo*: int64    ## inclusive lower bound when `hasRange` is set
    rangeHi*: int64    ## inclusive upper bound
    hasRange*: bool    ## type-derived range info present?

  ProcSig* = object
    name*:    string
    params*:  seq[IRParam]
    body*:    IRStmt
    retTy*:   IRType   ## tBool() sentinel for void; the runtime keys
                       ## off `isVoid` rather than the type itself
    isVoid*:  bool

  SymexProgram* = object
    params*: seq[IRParam]
    body*: IRStmt
    procs*: Table[string, ProcSig]   ## transitively reachable callees

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

  Interval* = object
    ## Closed integer interval `[lo, hi]`. Used by the abstraction
    ## layer (ADR-0001) for range tracking and BV-window containment.
    lo*, hi*: int64

  AbstractionEvidence* = enum
    aeTypeRange    ## "from typedesc range[lo..hi] (or Natural/Positive)"
    aeNumericFold  ## "from interval-composing arithmetic"

  AbstractionEntry* = object
    name*:        string
    interval*:    Interval
    evidence*:    AbstractionEvidence
    derivation*:  string

  AbstractionLog* = seq[AbstractionEntry]

  CallStat* = object
    name*:      string
    walked*:    int   ## times this callee's body was actually walked
    cacheHits*: int   ## times the call was served from the summary cache

  CallStats* = seq[CallStat]

  SymexResult*[T] = object
    abstractions*: AbstractionLog
    callStats*:    CallStats   ## per-callee walk + cache-hit counts
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
    maxCallDepth*: int     ## Phase-3 inline-call recursion bound; >= 1

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

proc mkLet*(name: string, ty: IRType, value: IRExpr): IRStmt =
  IRStmt(kind: isLet, lname: name, lty: ty, lvalue: value)

# IRType constructors — used by the parser/typebridge and by tests.
proc tBool*(): IRType =
  IRType(kind: itBool)

proc tInt*(width: int = 64, signed: bool = true): IRType =
  IRType(kind: itInt, width: width, signed: signed)

proc tUInt*(width: int): IRType =
  IRType(kind: itInt, width: width, signed: false)

proc `==`*(a, b: IRType): bool =
  if a.kind != b.kind: return false
  case a.kind
  of itBool: true
  of itInt:  a.width == b.width and a.signed == b.signed

proc `$`*(t: IRType): string =
  case t.kind
  of itBool: "bool"
  of itInt:
    let prefix = if t.signed: "i" else: "u"
    prefix & $t.width

proc mkReturn*(): IRStmt =
  IRStmt(kind: isReturn, retExpr: nil)

proc mkReturnVal*(e: IRExpr): IRStmt =
  IRStmt(kind: isReturn, retExpr: e)

proc mkCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy)

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
  ## Phase 2 endpoint: `isOptimised` is now the default. Range-typed
  ## parameters auto-promote to Z3Int when the abstraction-soundness
  ## proof holds; everything else falls back to BV[W]. `isExact` is
  ## available as an explicit override for users who want the
  ## abstraction layer's static analysis itself off the trust chain.
  SymexSettings(
    integerSemantics: isOptimised,
    queryTimeoutMs: 0,
    maxFrontierSize: 0,
    maxCallDepth: 3,
  )

proc tLabel*(name: string): SymexTarget =
  SymexTarget(kind: stkLabel, label: name)

proc tAssertionViolation*(): SymexTarget =
  SymexTarget(kind: stkAssertionViolation)

proc optimisedSymexSettings*(): SymexSettings =
  ## Convenience: settings with `integerSemantics: isOptimised`.
  ## (`defaultSymexSettings()` will flip to optimised at the end of
  ## Phase 2 once the abstraction layer has shipped end-to-end.)
  result = defaultSymexSettings()
  result.integerSemantics = isOptimised

proc looseSymexSettings*(): SymexSettings =
  ## Convenience: settings with `integerSemantics: isLoose` (UNSOUND
  ## — research/educational only; see ADR-0001).
  result = defaultSymexSettings()
  result.integerSemantics = isLoose

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
    # `$s.lty` uses the IRType stringifier defined below.
  of isReturn:
    if s.retExpr == nil: "return"
    else: "return(" & render(s.retExpr) & ")"
  of isAssert:       "assert(" & render(s.acond) & ")"
  of isCall:
    var argstr = ""
    for i, a in s.cargs:
      if i > 0: argstr.add ","
      argstr.add render(a)
    let lhs = if s.retName.len > 0: s.retName & ":=" else: ""
    "call(" & lhs & s.callee & "(" & argstr & "))"
  of isTargetLabel:  "target(" & s.tname & ")"
  of isUnsupported:  "unsupported(" & s.reason & ")"
