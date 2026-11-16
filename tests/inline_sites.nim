## Shared by `tsymex_0016_r8a_inlinecalls` and `tsymex_0016_r7a_liveness`.
##
## `inlineSites(proc)`: the parsed IR of a routine, walked structurally, names
## each site whose expression still applies a call (`irHasCall`): `if` (a
## guard, `elif` included), `ifJoin` (a short-circuit chain's synthetic
## guard), `while` (a loop test) and `return` (a value). The list is in
## source order and exact: `@[]` is a routine in which the parser hoisted every
## call into a statement of its own.
##
## `ifJoinCalls(proc)`: `(the ifJoin guards, how many of them apply a call)`.
##
## `closureApplications(proc)`: how many `iekClosureCall` nodes the routine's
## parsed IR holds in the expressions of its guards, loop tests, `return`
## values, `let`s and assignments. A closure the source applies once is
## applied once in the IR (R8-1: a `case` scrutinee was embedded in every
## `of` guard).

import std/macros
import nelli/smt/types
import nelli/smt/dsl_parser

proc walkIR(s: IRStmt; visit: proc (s: IRStmt)) =
  ## `visit` each statement under `s`, `s` first, in source order: a block's
  ## statements, an `if`'s branch bodies then its `else`, a loop body, a
  ## `try`'s body, handlers and `finally`.
  if s == nil: return
  visit(s)
  case s.kind
  of isBlock:
    for c in s.stmts: walkIR(c, visit)
  of isIf:
    for b in s.branches: walkIR(b.body, visit)
    walkIR(s.elseBody, visit)
  of isWhile:
    walkIR(s.wbody, visit)
  of isTry:
    walkIR(s.tryBody, visit)
    for h in s.tryHandlers: walkIR(h.body, visit)
    walkIR(s.tryFinally, visit)
  else: discard

macro inlineSites*(p: typed): untyped =
  var acc: seq[string]
  walkIR(parseProc(p.getImpl).body, proc (s: IRStmt) =
    case s.kind
    of isIf:
      for b in s.branches:
        if irHasCall(b.cond): acc.add(if s.ifJoin: "ifJoin" else: "if")
    of isWhile:
      if irHasCall(s.wcond): acc.add "while"
    of isReturn:
      if irHasCall(s.retExpr): acc.add "return"
    else: discard)
  newLit(acc)

macro ifJoinCalls*(p: typed): untyped =
  var joins, withCall: int
  walkIR(parseProc(p.getImpl).body, proc (s: IRStmt) =
    if s.kind == isIf and s.ifJoin:
      inc joins
      for b in s.branches:
        if irHasCall(b.cond): inc withCall)
  newLit((joins, withCall))

proc closureNodes(e: IRExpr): int =
  if e == nil: return 0
  if e.kind == iekClosureCall: result = 1
  for k in irKids(e): result += closureNodes(k)

macro closureApplications*(p: typed): untyped =
  var total: int
  walkIR(parseProc(p.getImpl).body, proc (s: IRStmt) =
    case s.kind
    of isIf:
      for b in s.branches: total += closureNodes(b.cond)
    of isWhile: total += closureNodes(s.wcond)
    of isReturn: total += closureNodes(s.retExpr)
    of isLet: total += closureNodes(s.lvalue)
    of isAssign: total += closureNodes(s.avalue)
    else: discard)
  newLit(total)
