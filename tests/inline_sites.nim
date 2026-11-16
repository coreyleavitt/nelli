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

import std/macros
import nelli/smt/types
import nelli/smt/dsl_parser

proc collectSites*(s: IRStmt; acc: var seq[string]) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: collectSites(c, acc)
  of isIf:
    for b in s.branches:
      if irHasCall(b.cond): acc.add(if s.ifJoin: "ifJoin" else: "if")
      collectSites(b.body, acc)
    collectSites(s.elseBody, acc)
  of isWhile:
    if irHasCall(s.wcond): acc.add "while"
    collectSites(s.wbody, acc)
  of isTry:
    collectSites(s.tryBody, acc)
    for h in s.tryHandlers: collectSites(h.body, acc)
    collectSites(s.tryFinally, acc)
  of isReturn:
    if irHasCall(s.retExpr): acc.add "return"
  else: discard

macro inlineSites*(p: typed): untyped =
  var acc: seq[string]
  collectSites(parseProc(p.getImpl).body, acc)
  newLit(acc)

proc countJoins(s: IRStmt; joins, withCall: var int) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: countJoins(c, joins, withCall)
  of isIf:
    if s.ifJoin:
      inc joins
      for b in s.branches:
        if irHasCall(b.cond): inc withCall
    for b in s.branches: countJoins(b.body, joins, withCall)
    countJoins(s.elseBody, joins, withCall)
  of isWhile: countJoins(s.wbody, joins, withCall)
  of isTry:
    countJoins(s.tryBody, joins, withCall)
    for h in s.tryHandlers: countJoins(h.body, joins, withCall)
    countJoins(s.tryFinally, joins, withCall)
  else: discard

macro ifJoinCalls*(p: typed): untyped =
  var joins, withCall: int
  countJoins(parseProc(p.getImpl).body, joins, withCall)
  newLit((joins, withCall))
