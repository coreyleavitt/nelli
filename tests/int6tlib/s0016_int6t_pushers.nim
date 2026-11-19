## RFC-0016 int6-t. Templates and macros that push check options into the
## routine body they expand in (`tsymex_0016_int6t_typedpush{,_off}`). They
## live in a module of their own: the check scan reads a push in a template's
## text as a possible state of its own module's positions, which would make
## the suites' callers deviate and hide the opaque scan's verdict.

import std/macros

template unchecked*(body: untyped) =
  {.push overflowChecks: off.}
  body
  {.pop.}

macro emitUnchecked*(body: untyped): untyped =
  result = newStmtList(
    nnkPragma.newTree(ident"push",
      nnkExprColonExpr.newTree(ident"overflowChecks", ident"off")),
    body,
    nnkPragma.newTree(ident"pop"))

template unCheckedInc*(x) =
  ## The stdlib template's text, in a user module: not the audited one.
  {.push overflowChecks: off.}
  inc(x)
  {.pop.}

template boundsOn*(body: untyped) =
  {.push boundChecks: on.}
  body
  {.pop.}

macro emitBoundsOn*(body: untyped): untyped =
  result = newStmtList(
    nnkPragma.newTree(ident"push",
      nnkExprColonExpr.newTree(ident"boundChecks", ident"on")),
    body,
    nnkPragma.newTree(ident"pop"))
