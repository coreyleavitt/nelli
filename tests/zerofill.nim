## RFC-0010 slice A1 — the pin.
##
## `zeroFilled(T(a: x, b: y))` means *"this literal, with the pre-RFC-0010
## meaning of every field it does not list"*: every unlisted field is the
## zero value, not the type's declared default.
##
## Why a macro. RFC-0010 §6 stages the fix pin-then-flip: A1 writes today's
## implicit values into the at-risk literals as an exact no-op, A2 flips the
## defaults, A3 removes the pins that were not actually wanted. Written by
## hand that is 115 literals × up to ten omitted fields, which is unreadable,
## typo-prone, and — worse — requires a per-literal judgement about which
## omitted fields "matter". Getting one of those judgements wrong shows up at
## A2 as a red that has to be told apart from the mechanism under test, which
## is precisely the conflation the staging exists to prevent. The macro makes
## the pin complete by construction and one token wide at each site, so A1's
## no-op property is provable by a sweep diff rather than argued per file.
##
## How. Purely syntactic — `T(a: x, b: y)` rewrites to
##
##     var tmp: T      # zero-fills
##     tmp.a = x
##     tmp.b = y
##     tmp
##
## A bare `var v: T` zero-fills *even when T declares field defaults*
## (RFC-0010 §3, the residual recorded in §7), so the rewrite keeps meaning
## the same thing on both sides of A2. That is the entire trick, and it is
## also why these pins would stop compiling if the deferred
## `{.requiresInit.}` slice ever lands — which is the correct outcome: A3
## removes them all first.
##
## Not recursive. A nested literal passed as a field value keeps its own
## meaning; wrap it explicitly if it needs pinning too. A1 only flips
## `Settings`, and the one nested settings type (`IntegerBiasConfig`) is
## C1's slice.
##
## Deleted by A3, along with `tests/tconfigcharacterize.nim`.

import std/macros

macro zeroFilled*(lit: untyped): untyped =
  ## Rewrite an object-construction expression so unlisted fields are zero.
  if lit.kind notin {nnkObjConstr, nnkCall}:
    error("zeroFilled expects an object construction like `Settings(a: 1)`, got " &
          $lit.kind, lit)
  let tmp = genSym(nskVar, "pinned")
  result = nnkStmtListExpr.newTree(
    nnkVarSection.newTree(nnkIdentDefs.newTree(tmp, lit[0], newEmptyNode())))
  for i in 1 ..< lit.len:
    let f = lit[i]
    if f.kind != nnkExprColonExpr:
      error("zeroFilled expects `field: value` arguments; positional arguments " &
            "are not object construction", f)
    result.add newAssignment(newDotExpr(tmp, f[0]), f[1])
  result.add tmp
