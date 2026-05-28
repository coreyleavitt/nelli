## The `property` DSL — a `std/unittest`-native form for property tests.
##
## ```
## property "reverse-reverse is identity":
##   given xs in lists(integers(0, 9))
##   ensure xs.reversed.reversed == xs
## ```
##
## The macro expands to a `test "..."` block that runs `forAll` over the given
## strategy and, on falsification or exhaustion, registers a unittest failure
## with the (already-shrunk) counterexample as a checkpoint.
##
## Only single-binding `given x in s` is implemented in this slice; multi-arg
## (`given a in sa, b in sb`) follows next.

import std/macros
import ./strategy, ./engine

export strategy, engine

macro property*(name: string, body: untyped): untyped =
  ## Define a property test bound to a `std/unittest` test block. Supports one
  ## or two `given` bindings (e.g. `given a in sa, b in sb`).
  expectKind body, nnkStmtList
  if body.len < 2:
    error("property body must start with `given x in s [, y in t]` and a predicate", body)

  let givenStmt = body[0]
  if givenStmt.kind != nnkCommand or givenStmt.len < 2 or
     givenStmt[0].kind != nnkIdent or $givenStmt[0] != "given":
    error("expected `given x in s [, y in t]` as the first statement", givenStmt)

  var bindings: seq[(NimNode, NimNode)]  # (name, strategy expression)
  for i in 1 ..< givenStmt.len:
    let inExpr = givenStmt[i]
    if inExpr.kind != nnkInfix or $inExpr[0] != "in":
      error("expected `x in s`", inExpr)
    bindings.add (inExpr[1], inExpr[2])

  if bindings.len notin 1 .. 2:
    error("property currently supports 1 or 2 `given` bindings", givenStmt)

  let predicate = newStmtList()
  for i in 1 ..< body.len:
    predicate.add body[i]

  let strat = genSym(nskLet, "stratPT")
  let rep = genSym(nskLet, "reportPT")

  # Build the strategy expression and the predicate proc body.
  var stratExpr: NimNode
  var propBody = newStmtList()
  var paramName: NimNode

  if bindings.len == 1:
    stratExpr = bindings[0][1]
    paramName = bindings[0][0]  # user's binding name becomes the proc param
    for s in predicate: propBody.add s
  else:  # 2 bindings
    let (n1, s1) = bindings[0]
    let (n2, s2) = bindings[1]
    stratExpr = quote do: tuples2(`s1`, `s2`)
    paramName = genSym(nskParam, "tup")
    propBody.add newLetStmt(n1, newTree(nnkBracketExpr, paramName, newLit(0)))
    propBody.add newLetStmt(n2, newTree(nnkBracketExpr, paramName, newLit(1)))
    for s in predicate: propBody.add s

  result = quote do:
    test `name`:
      let `strat` = `stratExpr`
      let `rep` = forAll(`strat`,
        proc(`paramName`: typeof(valueType(`strat`))) = `propBody`)
      case `rep`.outcome
      of otPassed:
        discard
      of otFalsified:
        checkpoint("counterexample: " & $`rep`.counterexample)
        if `rep`.message.len > 0:
          checkpoint(`rep`.message)
        check false
      of otExhausted:
        checkpoint("property exhausted (too many rejected examples)")
        check false
