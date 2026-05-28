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
## Supports an arbitrary number of `given` bindings (`given a in sa, b in sb,
## c in sc, ...`): the macro emits an inline tuple-producing strategy that
## draws each binding in order, then a property proc that destructures the
## tuple back into the user's names. The 1-binding case skips the tuple.

import std/macros
import ./strategy, ./engine, ./datasource

export strategy, engine

macro property*(name: string, body: untyped): untyped =
  ## Define a property test bound to a `std/unittest` test block. Supports any
  ## number of `given` bindings (e.g. `given a in sa, b in sb, c in sc`).
  expectKind body, nnkStmtList
  if body.len < 2:
    error("property body must start with `given x in s [, y in t, ...]` and a predicate", body)

  let givenStmt = body[0]
  if givenStmt.kind != nnkCommand or givenStmt.len < 2 or
     givenStmt[0].kind != nnkIdent or $givenStmt[0] != "given":
    error("expected `given x in s [, y in t, ...]` as the first statement", givenStmt)

  var bindings: seq[(NimNode, NimNode)]  # (name, strategy expression)
  for i in 1 ..< givenStmt.len:
    let inExpr = givenStmt[i]
    if inExpr.kind != nnkInfix or $inExpr[0] != "in":
      error("expected `x in s`", inExpr)
    bindings.add (inExpr[1], inExpr[2])

  if bindings.len == 0:
    error("at least one `given` binding required", givenStmt)

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
  else:
    # N >= 2: emit an inline tuple-producing strategy. The element type of
    # each binding is recovered via `typeof(valueType(s_i))`; the run proc
    # draws each in order and returns a positional tuple. The property's
    # proc destructures back to the user's names.
    paramName = genSym(nskParam, "tup")
    for i in 0 ..< bindings.len:
      let n = bindings[i][0]
      propBody.add newLetStmt(n, newTree(nnkBracketExpr, paramName, newLit(i)))
    for s in predicate: propBody.add s

    let srcSym = genSym(nskParam, "src")
    var tupleType = newNimNode(nnkTupleConstr)
    var procBody = newStmtList()
    var vSyms: seq[NimNode]
    for i in 0 ..< bindings.len:
      let s = bindings[i][1]
      tupleType.add newCall(bindSym"typeof", newCall(bindSym"valueType", s))
      let vSym = genSym(nskLet, "v" & $i)
      vSyms.add vSym
      procBody.add newLetStmt(vSym, newCall(newDotExpr(s, ident"run"), srcSym))
    var tupleConstr = newNimNode(nnkTupleConstr)
    for v in vSyms: tupleConstr.add v
    procBody.add tupleConstr

    let innerProc = newProc(
      params = @[tupleType,
                 newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
      body = procBody,
      procType = nnkLambda)
    stratExpr = newCall(bindSym"newStrategy", innerProc)

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
      of otFlaky:
        checkpoint("property is non-deterministic on input: " & $`rep`.counterexample)
        if `rep`.message.len > 0:
          checkpoint(`rep`.message)
        check false
