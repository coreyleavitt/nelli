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

  # Optional `with <Settings>` clause as the first statement; if present,
  # consume it and skip past for the `given` lookup. The clause makes the
  # DSL reach feature parity with `forAll(strat, prop, settings)` —
  # otherwise DB integration, custom seeds, etc. are unreachable via the
  # DSL. (We can't use `using` here because that's a Nim keyword.)
  var bodyStart = 0
  var settingsExpr: NimNode = newCall(bindSym"defaultSettings")
  if body[0].kind == nnkCommand and body[0].len >= 2 and
     body[0][0].kind == nnkIdent and $body[0][0] == "with":
    settingsExpr = body[0][1]
    bodyStart = 1
    if body.len < bodyStart + 2:
      error("property body must include `given` and a predicate after `with`", body)

  # Optional `examples <expr>` clauses *after* `with`, *before* `given`.
  # Each pins one regression-seed value (single binding) or tuple (N
  # bindings); the engine runs them through `prop` before the random
  # phase. We collect them as raw expressions and disambiguate against
  # binding arity once we know it.
  var explicitExprs: seq[NimNode]
  while bodyStart < body.len and
        body[bodyStart].kind == nnkCommand and body[bodyStart].len == 2 and
        body[bodyStart][0].kind == nnkIdent and $body[bodyStart][0] == "examples":
    explicitExprs.add body[bodyStart][1]
    inc bodyStart
    if bodyStart >= body.len:
      error("property body must include `given` and a predicate after `examples`", body)

  let givenStmt = body[bodyStart]
  if givenStmt.kind != nnkCommand or givenStmt.len < 2 or
     givenStmt[0].kind != nnkIdent or $givenStmt[0] != "given":
    error("expected `given x in s [, y in t, ...]` after optional `with`", givenStmt)

  var bindings: seq[(NimNode, NimNode)]  # (name, strategy expression)
  for i in 1 ..< givenStmt.len:
    let inExpr = givenStmt[i]
    if inExpr.kind != nnkInfix or $inExpr[0] != "in":
      error("expected `x in s`", inExpr)
    bindings.add (inExpr[1], inExpr[2])

  if bindings.len == 0:
    error("at least one `given` binding required", givenStmt)

  let predicate = newStmtList()
  for i in bodyStart + 1 ..< body.len:
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

  # Build an `Examples[T]` of explicit examples by appending each
  # user-supplied expression after declaring it. `Examples` (boxed) rather
  # than `seq[T]` so a no-valid-default element type (`{.requiresInit.}`
  # variant, etc.) never instantiates `seq[T]`'s shrink/reset path. `var;
  # .add` for each lets us mix bare values (single-binding) with tuples
  # (multi-binding) without disambiguating in the macro — the element type
  # rejects mismatches against the strategy's element type.
  let explicitSym = genSym(nskVar, "explicitPT")
  var addStmts = newStmtList()
  for e in explicitExprs:
    addStmts.add newCall(newDotExpr(explicitSym, ident"add"), e)

  result = quote do:
    test `name`:
      let `strat` = `stratExpr`
      var `explicitSym`: Examples[typeof(valueType(`strat`))]
      `addStmts`
      let `rep` = forAllWithExamples(`explicitSym`, `strat`,
        proc(`paramName`: typeof(valueType(`strat`))) = `propBody`,
        `settingsExpr`)
      case `rep`.outcome
      of otPassed:
        discard
      of otFalsified:
        # Notes first so they read in chronological order before the
        # counterexample / message — same order the user wrote them.
        for n in `rep`.notes:
          checkpoint("note: " & n[0] & ": " & n[1])
        checkpoint("counterexample: " & displayCounterexample(`rep`))
        if `rep`.message.len > 0:
          checkpoint(`rep`.message)
        check false
      of otExhausted:
        checkpoint("property exhausted (too many rejected examples)")
        check false
      of otFlaky:
        for n in `rep`.notes:
          checkpoint("note: " & n[0] & ": " & n[1])
        checkpoint("property is non-deterministic on input: " &
                   displayCounterexample(`rep`))
        if `rep`.message.len > 0:
          checkpoint(`rep`.message)
        check false
