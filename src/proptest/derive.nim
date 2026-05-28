## Compile-time derivation of `Strategy[T]` from `T`.
##
## `arbitrary(T)` is a macro that inspects `T`'s structure and emits a strategy
## tailored to that type — so a property test never needs to write a strategy
## for a user type by hand. Primitives map to the built-in strategies; compound
## types (tuples, objects, variants, refs, seqs, arrays, Tables, HashSets, the
## built-in `set[T]`) recurse over their components. Generic instantiations
## (`Box[int]`, `Pair[A, B]`) and `distinct` types are handled too.
##
## **Directly-recursive types** (variant trees, linked lists, ASTs) are
## auto-wrapped in a `recursive(base, extend, maxDepth)` call: we synthesize a
## *leaf* strategy by filling each self-position with a terminal value
## (`nil` for direct ref-self, `@[]` for `seq[Self]`, `initTable[K,V]()` for
## `Table[_, Self]`, `initHashSet[T]()` for `HashSet[Self]`), and an *extend*
## strategy that recurses on the child strategy `recursive` supplies. Any
## recursive shape we can't synthesize a leaf for (non-ref direct recursion;
## self under unsupported wrappers) still errors at compile time with a
## pointer at the manual `recursive(...)` combinator.

import std/[macros, sets]
import ./strategy

# ---------- type-AST helpers ----------

proc typeAsCallArg(t: NimNode): NimNode =
  ## Re-express a type AST as ident-based AST. Passing a type-sym as a macro
  ## call argument makes Nim treat it as a value; rebuilding with fresh idents
  ## re-resolves it as a type in the call site's scope.
  case t.kind
  of nnkSym, nnkIdent:
    newIdentNode($t)
  of nnkBracketExpr:
    let res = newNimNode(nnkBracketExpr)
    for c in t: res.add typeAsCallArg(c)
    res
  else:
    t

proc typeAsTypeSpec(t: NimNode): NimNode =
  ## Re-express a type AST so it can be spliced into a *type position* (return
  ## type, generic argument, etc.). Like `typeAsCallArg` but also rebuilds
  ## tuple-type ASTs with their IdentDefs structure preserved.
  case t.kind
  of nnkSym, nnkIdent:
    newIdentNode($t)
  of nnkBracketExpr:
    let res = newNimNode(nnkBracketExpr)
    for c in t: res.add typeAsTypeSpec(c)
    res
  of nnkTupleTy:
    let res = newNimNode(nnkTupleTy)
    for c in t:
      if c.kind == nnkIdentDefs:
        let copy = newNimNode(nnkIdentDefs)
        for i in 0 ..< c.len - 2:
          copy.add newIdentNode($c[i])
        copy.add typeAsTypeSpec(c[c.len - 2])
        copy.add newEmptyNode()
        res.add copy
      else:
        res.add typeAsTypeSpec(c)
    res
  else:
    t

# ---------- self-reference detection ----------

proc isSelfType(t: NimNode, selfName: string): bool =
  case t.kind
  of nnkSym, nnkIdent: $t == selfName
  else: false

proc selfRefInType(t: NimNode, selfName: string): bool =
  ## True if `t` references the enclosing type either directly or under one
  ## of the supported wrappers (`seq`, `HashSet`, `Option`, `Table`).
  if isSelfType(t, selfName): return true
  if t.kind == nnkBracketExpr:
    case $t[0]
    of "seq", "HashSet", "Option":
      return t.len >= 2 and selfRefInType(t[1], selfName)
    of "Table":
      return t.len >= 3 and selfRefInType(t[2], selfName)
    else: discard
  false

proc reachesTypeThroughFields(t: NimNode, target: string,
                              visited: var HashSet[string],
                              maxDepth: int): bool =
  ## True iff a transitive field of `t` references the type named `target`.
  ## Used to detect *mutual* recursion (`MutA → seq[MutB] → MutA`); the
  ## direct-self-reference case is handled separately and short-circuited by
  ## the caller. `visited` prevents revisiting types within the same walk.
  if maxDepth <= 0: return false
  var ty = t
  while ty.kind == nnkBracketExpr:
    case $ty[0]
    of "seq", "HashSet", "Option":
      if ty.len < 2: return false
      ty = ty[1]
    of "Table":
      if ty.len < 3: return false
      ty = ty[2]
    else: return false
  if ty.kind notin {nnkSym, nnkIdent}: return false
  let name = $ty
  if name == target: return true
  if name in visited: return false
  visited.incl name
  var impl: NimNode
  try:
    impl = ty.getTypeImpl
  except: return false
  if impl.kind == nnkRefTy:
    var inner = impl[0]
    if inner.kind == nnkSym:
      try: inner = inner.getTypeImpl
      except: return false
    impl = inner
  if impl.kind != nnkObjectTy: return false
  let recList = impl[2]
  if recList.kind != nnkRecList: return false
  for fd in recList:
    case fd.kind
    of nnkIdentDefs:
      let ft = fd[fd.len - 2]
      if reachesTypeThroughFields(ft, target, visited, maxDepth - 1):
        return true
    of nnkRecCase:
      for branch in fd[1 ..^ 1]:
        if branch.kind != nnkOfBranch: continue
        let branchRec = branch[^1]
        if branchRec.kind == nnkRecList:
          for ffd in branchRec:
            if ffd.kind != nnkIdentDefs: continue
            let ft = ffd[ffd.len - 2]
            if reachesTypeThroughFields(ft, target, visited, maxDepth - 1):
              return true
    else: discard
  false

# ---------- per-field value emission ----------

proc fieldValueExpr(ftype: NimNode, selfName: string,
                    childSym, srcSym: NimNode, leafMode: bool): NimNode =
  ## Emit the expression that produces this field's value, drawing from
  ## `srcSym`. `leafMode` controls how self-positions are filled — terminal
  ## values for the leaf strategy, `childSym`-based draws for the extender.
  if isSelfType(ftype, selfName):
    if leafMode:
      # Direct self-reference is only well-formed for `ref` types (Nim itself
      # rejects non-ref direct recursion as infinite size); `nil` is the
      # canonical leaf value.
      return newNilLit()
    else:
      return newCall(newDotExpr(childSym, ident"run"), srcSym)

  if ftype.kind == nnkBracketExpr and selfRefInType(ftype, selfName):
    let head = $ftype[0]
    case head
    of "seq":
      let es = typeAsTypeSpec(ftype[1])
      if leafMode:
        return newCall(newTree(nnkBracketExpr, ident"newSeq", es))
      if isSelfType(ftype[1], selfName):
        return newCall(newDotExpr(newCall(ident"lists", childSym), ident"run"), srcSym)
      error("auto-derive: self-reference nested deeper than one wrapper " &
            "in '" & ftype.repr & "' is not supported; build the strategy " &
            "manually with `recursive(base, extend, maxDepth)`.", ftype)
    of "HashSet":
      let es = typeAsTypeSpec(ftype[1])
      if leafMode:
        return newCall(newTree(nnkBracketExpr, ident"initHashSet", es))
      if isSelfType(ftype[1], selfName):
        return newCall(newDotExpr(newCall(ident"sets", childSym), ident"run"), srcSym)
      error("auto-derive: self-reference nested deeper than one wrapper " &
            "in '" & ftype.repr & "' is not supported", ftype)
    of "Option":
      let es = typeAsTypeSpec(ftype[1])
      if leafMode:
        return newCall(newTree(nnkBracketExpr, ident"none", es))
      error("auto-derive: self-reference inside `Option[T]` for the extend " &
            "case requires a manual `recursive(...)` strategy.", ftype)
    of "Table":
      let ks = typeAsTypeSpec(ftype[1])
      let vs = typeAsTypeSpec(ftype[2])
      if leafMode:
        return newCall(newTree(nnkBracketExpr, ident"initTable", ks, vs))
      if isSelfType(ftype[2], selfName):
        let kArg = typeAsCallArg(ftype[1])
        return newCall(newDotExpr(
          newCall(ident"tables", newCall(ident"arbitrary", kArg), childSym),
          ident"run"), srcSym)
      error("auto-derive: self-reference nested deeper than one wrapper " &
            "in '" & ftype.repr & "' is not supported", ftype)
    else: discard

  # Non-self field: just `arbitrary(ftype).run(srcSym)`.
  let fArg = typeAsCallArg(ftype)
  newCall(newDotExpr(newCall(ident"arbitrary", fArg), ident"run"), srcSym)

# ---------- object / variant strategy builder ----------

proc buildObjectStrategy(typeName, objTy: NimNode, isRef = false): NimNode =
  let recList = objTy[2]
  if recList.kind != nnkRecList:
    error("auto-derive: expected a RecList in object type", objTy)

  # `typeName` is either a plain sym (e.g. `Pair`) or a bracket-expr type
  # instance (e.g. `Box[int]`). For the strategy's `T` and any object-literal
  # constructor we want the full type spec; for self-reference detection we
  # want the textual head only.
  let typeIdent = typeAsTypeSpec(typeName)
  let selfName = (if typeName.kind == nnkBracketExpr: $typeName[0] else: $typeName)

  # Walk the recList once: collect common-fields + variant-case (if any),
  # and decide whether the type is self-referential.
  var commonDefs: seq[NimNode]
  var variantCase: NimNode = nil
  var hasSelfRef = false
  proc identDefsHasSelf(fd: NimNode): bool =
    fd.kind == nnkIdentDefs and selfRefInType(fd[fd.len - 2], selfName)

  proc checkMutualOrError(fd: NimNode) =
    ## For each field whose type does *not* directly self-reference (those are
    ## handled by the recursive-synthesis path), walk through the field type's
    ## own fields looking for a path back to `selfName`. A hit means the user
    ## has a *mutual* recursion (e.g. `A → seq[B] → A`) that we can't synthesize
    ## a sensible leaf for; force a manual `recursive(...)` instead of letting
    ## the macro infinite-loop at expansion.
    if fd.kind != nnkIdentDefs: return
    let ft = fd[fd.len - 2]
    if selfRefInType(ft, selfName): return  # direct self-ref handled below
    var visited: HashSet[string]
    visited.incl selfName
    if reachesTypeThroughFields(ft, selfName, visited, maxDepth = 6):
      error("auto-derive: type '" & selfName & "' is mutually recursive " &
            "with another type via field '" & ft.repr & "'. Build the " &
            "strategy manually with `recursive(base, extend, maxDepth)`.", fd)

  for entry in recList:
    case entry.kind
    of nnkIdentDefs:
      if identDefsHasSelf(entry): hasSelfRef = true
      else: checkMutualOrError(entry)
      commonDefs.add entry
    of nnkRecCase:
      if not variantCase.isNil:
        error("auto-derive: multiple variant cases per object are not supported",
              entry)
      variantCase = entry
      for branch in entry[1 ..^ 1]:
        if branch.kind != nnkOfBranch: continue
        let branchRec = branch[^1]
        if branchRec.kind == nnkRecList:
          for fd in branchRec:
            if identDefsHasSelf(fd): hasSelfRef = true
            else: checkMutualOrError(fd)
    of nnkNilLit, nnkEmpty: discard
    else:
      error("auto-derive: unsupported record entry " & $entry.kind, entry)

  proc emitBody(srcSym, childSym: NimNode, leafMode: bool): NimNode =
    ## Generate the closure body for either the leaf (`leafMode = true`) or the
    ## extender (`leafMode = false`). Both walk the same field structure.
    let body = newStmtList()
    if isRef:
      body.add newCall(ident"new", ident"result")

    if variantCase.isNil:
      for fd in commonDefs:
        let ftype = fd[fd.len - 2]
        for i in 0 ..< fd.len - 2:
          let fn = newIdentNode($fd[i])
          let val = fieldValueExpr(ftype, selfName, childSym, srcSym, leafMode)
          body.add newAssignment(newDotExpr(ident"result", fn), val)
    else:
      let discDef = variantCase[0]
      let discName = newIdentNode($discDef[0])
      let discType = discDef[1]
      let discTypeArg = typeAsCallArg(discType)
      let discValSym = genSym(nskLet, "discVal")
      body.add newLetStmt(discValSym,
        newCall(newDotExpr(newCall(ident"arbitrary", discTypeArg),
                           ident"run"), srcSym))

      let caseStmt = newNimNode(nnkCaseStmt)
      caseStmt.add discValSym
      for branch in variantCase[1 ..^ 1]:
        if branch.kind != nnkOfBranch:
          error("auto-derive: unsupported variant branch " & $branch.kind, branch)
        let ofNode = newNimNode(nnkOfBranch)
        for i in 0 ..< branch.len - 1:
          ofNode.add branch[i]
        let branchRec = branch[^1]
        var branchBody = newStmtList()
        let objConstr = newNimNode(nnkObjConstr)
        objConstr.add typeIdent
        objConstr.add nnkExprColonExpr.newTree(discName, discValSym)
        for fd in commonDefs:
          let ftype = fd[fd.len - 2]
          for i in 0 ..< fd.len - 2:
            let fn = newIdentNode($fd[i])
            let val = fieldValueExpr(ftype, selfName, childSym, srcSym, leafMode)
            objConstr.add nnkExprColonExpr.newTree(fn, val)
        if branchRec.kind == nnkRecList:
          for fd in branchRec:
            if fd.kind != nnkIdentDefs: continue
            let ftype = fd[fd.len - 2]
            for i in 0 ..< fd.len - 2:
              let fn = newIdentNode($fd[i])
              let val = fieldValueExpr(ftype, selfName, childSym, srcSym, leafMode)
              objConstr.add nnkExprColonExpr.newTree(fn, val)
        branchBody.add newAssignment(ident"result", objConstr)
        ofNode.add branchBody
        caseStmt.add ofNode
      body.add caseStmt
    body

  proc makeRunProc(srcSym, childSym, body: NimNode): NimNode =
    newProc(
      params = @[typeIdent,
                 newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
      body = body,
      procType = nnkLambda)

  if not hasSelfRef:
    let srcSym = genSym(nskParam, "src")
    let dummyChild = ident"_unused"
    let runBody = emitBody(srcSym, dummyChild, leafMode = false)
    let runProc = makeRunProc(srcSym, dummyChild, runBody)
    return quote do:
      Strategy[`typeIdent`](run: `runProc`)

  # Self-referential path: emit a leaf strategy + an extender, wrap in
  # `recursive(...)`. The extender's parameter is bound to the same sym used
  # inside `emitBody`'s extend-mode output so the inner closure captures it.
  let leafSrcSym = genSym(nskParam, "src")
  let leafChildSym = ident"_unused_in_leaf"
  let leafBody = emitBody(leafSrcSym, leafChildSym, leafMode = true)
  let leafRun = makeRunProc(leafSrcSym, leafChildSym, leafBody)

  let extChildSym = genSym(nskParam, "child")
  let extSrcSym = genSym(nskParam, "src")
  let extBody = emitBody(extSrcSym, extChildSym, leafMode = false)
  let extInnerRun = makeRunProc(extSrcSym, extChildSym, extBody)

  let extenderProc = newProc(
    params = @[
      newTree(nnkBracketExpr, ident"Strategy", typeIdent),
      newIdentDefs(extChildSym,
                   newTree(nnkBracketExpr, ident"Strategy", typeIdent))
    ],
    body = newStmtList(quote do:
      Strategy[`typeIdent`](run: `extInnerRun`)),
    procType = nnkLambda)

  result = quote do:
    block:
      let leafStrat = Strategy[`typeIdent`](run: `leafRun`)
      recursive(leafStrat, `extenderProc`, maxDepth = 4)

# ---------- public macro ----------

macro arbitrary*(T: typedesc): untyped =
  ## Synthesize a `Strategy[T]` for `T` by inspecting it at compile time.
  let typ = T.getTypeInst[1]
  case typ.kind
  of nnkSym:
    case $typ
    of "int":
      return newCall(bindSym"integers", newLit(low(int)), newLit(high(int)))
    of "bool":
      return newCall(bindSym"booleans")
    of "float", "float64":
      return newCall(bindSym"floats")
    of "string":
      return newCall(bindSym"strings")
    else: discard
    let impl = typ.getTypeImpl
    if impl.kind == nnkObjectTy:
      return buildObjectStrategy(typ, impl)
    if impl.kind == nnkEnumTy:
      let typeIdent = newIdentNode($typ)
      return newCall(newTree(nnkBracketExpr, bindSym"enums", typeIdent))
    if impl.kind == nnkDistinctTy:
      let typeIdent = newIdentNode($typ)
      let baseArg = typeAsCallArg(impl[0])
      return quote do:
        map(arbitrary(`baseArg`),
            proc(u: `baseArg`): `typeIdent` = `typeIdent`(u))
    if impl.kind == nnkRefTy:
      var inner = impl[0]
      if inner.kind == nnkSym:
        inner = inner.getTypeImpl
      if inner.kind == nnkObjectTy:
        return buildObjectStrategy(typ, inner, isRef = true)
  of nnkBracketExpr:
    if typ.len >= 2 and $typ[0] == "seq":
      let elemArg = typeAsCallArg(typ[1])
      return quote do:
        lists(arbitrary(`elemArg`))
    if typ.len >= 2 and $typ[0] == "set":
      let eArg = typeAsCallArg(typ[1])
      return newCall(newTree(nnkBracketExpr, bindSym"bitsets", eArg))
    if typ.len >= 2 and $typ[0] == "HashSet":
      let eArg = typeAsCallArg(typ[1])
      return quote do:
        sets(arbitrary(`eArg`))
    if typ.len >= 3 and $typ[0] == "Table":
      let kArg = typeAsCallArg(typ[1])
      let vArg = typeAsCallArg(typ[2])
      return quote do:
        tables(arbitrary(`kArg`), arbitrary(`vArg`))
    if typ.len >= 3 and $typ[0] == "array":
      let rangeNode = typ[1]
      let elemArg = typeAsCallArg(typ[2])
      var lengthLit: NimNode
      if rangeNode.kind == nnkInfix and rangeNode.len == 3 and $rangeNode[0] == "..":
        lengthLit = newLit(int(rangeNode[2].intVal - rangeNode[1].intVal + 1))
      else:
        let typSpec = typeAsTypeSpec(typ)
        return quote do:
          arrays[len(default(`typSpec`)), `elemArg`](arbitrary(`elemArg`))
      return quote do:
        arrays[`lengthLit`, `elemArg`](arbitrary(`elemArg`))
    # Generic instantiation: a user type `T[X, Y, …]`. Resolve via getTypeImpl.
    let body = typ.getTypeImpl
    if body.kind == nnkObjectTy:
      return buildObjectStrategy(typ, body)
    if body.kind == nnkRefTy:
      var innerB = body[0]
      if innerB.kind == nnkSym:
        innerB = innerB.getTypeImpl
      if innerB.kind == nnkObjectTy:
        return buildObjectStrategy(typ, innerB, isRef = true)
  of nnkTupleTy:
    let tupleType = typeAsTypeSpec(typ)
    let srcSym = genSym(nskParam, "src")
    let runBody = newStmtList()
    for fieldDef in typ:
      if fieldDef.kind != nnkIdentDefs: continue
      let fieldType = fieldDef[fieldDef.len - 2]
      let fieldTypeArg = typeAsCallArg(fieldType)
      for i in 0 ..< fieldDef.len - 2:
        let fieldName = newIdentNode($fieldDef[i])
        let stratVar = genSym(nskLet, "s_" & $fieldName)
        runBody.add quote do:
          let `stratVar` = arbitrary(`fieldTypeArg`)
        runBody.add nnkAsgn.newTree(
          newDotExpr(ident"result", fieldName),
          newCall(newDotExpr(stratVar, ident"run"), srcSym))
    let runProc = newProc(
      params = @[tupleType,
                 newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
      body = runBody,
      procType = nnkLambda)
    return quote do:
      Strategy[`tupleType`](run: `runProc`)
  else: discard
  error("arbitrary: cannot derive a strategy for type " & typ.repr, T)
