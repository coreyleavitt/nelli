## Compile-time derivation of `Strategy[T]` from `T`.
##
## `arbitrary(T)` is a macro that inspects `T`'s structure and emits a strategy
## tailored to that type — so a property test never needs to write a strategy
## for a user type by hand. Primitives map to the built-in strategies; compound
## types (tuples, objects, variants, refs, seqs) recurse over their components.
##
## This first slice covers the primitive leaves (int, bool, float, string).
## Compound types are added next.

import std/macros
import ./strategy, ./datasource

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

proc drawAndAssign(stratVar, fieldNameIdent, srcSym: NimNode,
                   fieldTypeArg: NimNode): (NimNode, NimNode) =
  ## Returns (let-decl, ColonExpr-for-objconstr-or-asgn) for one field.
  let letDecl = quote do:
    let `stratVar` = arbitrary(`fieldTypeArg`)
  let drawCall = newCall(newDotExpr(stratVar, ident"run"), srcSym)
  (letDecl, drawCall)

proc buildObjectStrategy(typeName, objTy: NimNode, isRef = false): NimNode =
  ## Emit a strategy that constructs an object by drawing each field.
  ##
  ## * Plain object (no variant): draws each field and assigns `result.f = …`.
  ## * Variant (`case kind: K of … of …`): draws the discriminator first, then
  ##   case-dispatches; each branch constructs the result via an object literal
  ##   `T(kind: chosen, branchField: …)` so only the active branch's fields are
  ##   touched (the only way Nim accepts setting variant fields).
  ## * If `isRef`, the result is a `ref object` and we `new(result)` first.
  let recList = objTy[2]
  if recList.kind != nnkRecList:
    error("auto-derive: expected a RecList in object type", objTy)

  let typeIdent = newIdentNode($typeName)
  let srcSym = genSym(nskParam, "src")

  # Separate common (always-present) fields from a variant case.
  var commonDefs: seq[NimNode]   # IdentDefs nodes for plain fields
  var variantCase: NimNode = nil
  for entry in recList:
    case entry.kind
    of nnkIdentDefs:
      commonDefs.add entry
    of nnkRecCase:
      if not variantCase.isNil:
        error("auto-derive: multiple variant cases per object are not supported",
              entry)
      variantCase = entry
    of nnkNilLit, nnkEmpty:
      discard
    else:
      error("auto-derive: unsupported record entry " & $entry.kind, entry)

  let runBody = newStmtList()
  if isRef:
    runBody.add newCall(ident"new", ident"result")

  proc emitFieldDecls(defs: seq[NimNode],
                      letsOut: var NimNode,
                      collectInto: var seq[(NimNode, NimNode)]) =
    ## For each (possibly-multi-name) IdentDefs, emit a let for that field's
    ## strategy and record (fieldNameIdent, drawCallExpr).
    for fieldDef in defs:
      let fieldType = fieldDef[fieldDef.len - 2]
      let fieldTypeArg = typeAsCallArg(fieldType)
      for i in 0 ..< fieldDef.len - 2:
        let fieldName = newIdentNode($fieldDef[i])
        let stratVar = genSym(nskLet, "s_" & $fieldName)
        let (decl, drawCall) = drawAndAssign(stratVar, fieldName, srcSym, fieldTypeArg)
        letsOut.add decl
        collectInto.add (fieldName, drawCall)

  if variantCase.isNil:
    # Plain object: declare each field's strategy, then assign result.f = draw.
    var lets = newStmtList()
    var fields: seq[(NimNode, NimNode)]
    emitFieldDecls(commonDefs, lets, fields)
    for s in lets: runBody.add s
    for (fName, drawCall) in fields:
      runBody.add newAssignment(newDotExpr(ident"result", fName), drawCall)
  else:
    # Variant: discriminator first, then per-branch construction.
    let discDef = variantCase[0]   # IdentDefs(discName, discType)
    let discName = newIdentNode($discDef[0])
    let discType = discDef[1]
    let discTypeArg = typeAsCallArg(discType)
    let discStratVar = genSym(nskLet, "s_disc")
    let discValueSym = genSym(nskLet, "discVal")
    runBody.add quote do:
      let `discStratVar` = arbitrary(`discTypeArg`)
      let `discValueSym` = `discStratVar`.run(`srcSym`)

    let caseStmt = newNimNode(nnkCaseStmt)
    caseStmt.add discValueSym
    for branch in variantCase[1 ..^ 1]:
      case branch.kind
      of nnkOfBranch:
        let ofNode = newNimNode(nnkOfBranch)
        # Carry the case labels (everything except the trailing RecList).
        for i in 0 ..< branch.len - 1:
          ofNode.add branch[i]
        let branchRecList = branch[^1]

        # For this branch: declare strats for common + branch fields, then
        # construct the object literal with discriminator and all those fields.
        var branchBody = newStmtList()
        var commonFields, branchFields: seq[(NimNode, NimNode)]
        emitFieldDecls(commonDefs, branchBody, commonFields)
        if branchRecList.kind == nnkRecList:
          var branchDefs: seq[NimNode]
          for fd in branchRecList:
            if fd.kind == nnkIdentDefs: branchDefs.add fd
          emitFieldDecls(branchDefs, branchBody, branchFields)

        let objConstr = newNimNode(nnkObjConstr)
        objConstr.add typeIdent
        objConstr.add nnkExprColonExpr.newTree(discName, discValueSym)
        for (fName, drawCall) in commonFields:
          objConstr.add nnkExprColonExpr.newTree(fName, drawCall)
        for (fName, drawCall) in branchFields:
          objConstr.add nnkExprColonExpr.newTree(fName, drawCall)
        branchBody.add newAssignment(ident"result", objConstr)
        ofNode.add branchBody
        caseStmt.add ofNode
      else:
        error("auto-derive: unsupported variant branch " & $branch.kind, branch)
    runBody.add caseStmt

  let runProc = newProc(
    params = @[typeIdent,
               newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
    body = runBody,
    procType = nnkLambda)

  result = quote do:
    Strategy[`typeIdent`](run: `runProc`)

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
    # Non-primitive sym: probably a user type. Inspect its implementation.
    let impl = typ.getTypeImpl
    if impl.kind == nnkObjectTy:
      return buildObjectStrategy(typ, impl)
    if impl.kind == nnkEnumTy:
      let typeIdent = newIdentNode($typ)
      return newCall(newTree(nnkBracketExpr, bindSym"enums", typeIdent))
    if impl.kind == nnkRefTy:
      # `ref object` reads as RefTy wrapping a generated Sym; resolve that Sym
      # to its ObjectTy via a second getTypeImpl.
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
  of nnkTupleTy:
    # Named tuple type. Build a strategy that draws each field, just like for an
    # object but with the tuple type as the strategy's T.
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
