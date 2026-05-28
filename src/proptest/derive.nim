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

proc buildObjectStrategy(typeName, objTy: NimNode, isRef = false): NimNode =
  ## Emit a strategy that constructs an object by drawing each field. If
  ## `isRef`, the result is a `ref object` and we `new(result)` first.
  let recList = objTy[2]
  if recList.kind != nnkRecList:
    error("auto-derive: expected a RecList in object type", objTy)

  let typeIdent = newIdentNode($typeName)
  let srcSym = genSym(nskParam, "src")
  var letDecls = newStmtList()
  var assigns = newStmtList()

  for fieldDef in recList:
    if fieldDef.kind != nnkIdentDefs:
      error("auto-derive does not yet support object variants or anonymous fields",
            fieldDef)
    let fieldType = fieldDef[fieldDef.len - 2]
    let fieldTypeArg = typeAsCallArg(fieldType)
    # One IdentDefs can declare multiple names: `a, b, c: int`
    for i in 0 ..< fieldDef.len - 2:
      let fieldName = fieldDef[i]
      let stratVar = genSym(nskLet, "s_" & $fieldName)
      letDecls.add quote do:
        let `stratVar` = arbitrary(`fieldTypeArg`)
      assigns.add newAssignment(
        newDotExpr(ident"result", fieldName),
        newCall(newDotExpr(stratVar, ident"run"), srcSym))

  # Place the per-field strategy lets *inside* the inner closure rather than at
  # block scope; otherwise something in the closure-capture chain produces a
  # dangling reference once a captured strategy itself contains a closure
  # (string/seq/list fields).  Cost: per-draw strategy construction; acceptable
  # for correctness MVP and easy to refactor later if it shows up in profiles.
  let combinedBody = newStmtList()
  if isRef:
    combinedBody.add newCall(ident"new", ident"result")
  for s in letDecls: combinedBody.add s
  for s in assigns: combinedBody.add s

  let runProc = newProc(
    params = @[typeIdent,
               newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
    body = combinedBody,
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
