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

proc buildObjectStrategy(typeName, objTy: NimNode): NimNode =
  ## Emit a strategy that constructs an object by drawing each field.
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

  let runProc = newProc(
    params = @[typeIdent,
               newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
    body = assigns)

  result = quote do:
    block:
      `letDecls`
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
  of nnkBracketExpr:
    if typ.len >= 2 and $typ[0] == "seq":
      let elemArg = typeAsCallArg(typ[1])
      return quote do:
        lists(arbitrary(`elemArg`))
  else: discard
  error("arbitrary: cannot derive a strategy for type " & typ.repr, T)
