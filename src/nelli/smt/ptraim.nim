## RFC-0005 S8bw (item 3). `ptrAimByName`: the replay's aim of a witness
## pointer at a field of a case object, named by the field (`ptrAimInto`'s
## `f<name>` step). `fieldPairs` walks only the active branch, and the
## pointer may address a field of a branch that becomes active only once
## the SUT runs (a global the SUT assigns): the field is reached by its
## name, with the branch check off where the caller takes its address.

import std/macros

proc ptrAimFieldNames(t: NimNode; acc: var seq[string]) =
  ## Every field `t` (an object type's implementation, or part of one)
  ## declares, every branch's and every ancestor's included.
  case t.kind
  of nnkRecList:
    for c in t: ptrAimFieldNames(c, acc)
  of nnkIdentDefs:
    for j in 0 ..< t.len - 2:
      var n = t[j]
      if n.kind == nnkPostfix: n = n[1]
      if n.kind == nnkPragmaExpr: n = n[0]
      if n.kind in {nnkIdent, nnkSym}: acc.add n.strVal
  of nnkRecCase:
    ptrAimFieldNames(t[0], acc)
    for j in 1 ..< t.len: ptrAimFieldNames(t[j][^1], acc)
  of nnkObjectTy:
    if t.len > 1 and t[1].kind == nnkOfInherit and t[1].len == 1:
      let par = t[1][0].getTypeImpl
      if par.kind == nnkObjectTy: ptrAimFieldNames(par, acc)
    if t.len > 2: ptrAimFieldNames(t[2], acc)
  else: discard

macro ptrAimByName*(x: typed; name: string; body: untyped): untyped =
  ## `body` once per field of `x`'s object type, with `it` that field of
  ## `x`, run when `name` is the field's name.
  var names: seq[string]
  ptrAimFieldNames(x.getTypeImpl, names)
  result = newStmtList()
  for nm in names:
    let acc = newDotExpr(x, ident nm)
    let b = body.copyNimTree
    result.add quote do:
      if `name` == `nm`:
        template it: untyped {.used.} = `acc`
        `b`
