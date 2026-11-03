## RFC-0005 S8cu fixture: a pushing template and a pushing macro, used from another
## module. The scan does not read what these expand to where they are called.
import std/macros
template pushOffTpl*() =
  {.push fieldChecks: off, rangeChecks: off, objChecks: off.}
macro pushOffMacro*(): untyped =
  result = newNimNode(nnkPragma)
  result.add ident"push"
  for o in ["fieldChecks", "rangeChecks", "objChecks"]:
    result.add newColonExpr(ident(o), ident"off")
