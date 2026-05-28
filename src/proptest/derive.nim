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
import ./strategy

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
  of nnkBracketExpr:
    # generic instantiations like seq[int]. The element type is `typ[1]` — but
    # when spliced as a sym into a call, Nim treats it as a value, so we
    # re-create it as a fresh ident so it resolves as a type in the call site.
    if typ.len >= 2 and $typ[0] == "seq":
      let elemIdent = newIdentNode($typ[1])
      return quote do:
        lists(arbitrary(`elemIdent`))
  else: discard
  error("arbitrary: cannot derive a strategy for type " & typ.repr, T)
