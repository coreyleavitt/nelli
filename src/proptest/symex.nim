## proptest/symex — public-API entry for the symbolic-execution capability.
##
## See:
##   * docs/SYMEX_PLAN.md     — build plan + scope
##   * docs/symex/ADR-0001-integer-semantics.md
##   * docs/symex/ADR-0002-dsl-factoring.md
##
## Phase 1 supports a small Nim fragment: int/bool params + locals,
## arithmetic + comparison + boolean, `if` / `elif` / `else`, the
## three body markers below. Each later phase widens the fragment.
##
## Body markers — these are templates so that the same SUT is
## simultaneously walkable by symex AND runnable under random PBT
## without source duplication. Outside symex:
##
##   * `symexTarget(name)`  — no-op (it's a coverage label)
##   * `symexAssert(cond)`  — `doAssert cond` (it's a stated invariant)
##   * `symexAssume(cond)`  — early return if violated (filter the
##                            execution to satisfying inputs)

import std/macros
import ./smt/dsl
export dsl

# ---- Body markers -----------------------------------------------------------

## Body markers are procs (not templates) so semcheck doesn't elide
## the call site before the symex parser sees it. The parser
## recognizes the call by callee name; outside symex these run as
## ordinary procs whose body provides the dual-mode semantics.

proc symexTarget*(name: string) {.inline.} =
  ## Marker: a coverage target for `symexFind(..., tLabel(name))`.
  ## Outside symex, calling this is a no-op — the SUT is unaffected.
  discard name

proc symexAssert*(cond: bool) {.inline.} =
  ## Marker: an invariant the user claims always holds. Outside
  ## symex, asserted at runtime via `doAssert` so random PBT also
  ## catches violations. Inside symex, the parser maps this to an
  ## IR node the walker treats as a fork point for
  ## `tAssertionViolation` searches.
  doAssert cond, "symexAssert violated"

proc symexAssume*(cond: bool) {.inline.} =
  ## Marker: a precondition restricting the input domain. Phase 1
  ## ships with no-op outside symex (the richer "early-return on
  ## violation" semantics is deferred until needed — `symexAssume`'s
  ## body markers in Phase 1 are recognized by the parser but don't
  ## yet affect the SUT's normal-run behavior). Inside symex, the
  ## walker conjoins `cond` into the path condition.
  discard cond

# ---- The driver macro -------------------------------------------------------

macro symexFind*(fn: typed,
                 target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): untyped =
  ## Symbolically execute `fn` searching for an input that reaches `target`.
  ## Returns `SymexResult[ParamTuple]` where `ParamTuple` is the proc's
  ## parameter list as a Nim tuple.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("symexFind: expected a `proc` symbol", fn)
  let parsed = parseProc(impl)

  # Build the tuple type and witness-construction tuple. We genSym a
  # local name for the RawWitness so the witness-constructor calls
  # share an identity-equal NimNode with the `let` that binds it —
  # plain `ident"…"` wouldn't bind under hygiene.
  let witId = genSym(nskLet, "rawWit")
  var tupleTy = newTree(nnkTupleConstr)
  var witnessTup = newTree(nnkTupleConstr)
  for p in parsed.params:
    case p.ty.kind
    of itBool:
      tupleTy.add ident"bool"
      witnessTup.add newCall(bindSym"readBool", witId, newLit(p.name))
    of itInt:
      # Map (width, signed) → Nim type + reader proc.
      var tyName, readerName: string
      if p.ty.signed:
        case p.ty.width
        of 8:  tyName = "int8";  readerName = "readInt8"
        of 16: tyName = "int16"; readerName = "readInt16"
        of 32: tyName = "int32"; readerName = "readInt32"
        of 64: tyName = "int";   readerName = "readInt"
        else: error("symex: unsupported signed int width " &
                    $p.ty.width & " for param `" & p.name & "`", fn)
      else:
        case p.ty.width
        of 8:  tyName = "uint8";  readerName = "readUInt8"
        of 16: tyName = "uint16"; readerName = "readUInt16"
        of 32: tyName = "uint32"; readerName = "readUInt32"
        of 64: tyName = "uint";   readerName = "readUInt"
        else: error("symex: unsupported unsigned int width " &
                    $p.ty.width & " for param `" & p.name & "`", fn)
      tupleTy.add ident(tyName)
      witnessTup.add newCall(ident(readerName), witId, newLit(p.name))

  # `(int,)` is a syntactic 1-tuple; nnkTupleConstr with one child
  # renders correctly for both the type and the value.

  let bodyExpr = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode

  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`, body: `bodyExpr`)
      let raw = runSymex(prog, `target`, `settings`)
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions)
