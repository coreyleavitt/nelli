## RFC-fuzzer-nextgen E1 stage 2: the call-site `fuzz(...)` macro (C4).
##
## `Strategy.run`/a property `proc` are opaque runtime closures — Nim cannot
## recover source from them, and a fresh OS process (Track E) cannot inherit
## them across `exec`. The RESOLVED design (RFC §Open items, the opaque-
## closure boundary) is a `macro` that captures the strategy/property
## *construction expressions* at the call site, not their closure values:
##
## - **Track G** (later, C7) gets the property as an emittable **typed proc
##   symbol** — the walker's ONLY ingestion door is `fn: typed` -> `getImpl`
##   -> `parseProc` -> `walk` (verified in code, `symex.nim:461`/`:1627`), so
##   this macro's job is to make sure a named, module-scope proc symbol
##   EXISTS for the property, lifting an inline `proc(x: T) = ...` literal to
##   one when needed (`liftPropIfNeeded` below). It does not itself drive the
##   walker (C7 is a separate follow-up).
## - **Track E** gets worker reconstruction with no new user-facing API (C5,
##   next cycle): the same macro will emit a hidden worker-mode entry, keyed
##   by a stable call-site id, that re-runs the captured construction to
##   rebuild a fresh `(Strategy[T], prop)` pair instead of reusing the
##   parent's objects.
##
## This cycle (C4) is the behavior-preserving front only: `fuzz(<strategyExpr>,
## <propExpr>, <settings?>)` expands to the exact wiring
## `tfuzzloop.nim`/`tfuzzcovcorpus.nim` already write by hand — a fresh
## `CoverageFrontier` plus `fuzz(s, inProcessTarget(prop), frontier,
## settings)` — so it is a drop-in, no-behavior-change entry point. The
## worker-mode registry (C5) and the compile-time capture checks (C6) land in
## their own cycles.

import std/macros
import ./fuzz

proc liftPropIfNeeded(propExpr: NimNode): tuple[def: NimNode, sym: NimNode] =
  ## RFC-fuzzer-nextgen E1 (C4/C7 pre-req): if `propExpr` already names a
  ## proc (`nnkSym` — the user wrote `fuzz(s, myProp, ...)`), it is ALREADY a
  ## named module-scope typed proc symbol — nothing to do. Otherwise
  ## (`nnkLambda` — an inline `proc(x: T) = ...` literal) lift it into a
  ## brand-new top-level `proc` definition (same params/body/pragmas, just a
  ## fresh name) so the property is a named, module-scope, referenceable
  ## typed proc symbol EITHER way — the shape Track G's walker will need
  ## later (`getImpl` on a symbol; a closure *value* is not enough).
  if propExpr.kind == nnkSym:
    (newEmptyNode(), propExpr)
  else:
    let liftedName = genSym(nskProc, "nelliFuzzProp")
    var children = newSeq[NimNode]()
    for c in propExpr: children.add c
    children[0] = liftedName
    (newTree(nnkProcDef, children), liftedName)

proc fuzzMacroImpl(stratExpr, propExpr, settingsExpr: NimNode): NimNode =
  let (liftedDef, propSym) = liftPropIfNeeded(propExpr)

  var stmts = newStmtList()
  if liftedDef.kind != nnkEmpty:
    stmts.add liftedDef

  # The behavior-preserving front (C4): identical wiring to what
  # `tfuzzloop`/`tfuzzcovcorpus` write by hand today — a fresh
  # `CoverageFrontier` plus `fuzz(s, inProcessTarget(prop), frontier,
  # settings)`. This is the macro's VALUE (last expression in the stmt list).
  stmts.add quote do:
    block:
      var nelliFuzzFrontier = newCoverageFrontier()
      fuzz(`stratExpr`, inProcessTarget(`propSym`), nelliFuzzFrontier, `settingsExpr`)

  result = stmts

macro fuzz*(stratExpr, propExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>)` — settings default to `FuzzSettings()`.
  ## See the module doc comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, newCall(ident"FuzzSettings"))

macro fuzz*(stratExpr, propExpr, settingsExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>, <settings>)`. See the module doc
  ## comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, settingsExpr)
