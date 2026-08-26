## RFC-fuzzer-nextgen E1 cycle C7 — the AST proof-spike / capture-
## consumability freeze-guard.
##
## This is a SPIKE that SHIPS: it exists to prove, before ~7 more Track-E
## slices weld onto the `fuzz(...)` capture point, that the shape
## `liftPropIfNeeded` (`src/nelli/fuzzmacro.nim`) emits for a property is
## actually consumable by the symex walker's REAL ingestion door — not a
## stub. Verified in code (do not re-derive): the walker's only ingestion
## path is a **typed proc symbol** — `symexForAll`/`symexFindAllWitnesses`
## (`symex.nim:461`/`:1627`) -> `resolveEntryImpl`/`getImpl` ->
## `parseProc` (NimNode -> IRStmt) -> `runSymex` -> `walk` (single symbolic
## mode; there is no `wmFollowConcrete` mode). "Syntactically capturable" is
## not "consumable by the real walker" — this file is where that gap either
## closes or fires.
##
## Two things must reach the real walker door, bounded:
##
## 1. A macro-lifted INLINE-LAMBDA property. `liftPropIfNeeded` lifts an
##    inline `proc(x: T) = ...` literal to a fresh top-level `proc` via
##    `genSym(nskProc)` + reassembling params/pragmas/body under a new
##    `nnkProcDef`. `spikeLiftPropIfNeeded` below reproduces that EXACT
##    mechanism (duplicated, not imported — `liftPropIfNeeded` is private to
##    `fuzzmacro.nim`, and the whole point of this spike is to prove the
##    SHAPE is walker-ingestible independent of that module's internals),
##    then in the SAME macro expansion feeds the lifted symbol straight to
##    `symexFindAllWitnesses` — the walker's real entry, not a stub.
##
## 2. A generic-instantiated `Strategy[T]` capture (T inferred at the call
##    site) PLUS a lifted property whose body calls a generic helper at two
##    DIFFERENT instantiation types — generics being the codebase's known
##    prior failure class (the bare-name monomorphization-cache collision;
##    see `tsymex_phase15_G1a_instkey.nim` for the load-bearing collision
##    demonstrator this mirrors, and `instKeyFor`, `dsl_parser.nim:5262`,
##    for the fix). This drives `symexForAll`'s multi-arg path, which is the
##    one that actually calls `s.getTypeInst()` to extract the strategy's
##    element type.
##
## If either macro-time step below had rejected the lifted shape (a
## `getImpl` failure, a `parseProc` rejection, or a walker abort), THAT is
## the freeze-guard firing — this file would report the exact failure
## instead of asserting green. It ships green: both shapes are consumable.
import std/[unittest, macros, sequtils]
import nelli
import nelli/symex
import nelli/engine/types

# ---------------------------------------------------------------------------
# Shared: reproduce `liftPropIfNeeded`'s exact lift mechanism.
# ---------------------------------------------------------------------------

proc spikeLiftPropIfNeeded(propExpr: NimNode): tuple[def: NimNode, sym: NimNode] =
  ## Test-only duplicate of `fuzzmacro.liftPropIfNeeded` (that proc is not
  ## exported). Same bimodal contract: an already-named proc symbol
  ## (`nnkSym`) passes through untouched; an inline lambda literal
  ## (`nnkLambda`) is lifted into a brand-new `nnkProcDef` under a
  ## `genSym(nskProc)` name by copying every child and overwriting the name
  ## slot — the identical params/pragmas/body/reserved-slot reassembly the
  ## real macro performs.
  if propExpr.kind == nnkSym:
    (newEmptyNode(), propExpr)
  else:
    let liftedName = genSym(nskProc, "spikeLiftedProp")
    var children = newSeq[NimNode]()
    for c in propExpr: children.add c
    children[0] = liftedName
    (newTree(nnkProcDef, children), liftedName)

# ---------------------------------------------------------------------------
# Sub-spike 1: macro-lifted inline-lambda proc -> the real walker door.
# ---------------------------------------------------------------------------

macro spikeFeedFindAllWitnesses(propLit: typed): untyped =
  ## Lifts `propLit` exactly like `liftPropIfNeeded`, splices the lifted
  ## `nnkProcDef`, then — in the SAME expansion — calls
  ## `symexFindAllWitnesses` on the lifted symbol. If the lifted proc were
  ## not walker-ingestible this call would fail to compile or the walker
  ## would reject the body; there is no stub standing in for it.
  let (def, sym) = spikeLiftPropIfNeeded(propLit)
  result = newStmtList()
  if def.kind != nnkEmpty:
    result.add def
  result.add quote do:
    symexFindAllWitnesses(`sym`, inMemoryDatabase())

# ---------------------------------------------------------------------------
# Sub-spike 2: generic Strategy[T] + lifted property with a generic callee.
# ---------------------------------------------------------------------------

proc gSpikeHelper[T](x: T): T =
  ## Called from the SUT below at TWO different instantiation types
  ## (int, bool) — the exact shape that collided under the pre-G1a
  ## bare-name `ctx.procs` key (`symex generics plan` memory / G1a fix).
  x

macro spikeFeedForAll(sExpr, propLit: typed): untyped =
  ## Same lift as above, but feeds `symexForAll(sExpr, liftedSym, db)` —
  ## the entry that extracts the strategy's element type via
  ## `s.getTypeInst()` (multi-arg path) and drives the full random +
  ## symex-seeded loop, not just Layer 1's witness search.
  let (def, sym) = spikeLiftPropIfNeeded(propLit)
  result = newStmtList()
  if def.kind != nnkEmpty:
    result.add def
  result.add quote do:
    symexForAll(`sExpr`, `sym`, inMemoryDatabase())

suite "E1 C7 — AST proof-spike (capture-consumability freeze-guard)":

  test "macro-lifted inline-lambda proc reaches the real walker door (getImpl -> parseProc -> walk)":
    # Reproduces the EXACT shape `fuzz(s, proc(x: int) = ..., settings)`
    # emits for its property argument: an inline lambda, lifted to a
    # genSym'd top-level proc, never a hand-written named proc. Bounded:
    # a single `doAssert` over a bare int, default (already-small) budget
    # (maxCallDepth 3 / maxLoopUnwind 5) — no loops, no recursion.
    discard consumeSymexFindings()
    let findings = spikeFeedFindAllWitnesses(proc(x: int) = doAssert x != 42)
    let raised = findings.filterIt(
      it.status == sfRaised and it.defectTypeId == "AssertionDefect")
    check raised.len >= 1
    check raised[0].witnessChoices.len > 0

  test "generic Strategy[T] (T inferred) + lifted property with a 2-instantiation generic callee reaches symexForAll (getTypeInst + instKeyFor, no bare-name collision)":
    # `just[T]` is a generic strategy CONSTRUCTOR — `just(0)`/`just(false)`
    # infer T at the call site, composed via `map` into `Strategy[(int,
    # bool)]`. The property (lifted, per sub-spike 1's mechanism) is
    # 2-arg, so `symexForAll` takes the `s.getTypeInst()` elemTy-extraction
    # path. Inside the property, `gSpikeHelper` is called at two DISTINCT
    # instantiation types (int, bool) from the same SUT — the load-bearing
    # G1a collision shape. Bounded: no loops, two trivial instantiations
    # well under the default maxInstantiationsPerProc=64 cap.
    discard consumeSymexFindings()
    let report = spikeFeedForAll(
      map(just(0), just(false)),
      proc(a: int, b: bool) =
        if gSpikeHelper(a) == 42 and gSpikeHelper(b) == true:
          symexTarget("generic-hit"))
    check report.outcome == otPassed
    var found = false
    for f in report.symexFindings:
      if f.targetDesc == "label(\"generic-hit\")" and f.status == sfSat:
        found = true
    check found
