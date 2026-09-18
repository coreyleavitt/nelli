## 13-finding wiring audit, finding W10 -- issue #163's `feOpaqueCallUnmodelled`
## classification names the call that cost the answer on the `symexFind` path
## (`runSymexImpl` drains `w.walkDegradeErrors` into `exnWarnings`, which rides
## every verdict branch) but NOT on the `concolicFlip`/`concolicCollect` path
## (the fuzzer's entry point, and the reason #163 was filed at all).
## `runConcolicCollectImpl` (`smt/runtime.nim`) reads `w.concolicAmbiguousBranches`
## off the walk but never `w.walkDegradeErrors` or `w.sawUnknown` -- so an
## opaque call ahead of a concolic collection silently produced a weaker
## collect (a smaller `branchTrace`, fewer symbolicated draws) with no way for
## a caller to tell a clean collect from a tainted one.
##
## This is diagnostics, not soundness: Track E re-verifies every candidate
## concretely, so a tainted collect can only waste a candidate, never yield a
## wrong result. The fix adds `ConcolicYieldCounters.walkDegradeCount`
## (`smt/concolictaxonomy.nim`), populated in `runConcolicCollectImpl`
## (`smt/runtime.nim`) from `w.walkDegradeErrors`, deduped by message exactly
## like `runSymexImpl`'s own `exnWarnings` drain. It rides the SAME public
## channel `ambiguousBranches` already does: `ConcolicCollectResult.counters`
## (read here via the public `concolicCollect` macro, `nelli/symex`) and, one
## layer up, `ConcolicFlipResult.collectCounters`.
##
## Method note (inherited from #162/#163): every symbolic expectation below is
## paired with the SAME computation run for real in this file.
import std/unittest
import nelli/symex
import nelli/coverage

# --- a genuinely opaque call: result IS used, so it still taints (#163's own
# `usesSensor` shape, `tsymex_163_opaque_transparent.nim`) -----------------

proc readSensor(): int {.symexOpaque.} = 42

proc opaqueGate(x: int) =
  let s = readSensor()          ## result is USED: the taint is correct
  if x + s == 100:
    symexTarget("hit")
  else:
    symexTarget("miss")

# --- a clean SUT: no opaque/unmodelled call anywhere on the walk ----------

proc cleanGate(x: int) =
  if x > 5:
    symexTarget("hi")
  else:
    symexTarget("lo")

# --- a `{.cover.}`-instrumented SUT: nelli's OWN instrumentation, transparent
# to the solver since #163 slice 1 (this is the case that ties W10 back to
# why #163 exists in the first place) --------------------------------------

proc coveredGate(x: int) {.cover.} =
  if x > 5:
    symexTarget("hi")
  else:
    symexTarget("lo")

# --- #163 review finding R9: a LOWERING-SITE degrade (the `loweringDegradeErrors`
# threadvar sink, `smt/runtime.nim`'s `cmpString`) rather than a WalkCtx-field
# degrade (`w.walkDegradeErrors`, what `opaqueGate` above exercises). String
# ordering (`<`/`<=`/`>`/`>=`) is not modeled until Cluster S3 and degrades
# in-band via `loweringDegradeErrors` -- a PURE helper with no `w: var WalkCtx`
# in scope. `resetSymexRunState` is called at `runConcolicCollectImpl`'s own
# entry, so the threadvar sink is live during a concolic walk; the bug is that
# its contents are never READ back into the counter afterward. -------------

proc strOrderGate(x: int) =
  let a = "apple"
  let b = "banana"
  if a < b:                     ## degrades via loweringDegradeErrors (cmpString)
    if x > 5:
      symexTarget("hi")
    else:
      symexTarget("lo")
  else:
    symexTarget("unreachable")

suite "163 audit W10 -- oracle: every gate SUT behaves as claimed":

  test "oracle: opaqueGate/cleanGate/coveredGate all gate on their stated predicate":
    # readSensor() really returns 42, so opaqueGate's hit predicate is x == 58.
    doAssert 42 + 58 == 100
    cleanGate(0)
    cleanGate(10)
    coveredGate(0)
    coveredGate(10)
    doAssert "apple" < "banana"
    strOrderGate(0)
    strOrderGate(10)

suite "163 audit W10 -- the concolic collect path reads w.walkDegradeErrors":

  test "an opaque call whose result is used taints a concolic collect -- nonzero degrade count":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(opaqueGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount > 0

  test "a clean SUT reports a zero degrade count -- the counter is not trivially always-on":
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cleanGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount == 0

  test "a {.cover.}'d SUT also reports zero -- #163 made nelli's own instrumentation transparent":
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(coveredGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount == 0

  test "#163 review R9 -- a lowering-site (threadvar sink) degrade also reports nonzero":
    ## Before the fix: `runConcolicCollectImpl` reads only `w.walkDegradeErrors`
    ## (the WalkCtx-field sink), never `loweringDegradeErrors` (the threadvar
    ## sink `cmpString`'s string-ordering degrade writes to) -- so this SUT's
    ## degrade was silently discarded and `walkDegradeCount` read 0,
    ## indistinguishable from `cleanGate`'s genuinely clean collect above.
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(strOrderGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount > 0
