## examples/symex_loops.nim
##
## Bounded loops + the UNKNOWN downgrade. Phase 6 ships a *k-bounded*
## walker: each `while`/`for` is unrolled at most `maxLoopUnwind`
## times (default 5). A path still looping at the bound is cut off,
## and the cut is recorded as a `beBudgetExhausted` gap of class
## `dcFabricated` (the analysis invented an end to the loop). If the
## target was only reachable along cut-off paths, the status is
## `sxUnknown`, and `gaps()` on the result names the bound that
## caused it -- the lever to pull.
##
## This is the right trade-off for an automatic tool: invariant
## inference would let us reason about unbounded loops symbolically,
## but it requires either user-supplied invariants or expensive
## inference. k-bounded model checking — used by SLAM, CBMC, Pex —
## is the practical sweet spot. We borrow it.
##
## When UNKNOWN means "the loop just needed more iterations than we
## have" (`gaps()` says `dcFabricated` / `beBudgetExhausted`, and
## `r.bounds` echoes the `maxLoopUnwind` it ran under), you have three
## honest moves:
##   1. Bump `maxLoopUnwind` in `SymexSettings` (Case B below).
##   2. Accept UNKNOWN as covered via `acceptUnknownAsCovered = true`
##      — appropriate when the loop is part of trusted code you
##      don't want to verify symbolically.
##   3. Refactor the SUT so the relevant target is reachable within
##      the unwind budget (often the right CS answer).

import std/[strformat]
import nelli/symex

# ---- Case A: a target reachable within the unwind budget ------------------

proc loopShort(x: int) =
  var i = 0
  while i < x:
    i = i + 1
  if i == 3:
    symexTarget("hit-3")

block reachable:
  let r = symexFind(loopShort, tLabel("hit-3"))
  doAssert r.status == sxSat
  echo &"loopShort: witness x = {r.witness[0]} (≤ maxLoopUnwind = 5)"

# ---- Case B: target beyond unwind budget → UNKNOWN ------------------------

proc loopDeep(x: int) =
  var i = 0
  while i < x:
    i = i + 1
  if i == 100:
    symexTarget("hit-100")

block unknownUnderBudget:
  # Default `maxLoopUnwind = 5`. The path needing 100 iterations
  # is cut off at the bound → sxUnknown, and not `trusted()`.
  let r = symexFind(loopDeep, tLabel("hit-100"))
  doAssert r.status == sxUnknown
  doAssert not r.trusted
  echo "loopDeep: status = sxUnknown (target beyond unwind budget)"

# ---- Case B': reading the gap, then pulling its lever (RFC-0005) ----------

proc loopEight(x: int) =
  var i = 0
  while i < x:
    i = i + 1
  if i == 8:
    symexTarget("hit-8")

block gapsWalkthrough:
  # `gaps()` lists each cause behind a not-trusted verdict, with the
  # `DegradeClass` that names its lever. Here every gap is the loop
  # bound: `dcFabricated` / `beBudgetExhausted`, and `r.bounds` echoes
  # the bound the run used.
  let r = symexFind(loopEight, tLabel("hit-8"))
  doAssert r.status == sxUnknown
  for g in r.gaps():
    doAssert g.class == dcFabricated and g.e.kind == beBudgetExhausted
  doAssert r.bounds.maxLoopUnwind == 5
  echo &"loopEight: sxUnknown, {r.gaps().len} gap(s), all dcFabricated " &
       &"at maxLoopUnwind = {r.bounds.maxLoopUnwind}"
  # Pull the lever the gap named.
  const deeper = SymexSettings(budget: ResourceBudget(maxLoopUnwind: 12))
  let r2 = symexFind(loopEight, tLabel("hit-8"), deeper)
  doAssert r2.status == sxSat and r2.trusted
  # Paths longer than 12 iterations still hit the new bound, so gaps()
  # still lists them -- they just no longer decide the verdict.
  echo &"loopEight at maxLoopUnwind = 12: sxSat, witness x = {r2.witness[0]}"

# ---- Case C: downgrade UNKNOWN via assertCoveredBy settings ---------------

block acceptUnknown:
  # The resource caps moved onto a `budget` sub-object at CR-9(b) and this
  # file was never updated, so it stopped compiling with nobody noticing --
  # `examples/` is built by neither CI nor `nimble test` (RFC-0010 C3b).
  #
  # Note what does NOT need saying any more: `integerSemantics`,
  # `maxCallDepth` and `maxLoopUnwind` were all being set to their own
  # defaults. Since RFC-0010 an unlisted field carries its default, so a
  # partial literal states only what it is actually changing -- here, a step
  # bound and a frontier cap, plus the downgrade this block is about.
  const lax = SymexSettings(
    budget: ResourceBudget(queryRLimit: 5000, maxFrontierSize: 256),
    acceptUnknownAsCovered: true)
  proc noop(x: int) = discard
  # Without the flag this would raise; with `acceptUnknownAsCovered`,
  # we treat UNKNOWN as "best-effort attempted" and pass.
  assertCoveredBy(loopDeep, tLabel("hit-100"), noop, lax)
  echo "assertCoveredBy: UNKNOWN downgraded to pass via settings — good."
