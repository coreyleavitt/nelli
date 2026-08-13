## examples/symex_loops.nim
##
## Bounded loops + the UNKNOWN downgrade. Phase 6 ships a *k-bounded*
## walker: each `while`/`for` is unrolled at most `maxLoopUnwind`
## times (default 5). If a path survives k iterations without
## reaching the target, it gets marked uncertain and the final
## status flips to `sxUnknown`.
##
## This is the right trade-off for an automatic tool: invariant
## inference would let us reason about unbounded loops symbolically,
## but it requires either user-supplied invariants or expensive
## inference. k-bounded model checking — used by SLAM, CBMC, Pex —
## is the practical sweet spot. We borrow it.
##
## When UNKNOWN means "the loop just needed more iterations than we
## have", you have three honest moves:
##   1. Bump `maxLoopUnwind` in `SymexSettings`.
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
  # gets marked uncertain → sxUnknown.
  let r = symexFind(loopDeep, tLabel("hit-100"))
  doAssert r.status == sxUnknown
  echo "loopDeep: status = sxUnknown (target beyond unwind budget)"

# ---- Case C: downgrade UNKNOWN via assertCoveredBy settings ---------------

block acceptUnknown:
  const lax = SymexSettings(integerSemantics: isOptimised,
                            queryRLimit: 5000, maxFrontierSize: 256,
                            maxCallDepth: 3, maxLoopUnwind: 5,
                            acceptUnknownAsCovered: true)
  proc noop(x: int) = discard
  # Without the flag this would raise; with `acceptUnknownAsCovered`,
  # we treat UNKNOWN as "best-effort attempted" and pass.
  assertCoveredBy(loopDeep, tLabel("hit-100"), noop, lax)
  echo "assertCoveredBy: UNKNOWN downgraded to pass via settings — good."
