## Phase 14 cycle C3 — `maxFrontierSize` enforcement (ADR-0004).
##
## Before C3, `SymexSettings.maxFrontierSize` participated in the
## canonical cache key (canonicalize.nim:390) but was BEHAVIORALLY
## INERT — the walker never consulted it. C3 wires `walkBlock` to
## prune the post-step frontier when `paths.len > maxFrontierSize`
## (highest-uncertainty paths dropped first), and to set
## `w.sawUnknown = true` so the final result is `sxUnknown` (NOT
## `sxUnsat`). `maxFrontierSize = 0` keeps the prior behaviour:
## unlimited frontier, no prune.
##
## Test shape: a SUT whose branching produces N>>1 paths after a
## few `if` levels. With `maxFrontierSize = 1`, the walker is
## forced to prune most of the frontier and the verdict must come
## back `sxUnknown`. With `maxFrontierSize = 0` (default) the SUT
## solves normally — `sxSat` on a reachable label.
import std/unittest
import proptest/symex
import proptest/smt/types

proc multiBranchReachable(x: int) =
  # 4 nested ifs ⇒ frontier grows from 1 → up to 16 paths.
  if x mod 2 == 0:
    if x mod 3 == 0:
      if x mod 5 == 0:
        if x mod 7 == 0:
          symexTarget("deep-hit")

proc multiBranchUnreachable(x: int) =
  # Same shape but the label is UNSAT: the conjunction `x == 1 AND
  # x == 2` cannot hold. Under unbounded frontier the walker
  # exhausts all paths and returns `sxUnsat`. Under a tight prune
  # the surviving paths can't establish UNSAT-on-all-paths, so the
  # verdict must downgrade to `sxUnknown`.
  if x mod 2 == 0:
    if x mod 3 == 0:
      if x mod 5 == 0:
        if x == 1 and x == 2:
          symexTarget("never")

suite "symex Phase 14 cycle C3 — frontier pruning":
  test "default settings (maxFrontierSize=0): unlimited frontier reaches deep target":
    let r = symexFind(multiBranchReachable, tLabel("deep-hit"))
    check r.status == sxSat

  test "tight maxFrontierSize=1 on UNSAT target: walker prunes + sxUnknown":
    const tightSettings = block:
      var s = defaultSymexSettings()
      s.maxFrontierSize = 1
      s
    let r = symexFind(multiBranchUnreachable, tLabel("never"), tightSettings)
    check r.status == sxUnknown

  test "unlimited frontier on UNSAT target: sxUnsat (control)":
    let r = symexFind(multiBranchUnreachable, tLabel("never"))
    check r.status == sxUnsat
