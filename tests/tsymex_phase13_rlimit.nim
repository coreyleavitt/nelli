## Phase 13 cycle 1 — `queryRLimit` actually bounds Z3.
##
## Pre-RFC, `SymexSettings.queryTimeoutMs` was a phantom field:
## present in the cache key but never applied to the solver. This
## test pins the new contract: `queryRLimit` is wired to Z3's
## `rlimit` parameter so that solving a non-trivial BV[64] formula
## with a tiny rlimit budget produces `sxUnknown` (the solver
## exhausted its step quota before deciding).
import std/unittest
import proptest/symex
import proptest/smt/types

# Tight rlimit budget that exhausts well before Z3 can decide the
# four-variable multiplicative formula below.
const tightSettings = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 1'u,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5))

# SUT at module scope so the macro can resolve via getImpl.
proc multConstraint(a, b, c, d: int) =
  if a * b * c * d == 1234567:
    symexTarget("rare")

suite "symex Phase 13 cycle 1 — queryRLimit wires Z3 rlimit":
  test "tiny rlimit forces sxUnknown on a non-trivial BV formula":
    # Four-variable multiplicative constraint over int64 BVs is
    # well within Z3's reach at default settings but burns far more
    # than 100 rlimit steps internally; with the bound, Z3 returns
    # Z3_L_UNDEF → sxUnknown.
    let r = symexFind(multConstraint, tLabel("rare"), tightSettings)
    check r.status == sxUnknown
