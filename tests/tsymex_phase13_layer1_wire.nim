## Phase 13 cycle 7 — Layer 1 wire: symexFindAllWitnesses consults
## the verdict cache on witness-cache miss.
##
## The test pattern is a **deliberate wrong-verdict pre-seed**
## (poisoned-cache style): for a SUT whose only target is
## TRIVIALLY SAT, we pre-seed the verdict cache with `sfUnsat`.
## A cold `runSymex` call would return `sxSat` (Z3 finds `x = 1`
## in a single trivial query). If the cache is consulted first
## and trusted, the macro returns `sfUnsat` instead — proving:
##   (a) the verdict cache was checked,
##   (b) on hit, `runSymex` was NOT invoked (cycle-1 counter
##       confirms `symexZ3CallCount == 0`),
##   (c) `fromCache = true` flags the loaded-vs-derived
##       provenance, and
##   (d) `recordSymexFinding` runs on the verdict-hit path so the
##       finding flows into `consumeSymexFindings()`.
##
## This pattern is *not* asserting correctness of UNSAT for `x ==
## 1` — Z3 would say SAT. It's asserting that the cache returns
## whatever was stored, which is the contract we're testing.
import std/[unittest, options]
import proptest/symex
import proptest/db
import proptest/choice
import proptest/int128
import proptest/engine/types

# Trivially-SAT SUT: Z3 finds `x = 1` in a handful of operations.
proc handle(x: int) =
  if x == 1:
    symexTarget("one")

suite "symex Phase 13 cycle 7 — Layer 1 verdict-cache wire":
  test "verdict cache hit returns sfUnsat, fromCache=true, Z3 not called":
    discard consumeSymexFindings()  # clear sink from prior tests
    let db = inMemoryDatabase()

    # Pre-seed the verdict cache directly: derive the
    # content-addressed key via cycle-2's helper, append the
    # `:unsat` suffix, write the sentinel `@[]` with the cycle-3
    # `verdictCacheMaxEntries` invariant.
    let bareKey = symexCacheKeyForFn(handle, tLabel("one"))
    db.save(bareKey & cacheKeyUnsat, @[], verdictCacheMaxEntries)

    symexZ3CallCount = 0
    let findings = symexFindAllWitnesses(handle, db)

    # Exactly one auto-discovered target (`tLabel("one")`).
    check findings.len == 1
    let f = findings[0]
    check f.targetDesc == "label(\"one\")"
    check f.status == sfUnsat
    check f.fromCache == true
    # Z3 was NOT called — cache served the load.
    check symexZ3CallCount == 0
    # The finding flowed through `recordSymexFinding` and is
    # available to drain via the sink (Layer 3 / `symexForAll`
    # picks it up that way).
    let drained = consumeSymexFindings()
    check drained.len == 1
    check drained[0].status == sfUnsat
    check drained[0].fromCache == true

# Cold-path SUT: target is provably unreachable (`x != x` is false
# for all int). Z3 returns UNSAT after a small handful of operations.
proc fnGhost(x: int) =
  if x != x:
    symexTarget("ghost")

suite "symex Phase 13 cycle 8 — cold path saves UNSAT verdict":
  test "first call: cold UNSAT (Z3 invoked); second call: warm (cache served)":
    let db = inMemoryDatabase()

    # Cold call — verdict cache empty; Z3 derives UNSAT; result
    # saved to the `:unsat` slot via the cycle-7 wire.
    discard consumeSymexFindings()
    symexZ3CallCount = 0
    let cold = symexFindAllWitnesses(fnGhost, db)
    check cold.len == 1
    check cold[0].status == sfUnsat
    check cold[0].fromCache == false
    check symexZ3CallCount == 1

    # Warm call — verdict cache hits; Z3 not invoked.
    discard consumeSymexFindings()
    symexZ3CallCount = 0
    let warm = symexFindAllWitnesses(fnGhost, db)
    check warm.len == 1
    check warm[0].status == sfUnsat
    check warm[0].fromCache == true
    check symexZ3CallCount == 0

# Walker-decided UNKNOWN: loop-unwind exhaustion. The `while` body
# unrolls at most `maxLoopUnwind` iterations; if the target is
# only reachable past that bound, surviving paths get
# `uncertain: true` and the walker sets `sawUnknown`, producing
# sxUnknown deterministically regardless of `queryRLimit`.
proc fnDeep(x: int) =
  var i = 0
  while i < x:
    i = i + 1
  if i == 100:
    symexTarget("deep")

const tightUnwind = SymexSettings(
  integerSemantics: isOptimised, queryRLimit: 0'u,
  maxFrontierSize: 0, maxCallDepth: 3, maxLoopUnwind: 2)

suite "symex Phase 13 cycle 9 — cold path saves UNKNOWN verdict":
  test "first call: cold UNKNOWN (walker-decided); second call: warm hit":
    let db = inMemoryDatabase()

    # Cold call. Deterministic UNKNOWN via loop-unwind exhaustion.
    # The walker MAY invoke Z3 on the in-arm path conditions even
    # before deciding UNKNOWN — we don't assert call count on the
    # cold call; `fromCache = false` is the discriminator.
    discard consumeSymexFindings()
    symexZ3CallCount = 0
    let cold = symexFindAllWitnesses(fnDeep, db, tightUnwind)
    check cold.len == 1
    check cold[0].status == sfUnknown
    check cold[0].fromCache == false

    # Warm call. Verdict cache hits; Z3 absolutely not invoked.
    discard consumeSymexFindings()
    symexZ3CallCount = 0
    let warm = symexFindAllWitnesses(fnDeep, db, tightUnwind)
    check warm.len == 1
    check warm[0].status == sfUnknown
    check warm[0].fromCache == true
    check symexZ3CallCount == 0
