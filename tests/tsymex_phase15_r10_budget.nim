## Phase 15 — Cluster R (FINAL cluster), cycle R10: `maxHeapDepth` cache-key
## participation + determinism.
##
## R9 wired the per-path heap-depth budget (`heapDepthExhausted`). R10 confirms
## the `maxHeapDepth` SETTING is fully part of the content-addressed cache key —
## so a solve under `maxHeapDepth = 1` does NOT serve a cache lookup under
## `maxHeapDepth = 2` — and documents the monotone exhaustion property in
## `determinism.md` (a SUT that is `sxSat` at heap depth N is `sxSat` at any
## M > N; the UNSAT-monotonicity analogue for heap depth).
##
## `maxHeapDepth = 0` means UNLIMITED (consistent with the `maxFrontierSize = 0`
## convention); it serialises in the cache key as `"heapDepth=unlimited"` for
## human-readability.
##
## DoD (RFC §R10):
##   1. A SUT with exactly 2 levels of deref (`node.next.val`):
##        maxHeapDepth = 2 → sxSat.
##        maxHeapDepth = 1 → sxUnknown with heDepthExhausted.
##        maxHeapDepth = 0 → sxSat (unlimited).
##   2. The serialised cache key string DIFFERS between a maxHeapDepth=1 and a
##      maxHeapDepth=2 query (so a depth-1 result is not served for depth-2).
##   3. The observable: a depth-1 query (sxUnknown) then a depth-2 query yields
##      sxSat — the cached depth-1 unknown is NOT served for the depth-2 query.
##
## R10 is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize
import proptest/smt/types

type
  Node = ref object
    val: int
    next: Node

# --- The 2-deref SUT ----------------------------------------------------------
# `node.next.val` performs exactly two levels of deref: `node[]` to read `.next`,
# then `.next[]` to read `.val`. Under maxHeapDepth = 2 the walk is within
# budget; under maxHeapDepth = 1 the second deref exhausts the budget.
proc reach2(node: Node) =
  if node.next != nil:
    if node.next.val == 5:
      symexTarget("two")

const depth2 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 2

const depth1 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 1

const depth0 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 0

suite "symex Phase 15 R10 — maxHeapDepth cache-key participation":

  test "R10: same SUT reaches sxSat at depth 2 and sxUnknown at depth 1":
    # Depth 2: the 2-deref walk is within budget → sxSat.
    let rSat = symexFind(reach2, tLabel("two"), depth2)
    check rSat.status == sxSat

    # Depth 1: the second deref exhausts the budget → sxUnknown with a
    # classified heDepthExhausted error.
    let rUnk = symexFind(reach2, tLabel("two"), depth1)
    check rUnk.status == sxUnknown
    var sawDepth = false
    for e in rUnk.errors:
      if e.kind == heDepthExhausted: sawDepth = true
    check sawDepth

  test "R10: maxHeapDepth=0 (unlimited) reaches sxSat":
    let r = symexFind(reach2, tLabel("two"), depth0)
    check r.status == sxSat

  test "R10: maxHeapDepth participates in the canonical settings key":
    # The cache key must distinguish depth-1 from depth-2: otherwise a cached
    # depth-1 sxUnknown would be served for a depth-2 sxSat query.
    var s1 = defaultSymexSettings(); s1.budget.maxHeapDepth = 1
    var s2 = defaultSymexSettings(); s2.budget.maxHeapDepth = 2
    check canonicalize(s1) != canonicalize(s2)

    # The full content-addressed cache key string differs too.
    let prog = SymexProgram(body: mkBlock(@[]))
    check symexCacheKey(prog, tLabel("two"), s1, "z3", "nim", "9", "2") !=
          symexCacheKey(prog, tLabel("two"), s2, "z3", "nim", "9", "2")

  test "R10: maxHeapDepth=0 serialises as heapDepth=unlimited":
    # Human-readable sentinel for the unlimited mode.
    var s0 = defaultSymexSettings(); s0.budget.maxHeapDepth = 0
    check canonicalize(s0).contains("heapDepth=unlimited")
    # A bounded budget renders the numeric value, NOT the sentinel.
    var s5 = defaultSymexSettings(); s5.budget.maxHeapDepth = 5
    check not canonicalize(s5).contains("heapDepth=unlimited")

  test "R10: depth-1 cached unknown is NOT served for a depth-2 query":
    # The observable of cache-key participation: run the depth-1 query (which
    # is sxUnknown), then the depth-2 query — the latter must be sxSat, NOT the
    # cached depth-1 unknown. Distinct keys → distinct cache slots.
    let rUnk = symexFind(reach2, tLabel("two"), depth1)
    check rUnk.status == sxUnknown
    let rSat = symexFind(reach2, tLabel("two"), depth2)
    check rSat.status == sxSat
