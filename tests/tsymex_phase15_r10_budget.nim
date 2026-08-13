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
##   1. A SUT with exactly 2 real heap derefs (`node.next`, then `.val` off
##      the result):
##        maxHeapDepth = 3 → sxSat.
##        maxHeapDepth = 2 → sxUnknown with heDepthExhausted.
##        maxHeapDepth = 0 → sxSat (unlimited).
##   2. The serialised cache key string DIFFERS between a maxHeapDepth=1 and a
##      maxHeapDepth=2 query (so a depth-1 result is not served for depth-2).
##   3. The observable: a depth-2 query (sxUnknown) then a depth-3 query yields
##      sxSat — the cached depth-2 unknown is NOT served for the depth-3 query.
##
## R10 is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
##
## Cluster H Step C (ADR-0022) RE-DERIVATION (not a relabel): pre-Step-C, a
## bare `node: Node` param was VALUE-MODELLED — `node.next` was a 0-cost tuple
## access, so only ONE real heap deref (the `.val` read off `node.next`'s
## svRef value) happened, and the DoD's "2 levels of deref" comment described
## the RFC's aspirational heap-resident model, not literally what walked pre-
## Step-C. Step C flips `node` itself to `itRef` (real heap identity) — so
## `node.next` is now ALSO a genuine heap deref (2 real derefs total: `node`→
## `.next`, then `.next`→`.val`), `node` can genuinely be nil (needs an
## explicit `!= nil` guard, else `symexFind` surfaces a reachable
## `NilAccessDefect` instead of exploring further — Phase 16 D1a's
## unconditional nil-fork), and — EMPIRICALLY RE-VERIFIED — the
## `heapDepthExhausted` check (`inc` THEN `>= limit`) means an N-real-deref
## walk needs `maxHeapDepth > N` (i.e. `>= N+1`) to survive, not `>= N`: a
## 2-deref walk needs budget 3 to succeed, exhausts at budget 2. The `let`
## caching below avoids a THIRD, redundant re-deref of `node.next` (Nim would
## never actually re-fetch a value it can bind once), keeping the deref count
## at exactly 2 — the cleanest re-derivation of the original "2 levels" intent.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

type
  Node = ref object
    val: int
    next: Node

# --- The 2-real-deref SUT ------------------------------------------------------
# `node != nil` guards the whole-`node` deref (no cost, plain nil-compare).
# `let n1 = node.next` is the FIRST real heap deref (through `node`). `n1.val`
# is the SECOND real heap deref (through `n1`). Two total — matches the
# original "2 levels of deref" DoD intent, now genuinely both heap-backed.
proc reach2(node: Node) =
  if node != nil:
    let n1 = node.next
    if n1 != nil:
      if n1.val == 5:
        symexTarget("two")

const depth3 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 3

const depth2 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 2

const depth0 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 0

suite "symex Phase 15 R10 — maxHeapDepth cache-key participation":

  test "R10: same SUT reaches sxSat at depth 3 and sxUnknown at depth 2":
    # Depth 3: the 2-real-deref walk is within budget (needs > 2) → sxSat.
    let rSat = symexFind(reach2, tLabel("two"), depth3)
    check rSat.status == sxSat

    # Depth 2: the second deref exhausts the budget (2 >= 2) → sxUnknown with
    # a classified heDepthExhausted error.
    let rUnk = symexFind(reach2, tLabel("two"), depth2)
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

  test "R10: depth-2 cached unknown is NOT served for a depth-3 query":
    # The observable of cache-key participation: run the depth-2 query (which
    # is sxUnknown), then the depth-3 query — the latter must be sxSat, NOT the
    # cached depth-2 unknown. Distinct keys → distinct cache slots.
    let rUnk = symexFind(reach2, tLabel("two"), depth2)
    check rUnk.status == sxUnknown
    let rSat = symexFind(reach2, tLabel("two"), depth3)
    check rSat.status == sxSat
