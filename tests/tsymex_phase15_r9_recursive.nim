## Phase 15 — Cluster R (FINAL cluster), cycle R9: recursive ref structures +
## heap-depth budget.
##
## A self-referential `ref object` (a singly-linked list `Node` whose `next`
## field is itself a `Node`) lets a SUT walk `n.next.next.next…` indefinitely.
## Each `isDeref` / `isDerefWrite` increments `path.heapDepth`; when the counter
## reaches the EFFECTIVE limit the walker HALTS that path with `sxUnknown` and a
## classified `SymexErrorInfo{kind: heDepthExhausted, msg: "heap depth budget of
## N exceeded"}`. The halt is per-path — shallower paths continue.
##
## EFFECTIVE limit (Des-LOW-D1): `if maxHeapDepth > 0: maxHeapDepth elif
## maxCallDepth > 0: maxCallDepth else: 256`. The sole guard is
## `if effectiveLimit > 0 and path.heapDepth >= effectiveLimit`.
##
## The recursive `next: Node` field is a REF-TYPED field — its field-split heap
## (R6) is `Z3Array[Ref_Node, Ref_Node]` (value sort = the field's own ref sort).
## R9 confirms the R6 field-split machinery loads/stores a `Ref_T` value (the
## `liftHeapValue`/`heapValueSort` extension to ref/ptr pointees).
##
## DoD (RFC §R9):
##   1. `maxHeapDepth = 3`  → `sxUnknown` with errors containing heDepthExhausted.
##   2. `maxHeapDepth = 8` (default) → `sxSat` (the depth-4 walk is within budget).
##   3. `maxHeapDepth = 0`  → falls back to maxCallDepth / 256; a shallow SUT does
##      NOT spuriously halt.
##
## R9 is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

type
  Node = ref object
    val: int
    next: Node

# --- The recursive walk SUT ---------------------------------------------------
# Phase 16 D1a: `n: Node` is VALUE-MODELLED (svTuple, not svRef) — `n != nil`
# is unsupported. Guard the REF-TYPED FIELD derefs with `n.next != nil` etc. so
# pcImpliesNonNil SHORT-CIRCUITs the nil fork at each heap deref.
#
# Depth accounting with guards (maxHeapDepth=3):
#   guard `n.next != nil`       → tuple-field access (0 heap derefs, depth=0)
#   guard `n.next.next != nil`  → deref n.next (depth=1)
#   guard `n.next.next.next != nil` → deref n.next, n.next.next (depth=2, then
#     depth=3 → heDepthExhausted → sxUnknown)  ← limit hit inside the guard!
#
# With maxHeapDepth=8 all guards pass; body adds 3 more derefs → depth=6 < 8 → sxSat.
proc walk4(n: Node) =
  if n.next != nil:
    if n.next.next != nil:
      if n.next.next.next != nil:
        if n.next.next.next.val == 5:
          symexTarget("deep")

# --- A shallow SUT for the maxHeapDepth=0 fallback ----------------------------
# Phase 16 D1a: `n.next.val` dereferences `n.next` (1 heap deref). Guard with
# `n.next != nil` so pcImpliesNonNil fires. Under maxHeapDepth=0 the effective
# limit resolves to maxCallDepth (>0) or 256 — well above 1 — so NOT halted.
proc shallow(n: Node) =
  if n.next != nil:
    if n.next.val == 7:
      symexTarget("shallow")

const depth3 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 3

const depth8 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 8

const depth0 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 0

suite "symex Phase 15 R9 — recursive ref heap-depth budget (heDepthExhausted)":

  test "R9: linked-list SUT with unknown depth halts cleanly at budget":
    # maxHeapDepth = 3: the depth-4 walk exhausts the budget → sxUnknown with a
    # heDepthExhausted error. CRITICAL: this must HALT, not hang.
    let r = symexFind(walk4, tLabel("deep"), depth3)
    check r.status == sxUnknown
    var sawDepth = false
    for e in r.errors:
      if e.kind == heDepthExhausted: sawDepth = true
    check sawDepth

  test "R9: depth-4 walk within an 8-budget is sxSat":
    # maxHeapDepth = 8: the depth-4 walk is within budget → sxSat.
    let r = symexFind(walk4, tLabel("deep"), depth8)
    check r.status == sxSat

  test "R9: maxHeapDepth=0 falls back to maxCallDepth/256 (shallow SUT not halted)":
    # A 2-deref SUT under the unlimited (=0) sentinel resolves the effective
    # limit to maxCallDepth (>0) or 256 — far above 2 — so it does NOT halt.
    let r = symexFind(shallow, tLabel("shallow"), depth0)
    check r.status == sxSat
