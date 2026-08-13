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
##
## Cluster H Step C (ADR-0022) RE-DERIVATION (not a relabel): before Step C, a
## bare `n: Node` PARAMETER was VALUE-MODELLED (svTuple, not svRef) — `n.next`
## (the FIRST field hop off the bare param) cost ZERO heap derefs (plain
## tuple-field access); only the SECOND-and-deeper hops (`(n.next).next`, …)
## touched the real field-split heap. Step C flips a bare named-ref parameter
## to `itRef` (real heap identity), so `n` ITSELF is now a genuine (possibly
## nil) `Ref_Node` address and `n.next` is ALSO a real heap deref — heap-depth
## counting now starts ONE LEVEL EARLIER, and (new) `n` can genuinely be nil
## (`n != nil` must be checked explicitly — a bare dereference of a possibly-
## nil `n` is a reachable `NilAccessDefect`, which `symexFind` now surfaces
## for these SUTs if the guard is omitted, per Phase 16 D1a's unconditional
## nil-fork). Both SUTs below gain an explicit `n != nil` guard AND cache each
## hop in a `let` (`n1`, `n2`, …) so a deeper guard does NOT re-walk the whole
## prefix chain from `n` on every nesting level — this is also simply more
## realistic Nim (no reason to redundantly re-dereference `n.next.next` three
## separate times when one `let` suffices), and it keeps the heap-depth
## ARITHMETIC identical in shape to the original pre-Step-C DoD numbers
## (empirically re-verified below): `maxHeapDepth=3` still exhausts,
## `maxHeapDepth=8` (default) still comfortably fits, `maxHeapDepth=0` still
## falls back to `maxCallDepth`/256 without spuriously halting a shallow SUT.
import std/unittest
import nelli/symex

type
  Node = ref object
    val: int
    next: Node

# --- The recursive walk SUT ---------------------------------------------------
# Depth accounting with `let`-cached hops (maxHeapDepth=3):
#   `n != nil`             → nil-compare only, no heap deref (depth=0)
#   `let n1 = n.next`      → 1 deref through `n` (depth=1)
#   `n1 != nil`            → no deref (depth=1)
#   `let n2 = n1.next`     → 1 deref through `n1` (depth=2)
#   `n2 != nil`            → no deref (depth=2)
#   `let n3 = n2.next`     → 1 deref through `n2` — INCREMENTS TO depth=3,
#     `path.heapDepth >= 3` → heDepthExhausted → sxUnknown (limit hit BEFORE
#     `n3 != nil`/`n3.val` are ever reached).
#
# With maxHeapDepth=8 (default) all four derefs (n1, n2, n3, n3.val) fit
# comfortably (depth=4 < 8) → sxSat.
proc walk4(n: Node) =
  if n != nil:
    let n1 = n.next
    if n1 != nil:
      let n2 = n1.next
      if n2 != nil:
        let n3 = n2.next
        if n3 != nil:
          if n3.val == 5:
            symexTarget("deep")

# --- A shallow SUT for the maxHeapDepth=0 fallback ----------------------------
# `n != nil` guards the whole-`n` deref (no cost); `let n1 = n.next` is 1 heap
# deref (depth=1); `n1.val` is a 2nd deref (depth=2). Under maxHeapDepth=0 the
# effective limit resolves to maxCallDepth (default 3, `>0`) or 256 — 2 is
# comfortably under either — so NOT halted.
proc shallow(n: Node) =
  if n != nil:
    let n1 = n.next
    if n1 != nil:
      if n1.val == 7:
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
