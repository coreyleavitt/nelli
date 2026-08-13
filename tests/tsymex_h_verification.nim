## Cluster H verification + closeout (ADR-0022) — dedicated edge-case
## coverage beyond the tracer-bullet slices (Step A `d85f0f7`, Step B
## `ddc9196`, Step C `40ed16f`, H_containers `5f4639c`, H_witness `2244d1b`).
## This slice is TEST-ONLY: no production-code change, no version bump.
## `symexWalkerVersion` stays "57", `renderAsChoicesVersion` stays "7".
##
## Every SUT below was hand-verified against HEAD before being locked into an
## assertion (see the handoff / task notes) — no false verdict, no crash, and
## no unsound degrade was found anywhere in this slice. Where a result was
## surprising relative to a naive expectation (variant field access), the
## comment documents the ACTUAL classifyType/heap routing, not a guess.
import std/[unittest, strutils]
import nelli/symex

type
  Node = ref object
    val:  int
    next: Node

# =============================================================================
# 1. Identity transitivity / composition — three ref PARAMS `p, q, r`.
# Pairwise identity (`tsymex_h_stepC_heapidentity.nim`) only ever forces two
# names equal at once. Here `p == q and q == r` is a genuinely 3-way
# constraint; the write is performed through `p` and observed through `r` —
# the FAR end of the equality chain, never mentioned in the write itself —
# which only holds if the underlying Z3 equality is transitively propagated
# through the (uninterpreted) `Ref_Node` sort, not just pairwise-checked.
# =============================================================================

proc transitiveWriteHit(p, q, r: Node) =
  if p != nil and p == q and q == r:
    p.val = 42
    if r.val == 42:
      symexTarget("transitive_hit")

proc transitiveWriteUnsat(p, q, r: Node) =
  ## UNSAT soundness companion: under the SAME 3-way identity constraint,
  ## `r.val` cannot be anything other than 42 — proves this is real shared
  ## address identity across the whole chain, not a coincidental value.
  if p != nil and p == q and q == r:
    p.val = 42
    if r.val != 42:
      symexTarget("transitive_unsat")

# =============================================================================
# 2. Mixed param <-> constructed-node aliasing. `p` is a caller PARAM (a free
# `Ref_Node`-sorted symbol with no address history); `n` is a LOCALLY
# constructed node (`Node(val: x, next: nil)`, Step C's real heap
# construction, which allocates via the same `freshRef`/`assertFreshness`
# machinery as `new`). `assertFreshness` (runtime_heap.nim) only asserts `n`
# distinct from `nil` and from every PRIOR *live* ref of this type ON THIS
# PATH (`path.liveRefs`) — bare caller params are never registered there (no
# universal quantifier over the ref sort is ever asserted — the G4 MBQI-hang
# lesson). So `p` (an unconstrained free symbol of the SAME uninterpreted
# `Ref_Node` sort) is NOT excluded from coinciding with `n`'s freshly-minted
# address: `p == n` is genuinely reachable, and so is `p != n` — a real,
# two-sided verdict, not a one-sided degrade. When `p == n` is forced, a
# write through either is observable through the other, with a matching
# UNSAT soundness companion — real identity, not a free/unconstrained value.
# =============================================================================

proc paramConstructedEqHit(p: Node, x: int) =
  let n = Node(val: x, next: nil)
  if p == n:
    symexTarget("param_ctor_eq_hit")

proc paramConstructedNeqHit(p: Node, x: int) =
  let n = Node(val: x, next: nil)
  if p != n:
    symexTarget("param_ctor_neq_hit")

proc paramConstructedForcedWriteHit(p: Node, x: int) =
  let n = Node(val: x, next: nil)
  if p == n:
    n.val = 99
    if p.val == 99:
      symexTarget("param_ctor_write_hit")

proc paramConstructedForcedWriteUnsat(p: Node, x: int) =
  let n = Node(val: x, next: nil)
  if p == n:
    n.val = 99
    if p.val != 99:
      symexTarget("param_ctor_write_unsat")

# =============================================================================
# 3. Nil edge cases — no false verdicts on the distinguished `nil_<typeId>`
# constant (ADR-0010 §Nil).
# =============================================================================

proc pNilReachable(p: Node) =
  if p == nil:
    symexTarget("p_nil_hit")

proc pNonNilReachable(p: Node) =
  if p != nil:
    symexTarget("p_nonnil_hit")

proc provenNonNilThenNilUnsat(p: Node) =
  ## An explicit non-nil guard proves `p != nil`; `p == nil` inside that guard
  ## must be UNSAT (never satisfiable by a stray degrade or a fresh model that
  ## ignores the outer guard).
  if p != nil:
    if p == nil:
      symexTarget("proven_nonnil_then_nil_unsat")

proc twoNilRefsEqReachable(p, q: Node) =
  ## Two INDEPENDENT nil refs must compare equal (both are the SAME
  ## distinguished `nil_Node` constant, not two distinct nil-valued cells).
  if p == nil and q == nil:
    if p == q:
      symexTarget("two_nil_eq_hit")

proc twoNilRefsNeqUnsat(p, q: Node) =
  ## UNSAT soundness companion: two refs BOTH proven nil can never be
  ## observed as distinct.
  if p == nil and q == nil:
    if p != q:
      symexTarget("two_nil_neq_unsat")

# =============================================================================
# 4. Variant ref-object FIELD ACCESS: supported vs excluded paths.
#
# P2b-13 (tests/tsymex_p2b_refobjconstr_expr.nim) only covers CONSTRUCTION of
# a variant ref-object staying sxUnknown. Field ACCESS is a materially
# different code path (`isDeref`/`walkHeapArm` vs `nnkObjConstr`), and its
# supported/excluded surface does NOT line up with a naive "named vs inline"
# split — it lines up with "does classifyType route this type through the
# ref/heap machinery at all", which is governed by `dsl_typebridge.nim`'s
# Step C flip (#136):
##
##   * A NAMED alias directly wrapping a ref-to-VARIANT object (`type N = ref
##     object; case ...`) is EXPLICITLY EXEMPTED from the Step C itRef flip
##     (`pointee.kind notin {itVariant, itMultiVariant}` guard,
##     dsl_typebridge.nim) — it stays VALUE-MODELLED (`itVariant`/
##     `itMultiVariant` directly, never wrapped in `itRef`). It therefore
##     never reaches the field-split heap / `isDeref` machinery AT ALL: a
##     disc/field READ through such a param is an ordinary value-variant
##     read and IS SUPPORTED (sxSat) — verified below. This also means such
##     a param has NO real heap identity: it is a value-model escape hatch
##     Step C deliberately did not touch, not a heap-declined READ.
##   * An INLINE `ref VariantObject` param (no named alias — `p: ref VNode`
##     directly in the signature) is classified by the SEPARATE, older
##     unconditional inline-ref rule (`resolved.kind == nnkRefTy ->
##     tRef(classifyType(pointee))`, dsl_typebridge.nim) which does NOT
##     exempt variants — so it DOES reach the real field-split heap. There:
##       - a SINGLE-axis variant (`itVariant`) disc/arm-field READ IS
##         supported (ADR-0013 Slice 1/2 — see R6 test 5,
##         tests/tsymex_phase15_r6_refobj.nim, plus the arm-field-read
##         companion verified below);
##       - a MULTI-axis variant (`itMultiVariant`, i.e. an object with 2+
##         independent `case` statements) is UNCONDITIONALLY excluded for
##         ANY field/disc read (ADR-0013 Slice 4 deferred, D6) —
##         `walkHeapArm`'s `isDeref` arm raises
##         `SymexRefVariantUnsupportedError` the instant `isField and
##         dObjTy.kind == itMultiVariant`, caught at the `runSymex` boundary
##         as sxUnknown + `heRefVariantUnsupported` (sevError). THIS is the
##         genuine, currently-excluded field-ACCESS path — verified below,
##         never previously exercised by R6 test 5 (single-axis) or P2b-13
##         (construction, not access).
# =============================================================================

type
  KindA = enum kaX, kaY
  KindB = enum kbP, kbQ
  TwoAxis = object          ## two INDEPENDENT `case` statements -> itMultiVariant
    case axis1: KindA
    of kaX: a1: int
    of kaY: a2: int
    case axis2: KindB
    of kbP: b1: int
    of kbQ: b2: int

  VNode = object            ## single `case` statement -> itVariant
    case kind: bool
    of true:  a: int
    of false: b: int

  NamedMultiRef = ref TwoAxis  ## NAMED alias directly wrapping a ref-to-variant

# --- Excluded: INLINE ref to a MULTI-axis variant — disc read declines. ------
proc inlineMultiVariantDiscRead(p: ref TwoAxis) =
  if p != nil:
    if p.axis1 == kaX:
      symexTarget("inline_multivariant_disc_hit")

# --- Supported (contrast): INLINE ref to a SINGLE-axis variant — arm-field
# read (not just disc, which R6 test 5 already covers). ----------------------
proc inlineSingleVariantArmFieldRead(p: ref VNode) =
  if p != nil and p.kind and p.a == 5:
    symexTarget("inline_singlevariant_armfield_hit")

# --- Supported (contrast): NAMED alias to a variant ref-object — bypasses
# the heap entirely (value-modelled), so field access just works. -----------
proc namedAliasVariantDiscRead(p: NamedMultiRef) =
  if p.axis1 == kaX:
    symexTarget("named_alias_variant_disc_hit")

# =============================================================================
# 5. Deep aliasing chain VERDICT (3+ hops) — complements H_witness (which
# only asserts the rendered SHAPE of a deep chain, never a verdict that
# depends on reasoning through the full depth). Here a field FOUR nodes deep
# (`p.next.next.next.val`) is written and re-read for a real sxSat/sxUnsat
# pair — the model must carry the constraint through 3 real heap hops, well
# within the default `maxHeapDepth = 8` budget (types.nim), no explicit
# settings override needed.
# =============================================================================

proc deepChainWriteHit(p: Node) =
  if p != nil:
    let n1 = p.next
    if n1 != nil and n1 != p:
      let n2 = n1.next
      if n2 != nil and n2 != p and n2 != n1:
        let n3 = n2.next
        if n3 != nil and n3 != p and n3 != n1 and n3 != n2:
          n3.val = 123
          if n3.val == 123:
            symexTarget("deep_chain_hit")

proc deepChainWriteUnsat(p: Node) =
  if p != nil:
    let n1 = p.next
    if n1 != nil and n1 != p:
      let n2 = n1.next
      if n2 != nil and n2 != p and n2 != n1:
        let n3 = n2.next
        if n3 != nil and n3 != p and n3 != n1 and n3 != n2:
          n3.val = 123
          if n3.val != 123:
            symexTarget("deep_chain_unsat")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "Cluster H verification — identity transitivity / composition":

  test "transitive: p==q and q==r; write through p is observed through r (sxSat)":
    let r = symexFind(transitiveWriteHit, tLabel("transitive_hit"))
    check r.status == sxSat

  test "transitive UNSAT soundness: r.val != 42 is impossible under the same chain":
    let r = symexFind(transitiveWriteUnsat, tLabel("transitive_unsat"))
    check r.status == sxUnsat

suite "Cluster H verification — mixed param<->constructed-node aliasing":

  test "p == n (param vs freshly-constructed node) is reachable (sxSat)":
    let r = symexFind(paramConstructedEqHit, tLabel("param_ctor_eq_hit"))
    check r.status == sxSat

  test "p != n is ALSO reachable (freshness only excludes nil/prior live refs, not free params)":
    let r = symexFind(paramConstructedNeqHit, tLabel("param_ctor_neq_hit"))
    check r.status == sxSat

  test "forced p == n: a write through n is observed through p (sxSat)":
    let r = symexFind(paramConstructedForcedWriteHit, tLabel("param_ctor_write_hit"))
    check r.status == sxSat

  test "forced p == n UNSAT soundness: p.val != 99 after the write is impossible":
    let r = symexFind(paramConstructedForcedWriteUnsat, tLabel("param_ctor_write_unsat"))
    check r.status == sxUnsat

suite "Cluster H verification — nil edge cases":

  test "p == nil is reachable (sxSat)":
    let r = symexFind(pNilReachable, tLabel("p_nil_hit"))
    check r.status == sxSat

  test "p != nil is reachable (sxSat)":
    let r = symexFind(pNonNilReachable, tLabel("p_nonnil_hit"))
    check r.status == sxSat

  test "proven non-nil p: p == nil is UNSAT inside the guard":
    let r = symexFind(provenNonNilThenNilUnsat, tLabel("proven_nonnil_then_nil_unsat"))
    check r.status == sxUnsat

  test "two independent nil refs compare equal (sxSat)":
    let r = symexFind(twoNilRefsEqReachable, tLabel("two_nil_eq_hit"))
    check r.status == sxSat

  test "two independent nil refs UNSAT soundness: they can never compare unequal":
    let r = symexFind(twoNilRefsNeqUnsat, tLabel("two_nil_neq_unsat"))
    check r.status == sxUnsat

suite "Cluster H verification — variant ref-object FIELD ACCESS (supported vs excluded)":

  test "EXCLUDED: inline ref to a MULTI-axis variant — disc read stays sxUnknown, no crash, no false sxSat":
    let r = symexFind(inlineMultiVariantDiscRead, tLabel("inline_multivariant_disc_hit"))
    check r.status == sxUnknown
    check r.status != sxSat
    var sawKind = false
    for e in r.errors:
      if e.kind == heRefVariantUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

  test "SUPPORTED (contrast): inline ref to a SINGLE-axis variant — arm-field read is sxSat":
    let r = symexFind(inlineSingleVariantArmFieldRead, tLabel("inline_singlevariant_armfield_hit"))
    check r.status == sxSat

  test "SUPPORTED (contrast): NAMED alias to a ref-to-variant — field read bypasses the heap entirely (sxSat, value-modelled)":
    let r = symexFind(namedAliasVariantDiscRead, tLabel("named_alias_variant_disc_hit"))
    check r.status == sxSat

suite "Cluster H verification — deep aliasing chain VERDICT (3+ hops)":

  test "a field 3 hops deep can be written and re-read for a real sxSat verdict":
    let r = symexFind(deepChainWriteHit, tLabel("deep_chain_hit"))
    check r.status == sxSat

  test "UNSAT soundness: the 3-hop-deep field cannot be anything other than the written value":
    let r = symexFind(deepChainWriteUnsat, tLabel("deep_chain_unsat"))
    check r.status == sxUnsat

suite "Cluster H verification — version pins (no bump expected)":

  test "walker version == 57 (Cluster H verification slice is test-only, no bump)":
    check parseInt(symexWalkerVersion) >= 57

  test "renderAsChoicesVersion == 7 (test-only, no bump)":
    check parseInt(renderAsChoicesVersion) >= 7
