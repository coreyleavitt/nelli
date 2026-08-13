## Cluster H Step C (ADR-0022, the atomic H1) — flagship heap-identity tests.
##
## These are the TRACER-BULLET tests that drove Step C: the concrete new
## capability the classifyType flip (`dsl_typebridge.nim`) + real heap
## construction (`dsl_parser.nim`'s P2b `nnkObjConstr` arm) + universal
## `isNew` zero-write (`runtime_heap.nim`) together unlock. Every test below
## was RE-VERIFIED RED against HEAD `ddc9196` (Step B, before Step C landed):
##   * the aliasing/identity/sym-indirection tests all returned `sxUnknown`
##     (the bare named-ref symbol was value-modelled — `classifyType`
##     unwrapped it to `itTuple`, so `q = p; q.val = 99; p.val == 99` had no
##     shared address to observe the write through, and `p == q`/`p == nil`
##     degraded rather than resolving);
##   * the zero-field `Token` case did not even COMPILE — `classifyType`'s
##     ref-wrap arm (and its shared `classifyObjectRecordFields` helper)
##     unconditionally called `recList.expectKind nnkRecList`, which crashes
##     on a genuinely zero-field object body (`nnkEmpty`, not an empty
##     `nnkRecList`) — a latent pre-existing gap this slice also closes.
## GREEN under Step C: every test below now yields a REAL, sound verdict.
import std/[unittest, strutils]
import nelli/symex

# ---------------------------------------------------------------------------
# Aliasing: q = p; q.val = 99; assert p.val == 99 — the core new capability.
# A write through one alias (`q`) of a bare named-ref PARAMETER is now
# visible through the other (`p`) — true heap identity, not two independent
# value copies. Previously `sxUnknown` (ADR-0021's value-model had no shared
# address to observe the write through).
# ---------------------------------------------------------------------------
type
  Node = ref object
    val: int
    next: Node

proc aliasWriteHit(p: Node) =
  if p != nil:
    let q = p
    q.val = 99
    if p.val == 99:
      symexTarget("alias_write_hit")

proc aliasWriteUnsat(p: Node) =
  ## UNSAT-soundness companion: `p.val` CANNOT be anything other than 99
  ## after the alias write — proves this is REAL identity (a shared Z3
  ## address), not a free/unconstrained value that merely happens to permit
  ## 99 as one possibility among many.
  if p != nil:
    let q = p
    q.val = 99
    if p.val != 99:
      symexTarget("alias_write_unsat")

# ---------------------------------------------------------------------------
# Identity: `p == q` reasoning over two independent bare-ref PARAMETERS.
# Two ORDINARY (unconstrained) ref params can be modelled as equal in one
# solution and as distinct in another — a real, non-degraded Z3 verdict on
# reference identity, in both directions.
# ---------------------------------------------------------------------------
proc identityEqReachable(p, q: Node) =
  if p == q:
    symexTarget("identity_eq_hit")

proc identityNeqReachable(p, q: Node) =
  if p != q:
    symexTarget("identity_neq_hit")

# Identity composes with aliasing: if p == q (forced), a write through p is
# observed through q — the SAME address, not a coincidence.
proc identityImpliesSharedWrite(p, q: Node) =
  if p != nil and p == q:
    p.val = 7
    if q.val == 7:
      symexTarget("identity_shared_write_hit")

# ---------------------------------------------------------------------------
# Nil / sym-indirection: `type NodeRef = ref Obj; p: NodeRef; p == nil` +
# a field-write. Obj is a genuinely SEPARATE, non-ref-aliased object name
# (unlike the direct `type Node = ref object` case above); Step C's
# `classifyType` sym-indirection branch must route `NodeRef` to `itRef(full
# pointee of Obj)` too, keyed on Obj's OWN nominal id.
# ---------------------------------------------------------------------------
type
  Obj = object
    val: int
  NodeRef = ref Obj

proc symIndirectNilReachable(p: NodeRef) =
  if p == nil:
    symexTarget("sym_indirect_nil_hit")

proc symIndirectNonNilFieldWrite(p: NodeRef, x: int) =
  if p != nil:
    p.val = x
    if p.val == x:
      symexTarget("sym_indirect_write_hit")

# ---------------------------------------------------------------------------
# Zero-field witness provenance: `type Token = ref object` (no fields at
# all) — a proven-non-nil `t: Token` must render as a genuinely non-nil
# witness, NOT `nil`. The `fields.len == 0` heuristic this replaces
# (`isRecursionPlaceholder` / `IRType.isPlaceholder`) could not distinguish
# a legitimately empty top-level object from a recursion-truncated
# placeholder — both have zero fields — so it would have mis-rendered this
# case as `nil` even though the model proves `t != nil`.
# ---------------------------------------------------------------------------
type Token = ref object

proc tokenProvenNonNil(t: Token) =
  if t != nil:
    symexTarget("token_nonnil_hit")

suite "symex Cluster H Step C — flagship heap-identity tests (ADR-0022)":

  test "aliasing: q = p; q.val = 99; p.val == 99 is REAL sxSat (was sxUnknown)":
    let r = symexFind(aliasWriteHit, tLabel("alias_write_hit"))
    check r.status == sxSat

  test "aliasing UNSAT soundness: p.val != 99 after the alias write is impossible":
    let r = symexFind(aliasWriteUnsat, tLabel("alias_write_unsat"))
    check r.status == sxUnsat

  test "identity: p == q is reachable (real verdict, was sxUnknown)":
    let r = symexFind(identityEqReachable, tLabel("identity_eq_hit"))
    check r.status == sxSat

  test "identity: p != q is ALSO reachable (two independent params can differ)":
    let r = symexFind(identityNeqReachable, tLabel("identity_neq_hit"))
    check r.status == sxSat

  test "identity composes with aliasing: p == q forces a shared write to be observed":
    let r = symexFind(identityImpliesSharedWrite,
                       tLabel("identity_shared_write_hit"))
    check r.status == sxSat

  test "sym-indirection nil: `type NodeRef = ref Obj`; p == nil is reachable (real verdict)":
    let r = symexFind(symIndirectNilReachable, tLabel("sym_indirect_nil_hit"))
    check r.status == sxSat

  test "sym-indirection field-write: p.val = x; p.val == x round-trips through the heap":
    let r = symexFind(symIndirectNonNilFieldWrite,
                       tLabel("sym_indirect_write_hit"))
    check r.status == sxSat

  test "zero-field witness provenance: proven non-nil `t: Token` renders NON-nil (not the old fields.len==0 mis-render)":
    let r = symexFind(tokenProvenNonNil, tLabel("token_nonnil_hit"))
    check r.status == sxSat
    check not r.witness[0].isNil

  test "walker version floor >= 56 (Cluster H Step C introduced at 56)":
    check parseInt(symexWalkerVersion) >= 56

  test "renderAsChoicesVersion floor >= 6 (Step C bumps for the new svRef-param witness shape)":
    check parseInt(renderAsChoicesVersion) >= 6
