## Cluster H, H_containers (ADR-0022) — containers OF named ref-objects.
##
## Step C (atomic H1, commit `40ed16f`) flipped a bare named `ref object`
## alias to heap identity (`classifyType` -> `itRef`). H_containers makes
## CONTAINERS of such refs constructible/accessible with a REAL verdict:
##
##   * `seq[Node]`   — literal construction (`@[a, b]`) + element access.
##     `storeSeqElem` (runtime.nim) had no `itRef`/`itPtr` arm (it raised
##     `ValueError: storeSeqElem: unsupported elem kind itRef` for any
##     `seq[Node]` LITERAL) — the erased seq-data-array STORE side never
##     got an itRef case even though the ALLOCATION side
##     (`allocateSeqDataRaw`) already had one (built for Phase 15 R3's
##     `seq[ref T]` INLINE-ref support). Per-element witness fidelity for
##     `seq[Node]` stays LENGTH-ONLY (`extractSeqElements`'s itRef arm is a
##     pre-existing R3 stub, deferred to a later R11b/R12-style witness
##     slice, H_witness) — this slice only asserts the VERDICT, never a
##     per-element rendered value.
##   * `array[N, Node]` — construction (`[a, b]`) was ALREADY reachable
##     (`svArray.arrElems` is a plain `seq[SymVal]`, no Z3Array store to
##     gap), but INDEXING a >1-element array always routes through
##     `iteSV`'s per-position merge chain (`isIndex`'s static-array arm,
##     even for a compile-time-literal index) — and `iteSV` had NO
##     `svRef`/`svPtr` arm (it raised `ValueError: iteSV: svRef/svPtr merge
##     lands with Cluster R R5/R7`). H_containers adds that arm: a plain
##     per-position `Z3_mk_ite` over the two `Ref_T` addresses (the same
##     shape as the existing `svBV*`/`svInt` arms just above it) — sound,
##     since every element of a homogeneous `array[N, Node]` shares the
##     same `Ref_T` sort.
##   * `tuple[a: Node]` — ALREADY fully real, no code change: `svTuple.
##     fields` is a plain `seq[SymVal]` built by `lowerTupleLit`'s
##     per-field `lower` recursion (kind-agnostic), and field ACCESS never
##     touches `iteSV` (no merge on a straight-line field read).
##   * `Table[K, Node]` / `HashSet[Node]` — STAY degraded (`sxUnknown`),
##     confirmed-out-of-scope per the ADR: `allocateSym` hard-restricts
##     table keys to `string` / values to `int` and set elements to
##     `int64`, orthogonal to Node's ref-ness. Guard tests below lock in
##     the sound degrade (no crash, no false verdict).
##
## Bumps `symexWalkerVersion` 56->57 (verdict-surface change: seq[Node]
## literal construction + array[N, Node] indexing move from a raised
## native exception to a real `sxSat`/`sxUnsat`). `renderAsChoicesVersion`
## STAYS "6" — no new rendered WITNESS SHAPE lands in this slice (the
## `seq[Node]` per-element witness is the pre-existing R3 length-only stub,
## unchanged; `array`/`tuple` of a ref were already witness-renderable
## structurally, this slice only changes what verdicts are REACHABLE, not
## what shape a witness takes).
import std/[unittest, strutils]
import nelli/symex

type
  Node = ref object
    val: int
    next: Node

# ---------------------------------------------------------------------------
# seq[Node] — literal construction + element access.
# ---------------------------------------------------------------------------

proc seqNodeReadHit(a, b: Node) =
  ## a.val is written to 5 BEFORE the seq literal is built; s[0] holds the
  ## SAME Ref_T address as `a` (storeSeqElem now stores the ref ast, not a
  ## degrade), so reading THROUGH the seq observes the earlier write — a
  ## real aliasing verdict, not a free/unconstrained value.
  if a != nil and b != nil:
    a.val = 5
    let s = @[a, b]
    if s[0].val == 5:
      symexTarget("seq_node_read_hit")

proc seqNodeReadUnsat(a, b: Node; x: range[0 .. 1000]) =
  ## Load-bearing UNSAT companion: s[0].val is ALWAYS x+1 by construction
  ## (range-bounded so x+1 never overflows) — s[0].val == x is impossible.
  ## Proves this is REAL modeling (a dummy/free ref could satisfy this),
  ## not a degrade.
  if a != nil and b != nil:
    a.val = x + 1
    let s = @[a, b]
    if s[0].val == x:
      symexTarget("seq_node_read_unsat")

proc seqNodeWriteThroughAliasHit(a, b: Node) =
  ## Aliasing case: `p = s[0]` binds the SAME ref address as `a`; a write
  ## through `p` is visible through `a` — true heap identity carried
  ## through a container element, not a value copy.
  if a != nil and b != nil:
    let s = @[a, b]
    let p = s[0]
    p.val = 7
    if a.val == 7:
      symexTarget("seq_node_alias_hit")

# ---------------------------------------------------------------------------
# array[N, Node] — construction + indexed access.
# ---------------------------------------------------------------------------

proc arrNodeReadHit(a, b: Node) =
  if a != nil and b != nil:
    a.val = 5
    let arr = [a, b]
    if arr[0].val == 5:
      symexTarget("arr_node_read_hit")

proc arrNodeReadUnsat(a, b: Node; x: range[0 .. 1000]) =
  if a != nil and b != nil:
    a.val = x + 1
    let arr = [a, b]
    if arr[0].val == x:
      symexTarget("arr_node_read_unsat")

proc arrNodeSecondElemHit(a, b: Node) =
  ## Exercises the OTHER array slot (`arr[1]`) through the same ite-merge
  ## chain — proves the merge picks the correct branch, not just the first.
  if a != nil and b != nil:
    b.val = 9
    let arr = [a, b]
    if arr[1].val == 9:
      symexTarget("arr_node_second_hit")

# ---------------------------------------------------------------------------
# tuple[a: Node] — construction + field access.
# ---------------------------------------------------------------------------

proc tupleNodeReadHit(a: Node) =
  if a != nil:
    a.val = 11
    let t = (n: a)
    if t.n.val == 11:
      symexTarget("tuple_node_read_hit")

proc tupleNodeReadUnsat(a: Node; x: range[0 .. 1000]) =
  if a != nil:
    a.val = x + 1
    let t = (n: a)
    if t.n.val == x:
      symexTarget("tuple_node_read_unsat")

# ---------------------------------------------------------------------------
# OUT-OF-SCOPE guards: Table[K, Node] / HashSet[Node] stay degraded.
# `allocateSym`'s itTable/itSet arms hard-restrict value/elem kinds
# (string keys/int values; int64 elements) — orthogonal to Node's
# ref-ness. These MUST stay a sound classified `sxUnknown`: no crash, no
# false `sxSat`.
# ---------------------------------------------------------------------------

import std/[tables, sets]

proc tableNodeGuard(t: Table[string, Node]) =
  if t.len > 0:
    symexTarget("table_node_guard_hit")

proc setNodeGuard(s: HashSet[Node]) =
  if s.len > 0:
    symexTarget("set_node_guard_hit")

suite "Cluster H H_containers — seq/array/tuple of named ref-objects":

  test "seq[Node]: read through s[0] after a.val write is REAL sxSat (was raised)":
    let r = symexFind(seqNodeReadHit, tLabel("seq_node_read_hit"))
    check r.status == sxSat

  test "seq[Node] UNSAT soundness: s[0].val == x is impossible after a.val := x+1":
    let r = symexFind(seqNodeReadUnsat, tLabel("seq_node_read_unsat"))
    check r.status == sxUnsat

  test "seq[Node] aliasing: write through s[0] alias is visible through the original param":
    let r = symexFind(seqNodeWriteThroughAliasHit, tLabel("seq_node_alias_hit"))
    check r.status == sxSat

  test "array[N, Node]: read through arr[0] after a.val write is REAL sxSat (was raised)":
    let r = symexFind(arrNodeReadHit, tLabel("arr_node_read_hit"))
    check r.status == sxSat

  test "array[N, Node] UNSAT soundness: arr[0].val == x is impossible after a.val := x+1":
    let r = symexFind(arrNodeReadUnsat, tLabel("arr_node_read_unsat"))
    check r.status == sxUnsat

  test "array[N, Node]: second slot arr[1] resolves through the same merge chain":
    let r = symexFind(arrNodeSecondElemHit, tLabel("arr_node_second_hit"))
    check r.status == sxSat

  test "tuple[a: Node]: field read t.n.val after a.val write is REAL sxSat":
    let r = symexFind(tupleNodeReadHit, tLabel("tuple_node_read_hit"))
    check r.status == sxSat

  test "tuple[a: Node] UNSAT soundness: t.n.val == x is impossible after a.val := x+1":
    let r = symexFind(tupleNodeReadUnsat, tLabel("tuple_node_read_unsat"))
    check r.status == sxUnsat

  test "Table[string, Node] STAYS degraded: sxUnknown, no crash, no false verdict":
    let r = symexFind(tableNodeGuard, tLabel("table_node_guard_hit"))
    check r.status == sxUnknown

  test "HashSet[Node] STAYS degraded: sxUnknown, no crash, no false verdict":
    let r = symexFind(setNodeGuard, tLabel("set_node_guard_hit"))
    check r.status == sxUnknown

  test "walker version floor >= 57 (H_containers introduced at 57)":
    check parseInt(symexWalkerVersion) >= 57

  test "renderAsChoicesVersion floor >= 6 (H_containers introduces no new witness shape)":
    check parseInt(renderAsChoicesVersion) >= 6
