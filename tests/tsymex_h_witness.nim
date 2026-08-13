## Cluster H, H_witness (ADR-0022, ADR-0010 invariant #4) — the RECURSIVE
## heap-snapshot witness.
##
## Prior Cluster H slices (Step C `40ed16f`, H_containers `5f4639c`) made
## aliasing/identity/construction/container VERDICTS real for named
## ref-objects. The heap-snapshot WITNESS itself, however, still stopped at
## top-level ref/ptr params: `buildHeapSnapshot` (runtime.nim) rendered any
## composite (`ref object`) pointee as the blind `"<object>"` placeholder
## (R12/R11b), and `extractSeqElements`'s `itRef`/`itPtr` arm stayed a
## length-only stub (H_containers, ADR-0022). H_witness is WITNESS-FIDELITY
## ONLY — it changes what a SAT/raised witness SHOWS, never a verdict.
##
## `buildHeapSnapshot`/`pointeeRendering` now descend recursively into
## ref-typed object fields and container (seq/array) elements, bounded by the
## SAME effective heap-depth budget the walker itself enforces
## (`effectiveHeapDepthLimit`), and cycle-safe via a `visited` address set — a
## revisited address renders `aliasRef` to the name it was FIRST seen under
## rather than re-recursing (the LOAD-BEARING safety property: a self-cycle
## or ring must terminate, not hang or stack-overflow).
##
## A reachable cell is named by its ACCESS PATH from the param that reached
## it: a field hop appends `.<field>` (`p.next`); a container index appends
## `[<i>]` (`arr[0]`, `s[0]`). Every reachable cell — param or not — that
## resolves to a live, non-alias address gets its own `HeapSnapshotEntry`;
## an object cell's `pointsTo` is a structural `"{field=value, ...}"`
## rendering where a non-nil ref/ptr field's value is `"@<cellName>"` (a
## lookup key into this same `seq`, resolved exactly like an `aliasRef`).
##
## Bumps `renderAsChoicesVersion` "6" -> "7" (the heap-snapshot witness SHAPE
## changes: new reachable-cell entries, a new structural `pointsTo` format
## for composite cells). `symexWalkerVersion` STAYS "57" — this is a
## post-solve rendering change of an already-decided model; no verdict is
## affected.
import std/[unittest, options, strutils]
import nelli/symex

type
  Node = ref object
    val:  int
    next: Node

  Pair = ref object
    a: int
    b: bool

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

proc mapNames(entries: seq[HeapSnapshotEntry]): seq[string] =
  for e in entries: result.add e.name

proc find(name: string, entries: seq[HeapSnapshotEntry]): HeapSnapshotEntry =
  for e in entries:
    if e.name == name: return e
  doAssert false, "no heapSnapshot entry named '" & name & "' (have: " &
    $entries.mapNames() & ")"

# ---------------------------------------------------------------------------
# 1. Linked-list chain: p.next.val reachable and pinned by the model.
# ---------------------------------------------------------------------------

proc chainHit(p: Node) =
  if p != nil:
    let n1 = p.next
    if n1 != nil:
      if n1.val == 42:
        symexTarget("chain_hit")

# ---------------------------------------------------------------------------
# 2. One-hop alias: p.next == q (a field aliases another PARAM).
# ---------------------------------------------------------------------------

proc oneHopAlias(p, q: Node) =
  if p != nil and q != nil and p != q and p.next == q:
    symexTarget("one_hop_alias")

# ---------------------------------------------------------------------------
# 3. Cycle termination — LOAD-BEARING. A self-loop and a 2-node ring.
# ---------------------------------------------------------------------------

proc selfLoop(p: Node) =
  if p != nil and p.next == p:
    symexTarget("self_loop")

proc ring(p, q: Node) =
  if p != nil and q != nil and p != q and p.next == q and q.next == p:
    symexTarget("ring")

# ---------------------------------------------------------------------------
# 4. Depth bound: a chain forced (via pairwise distinctness) to be genuinely
#    3 nodes deep, rendered under a budget that only fits 2 hops.
# ---------------------------------------------------------------------------

proc longChain(p: Node) =
  if p != nil:
    let n1 = p.next
    if n1 != nil and n1 != p:
      let n2 = n1.next
      if n2 != nil and n2 != p and n2 != n1:
        symexTarget("long_chain")

const depth3 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 3

# ---------------------------------------------------------------------------
# 5. Container elements: array[N, Node] and seq[Node] PARAMS.
# ---------------------------------------------------------------------------

proc arrElemHit(arr: array[2, Node]) =
  if arr[0] != nil and arr[0].val == 9:
    symexTarget("arr_elem_hit")

proc seqElemHit(s: seq[Node]) =
  if s.len > 0 and s[0] != nil and s[0].val == 7:
    symexTarget("seq_elem_hit")

# ---------------------------------------------------------------------------
# 6. Regression: a flat ref param (no ref-typed fields) still renders — the
#    ONLY difference from pre-H_witness is the "<object>" placeholder being
#    replaced by a real per-field rendering (never asserted as "<object>" by
#    any prior test, so this is a pure upgrade, not a behaviour break).
# ---------------------------------------------------------------------------

proc flatRefHit(p: Pair) =
  if p != nil and p.a == 5 and p.b == true:
    symexTarget("flat_ref_hit")

proc plainRefIntHit(p: ref int) =
  if p != nil and p[] == 42:
    symexTarget("plain_ref_int_hit")

suite "Cluster H H_witness — recursive heap-snapshot witness":

  test "linked-list chain: p.next renders real fields, not <object>":
    let r = symexFind(chainHit, tLabel("chain_hit"))
    check r.status == sxSat
    let pEntry = find("p", r.heapSnapshot)
    check pEntry.pointsTo.isSome
    check "<object>" notin pEntry.pointsTo.get
    check "@p.next" in pEntry.pointsTo.get
    let nextEntry = find("p.next", r.heapSnapshot)
    check nextEntry.pointsTo.isSome
    check "<object>" notin nextEntry.pointsTo.get
    check "val=42" in nextEntry.pointsTo.get

  test "one-hop alias: p.next == q renders p.next as an aliasRef to q":
    let r = symexFind(oneHopAlias, tLabel("one_hop_alias"))
    check r.status == sxSat
    let pEntry = find("p", r.heapSnapshot)
    check pEntry.pointsTo.isSome
    check "@p.next" in pEntry.pointsTo.get
    let nextEntry = find("p.next", r.heapSnapshot)
    check nextEntry.aliasRef.isSome
    check nextEntry.aliasRef.get == "q"
    check nextEntry.pointsTo.isNone

  test "cycle termination (LOAD-BEARING): self-loop p.next == p terminates via aliasRef":
    let r = symexFind(selfLoop, tLabel("self_loop"))
    check r.status == sxSat
    # Boundedness: exactly 2 entries (p, p.next) — no runaway recursion.
    check r.heapSnapshot.len == 2
    let nextEntry = find("p.next", r.heapSnapshot)
    check nextEntry.aliasRef.isSome
    check nextEntry.aliasRef.get == "p"
    check nextEntry.pointsTo.isNone

  test "cycle termination (LOAD-BEARING): 2-node ring terminates via aliasRef":
    let r = symexFind(ring, tLabel("ring"))
    check r.status == sxSat
    # Exactly 4 entries: p, q (params) + p.next, q.next (both aliases).
    check r.heapSnapshot.len == 4
    let pNext = find("p.next", r.heapSnapshot)
    check pNext.aliasRef.isSome
    check pNext.aliasRef.get == "q"
    let qNext = find("q.next", r.heapSnapshot)
    check qNext.aliasRef.isSome
    check qNext.aliasRef.get == "p"

  test "depth bound: a 3-deep forced chain renders exactly 2 hops under maxHeapDepth=3":
    let r = symexFind(longChain, tLabel("long_chain"), depth3)
    check r.status == sxSat
    # p, p.next, p.next.next — the third hop is never taken (never selected).
    check r.heapSnapshot.len == 3
    let pEntry = find("p", r.heapSnapshot)
    check "@p.next" in pEntry.pointsTo.get
    let n1Entry = find("p.next", r.heapSnapshot)
    check n1Entry.pointsTo.isSome
    check "@p.next.next" in n1Entry.pointsTo.get
    let n2Entry = find("p.next.next", r.heapSnapshot)
    check n2Entry.pointsTo.isSome
    # The third hop is BLOCKED (never selected) — honest, not fabricated.
    check "<max-heap-depth>" in n2Entry.pointsTo.get
    check "p.next.next.next" notin mapNames(r.heapSnapshot)

  test "container element: array[2, Node] element renders its pointee":
    let r = symexFind(arrElemHit, tLabel("arr_elem_hit"))
    check r.status == sxSat
    let elemEntry = find("arr[0]", r.heapSnapshot)
    check elemEntry.pointsTo.isSome
    check "val=9" in elemEntry.pointsTo.get

  test "container element: seq[Node] element renders its pointee":
    let r = symexFind(seqElemHit, tLabel("seq_elem_hit"))
    check r.status == sxSat
    let elemEntry = find("s[0]", r.heapSnapshot)
    check elemEntry.pointsTo.isSome
    check "val=7" in elemEntry.pointsTo.get

  test "regression: a flat (no ref-field) ref param renders real fields (was <object>)":
    let r = symexFind(flatRefHit, tLabel("flat_ref_hit"))
    check r.status == sxSat
    let e = find("p", r.heapSnapshot)
    check e.pointsTo.isSome
    check "<object>" notin e.pointsTo.get
    check "a=5" in e.pointsTo.get
    check "b=true" in e.pointsTo.get

  test "regression: a bare ref int param is unaffected (unchanged primitive path)":
    let r = symexFind(plainRefIntHit, tLabel("plain_ref_int_hit"))
    check r.status == sxSat
    check r.heapSnapshot.len == 1
    let e = r.heapSnapshot[0]
    check e.pointsTo.isSome
    check e.pointsTo.get == "42"

  test "walker version floor >= 57 (H_witness does NOT bump the walker)":
    check parseInt(symexWalkerVersion) >= 57

  test "renderAsChoicesVersion floor >= 7 (H_witness's recursive witness shape)":
    check parseInt(renderAsChoicesVersion) >= 7
