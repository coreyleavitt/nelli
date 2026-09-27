## RFC-0005 (soundness channels) slice S8h -- `ref` witnesses that reproduce.
## Walker 155 -> 156.
##
## The RFC-0005 minimum: a witness that does not reproduce on the real SUT is
## never reported as a clean `sxSat`/`sxRaised`. S8f's replay audit found the
## typed `ref` witness violating it four ways, each a false clean `sxSat`:
##   (1) a nil top-level `ref` param rendered non-nil;
##   (2) two params at one address rendered as two distinct cells;
##   (3) a live recursive `ref` field (`n.next != nil`) rendered nil;
##   (4) a `ref` inside a by-value object field was not rendered (nil).
## S10's replay cannot catch these: a `ref` witness was `wfLossy` or
## `wfUnexecutable`, and a miss on such a witness is inconclusive by S10's own
## rule. So the fix is by construction: the typed witness is now built from
## the solver model's INPUT heap -- nil-ness, identity (one cell per address,
## bound to every position that holds it), recursive structure and cycles,
## and refs nested in by-value fields.
##   (5) the same mechanism, found on the way: a `ref` cell's fields rendered
##       the heap the SUT had WRITTEN by the end of the path, not the heap it
##       was called with, so `p.v == 0` followed by `p.v = 1` rendered `v: 1`.
## Every `sxSat` below is checked by RUNNING the SUT on the witness.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

type
  Node = ref object
    v: int
    next: Node

  Holder = object
    k: int
    n: Node

  Cell = object
    x: int

# ---- (1) a nil top-level ref -------------------------------------------------

proc nilTop(p: Node) =
  if p == nil:
    symexTarget("s8h_niltop")

proc nilRefObj(p: ref Cell) =
  if p == nil:
    symexTarget("s8h_nilrefobj")

proc nilRefInt(p: ref int) =
  if p == nil:
    symexTarget("s8h_nilrefint")

proc nilOneOfTwo(p, q: Node) =
  if p != nil and q == nil and p.v == 4:
    symexTarget("s8h_niloneoftwo")

suite "S8h (1) a nil top-level ref renders nil":
  test "named ref object":
    let r = symexFind(nilTop, tLabel("s8h_niltop"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == nil
    check reproduces(nilTop(r.witness[0]), "s8h_niltop")

  test "inline ref to an object":
    let r = symexFind(nilRefObj, tLabel("s8h_nilrefobj"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == nil
    check reproduces(nilRefObj(r.witness[0]), "s8h_nilrefobj")

  test "ref int":
    let r = symexFind(nilRefInt, tLabel("s8h_nilrefint"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == nil
    check reproduces(nilRefInt(r.witness[0]), "s8h_nilrefint")

  test "one nil and one live param":
    let r = symexFind(nilOneOfTwo, tLabel("s8h_niloneoftwo"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[1] == nil
    check reproduces(nilOneOfTwo(r.witness[0], r.witness[1]), "s8h_niloneoftwo")

# ---- (2) params at one address -----------------------------------------------

proc aliasEq(p, q: Node) =
  if p != nil and p == q:
    symexTarget("s8h_aliaseq")

proc aliasWrite(p, q: Node) =
  ## Reaches only when `q` IS `p`: the write through `p` shows through `q`.
  if p != nil and q != nil:
    q.v = 1
    p.v = 5
    if q.v == 5:
      symexTarget("s8h_aliaswrite")

proc aliasRefInt(p, q: ref int) =
  if p != nil and q != nil:
    q[] = 1
    p[] = 5
    if q[] == 5:
      symexTarget("s8h_aliasrefint")

proc aliasThree(p, q, r: Node) =
  if p != nil and p == r and q != p and q != nil and r.v == 2 and q.v == 3:
    symexTarget("s8h_aliasthree")

suite "S8h (2) params at one address render as one ref":
  test "p == q":
    let r = symexFind(aliasEq, tLabel("s8h_aliaseq"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil
    check r.witness[0] == r.witness[1]
    check reproduces(aliasEq(r.witness[0], r.witness[1]), "s8h_aliaseq")

  test "a write through one alias is read through the other":
    let r = symexFind(aliasWrite, tLabel("s8h_aliaswrite"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == r.witness[1]
    check reproduces(aliasWrite(r.witness[0], r.witness[1]), "s8h_aliaswrite")

  test "ref int aliasing":
    let r = symexFind(aliasRefInt, tLabel("s8h_aliasrefint"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == r.witness[1]
    check reproduces(aliasRefInt(r.witness[0], r.witness[1]), "s8h_aliasrefint")

  test "three params, two aliased":
    let r = symexFind(aliasThree, tLabel("s8h_aliasthree"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == r.witness[2] and r.witness[0] != r.witness[1]
    check reproduces(aliasThree(r.witness[0], r.witness[1], r.witness[2]),
                     "s8h_aliasthree")

# ---- (3) a live recursive ref field ------------------------------------------

proc liveNext(n: Node) =
  if n != nil and n.next != nil and n.next.v == 7:
    symexTarget("s8h_livenext")

proc liveChain3(n: Node) =
  ## Locals keep each cell to one dereference, inside the default heap-depth
  ## budget; `n.next.next.next` spelled out re-dereferences every hop.
  if n != nil:
    let a = n.next
    if a != nil:
      let b = a.next
      if b != nil and b.v == 11 and b.next == nil:
        symexTarget("s8h_livechain3")

proc liveNextNil(n: Node) =
  if n != nil and n.next == nil and n.v == 2:
    symexTarget("s8h_livenextnil")

suite "S8h (3) a live recursive ref field renders its cell":
  test "n.next != nil and n.next.v == 7":
    let r = symexFind(liveNext, tLabel("s8h_livenext"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0].next != nil
    check reproduces(liveNext(r.witness[0]), "s8h_livenext")

  test "a three-cell chain ending in nil":
    let r = symexFind(liveChain3, tLabel("s8h_livechain3"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(liveChain3(r.witness[0]), "s8h_livechain3")

  test "a nil recursive field stays nil":
    let r = symexFind(liveNextNil, tLabel("s8h_livenextnil"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(liveNextNil(r.witness[0]), "s8h_livenextnil")

# ---- (4) a ref inside a by-value field ---------------------------------------

proc holderRef(h: Holder) =
  if h.n != nil and h.n.v == 3:
    symexTarget("s8h_holderref")

proc holderNil(h: Holder) =
  if h.n == nil and h.k == 8:
    symexTarget("s8h_holdernil")

proc holderAlias(h: Holder; p: Node) =
  if p != nil and h.n == p and p.v == 6:
    symexTarget("s8h_holderalias")

proc tupleRef(t: tuple[a: int, n: Node]) =
  if t.n != nil and t.n.next != nil and t.n.next.v == 4:
    symexTarget("s8h_tupleref")

suite "S8h (4) a ref inside a by-value field renders":
  test "object field":
    let r = symexFind(holderRef, tLabel("s8h_holderref"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].n != nil
    check reproduces(holderRef(r.witness[0]), "s8h_holderref")

  test "a nil object field stays nil":
    let r = symexFind(holderNil, tLabel("s8h_holdernil"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(holderNil(r.witness[0]), "s8h_holdernil")

  test "an object field aliasing a param":
    let r = symexFind(holderAlias, tLabel("s8h_holderalias"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].n == r.witness[1]
    check reproduces(holderAlias(r.witness[0], r.witness[1]), "s8h_holderalias")

  test "a tuple field, followed one hop":
    let r = symexFind(tupleRef, tLabel("s8h_tupleref"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(tupleRef(r.witness[0]), "s8h_tupleref")

# ---- cycles and aliasing through a field -------------------------------------

proc selfLoop(n: Node) =
  if n != nil and n.next == n and n.v == 1:
    symexTarget("s8h_selfloop")

proc ringOne(n: Node) =
  ## A two-cell ring reached from ONE param.
  if n != nil and n.next != nil and n.next != n and n.next.next == n:
    symexTarget("s8h_ringone")

proc ringTwo(p, q: Node) =
  if p != nil and q != nil and p != q and p.next == q and q.next == p:
    symexTarget("s8h_ringtwo")

proc aliasField(p, q: Node) =
  if p != nil and q != nil and p != q and p.next == q and q.v == 9:
    symexTarget("s8h_aliasfield")

proc aliasFieldWrite(p, q: Node) =
  ## `p.next` IS `q`: a write through `q` is read through `p.next`.
  if p != nil and q != nil and p.next != nil:
    q.v = 0
    p.next.v = 13
    if q.v == 13:
      symexTarget("s8h_aliasfieldwrite")

suite "S8h cycles and aliasing through a field":
  test "a self-loop":
    let r = symexFind(selfLoop, tLabel("s8h_selfloop"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0].next == r.witness[0]
    check reproduces(selfLoop(r.witness[0]), "s8h_selfloop")

  test "a two-cell ring from one param":
    let r = symexFind(ringOne, tLabel("s8h_ringone"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(ringOne(r.witness[0]), "s8h_ringone")

  test "a two-cell ring across two params":
    let r = symexFind(ringTwo, tLabel("s8h_ringtwo"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].next == r.witness[1] and r.witness[1].next == r.witness[0]
    check reproduces(ringTwo(r.witness[0], r.witness[1]), "s8h_ringtwo")

  test "a field aliasing another param":
    let r = symexFind(aliasField, tLabel("s8h_aliasfield"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].next == r.witness[1]
    check reproduces(aliasField(r.witness[0], r.witness[1]), "s8h_aliasfield")

  test "a write through a param read through a field alias":
    let r = symexFind(aliasFieldWrite, tLabel("s8h_aliasfieldwrite"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(aliasFieldWrite(r.witness[0], r.witness[1]),
                     "s8h_aliasfieldwrite")

# ---- (5) the input heap, not the heap the SUT wrote ---------------------------

proc postField(p: Node) =
  if p != nil and p.v == 0:
    p.v = 1
    if p.v == 1:
      symexTarget("s8h_postfield")

proc postRefInt(p: ref int) =
  if p != nil and p[] == 0:
    p[] = 1
    if p[] == 1:
      symexTarget("s8h_postrefint")

proc postNext(p: Node) =
  if p != nil and p.next == nil:
    p.next = p
    if p.next == p:
      symexTarget("s8h_postnext")

suite "S8h (5) a ref cell renders the input heap":
  test "a field written after it was read":
    let r = symexFind(postField, tLabel("s8h_postfield"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(postField(r.witness[0]), "s8h_postfield")

  test "a ref int written after it was read":
    let r = symexFind(postRefInt, tLabel("s8h_postrefint"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(postRefInt(r.witness[0]), "s8h_postrefint")

  test "a ref field written after it was read":
    let r = symexFind(postNext, tLabel("s8h_postnext"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(postNext(r.witness[0]), "s8h_postnext")

# ---- the same mechanism at other positions -----------------------------------

type
  VK = enum vkA, vkB
  VObj = object
    case kind: VK
    of vkA: a: int
    of vkB: b: int
  VRef = ref VObj
  VHolder = ref object
    tag: int
    v: VRef

proc ptrCell(p: ptr Cell) =
  if p != nil and p.x == 3:
    symexTarget("s8h_ptrcell")

proc variantField(h: VHolder) =
  ## A case object reached through a field: its IR pointee is a placeholder.
  if h != nil and h.v != nil and h.v.kind == vkB and h.v.b == 5:
    symexTarget("s8h_variantfield")

proc seqAlias(s: seq[Node]; p: Node) =
  if s.len == 2 and p != nil and s[1] == p and s[0] == nil and p.v == 4:
    symexTarget("s8h_seqalias")

suite "S8h the same mechanism at other positions":
  test "a ptr to an object renders its cell":
    let r = symexFind(ptrCell, tLabel("s8h_ptrcell"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil
    check reproduces(ptrCell(r.witness[0]), "s8h_ptrcell")

  test "a case object reached through a field renders its branch":
    let r = symexFind(variantField, tLabel("s8h_variantfield"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0].v != nil
    check reproduces(variantField(r.witness[0]), "s8h_variantfield")

  test "a seq element aliasing a param":
    let r = symexFind(seqAlias, tLabel("s8h_seqalias"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 2 and r.witness[0][1] == r.witness[1]
    check reproduces(seqAlias(r.witness[0], r.witness[1]), "s8h_seqalias")

# ---- walker version floor -----------------------------------------------------

suite "S8h walker version":
  test "the walker version is at least 156":
    check parseInt(symexWalkerVersion) >= 156
