## RFC-0016 INT-82 (soundness, red until fixed): a ref parameter compared
## with a node the SUT allocates is a false sxSat. `Node(...)` and `new`
## mint a fresh address that `assertFreshness` (runtime_heap.nim) keeps
## distinct from nil and from the path's live refs only; a caller's ref
## parameter is never among them, so the walker lets `p == n` hold. Natively
## no caller's object is the one the SUT has just allocated: `p == n` is
## false on every input, and so is every target behind it. Found converting
## the ref family (K9d-10): `tsymex_h_verification` asserted the false sxSat
## (`param_ctor_eq_hit`, `param_ctor_write_hit`) and its witnesses do not hit
## natively.
##
## The bar: a fresh allocation is distinct from every ref that existed before
## it (parameters, their fields and elements, globals) and from every earlier
## allocation, so each verdict below is sxUnsat, pinned natively over the ref
## domain (nil, fresh cells, cycles, chains, aliases). A fresh node stored
## into a parameter's field is read back as itself, through the parameter or
## an alias of it: those stay sxSat, their witnesses hit natively. The fix
## states it at the allocation (`refProvenanceRoots`, heap_model.nim).
import std/[unittest, sequtils, strutils]
import nelli/symex
from ./s8cu_helpers import pinFind

type Node = ref object
  val: int
  next: Node

proc paramEqFresh(p: Node; x: int) =
  let n = Node(val: x, next: nil)
  if p == n: symexTarget("hit")

proc paramEqNew(p: Node) =
  var n: Node
  new(n)
  if p == n: symexTarget("hit")

proc fieldEqFresh(p: Node) =
  if p != nil:
    let n = Node(val: 1)
    if p.next == n: symexTarget("hit")

proc writeThroughFresh(p: Node; x: int) =
  let n = Node(val: x, next: nil)
  if p == n:
    n.val = 99
    if p.val == 99: symexTarget("hit")

proc deepFieldEqFresh(p: Node) =
  if p != nil and p.next != nil:
    let n = Node(val: 2)
    if p.next.next == n: symexTarget("hit")

proc seqElemEqFresh(s: seq[Node]) =
  let n = Node(val: 3)
  if s.len > 0 and s[0] == n: symexTarget("hit")

var gNode: Node   # its entry value: whatever earlier code left there

proc globalEqFresh(x: int) =
  let n = Node(val: x)
  if gNode == n: symexTarget("hit")

proc newEqCtor(x: int) =
  var a: Node
  new(a)
  let b = Node(val: x)
  if a == b: symexTarget("hit")

proc twoCtors(x: int) =
  let a = Node(val: x)
  let b = Node(val: x)
  if a == b: symexTarget("hit")

proc storedReadBack(p: Node) =
  if p != nil:
    let n = Node(val: 5)
    p.next = n
    if p.next == n: symexTarget("hit")

proc storedReadThroughAlias(p, q: Node) =
  if p != nil and q != nil:
    let n = Node(val: 5)
    p.next = n
    if q.next == n: symexTarget("hit")

proc storedIntoGlobal(x: int) =
  let n = Node(val: x)
  gNode = n
  if gNode == n: symexTarget("hit")

suite "INT-82: a fresh allocation is never a caller's ref":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 440

  test "a parameter is not a node the SUT constructs":
    check pinFind(paramEqFresh, tLabel("hit")).status == sxUnsat

  test "a parameter is not a node the SUT allocates with new":
    check pinFind(paramEqNew, tLabel("hit")).status == sxUnsat

  test "a parameter's field is not a node the SUT constructs":
    check pinFind(fieldEqFresh, tLabel("hit")).status == sxUnsat

  test "no write through the fresh node is seen through the parameter":
    check pinFind(writeThroughFresh, tLabel("hit")).status == sxUnsat

  test "a ref two fields down a parameter is not a node the SUT constructs":
    check pinFind(deepFieldEqFresh, tLabel("hit")).status == sxUnsat

  test "a seq parameter's element is not a node the SUT constructs":
    check pinFind(seqElemEqFresh, tLabel("hit")).status == sxUnsat

  test "a global ref read before any write is declined, not answered":
    # A module-level ref's entry value is not modelled (no false sxSat to
    # fix): the read declines. Were it modelled, `entryValueOf` notes it as
    # entry state and this becomes the sxUnsat the others are.
    let r = pinFind(globalEqFresh, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feGlobalReadUnmodelled)

  test "an object of new and one of a constructor are two objects":
    check pinFind(newEqCtor, tLabel("hit")).status == sxUnsat

  test "two constructor calls are two objects":
    check pinFind(twoCtors, tLabel("hit")).status == sxUnsat

  test "a fresh node stored into a parameter's field is read back as itself":
    check pinFind(storedReadBack, tLabel("hit")).status == sxSat

  test "and through a second parameter aliasing the first":
    check pinFind(storedReadThroughAlias, tLabel("hit")).status == sxSat

  test "a fresh node stored into a global is that global's value":
    check pinFind(storedIntoGlobal, tLabel("hit")).status == sxSat
