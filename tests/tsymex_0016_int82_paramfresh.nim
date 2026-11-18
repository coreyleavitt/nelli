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
## it (parameters, their fields and elements, globals), so both verdicts below
## are sxUnsat, pinned natively over the ref domain (nil, fresh cells, cycles,
## chains, aliases).
import std/unittest
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

suite "INT-82: a fresh allocation is never a caller's ref":
  test "a parameter is not a node the SUT constructs":
    check pinFind(paramEqFresh, tLabel("hit")).status == sxUnsat

  test "a parameter is not a node the SUT allocates with new":
    check pinFind(paramEqNew, tLabel("hit")).status == sxUnsat

  test "a parameter's field is not a node the SUT constructs":
    check pinFind(fieldEqFresh, tLabel("hit")).status == sxUnsat

  test "no write through the fresh node is seen through the parameter":
    check pinFind(writeThroughFresh, tLabel("hit")).status == sxUnsat
