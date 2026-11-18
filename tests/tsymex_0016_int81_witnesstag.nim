## RFC-0016 INT-81 (witness fidelity): the walker's witness built a ref cell
## as the static type of the position it fills (`resolveRef`, `new(result)`
## in runtime.nim), not the dynamic type the model chose. A verdict that
## needs a descendant behind a base-typed parameter (a method override, a
## down-conversion, `of`) was correct, but its witness replayed as the base
## type and missed the target natively; a cell shared by a base-typed and a
## descendant-typed position was allocated at the size of whichever was
## built first. Found converting the ref family (K9d-10).
##
## The bar: a witness cell is built once per model address, as the dynamic
## type its run-type tags name (`<cell>.@lvl<j>`, `cellDynBuild`), and every
## position holding the address gets that object, upcast. Each `sxSat` below
## replays natively to its target (`pinFind`); each `sxUnsat` is refuted by
## the native domain.
import std/unittest
import nelli/symex
from ./s8cu_helpers import pinFind

type
  Shape = ref object of RootObj
  Square = ref object of Shape
  Base = ref object of RootObj
    x: int
  Mid = ref object of Base
    y: int
  Leaf = ref object of Mid
    z: int
  Holder = ref object
    m: Mid
  Node = ref object of RootObj
    next: Node
    v: int
  Twig = ref object of Node
    w: int

method m(o: Shape): int {.base.} = 5
method m(o: Square): int = 6

proc dispatch(o: Shape) =
  if o != nil and o.m == 6: symexTarget("hit")

proc dispatchDead(o: Shape) =
  if o != nil and o.m != 5 and o.m != 6: symexTarget("hit")

proc isMid(b: Base) =
  if b != nil and b of Mid: symexTarget("hit")

proc downConv(b: Base; d: Mid) =
  if b != nil and d != nil and Base(d) == b:
    try:
      if Mid(b).y == d.y: symexTarget("hit")
    except ObjectConversionDefect:
      discard

proc shared(b: Base; d: Mid) =
  # one cell at a base-typed and a descendant-typed position: `b` comes
  # first, and the cell must still be a `Mid` (it is read as one through `d`)
  if b != nil and d != nil and Base(d) == b and b.x == 3 and d.y == 4:
    symexTarget("hit")

proc sharedDead(b: Base; d: Mid) =
  if b != nil and d != nil and Base(d) == b and not (b of Mid):
    symexTarget("hit")

proc leafFields(b: Base) =
  # a descendant's own fields, declared two levels below the static type
  if b != nil and b of Leaf and Leaf(b).z == 7 and Mid(b).y == 2 and b.x == 1:
    symexTarget("hit")

proc viaField(h: Holder) =
  # a cell reached only through a field of a static type below the root
  if h != nil and h.m != nil and h.m of Leaf and Leaf(h.m).z == 9:
    symexTarget("hit")

proc cycle(n: Node) =
  # a cycle through two descendant cells
  if n != nil and n of Twig and n.next != nil and n.next of Twig and
     n.next.next == n and n.next != n and Twig(n.next).w == 5 and
     Twig(n).w == 6:
    symexTarget("hit")

template pinned(fn: typed; want: SymexStatusKind) =
  ## `pinFind` pins only a trusted verdict: an untrusted one (a witness the
  ## replay did not confirm) comes back unpinned, so trust is checked too
  let r = pinFind(fn, tLabel("hit"))
  check r.status == want
  check r.trusted

suite "INT-81: a witness cell is its address's dynamic type":
  test "nim":
    check Square().m == 6
    let l = Leaf(x: 1, y: 2, z: 7)
    leafFields(l)
    let a = Twig(w: 6)
    let b = Twig(w: 5, next: a)
    a.next = b
    cycle(a)

  test "a method call on a base-typed parameter reaches the override":
    pinned(dispatch, sxSat)
    pinned(dispatchDead, sxUnsat)

  test "a base-typed parameter that is a descendant (`of`)":
    pinned(isMid, sxSat)

  test "a down-conversion of a parameter aliasing a descendant one":
    pinned(downConv, sxSat)

  test "a cell shared by a base-typed and a descendant-typed position":
    pinned(shared, sxSat)
    pinned(sharedDead, sxUnsat)

  test "a descendant's own fields, read":
    pinned(leafFields, sxSat)

  test "a descendant reached through a field of a non-root static type":
    pinned(viaField, sxSat)

  test "a cycle through descendants":
    pinned(cycle, sxSat)
