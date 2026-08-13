## Phase 4 — tuples + objects via per-field tracking.
##
## Each tuple/object is represented in the runtime as a `svTuple`
## SymVal carrying one `SymVal` per field. Field access (`t.a` or
## `t[0]`) dispatches structurally through the variant kind.
import std/unittest
import nelli/symex

proc orderedPair(t: (int, int)) =
  if t[0] > t[1]:
    symexTarget("hit")

proc namedFields(t: tuple[a, b: int]) =
  if t.a > t.b:
    symexTarget("named-hit")

suite "symex Phase 4 — tuples":
  test "anonymous (int, int) param + positional index":
    let r = symexFind(orderedPair, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0][0] > r.witness[0][1]

  test "named-field tuple via dot-expr":
    let r = symexFind(namedFields, tLabel("named-hit"))
    check r.status == sxSat
    check r.witness[0].a > r.witness[0].b

  test "mixed-type tuple (bool, int) — boolean field guards target":
    proc mixed(t: tuple[active: bool, n: int]) =
      if t.active and t.n > 100:
        symexTarget("mix-hit")
    let r = symexFind(mixed, tLabel("mix-hit"))
    check r.status == sxSat
    check r.witness[0].active == true
    check r.witness[0].n > 100

  test "named-object type `type Point = object; x, y: int` recognised":
    type Point = object
      x, y: int
    proc nearAxis(p: Point) =
      if p.x == 0 and p.y > 7:
        symexTarget("axis")
    let r = symexFind(nearAxis, tLabel("axis"))
    check r.status == sxSat
    check r.witness[0].x == 0
    check r.witness[0].y > 7
