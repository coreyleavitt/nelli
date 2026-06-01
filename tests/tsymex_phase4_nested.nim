## Phase 4 — nested tuples.
import std/unittest
import proptest/symex

proc nestedSum(t: tuple[inner: tuple[x, y: int], outer: int]) =
  if t.inner.x + t.inner.y == t.outer:
    symexTarget("sum-match")

suite "symex Phase 4 — nested tuples":
  test "nested tuple field path `t.inner.x` works":
    let r = symexFind(nestedSum, tLabel("sum-match"))
    check r.status == sxSat
    check r.witness[0].inner.x + r.witness[0].inner.y == r.witness[0].outer
