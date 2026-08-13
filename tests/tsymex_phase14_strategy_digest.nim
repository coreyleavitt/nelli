## Phase 14 cycle B1 — Strategy[T].constraintDigest.
##
## Stable descriptor of a strategy's value-domain constraints,
## used as a participant in the symex cache key so distinct
## strategies don't share cached witnesses.
##
## RED tests pin the digest format for a few representative
## combinators and verify the cascade through `map`. Custom
## (`newStrategy`) strategies retain an empty digest (silent-clamp
## documented in the field's doc comment).
import std/[unittest, strutils]
import nelli

suite "symex Phase 14 cycle B1 — Strategy.constraintDigest":
  test "integers(lo, hi) carries `integers:lo=…;hi=…` digest":
    let s = integers(0, 100)
    check s.constraintDigest.startsWith("integers:")
    check s.constraintDigest.contains("lo=0")
    check s.constraintDigest.contains("hi=100")

  test "different bounds produce different digests":
    let s1 = integers(0, 100)
    let s2 = integers(0, 200)
    check s1.constraintDigest != s2.constraintDigest

  test "map cascades the inner digest":
    let inner = integers(0, 10)
    let outer = inner.map(proc(x: int): int = x * 2)
    check outer.constraintDigest.startsWith("map:")
    check outer.constraintDigest.contains(inner.constraintDigest)

  test "newStrategy yields an empty digest (custom-strategy clamp)":
    let custom = newStrategy[int](proc(src: var DataSource): int = 42)
    check custom.constraintDigest == ""
