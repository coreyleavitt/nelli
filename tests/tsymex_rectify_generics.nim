## Rectify #139 — generic procs via monomorphization.
import std/unittest
import proptest/symex

proc doubleIt[T](x: T): T = x * 2

proc f(a: int) =
  if doubleIt(a) == 10:
    symexTarget("found")

suite "symex generics #139":
  test "generic doubleIt[int] resolves":
    let r = symexFind(f, tLabel("found"))
    check r.status == sxSat
    check r.witness[0] == 5
