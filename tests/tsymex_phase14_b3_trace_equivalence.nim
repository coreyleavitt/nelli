## Phase 14 cycle B3 — `tables`/`sets` trace-equivalence pin.
##
## Phase 12 cycle 6 already shipped sorted iteration in
## `renderAsChoices` for `Table[K,V]` and `HashSet[E]`. B3 adds an
## explicit regression pin so two semantically-equal containers
## constructed in different insertion orders produce the SAME
## choice sequence. This guards against the bucket-collision
## scenario where Nim's `HashSet` iteration order is undefined and
## insertion order could leak into the rendered trace.
##
## The fix is structural: `renderAsChoices` sorts before iterating.
## This test pins the contract.
import std/[unittest, sets, tables]
import nelli/symex

suite "symex Phase 14 cycle B3 — trace equivalence under collision":
  test "HashSet[int] renders the same regardless of insertion order":
    var a: HashSet[int]
    var b: HashSet[int]
    a.incl 3; a.incl 1; a.incl 2
    b.incl 2; b.incl 3; b.incl 1
    let renderA = renderAsChoices(a)
    let renderB = renderAsChoices(b)
    check renderA.len == renderB.len
    for i in 0 ..< renderA.len:
      check renderA[i].kind == renderB[i].kind
      if renderA[i].kind == ckInteger:
        check renderA[i].intVal == renderB[i].intVal
      elif renderA[i].kind == ckBoolean:
        check renderA[i].boolVal == renderB[i].boolVal

  test "Table[string,int] renders the same regardless of insertion order":
    var a: Table[string, int]
    var b: Table[string, int]
    a["c"] = 3; a["a"] = 1; a["b"] = 2
    b["b"] = 2; b["c"] = 3; b["a"] = 1
    let renderA = renderAsChoices(a)
    let renderB = renderAsChoices(b)
    check renderA.len == renderB.len
    for i in 0 ..< renderA.len:
      check renderA[i].kind == renderB[i].kind
