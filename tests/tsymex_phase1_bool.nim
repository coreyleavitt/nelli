## Phase 1 — `bool` as a first-class parameter type.
## Exercises Z3Bool encoding + path conditions over bools.
import std/unittest
import nelli/symex

suite "symex Phase 1 — booleans":
  test "bool parameter participates in path condition":
    proc bothPos(b: bool, x: int) =
      if b and x > 0:
        symexTarget("both")
    let r = symexFind(bothPos, tLabel("both"))
    check r.status == sxSat
    check r.witness[0] == true
    check r.witness[1] > 0
