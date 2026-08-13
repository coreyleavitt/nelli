## Phase 1 — `let`-bound locals flow symbolically across branches.
import std/unittest
import nelli/symex

suite "symex Phase 1 — let bindings":
  test "let-bound local flows into branch condition":
    proc doubleThenCheck(x: int) =
      let y = x * 2
      if y > 10:
        symexTarget("doubled-big")
    let r = symexFind(doubleThenCheck, tLabel("doubled-big"))
    check r.status == sxSat
    check r.witness[0] * 2 > 10
