## Phase 6 — case statement.
##
## Lowered to if-elif chain at parse time. No new walker code —
## reuses the existing isIf semantics.
import std/unittest
import proptest/symex

type Color = enum red, green, blue

proc colorReach(c: Color) =
  case c
  of red:   symexTarget("r")
  of green: symexTarget("g")
  of blue:  symexTarget("b")

suite "symex Phase 6 — case":
  test "case over enum reaches matching arm":
    let r = symexFind(colorReach, tLabel("g"))
    check r.status == sxSat
    check r.witness[0] == ord(green).uint8

  test "case with multiple labels per branch":
    proc small(n: int) =
      case n
      of 1, 2, 3: symexTarget("small")
      else: discard
    let r = symexFind(small, tLabel("small"))
    check r.status == sxSat
    check r.witness[0] in {1, 2, 3}

  test "case with else clause":
    proc anyOther(n: int) =
      case n
      of 1: symexTarget("one")
      else: symexTarget("other")
    let r = symexFind(anyOther, tLabel("other"))
    check r.status == sxSat
    check r.witness[0] != 1
