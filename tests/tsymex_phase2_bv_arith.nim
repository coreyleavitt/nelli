## Phase 2 — width-specific BV arithmetic.
##
## Demonstrates that Nim's fixed-width int family (`int8`/`int16`/...,
## `uint8`/`uint16`/...) maps to `Z3BitVec[W]` of the right width,
## with signed-vs-unsigned operator dispatch driven by the
## declaration's `IRType.signed`.
import std/unittest
import proptest/symex

suite "symex Phase 2 — width-specific BV arithmetic":
  test "uint16: high byte extracted via shr finds the right witness":
    # Byte-parser shape: `b shr 8` is the high byte; target = "high byte is 0xFF".
    # Only inputs with bits 15..8 == 0xFF satisfy. Witness has b in 0xFF00..0xFFFF.
    proc highByteIsFF(b: uint16) =
      if (b shr 8) == 0xFF'u16:
        symexTarget("hi-ff")
    let r = symexFind(highByteIsFF, tLabel("hi-ff"))
    check r.status == sxSat
    check (r.witness[0] shr 8) == 0xFF'u16

  test "int8 < 0 is satisfiable via signed less-than":
    proc isNeg(x: int8) =
      if x < 0:
        symexTarget("neg")
    let r = symexFind(isNeg, tLabel("neg"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "uint8 < 0 is UNSAT (unsigned less-than)":
    proc cantBeNeg(x: uint8) =
      if x < 0'u8:
        symexTarget("impossible")
    let r = symexFind(cantBeNeg, tLabel("impossible"))
    check r.status == sxUnsat

  test "int8 addition wraps at the BV[8] boundary":
    # `x + 1 < x` only holds when the addition wraps — i.e. x = 127
    # (int8.high). Under unbounded arithmetic the inequality is
    # always false; under BV[8] it is reachable with x = 127.
    proc wrapNeeded(x: int8) =
      if x + 1 < x:
        symexTarget("wrapped")
    let r = symexFind(wrapNeeded, tLabel("wrapped"))
    check r.status == sxSat
    check r.witness[0] == 127
