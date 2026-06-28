## Phase 14 cycle A3 — non-enum discriminator types.
##
## Pre-A3 the typebridge errored out when a variant's discriminator
## wasn't an enum (dsl_typebridge.nim:195-197). A3 relaxes the
## assertion: the walker uses the disc type's ordinal range to
## bound legal values when needed; explicit `of N:` arms pin the
## disc directly; `else:` uses the same conjunction-of-negations
## the enum path uses.
##
## RFC v3 §A3 RED test: SUT with `case kind: int` over a couple of
## `of` arms compiles past the parser and produces a correct
## witness on a target reachable through one of the arms.
import std/unittest
import proptest/symex
import proptest/smt/types

type
  # Nim requires `low(T) == 0` for discriminator types; plain `int`
  # is rejected by the compiler. `range[0..255]` is the canonical
  # non-enum-but-ordinal form A3's relaxation needs to cover.
  Tag = range[0..255]
  IntDisc = object
    case kind: Tag
    of 1: a: int
    of 2: b: int
    else: x: int

proc gatedIntDisc(v: IntDisc) =
  # Reach gated on disc-pin to arm `of 1:`.
  # Nested ifs: disc guard must be in pc before arm-field access.
  if v.kind == 1:
    if v.a == 7:
      symexTarget("int-arm")

suite "symex Phase 14 cycle A3 — non-enum discriminator types":
  test "variant with `case kind: int` parses + walker finds witness":
    let r = symexFind(gatedIntDisc, tLabel("int-arm"))
    check r.status == sxSat
    check r.witness[0].kind == 1
    check r.witness[0].a == 7
