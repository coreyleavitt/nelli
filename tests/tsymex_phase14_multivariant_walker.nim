## Phase 14 cycle A1c — walker handles `itMultiVariant` allocation
## + witness extraction.
##
## A1a added the IR kind and `allocateSym` stubs (raises). A1b
## fixed the typebridge to emit `itMultiVariant` for multi-recCase
## objects. A1c replaces the walker stub with a real per-axis
## disjunction allocation (ADR-0003 D1) and extends witness
## extraction to walk all axes.
##
## Slice 1 — minimal allocation + extraction: SUT takes a
## multi-axis variant parameter and unconditionally hits a target.
## The walker must allocate per-axis discriminators, constrain each
## to its arms' legal ordinals, and produce a SAT witness binding
## both discriminators to valid values.
import std/unittest
import proptest/symex
import proptest/smt/types

type
  KindA = enum kaX, kaY
  KindB = enum kbP, kbQ
  TwoAxis = object
    case axis1: KindA
    of kaX: a1: int
    of kaY: a2: int
    case axis2: KindB
    of kbP: b1: int
    of kbQ: b2: int

proc anyTwoAxis(obj: TwoAxis) =
  # Unconditional reach — walker just needs to allocate the param
  # and emit the per-axis disjunction constraints. Z3 picks any
  # legal arm-ordinal pair for the two discriminators.
  symexTarget("hit")

suite "symex Phase 14 cycle A1c — itMultiVariant walker":
  test "two-axis variant param: walker allocates + produces SAT witness":
    let r = symexFind(anyTwoAxis, tLabel("hit"))
    check r.status == sxSat

  test "axis1 field access: walker constrains axis1 disc to owning arm":
    # The body reads `obj.a1` — a field that lives ONLY in axis1's
    # `kaX` arm (per the TwoAxis type def). The walker's
    # `isVariantField` for itMultiVariant must:
    #   (a) find that axis1 owns `a1` (axis2's arms have b1/b2 only);
    #   (b) constrain axis1.disc == kaX.ord (== 0);
    #   (c) gate the target hit on the field's value matching 42.
    # Witness: obj.axis1 == kaX (ordinal 0) and the kaX arm's a1 ==
    # 42; axis2 is unconstrained but must satisfy its disjunction.
    proc gatedByAxis1Field(obj: TwoAxis) =
      if obj.a1 == 42:
        symexTarget("a1-matched")
    let r = symexFind(gatedByAxis1Field, tLabel("a1-matched"))
    check r.status == sxSat
