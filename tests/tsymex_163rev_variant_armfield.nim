## Issue #163 review finding R3 (High, verified) -- a ranged arm-specific
## field of a ref-to-variant object never reaches EITHER obligation a
## declared `range[lo..hi]` type carries:
##
##   (a) CONSTRAINT -- `walkHeapArm`'s `isArmField` branch (the ONLY place a
##       ref-to-variant arm field is read) `heapSelect`s the value and never
##       calls `bvRangeConds`, even when the field's type `hasRange`. The
##       generic (non-arm) `isDeref` arm got this at issue #163 W4
##       (`runtime_heap.nim:895-897`, commit 61fca8b); `isArmField` sits
##       entirely above that insertion point and was never touched.
##
##   (b) WITNESS CLAMP -- `extractFromSymVal`'s ref-to-`itVariant` pointee arm
##       (`runtime.nim`, the `of itVariant:` block under the pointee-witness
##       proc) extracts every plain AND arm field from a disconnected proto
##       allocation whose OWN `bvRangeConds` obligations were pushed into a
##       throwaway `scratchPC` -- exactly the same gap W4 already fixed for
##       the sibling `itTuple` pointee arm (`runtime.nim:6565-6573`) -- and
##       was never mirrored here.
##
## This is the SAME shape as `tsymex_163audit_range_elem.nim`'s W2/W4 findings
## (a seq element, a plain ref-object field), one heap-select arm over: a
## RANGED field declared inside an `of` branch of a variant `case` object,
## read through a `ref`. `tsymex_a2_refvariant_fields.nim` proves this exact
## arm-field-through-a-ref shape is reachable and already exercised end to
## end for plain `int` arm fields (Slice 2/3, walker v28/29) -- this file is
## that shape with `range[0..10]` on one arm field instead of a bare `int`.
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation actually executed in Nim, in this file -- so the test
## pins truth rather than the engine's own (possibly wrong) model.

import std/unittest
import nelli/symex

type
  Color = enum cRed, cGreen, cBlue
  CNode = object
    case col: Color
    of cRed:   r: int
    of cGreen: g: range[0..10]
    of cBlue:  b: int

proc mkRange0to10(x: int): range[0..10] = range[0..10](x)

# ---- Part A: missing CONSTRAINT ---------------------------------------------
# `p.g > 10` is unreachable in real Nim: a `range[0..10]` field can never hold
# a value outside [0,10] in any legal construction. Without D2's `bvRangeConds`
# on the arm-select, Z3 is free to pick `g = 11` and the engine wrongly reports
# `sxSat`.
proc readGreenOutOfRange(p: ref CNode) =
  if p != nil and p.col == cGreen and p.g > 10:
    symexTarget("outOfRange")

# ---- Non-regression: an in-range arm-field target is still sxSat -----------
proc readGreenInRange(p: ref CNode) =
  if p != nil and p.col == cGreen and p.g == 7:
    symexTarget("inRange")

# ---- Part B: missing WITNESS CLAMP ------------------------------------------
# `p.g` is never itself read on the winning path -- only the discriminator is
# compared -- so the D2 fix above (which only asserts a range clause on a
# value that is actually `heapSelect`ed at an arm-field READ site) cannot
# reach it. Mirrors `tsymex_163audit_range_elem.nim`'s `onlyLen` precedent:
# reach a target without reading the ranged value, then convert the witness
# value into the declared range type and prove no `RangeDefect`.
proc onlyDisc(p: ref CNode) =
  if p != nil and p.col == cGreen:
    symexTarget("disc")

suite "#163 review R3 -- the oracle":

  test "Nim itself refuses an out-of-declared-range arm-field value":
    expect RangeDefect:
      discard mkRange0to10(11)
    expect RangeDefect:
      discard mkRange0to10(-1)
    check mkRange0to10(7) == 7

suite "#163 review R3 Part A -- ref-to-variant arm field reaches the path condition":

  test "an out-of-range arm-field target is sxUnsat":
    ## Was `sxSat` before the fix: with no constraint on the `heapSelect`ed
    ## arm value, `p.g > 10` was satisfiable for a field declared
    ## `range[0..10]` -- the model was free to pick 11 (already a
    ## `RangeDefect` waiting to happen, per the oracle suite above).
    let r = symexFind(readGreenOutOfRange, tLabel("outOfRange"))
    check r.status == sxUnsat

  test "the bound is a refinement, not a ban -- an in-range arm-field target survives":
    let r = symexFind(readGreenInRange, tLabel("inRange"))
    check r.status == sxSat
    check not r.witness[0].isNil
    let node = r.witness[0][]
    check node.col == cGreen
    check node.g == 7

suite "#163 review R3 Part B -- an unread arm field's witness stays inside its declared range":

  test "the disc-only target's unread arm field extracts in range":
    ## The crash class. `p.g` is never read on the winning path -- only
    ## `p.col == cGreen` is compared -- so the verdict is correctly `sxSat`
    ## before and after the fix; only the WITNESS's `g` field was ever wrong
    ## (a disconnected, unclamped proto default that can fall outside
    ## `range[0..10]`, per Part B).
    let r = symexFind(onlyDisc, tLabel("disc"))
    check r.status == sxSat
    check not r.witness[0].isNil
    let node = r.witness[0][]
    check node.col == cGreen
    check node.g in 0 .. 10
    discard mkRange0to10(node.g)  ## does not raise -- the point of the fix

suite "#163 review R3 non-regression -- A2 plain-field/discriminator routes":

  test "a plain (non-ranged) arm-field read is still sound (A2 Slice 2 shape)":
    let r = symexFind(readGreenInRange, tLabel("inRange"))
    check r.status == sxSat
