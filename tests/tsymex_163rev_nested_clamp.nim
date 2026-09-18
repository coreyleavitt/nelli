## Issue #163 review finding R8 (Medium) -- W4's witness clamp for a
## ref-to-object pointee (`extractFromSymVal`'s `itTuple` pointee arm,
## `runtime.nim`, just below the `## Issue #163 wiring-audit W4.` comment)
## iterates only `pointee.fieldNames`/`pointee.fields` -- the pointee's OWN
## IMMEDIATE fields. But the recursive `extractFromSymVal(m, w, path,
## protoObj, ...)` call just above it recurses arbitrarily deep through
## nested `svTuple`/`svArray` fields, populating deeper dotted paths
## (`path.outer.inner`). Those deeper paths are never visited by the flat
## clamp loop.
##
## Trigger: an unread `ref object` field whose type is itself an object
## containing a `range[lo..hi]` subfield two levels down. The witness
## reconstructs that subfield unclamped and can raise a real `RangeDefect`
## in the caller's own process -- the same crash class W4 targets, one
## nesting level deeper than the fix reached.
##
## `tsymex_163audit_range_elem.nim`'s own W4 suite (`twoRefs`) is the
## precedent this file extends one nesting level deeper: a second ref param
## of the SAME type, never dereffed/field-accessed anywhere, forces witness
## reconstruction through the proto-default branch (no heap key exists for
## it at all). There the ranged field was DIRECT (`w: range[50..60]`); here
## it sits inside a nested plain object field (`inner.r: range[lo..hi]`).
##
## House rule (the #162/#163 discipline): every symbolic expectation is
## paired with an ORACLE -- the same computation run for real in Nim, in
## this file -- so a range/width bug can never be pinned by a test that
## merely encodes the engine's own wrong model.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

type
  InnerCfg = object
    r: range[10'i32..20'i32]
  OuterCfg = ref object
    inner: InnerCfg
    tag: int32

  # Non-regression fixture: W4's ORIGINAL one-level-deep shape.
  FlatCfg = ref object
    w: range[50'i32..60'i32]

proc mkInnerR(x: int32): range[10'i32..20'i32] = range[10'i32..20'i32](x)
proc mkFlatW(x: int32): range[50'i32..60'i32] = range[50'i32..60'i32](x)

# ---- Headline: a ranged subfield TWO LEVELS down in an unread ref-object --
# `c2` is never dereffed or field-accessed anywhere -- only `c1.tag` drives
# the target -- so witness reconstruction for `c2` goes through the
# proto-default branch (no heap key exists for it at all), exactly W4's
# `twoRefs` shape, one nesting level deeper: `c2`'s pointee has a NESTED
# object field (`inner.r`) rather than a direct one.
proc twoOuterRefs(c1, c2: OuterCfg) =
  if c1 != nil and c1.tag == 55'i32:
    symexTarget("hit")

# ---- Non-regression: W4's original one-level-deep case still clamps -------
proc twoFlatRefs(c1, c2: FlatCfg) =
  if c1 != nil and c1.w == 55'i32:
    symexTarget("hit")

suite "#163 review R8 -- the oracle":

  test "Nim itself refuses an out-of-declared-range nested subfield":
    expect RangeDefect:
      discard mkInnerR(0'i32)
    expect RangeDefect:
      discard mkInnerR(21'i32)
    check mkInnerR(15'i32) == 15'i32

  test "Nim itself refuses an out-of-declared-range flat (one-level) field":
    expect RangeDefect:
      discard mkFlatW(0'i32)
    expect RangeDefect:
      discard mkFlatW(61'i32)
    check mkFlatW(55'i32) == 55'i32

suite "#163 review R8 -- a ranged subfield two levels deep in an unread ref-object stays in range":

  test "an unread sibling ref's nested subfield witness stays inside its declared range":
    ## The crash class. `c2` is never dereffed or field-accessed anywhere,
    ## so witness reconstruction materialises a fresh, disconnected proto
    ## object for it, then evaluates that proto's fields (recursively,
    ## through the nested `inner` object) under the already-solved model --
    ## unconstrained, `inner.r` extracts as the model's bare default, which
    ## `range[10..20]` need not contain. Reconstructing it into the SUT's
    ## own declared range type raised `RangeDefect` before this fix.
    let r = symexFind(twoOuterRefs, tLabel("hit"))
    check r.status == sxSat  ## did not crash constructing this result
    if r.status == sxSat:
      let c2 = r.witness[1][]
      discard mkInnerR(c2.inner.r)  ## does not raise -- the point of the fix

suite "#163 review R8 non-regression -- W4's original one-level-deep field still clamps":

  test "an unread sibling ref's direct field witness still stays inside its declared range":
    let r = symexFind(twoFlatRefs, tLabel("hit"))
    check r.status == sxSat
    if r.status == sxSat:
      let c2 = r.witness[1][]
      discard mkFlatW(c2.w)  ## does not raise -- unaffected by the R8 change

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 135
