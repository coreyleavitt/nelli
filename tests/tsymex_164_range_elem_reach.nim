## Issue #163 wiring-audit findings W2 and W4 -- a declared `range[lo..hi]`
## reaches only ONE kind of value, and silently evaporates for the rest.
##
## Issue #162 slice 5 moved a range's bounds from `IRParam` onto `IRType`
## (in Nim, `range[lo..hi]` IS a type) so a value-object FIELD would inherit
## the constraint through `allocateSym`'s recursion. `ty.hasRange` has
## exactly ONE consumer in the whole runtime -- `allocateSym`'s `itInt`
## arm -- and neither a `seq[range[lo..hi]]` element (W2) nor a `ref
## object` field (W4) ever reaches it: a seq's data is a raw Z3 array
## (`allocateSeqDataRaw`), and a ref/ptr's pointee is read lazily through a
## field-split heap array (`runtime_heap.nim`) -- neither passes through
## per-element allocation.
##
## Two consequences, both already fixed for the object-VALUE-field case one
## container over:
##   - VERDICT: a comparison against an out-of-declared-range value that the
##     solver was free to pick is satisfiable when it should not be.
##   - WITNESS: an element/field the walker never itself read/dereffed on
##     the winning path stays entirely unconstrained in-solver (sound for
##     the verdict, which never depended on it) -- and the solver's own
##     default for a free bitvector can fall outside the declared range,
##     so reconstructing it into the SUT's own `range[lo..hi]`-typed slot
##     raises a real `RangeDefect` out of the caller's OWN test process.
##
## Every symbolic expectation below is paired with the same computation run
## for real in the same file (the #162 discipline): a range/width bug is
## exactly the shape where a test can encode the engine's own wrong model
## and pass. The "unread" witness tests reproduce the crash directly: the
## same value the pre-fix solver actually picked (empirically -- see the
## fix commits) fed into the SUT's own declared range type.

import std/unittest
import nelli/symex

proc readFirst(s: seq[range[0..100]]) =
  if s.len > 0 and s[0] > 100:
    symexTarget("big")

proc edgeInRange(s: seq[range[0..100]]) =
  if s.len > 0 and s[0] == 100:
    symexTarget("edge")

proc onlyLen(s: seq[range[50..60]]) =
  ## `s` is never indexed at all -- only `.len` is compared. Every element
  ## is "unread" in the sense the read-site (isIndex) fix cannot reach: it
  ## asserts bounds only on a value that is actually selected out of the
  ## backing array on the winning path.
  if s.len == 2:
    symexTarget("hit")

proc mkRange50to60(x: int): range[50..60] = range[50..60](x)

suite "#163 wiring-audit W2 -- seq[range[lo..hi]] elements reach the constraint":

  test "the oracle -- Nim itself refuses an out-of-range value at this width":
    expect RangeDefect:
      discard mkRange50to60(0)
    expect RangeDefect:
      discard mkRange50to60(101)
    check mkRange50to60(55) == 55

  test "a range-typed seq element's bounds reach the path condition":
    ## Was `sxSat`: with no constraint on the element, `s[0] > 100` was
    ## satisfiable for a seq declared `seq[range[0..100]]` -- the model
    ## picked `101`, itself already a `RangeDefect` waiting to happen.
    let r = symexFind(readFirst, tLabel("big"))
    check r.status == sxUnsat

  test "the bounds are a refinement, not a ban -- an in-range target survives":
    let r = symexFind(edgeInRange, tLabel("edge"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len > 0
      check r.witness[0][0] == 100

  test "an unread element's witness stays inside its declared range":
    ## The crash class. Empirically, an element the SUT never indexes
    ## extracts as the solver's bare default for a free bitvector -- `0` --
    ## which `range[50..60]` cannot hold. `s.len == 2` alone does not depend
    ## on any element value, so the verdict is correctly `sxSat` before and
    ## after the fix; only the WITNESS was ever wrong.
    let r = symexFind(onlyLen, tLabel("hit"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 2
      for e in r.witness[0]:
        check e in 50 .. 60
        discard mkRange50to60(e)  ## does not raise -- the point of the fix

# ---------------------------------------------------------------------------
# W4 -- range-typed fields of a `ref object`

type
  CfgR = ref object
    w: range[50'i32..60'i32]

proc mkCfgR(x: int32): CfgR = CfgR(w: x)

proc beyondR(c: CfgR) =
  if c != nil and c.w > 60'i32:
    symexTarget("impossible")

proc withinR(c: CfgR) =
  if c != nil and c.w == 55'i32:
    symexTarget("reachable")

proc twoRefs(c1, c2: CfgR) =
  ## `c2` is a second top-level param of the SAME ref type: it shares
  ## CfgR's per-TYPE field-split heap array with `c1` (`fieldHeapKey` keys
  ## on (objType, fieldName) alone, not on the address) but the SUT never
  ## itself dereferences or field-accesses `c2`.
  if c1 != nil and c1.w == 55'i32:
    symexTarget("hit")

suite "#163 wiring-audit W4 -- ref object range-typed fields reach the constraint":

  test "the oracle -- Nim itself refuses an out-of-range ref-object field":
    expect RangeDefect:
      discard mkCfgR(61'i32)
    expect RangeDefect:
      discard mkCfgR(0'i32)
    check mkCfgR(55'i32).w == 55'i32

  test "a range-typed ref field's bounds reach the path condition":
    ## Was `sxSat` (and, empirically, before this fix `symexFind` itself
    ## crashed with a real `RangeDefect` reconstructing this exact result --
    ## `c.w` is read only through the lazily-materialised field-split heap
    ## (`runtime_heap.nim`'s `isDeref`), which never asserted the declared
    ## bounds, so the model was free to pick `61` to satisfy `c.w > 60`).
    let r = symexFind(beyondR, tLabel("impossible"))
    check r.status == sxUnsat

  test "the bounds are a refinement, not a ban -- an in-range target survives":
    let r = symexFind(withinR, tLabel("reachable"))
    check r.status == sxSat

  test "an unread sibling ref sharing the field-split heap stays in range":
    ## The crash class, one container over from #162 slice 5's `Cfg32`.
    ## `c2` is never dereffed or field-accessed anywhere in `twoRefs`, so
    ## witness reconstruction has no observed value for it and instead
    ## materialises a FRESH, disconnected proto object, then evaluates that
    ## proto's fields under the already-solved model -- unconstrained, `w`
    ## extracted as the model's bare default `0`, and assigning `0` into
    ## `CfgR.w`'s declared `range[50..60]` raised `RangeDefect` out of the
    ## caller's own test process, even though `c1`'s OWN `w` was perfectly
    ## sound.
    let r = symexFind(twoRefs, tLabel("hit"))
    check r.status == sxSat  ## did not crash constructing this result

# ---------------------------------------------------------------------------
# Non-regression -- #162 slice 5's value-OBJECT field fix still holds

type
  BoxNonReg = object
    lo: range[0..100]
    hi: range[0..100]

proc beyondBoxNonReg(b: BoxNonReg) =
  if b.lo > 100:
    symexTarget("impossible")

proc withinBoxNonReg(b: BoxNonReg) =
  if b.lo == 100:
    symexTarget("reachable")

suite "#163 wiring-audit non-regression -- #162 slice 5 value-object fields":

  test "a value-object field's bounds still reach the path condition":
    let r = symexFind(beyondBoxNonReg, tLabel("impossible"))
    check r.status == sxUnsat

  test "an in-range value-object target still survives":
    let r = symexFind(withinBoxNonReg, tLabel("reachable"))
    check r.status == sxSat
