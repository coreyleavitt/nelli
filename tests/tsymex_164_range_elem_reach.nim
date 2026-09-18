## Issue #163 wiring-audit finding W2 -- a declared `range[lo..hi]` silently
## evaporates for `seq[range[lo..hi]]` elements.
##
## Issue #162 slice 5 moved a range's bounds from `IRParam` onto `IRType`
## (in Nim, `range[lo..hi]` IS a type) so a value-object FIELD would inherit
## the constraint through `allocateSym`'s recursion. `ty.hasRange` has
## exactly ONE consumer in the whole runtime -- `allocateSym`'s `itInt`
## arm -- and a `seq[range[lo..hi]]` element never reaches it: a seq's
## data is a raw Z3 array (`allocateSeqDataRaw`), never a per-element
## allocation.
##
## Two consequences, both already fixed for the object-VALUE-field case one
## container over:
##   - VERDICT: a comparison against an out-of-declared-range value that the
##     solver was free to pick is satisfiable when it should not be.
##   - WITNESS: an element the walker never itself read (indexed) on the
##     winning path stays entirely unconstrained in-solver (sound for the
##     verdict, which never depended on it) -- and the solver's own default
##     for a free bitvector can fall outside the declared range, so
##     reconstructing it into the SUT's own `range[lo..hi]`-typed slot
##     raises a real `RangeDefect` out of the caller's OWN test process.
##
## Every symbolic expectation below is paired with the same computation run
## for real in the same file (the #162 discipline): a range/width bug is
## exactly the shape where a test can encode the engine's own wrong model
## and pass. The "unread" witness test reproduces the crash directly: the
## same value the pre-fix solver actually picked (empirically -- see the
## fix commit) fed into the SUT's own declared range type.

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
