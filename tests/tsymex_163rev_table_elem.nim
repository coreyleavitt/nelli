## Issue #163 review finding R4 -- `extractTableEntries` (runtime.nim) never
## checks `sv.tabValTy.hasRange` and never clamps, unlike its three sibling
## extractors (`extractSeqElements`, `extractFromSymVal`'s ref-object-field
## arm, `renderLeafFieldAt`). Commit a4ec45f ("#163 audit W2 -- seq[range
## [lo..hi]] elements reach the bound") mirrored the CONSTRAINT side for
## Table reads (`tblRangeConds` at the `isIndex`/svTable site,
## runtime.nim:9339-9343) but never touched the WITNESS-CLAMP side for
## `extractTableEntries` -- the exact gap `extractSeqElements` already had
## to close for `seq[range[lo..hi]]` one container over.
##
## The escalation: `collectTableLitKeys`/`collectTableLitKeysExpr` is a pure
## STATIC scan of the whole `prog.body` (both branches of every `if`,
## `while`, `try`), run once per Table param BEFORE any path walking. A
## literal key referenced ANYWHERE lands in `tabKeys[paramName]`, regardless
## of which path the solver actually walks. Presence and the range
## constraint are asserted only by the `isIndex` walk site itself, on
## whichever path executes it. So a key that is only ever READ on a branch
## the winning path does NOT take is still extracted by
## `extractTableEntries` (its literal is in `tabKeys`) but was never range-
## constrained on this path -- worse than the seq case: the seq fix
## constrains every INDEX 0..<len uniformly, but Table's per-key constraint
## is genuinely path-conditional.
##
## Every symbolic expectation below is paired with the same computation
## run for real in the same file (the #162/#163 discipline): a range/width
## bug is exactly the shape where a test can encode the engine's own wrong
## model and pass.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

proc mkRange50to60(x: int): range[50..60] = range[50..60](x)

suite "#163 review R4 -- Table[string, range[lo..hi]] values reach the declared bound":

  test "the oracle -- Nim itself refuses an out-of-range value at this width":
    expect RangeDefect:
      discard mkRange50to60(0)
    expect RangeDefect:
      discard mkRange50to60(101)
    check mkRange50to60(55) == 55

  test "a range-typed Table value's bounds reach the path condition (non-regression)":
    ## Pins the constraint side (`tblRangeConds`, commit a4ec45f) already
    ## wired at the `isIndex`/svTable site: a read that IS on the winning
    ## path cannot pick an out-of-range value.
    proc probeBig(t: Table[string, range[0..100]]) =
      if t["a"] > 100:
        symexTarget("big")
    let r = symexFind(probeBig, tLabel("big"))
    check r.status == sxUnsat

  test "the bounds are a refinement, not a ban -- an in-range target survives":
    proc probeEdge(t: Table[string, range[0..100]]) =
      if t["a"] == 100:
        symexTarget("edge")
    let r = symexFind(probeEdge, tLabel("edge"))
    check r.status == sxSat
    if r.status == sxSat:
      check "a" in r.witness[0]
      check r.witness[0]["a"] == 100

  test "an unread key's witness stays inside its declared range":
    ## The crash class (R4, High). `"a" in t` forces presence of "a" true
    ## on the winning path (`iekContains` lowers straight to a boolean
    ## `select` on the presence array, asserted via the `if` itself -- no
    ## fork/isIndex needed), so `extractTableEntries` DOES extract a value
    ## for "a" (present == true in the model). But the `flag == false`
    ## branch below never executes `t["a"]` (the `isIndex` statement that
    ## is the ONLY site asserting `tblRangeConds`), so the raw value at
    ## key "a" is entirely free in the model. `t.len == 1` alone does not
    ## depend on any table VALUE, so the verdict is correctly `sxSat`
    ## before and after the fix; only the WITNESS was ever wrong.
    proc probeUnread(t: Table[string, range[50..60]], flag: bool) =
      if "a" in t:
        if flag:
          discard t["a"]
        else:
          if t.len == 1:
            symexTarget("hit")
    let r = symexFind(probeUnread, tLabel("hit"))
    check r.status == sxSat
    if r.status == sxSat:
      check "a" in r.witness[0]
      let v = r.witness[0]["a"]
      check v in 50 .. 60
      discard mkRange50to60(v)  ## does not raise -- the point of the fix

  test "a key that IS read on the winning path still solves correctly (non-regression)":
    proc probeReadWinning(t: Table[string, range[50..60]], flag: bool) =
      if flag:
        if t["a"] == 55:
          symexTarget("hit2")
    let r = symexFind(probeReadWinning, tLabel("hit2"))
    check r.status == sxSat
    if r.status == sxSat:
      check "a" in r.witness[0]
      check r.witness[0]["a"] == 55
      discard mkRange50to60(r.witness[0]["a"])  ## does not raise


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. Compared numerically, not lexicographically:
    ## `"1000" < "135"` as strings.
    check parseInt(symexWalkerVersion) >= 135
