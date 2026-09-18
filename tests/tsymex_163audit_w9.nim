## Issue #163 audit W9 — the overflow-obligation guard keys on the LEFT
## operand's OWN stamp only.
##
## `lowerArith`'s two overflow-obligation guards (`runtime.nim`, the BV arm
## and its `svInt` sibling) both test `a.ziWidth`/`a.ziSigned` — the LEFT
## operand of the binop — never `b`'s. Integer literals are rescued by
## `coerceIntLit`'s proto-shaping (copies the surrounding expression's width
## onto the literal), so `x + 1` and `1 + x` both work. But a width-LESS
## `svInt` on the LEFT of a STAMPED operand on the RIGHT raises no
## obligation at all: `.len`'s lowering (`iekSeqLen`, `runtime.nim`) builds
## a bare `SymVal(kind: svInt, zi: recv.seqLen)` with `ziWidth: 0` (the Nim
## zero-value default) — no promotion site ever touches it — so `s.len * x`
## for a promoted range-typed `x` skips the fork entirely, where `x * s.len`
## (same values, operands swapped) already worked correctly.
##
## This is pre-existing, not a #161/#162 regression — but it is a hole in
## exactly the invariant #161's own header declares: the forbidden third
## state, an obligation neither discharged nor kept live.
##
## Method note (inherited from #162/#163 wave 1): every symbolic expectation
## is paired with the same computation run for real in this file — a taint/
## soundness bug is exactly the shape where a test can encode the engine's
## own wrong model and pass, and running Nim removes the model from the loop.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# A named `int`-typed bound, so the range's base type unifies with `.len`'s
# own `int` -- an un-annotated literal this large would default to `int64`
# (Nim: literals that do not fit `int32` default to `int64`), which would
# make `s.len * x` a plain type-mismatch rather than the shape under test.
const hugeBound: int = 9_000_000_000_000_000_000

# The repro. `s.len` (unstamped, LEFT) times a promoted huge-range param
# (stamped, RIGHT). A 2-element seq times ~9e18 reaches ~1.8e19 -- past
# int64.high (~9.223e18).
proc lenTimesParam(s: seq[int], x: range[0..hugeBound]) =
  let c = s.len * x
  symexTarget("t")
  discard c

# The mirror: SAME values, operands swapped. `x` (stamped) is now on the
# LEFT, `s.len` (unstamped) on the RIGHT -- the shape the guard already
# handled correctly. Pinned unchanged so the fix cannot regress the common
# path while closing the gap above.
proc paramTimesLen(s: seq[int], x: range[0..hugeBound]) =
  let c = x * s.len
  symexTarget("t")
  discard c

# The over-constraint guard. `x` here is narrow enough that even at the
# `.len` allocation ceiling (1024, `allocateSym`'s itSeq arm) the product
# cannot leave int64's window: 1024 * 1000 = 1_024_000. The fix must not
# manufacture a reachable overflow where none exists.
proc lenTimesSmallParam(s: seq[int], x: range[0..1000]) =
  let c = s.len * x
  symexTarget("t")
  discard c

suite "#163 W9 -- overflow guard must key on EITHER operand's stamp":

  test "the oracle -- Nim itself raises OverflowDefect for len(2) * ~9e18":
    proc rt(s: seq[int], x: range[0..hugeBound]): int = s.len * x
    expect OverflowDefect:
      discard rt(@[1, 2], hugeBound)

  test "unstamped .len on the LEFT of a stamped param still finds the overflow":
    ## The load-bearing property. Was `sxUnsat` (false negative): the guard
    ## never even built the fork because `a` (`s.len`) carried no stamp.
    let r = symexFind(lenTimesParam, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "non-regression -- stamped param on the LEFT, .len on the RIGHT, unchanged":
    ## Same values, operands swapped. This shape already worked before the
    ## fix (the guard reads `a`'s stamp, and `a` here is the promoted `x`);
    ## it must keep working identically after.
    let r = symexFind(paramTimesLen, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "a genuinely in-range product is not over-constrained into a false overflow":
    ## `x` is narrow enough that no achievable `.len` (capped at 1024) can
    ## push the product outside int64. The fix borrows a stamp; it must not
    ## invent a reachable defect that was never real.
    let r = symexFind(lenTimesSmallParam, tRaisedExn("OverflowDefect"))
    check r.status == sxUnsat

  test "the in-range case still reaches its ordinary target":
    ## Complement of the above -- the fix must not suppress the ordinary
    ## (non-defect) path either.
    let r = symexFind(lenTimesSmallParam, tLabel("t"))
    check r.status == sxSat
