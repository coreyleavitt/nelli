## Issue #163 review finding W8 -- `allocateSym`'s two `isIntOffset` arms
## (`runtime.nim`: the bare/non-tuple scan-offset return, and the traced
## tuple position) allocate a Z3-Int-sorted `svInt` directly for a call's
## fresh return placeholder, but previously IGNORED `ty.hasRange`/
## `ft.hasRange` -- a range-typed value materialised through either arm got
## no declared-range constraint, unlike the ordinary (non-offset) `itInt`
## allocation arm a few lines below (issue #162's own fix site), which
## already routed through `rangeCondsIfNeeded`.
##
## Fixed by routing both arms through `rangeCondsIfNeeded` too, which was
## ALSO extended with an `svInt` branch: it forwarded unconditionally to
## `bvRangeConds`, which dispatches on `v.kind` and silently returns `@[]`
## for `svInt` (sound for a BV-allocated value, a no-op -- and therefore
## WRONG -- for the `svInt` kind these two arms produce).
##
## Reachability, and why this took three prior attempts to pin: both arms
## are reached ONLY through `calleeIntOffsetReturnPositions`
## (`dsl_parser.nim`) -- a PARSE-TIME collector that recognizes a CALLEE's
## own body as a B3 (`tryMatchScanPairIdiomShape`, early-return-on-match) or
## B4 (`tryMatchAccumulatingScanIdiomShape`, accumulating scan) closed form,
## and marks the CALL's return position(s) so the caller's fresh retSym
## placeholder (`freshRetSym` -> `allocateSym`) allocates `svInt` directly.
## Q1/B0's skip-while idiom is NOT one of the two shapes this collector
## recognizes, so a callee written in that shape never reaches either arm at
## all -- confirmed by instrumentation below (no trace fires for it).
##
## The prior blocker was never about range-typing: three attempts hung or
## pinned nothing using shapes with a PLAIN-int loop counter and only a
## range-typed CALLEE RETURN type -- B3-shaped callees called through a real
## proc boundary were, at the time, believed to be a pre-existing Linux/
## podman non-termination (independent of this fix). That no longer
## reproduces: instrumentation (temporary stderr tracing in both arms,
## removed before this commit) confirms both arms fire with `hasRange=true`
## for a B3-shaped bare return and a B4-shaped tuple position, each reached
## through a genuine cross-proc call, and the whole suite completes in
## seconds. (Q1/B0's skip-while shape was also probed through a call
## boundary and terminates too, but -- as above -- never reaches either arm,
## so it is not part of this pin.)

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

# ---------------------------------------------------------------------------
# Bare (non-tuple) scan-offset return -- B3 early-return-on-match shape,
# range-typed CALLEE RETURN type.
# ---------------------------------------------------------------------------

proc findColonRangedEarly(s: string, offset: int): range[0..1000] =
  ## `calleeIntOffsetReturnPositions` recognizes this loop (B3 shape) purely
  ## by AST shape -- it never inspects the declared return type -- so this
  ## callee's return positions are marked, and `allocateSym`'s bare
  ## `isIntOffset` arm allocates the caller's placeholder for it.
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return i
    i = i + 1
  return i

proc callerBareEarly(s: string) =
  let p = findColonRangedEarly(s, 0)
  if p > 1000:
    symexTarget("impossible_bare_early")

suite "#163 review W8 -- the oracle (bare scan-offset return, B3 shape)":

  test "Nim itself never returns past the declared range -- it raises RangeDefect instead":
    check findColonRangedEarly("ab:cd", 0) == 2
    check findColonRangedEarly("abcde", 0) == 5   ## not found, short string: in range
    let tooFar = repeat('x', 1500)                ## not found, no ':' -- falls through past 1000
    expect RangeDefect:
      discard findColonRangedEarly(tooFar, 0)

suite "#163 review W8 -- bare scan-offset return: the placeholder keeps the callee's declared range":

  test "an out-of-range placeholder is unreachable (was falsely satisfiable pre-fix)":
    ## Before the fix: `allocateSym`'s bare `isIntOffset` arm allocated the
    ## call's fresh retSym as a bare `svInt` with no range assertion, so Z3
    ## was free to pick `p > 1000` for the placeholder even though the real
    ## callee's declared `range[0..1000]` return type makes that impossible
    ## (Nim itself would have raised `RangeDefect` first, per the oracle
    ## above) -- a false `sxSat` witness.
    let r = symexFind(callerBareEarly, tLabel("impossible_bare_early"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Traced tuple position -- B4 accumulating-scan shape, range-typed second
# tuple field.
# ---------------------------------------------------------------------------

proc scanAccRanged(s: string, offset: int): (string, range[0..1000]) =
  ## `calleeIntOffsetReturnPositions` recognizes this loop (B4 shape) and
  ## marks tuple position 1 (the "next scan position" field) as an
  ## int-offset position, so `allocateSym`'s traced-tuple-position arm
  ## allocates that field of the caller's placeholder.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  return (acc, i)

proc callerTuple(s: string) =
  let (_, p2) = scanAccRanged(s, 0)
  if p2 > 1000:
    symexTarget("impossible_tuple")

suite "#163 review W8 -- the oracle (traced tuple position, B4 shape)":

  test "Nim itself never returns past the declared range -- it raises RangeDefect instead":
    let (acc, off) = scanAccRanged("ab:cd", 0)
    check acc == "ab"
    check off == 3
    let (acc2, off2) = scanAccRanged("abcde", 0)  ## not found, short string: in range
    check acc2 == "abcde"
    check off2 == 5
    let tooFar = repeat('x', 1500)                ## not found, no ':' -- falls through past 1000
    expect RangeDefect:
      discard scanAccRanged(tooFar, 0)

suite "#163 review W8 -- traced tuple position: the placeholder keeps the callee's declared range":

  test "an out-of-range placeholder is unreachable (was falsely satisfiable pre-fix)":
    ## Before the fix: `allocateSym`'s traced-tuple-position arm allocated
    ## the field as a bare `svInt` with no range assertion -- same false
    ## `sxSat` mechanism as the bare arm above, at the OTHER call-return
    ## site the fix touches.
    let r = symexFind(callerTuple, tLabel("impossible_tuple"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Non-regression: Q1/B0's skip-while shape does not reach either arm at all
# (`calleeIntOffsetReturnPositions` only recognizes B3/B4), so it stays
# BV-allocated via the ordinary `itInt` route and is unaffected by this fix
# either way. Recorded so nobody mistakes its silence in the instrumentation
# for a third fixed site.
# ---------------------------------------------------------------------------

proc findColonSkipWhile(s: string, offset: int): range[0..1000] =
  var i = offset
  while i < s.len and s[i] != ':':
    inc i
  return i

proc callerBareSkipWhile(s: string) =
  let p = findColonSkipWhile(s, 0)
  if p > 1000:
    symexTarget("impossible_bare_skipwhile")

suite "#163 review W8 -- non-regression: Q1/B0 never reaches these arms":

  test "the skip-while shape still terminates and still respects the range (ordinary BV route)":
    let r = symexFind(callerBareSkipWhile, tLabel("impossible_bare_skipwhile"))
    check r.status == sxUnsat

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138":
    check parseInt(symexWalkerVersion) >= 138
