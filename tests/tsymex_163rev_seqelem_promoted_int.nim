## Discovered while building #163 review R22's seq-element-write site (see
## `tsymex_163rev_assign_sites.nim`'s site 3) -- a PRE-EXISTING defect,
## orthogonal to the RangeDefect-fork work itself.
##
## `storeSeqElem`'s `itInt` arm (`runtime.nim`) reads `val.bv8`/`bv16`/
## `bv32`/`bv64` directly, with no `svInt` handling at all -- unlike its two
## siblings at the OTHER two heap-write sites (`isDerefWrite`'s plain-field
## and arm-field branches, `runtime_heap.nim`), which both reconcile an
## `svInt` value to the array's BV sort before storing (the "N42 audit"
## idiom). `allocateSeqDataRaw`'s `itInt` arm always backs a `seq[T]` with a
## BV array regardless of whether `T` carries a declared range, so this
## reconciliation gap fires for ANY seq element write whose RHS is
## `svInt`-shaped -- not only a `range[lo..hi]`-typed element.
##
## The concrete trigger: with the engine's DEFAULT integer semantics
## (`isOptimised`), a range[lo..hi]-typed TOP-LEVEL PARAMETER promotes to an
## `svInt` (Z3 Int-sorted) representation at allocation time
## (`runSymexImpl`'s `promoteSound`), carrying `SymVal.ziIvl` for #161's
## static overflow-obligation discharge. Writing that promoted param's value
## directly into ANY int-family seq element (`ys[i] = x`) crashes
## `storeSeqElem` with an internal `FieldDefect` reconstructing `.bv64` on an
## `svInt`-kinded `SymVal` -- reported as `sxUnknown`/`weInternalWalkerFault`
## rather than the correct verdict, for a perfectly ordinary SUT.
##
## Fix: `storeSeqElem`'s `itInt` arm now reconciles an incoming `svInt` to
## the element type's declared BV width/signedness first, mirroring the
## EXACT coercion already established at `isDerefWrite`'s two write sites --
## no new sink, no new abstraction, the same fix applied a third time at
## the third place a range/int value gets stored into Z3.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

proc writePromotedParamIntoUnrangedSeq(xs: seq[int], i: int, x: range[0..100]) =
  ## `xs`'s element type carries NO declared range -- this crash is not
  ## about range checking at all, only about the promoted param's
  ## REPRESENTATION reaching the BV-backed store.
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = x
  symexTarget("t")
  discard ys[i]

proc writePromotedParamIntoRangedSeq(xs: seq[range[1..100]], i: int,
                                      x: range[10..90]) =
  ## The site 3 precision-case shape itself: a promoted, provably-in-range
  ## param written into a ranged seq element.
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = x
  symexTarget("t")
  discard ys[i]

suite "#163 review R22 site 3 prerequisite -- storeSeqElem reconciles a promoted svInt":

  test "a promoted param written into an UNRANGED seq element does not crash the walker":
    ## Before the fix: sxUnknown, r.errors[0].kind == weInternalWalkerFault
    ## (an internal FieldDefect reconstructing `.bv64` on an svInt SymVal).
    let r = symexFind(writePromotedParamIntoUnrangedSeq, tLabel("t"))
    check r.status == sxSat
    check r.errors.len == 0

  test "a promoted param written into a RANGED seq element does not crash the walker":
    let r = symexFind(writePromotedParamIntoRangedSeq, tLabel("t"))
    check r.status == sxSat
    check r.errors.len == 0


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138 (no bump owed -- storeSeqElem's own coercion mirrors an existing idiom; no new walker semantics)":
    check parseInt(symexWalkerVersion) >= 138
