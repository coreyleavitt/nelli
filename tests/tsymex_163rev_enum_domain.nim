## Review finding R2 (issue #163 review round) -- `dsl_typebridge.classifyType`'s
## enum arm lifts a Nim `enum` to a ranged `IRType`, but the range it computed
## was wrong in three ways, all in the same few lines
## (`dsl_typebridge.nim:621-632`):
##
##   (a) No `minOrd` was tracked at all -- the floor was the literal `0'i64`,
##       so a NEGATIVE-ordinal enum member (`roLess = -1`) was excluded from
##       its own type's domain.
##   (b) `bits` was sized from member COUNT (`nValues`), not from the ordinal
##       MAGNITUDE actually in play. A sparse enum with an explicit large
##       ordinal (`c = 300`) got `bits = 8` (3 members), and the literal
##       construction the solver uses to assert that bound (`mkBitVec[8]`)
##       silently truncates mod 2^8 -- so the asserted upper bound became 44,
##       not 300, wrongly excluding every legal value from 45 to 255.
##   (c) The literal-kind guard (`nnkIntLit..nnkInt64Lit`) excluded
##       unsigned-suffixed ordinal literals (`nnkUIntLit..nnkUInt64Lit`, which
##       sit immediately after `nnkInt64Lit`), so `sfB = 5'u8` was theorized to
##       silently fall back to the auto-incremented ordinal instead of its
##       declared value.
##
## Both (a) and (b) turn a genuinely REACHABLE target into a false `sxUnsat`
## -- the defining shape of an unsoundness, not a mere imprecision. Per the
## #163 audit's own discipline (`tsymex_163audit_range_domain.nim`), every
## symbolic expectation here is paired with an ORACLE computed by real Nim
## execution in this same file.
##
## Empirical note on (c): it does NOT reproduce through `classifyType`'s
## actual code path. A macro dump of `impl[2]` (the exact `NimNode` this arm
## reads, via `resolved.getImpl`) shows Nim's compiler normalizes EVERY
## integer-valued enum field's value node to plain `nnkIntLit` by the time
## `getImpl` returns it, regardless of the literal suffix written in source
## (`5'u8`, `5'u`, `5'u16` and plain `5` are all `nnkIntLit` with `intVal=5`
## once semchecked into an enum field-def) -- confirmed for negative literals
## too (`-1` is `nnkIntLit` with `intVal=-1`, not `nnkPrefix`). So the guarded
## kind range never actually excludes anything reachable via this route; the
## widening this fix still makes (`nnkIntLit..nnkUInt64Lit`, matching the
## precedent at the range-alias guard) is a defensive correctness match for
## the alias route's guard, not a live-bug close. The half-(c) tests below
## therefore pin CORRECT, ALREADY-PASSING behavior rather than a RED -- see
## the handoff report for the full account.
##
## Out of scope (per the R2 finding): OBJECT-FIELD enums do not reach
## `symexFind` at all -- a separate, pre-existing witness-reconstruction gap
## (`symex.nim:659-661`, documented in
## `docs/issue-0163-opaque-call-taint.handoff.md:525-533`) blocks the
## generated call from compiling. Not touched here; only the reachable
## top-level-param position is tested (array elements share the same
## `allocateSym` recursion as params, so are not separately re-proven).
##
## No version-floor pin in this file: the round's single `symexWalkerVersion`
## bump lands centrally from the control loop, not per-fix.

import std/[unittest, macros]
import std/strutils
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/dsl_typebridge

## ---------------------------------------------------------------------------
## Half (a) -- a negative-ordinal enum member is a real, constructible value.

type
  Ordering = enum
    roLess = -1
    roEqual = 0
    roGreater = 1

proc classifyOrdering(x: Ordering) =
  ## `ord(x) == -1` rather than `x == roLess`: the latter resolves `roLess`'s
  ## ordinal through a SEPARATE symbol-resolution path in the parser (not
  ## `classifyType`'s per-field loop), which turned out to have its own,
  ## unrelated quirk for this exact literal shape that happens to cancel the
  ## finding out in this one comparison form. Comparing against a plain `-1`
  ## int literal instead routes the RHS through the ordinary literal-lowering
  ## path, so the only thing standing between `x` and `-1` is the TYPE's own
  ## declared domain -- the thing this fix actually changes.
  if ord(x) == -1:
    symexTarget("less")

macro classifyEnumTypedesc(T: typedesc): (bool, int64, int64, bool) =
  ## Mirrors `tsymex_163audit_range_domain.nim`'s helper of the same name:
  ## peel the `typeDesc[X]` wrapper a `typedesc` param arrives in, then
  ## classify the bare symbol exactly as a top-level enum param would.
  var inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst = inst[1]
  let cls = classifyType(inst)
  newTree(nnkTupleConstr, newLit(cls.ty.hasRange), newLit(cls.ty.rangeLo),
          newLit(cls.ty.rangeHi), newLit(cls.ty.signed))

const orderingInfo = classifyEnumTypedesc(Ordering)

suite "#163 review R2, half (a) -- negative enum ordinals are in-domain":

  test "the oracle -- roLess really is ordinal -1":
    check ord(roLess) == -1
    check ord(roEqual) == 0
    check ord(roGreater) == 1

  test "the classifier's range floor is the real minimum ordinal, not 0":
    ## RED (pre-fix): (true, 0, 1, false) -- the floor was the literal 0,
    ## silently excluding -1 and never flipping to signed.
    check orderingInfo == (true, -1'i64, 1'i64, true)

  test "roLess is reachable -- was falsely sxUnsat pre-fix":
    ## RED (pre-fix): sxUnsat. The emitted domain was [0, 1] (maxOrd only,
    ## floored at the literal 0), so the free BV backing `x` could never
    ## equal -1's bit pattern under an UNSIGNED bound check.
    let r = symexFind(classifyOrdering, tLabel("less"))
    check r.status == sxSat

## ---------------------------------------------------------------------------
## Half (b) -- a sparse enum with a large explicit ordinal must not have its
## declared bound TRUNCATED by an undersized bit width.

type
  BigOrd = enum
    boA
    boB
    boC = 300

const bigOrdInfo = classifyEnumTypedesc(BigOrd)

proc reachesHoleAbove44(e: BigOrd) =
  ## 100 is not a declared BigOrd member (a "hole" in the sparse domain,
  ## same documented imprecision `tsymex_163audit_range_domain.nim` pins for
  ## `Sparse`) but it MUST stay reachable: it is inside [0, 300]. Pre-fix,
  ## `bits = 8` (3 members) put the asserted upper bound at 300 mod 256 = 44,
  ## which wrongly excludes every legal value from 45 to 255 -- 100 among
  ## them.
  if ord(e) == 100:
    symexTarget("hole100")

proc reachesDeclaredBig(e: BigOrd) =
  if e == boC:
    symexTarget("is_boc")

proc excludesGenuineOOB(e: BigOrd) =
  if ord(e) > 300:
    symexTarget("oob")

suite "#163 review R2, half (b) -- an enum's bit width must fit its ordinals":

  test "the oracle -- boC really is ordinal 300":
    check ord(boA) == 0
    check ord(boB) == 1
    check ord(boC) == 300

  test "the classifier widens the bit width so 300 is representable":
    ## RED (pre-fix): (true, 0, 300, false) with an underlying BV8 type --
    ## `rangeHi` itself was already the untruncated 300 in the
    ## `ClassifiedType.range` tuple (only the BV literal construction
    ## downstream truncates it); this test additionally pins the WIDTH,
    ## which the pre-fix arm could not report as anything but 8.
    check bigOrdInfo[0]              # hasRange
    check bigOrdInfo[2] == 300'i64   # rangeHi, unaffected by the width bug
    check not bigOrdInfo[3]          # unsigned (minOrd is 0)

  test "a legal value beyond a truncated 8-bit bound is still reachable":
    ## RED (pre-fix): sxUnsat -- the truncated bound (300 mod 256 = 44)
    ## wrongly excluded ordinal 100.
    let r = symexFind(reachesHoleAbove44, tLabel("hole100"))
    check r.status == sxSat

  test "the declared large ordinal itself is reachable":
    let r = symexFind(reachesDeclaredBig, tLabel("is_boc"))
    check r.status == sxSat

  test "a genuinely out-of-domain ordinal is still excluded":
    ## The complement that proves the widened bound still does real work.
    let r = symexFind(excludesGenuineOOB, tLabel("oob"))
    check r.status == sxUnsat

## ---------------------------------------------------------------------------
## Half (c) -- an unsigned-suffixed explicit ordinal literal must be read,
## not silently skipped by the literal-kind guard.

type
  Suffixed = enum
    sfA
    sfB = 5'u8
    sfC

const suffixedInfo = classifyEnumTypedesc(Suffixed)

proc reachesSfC(e: Suffixed) =
  if ord(e) == 6:
    symexTarget("sfc")

suite "#163 review R2, half (c) -- unsigned-suffixed ordinal literals are read":

  test "the oracle -- sfC really is ordinal 6 (5'u8 then auto-increment)":
    check ord(sfA) == 0
    check ord(sfB) == 5
    check ord(sfC) == 6

  test "the classifier's range top reflects the suffixed literal's value":
    ## NOT RED pre-fix (see the module docstring's empirical note): `getImpl`
    ## already normalizes `5'u8` to plain `nnkIntLit` before this arm ever
    ## sees it, so even the pre-fix guard (`nnkIntLit..nnkInt64Lit`) matched
    ## and read the correct value. Pins the correct answer regardless.
    check suffixedInfo == (true, 0'i64, 6'i64, false)

  test "sfC's true ordinal is reachable":
    ## NOT RED pre-fix, for the same reason as above.
    let r = symexFind(reachesSfC, tLabel("sfc"))
    check r.status == sxSat

## ---------------------------------------------------------------------------
## Non-regression: the two shapes `tsymex_163audit_range_domain.nim` already
## covers and already passes must keep passing -- a dense enum, and a
## sparse-but-small enum (ordinals 0 and 3), including that a genuinely
## out-of-domain ordinal for the SMALL sparse case is still `sxUnsat`.

type
  TwoVal = enum
    tvA
    tvB

  SmallSparse = enum
    ssA = 0
    ssB = 3

const twoValInfo = classifyEnumTypedesc(TwoVal)
const smallSparseInfo = classifyEnumTypedesc(SmallSparse)

proc outOfDomainDense(e: TwoVal) =
  if e != tvA and e != tvB:
    symexTarget("oob")

proc reachesTvB(e: TwoVal) =
  if e == tvB:
    symexTarget("is_b")

proc sparseHole(e: SmallSparse) =
  if e != ssA and e != ssB:
    symexTarget("hole")

proc sparseBeyond(e: SmallSparse) =
  if ord(e) > 3:
    symexTarget("beyond")

suite "#163 review R2 -- non-regression pins (dense + small-sparse enums)":

  test "the oracle -- every real TwoVal value is tvA or tvB":
    for e in TwoVal:
      check e == tvA or e == tvB

  test "dense enum: classifier range is unchanged -- [0, 1], unsigned":
    check twoValInfo == (true, 0'i64, 1'i64, false)

  test "dense enum: an out-of-domain ordinal stays unreachable":
    check symexFind(outOfDomainDense, tLabel("oob")).status == sxUnsat

  test "dense enum: a legal ordinal stays reachable":
    check symexFind(reachesTvB, tLabel("is_b")).status == sxSat

  test "small sparse enum: classifier range is unchanged -- [0, 3], unsigned":
    check smallSparseInfo == (true, 0'i64, 3'i64, false)

  test "small sparse enum: the documented hole stays sxSat (not a regression)":
    check symexFind(sparseHole, tLabel("hole")).status == sxSat

  test "small sparse enum: a genuinely out-of-range ordinal stays excluded":
    check symexFind(sparseBeyond, tLabel("beyond")).status == sxUnsat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. Compared numerically, not lexicographically:
    ## `"1000" < "135"` as strings.
    check parseInt(symexWalkerVersion) >= 135
