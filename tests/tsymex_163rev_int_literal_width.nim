## Issue #163 item 2 (rev) -- an un-suffixed int literal above `int32.high`
## defaults to `int64` in real Nim; confirmed the engine modeled it at a
## DIFFERENT (narrower) width in one concrete shape, and fixed it.
##
## REPRODUCED (this session, `scratchpad/probe_163item2_symex_width.nim` /
## `scratchpad/probe_163item2_treerepr.nim`, not committed): `a: int32`
## compared directly against the untyped literal `3_000_000_000` COMPILES in
## real Nim -- `treeRepr`/`getTypeInst` confirm the compiler inserts an
## `nnkHiddenStdConv` widening `a` from `int32` to `int64` (the literal
## itself is already typed `int64`, since it does not fit `int32`), so the
## comparison happens entirely at 64 bits. `a > 3_000_000_000` is therefore
## UNSATISFIABLE for every possible `int32` value (`int32.high` is
## 2_147_483_647, far below three billion).
##
## Before this fix, `dsl_parser.parseExpr`'s `nnkHiddenStdConv` arm was a
## BLIND pass-through (`parseExpr(n[n.len-1], ...)`), justified only for the
## representation-preserving subrange-strip case (`range[T]` -> its base
## type). Applied to a genuine WIDTH-changing hidden conversion, it parsed
## `a` at its narrow (32-bit) width with no record of the widening; the
## comparison's literal then got folded into a same-sized BV downstream and
## silently WRAPPED (`3_000_000_000` truncated into 32 bits reads back as
## the negative `-1_294_967_296`), so `symexFind` reported `sxSat` with
## witness `a = -1294967295` for a target genuinely unreachable in real Nim
## -- a soundness bug (a false SAT), not merely an imprecision.
##
## THE FIX: the same `nnkHiddenStdConv`/`nnkHiddenSubConv` arm now detects a
## genuine width change between the hidden conversion's own resolved type
## and its wrapped operand's type (`classifyType(n).ty.width !=
## classifyType(wrapped).ty.width`) and routes it through the same
## `mkConvIntWidth` widening machinery the explicit `nnkConv` case already
## used. A same-width hidden conversion (the subrange-strip case, and
## `nnkHiddenAddr`) is untouched.
##
## House rule: every symbolic expectation is paired with an oracle computed
## by real Nim execution in this same file.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

proc reachOversizedLiteral(a: int32) =
  if a > 3_000_000_000:
    symexTarget("hit")

proc reachOversizedLiteralLe(a: int32) =
  ## The mirror comparison direction -- `a >= 3_000_000_001` reduces to the
  ## same width question from the other side, catching a fix that only
  ## patches one specific infix spelling.
  if a >= 3_000_000_001:
    symexTarget("hit")

suite "#163 item 2 -- an oversized untyped literal compared against a narrower int":

  test "oracle -- no int32 value satisfies a > 3_000_000_000":
    check int32.high.int64 < 3_000_000_000'i64
    for a in [int32.low, -1'i32, 0'i32, 1'i32, int32.high]:
      check not (a > 3_000_000_000)
      check not (a >= 3_000_000_001)

  test "the comparison genuinely compiles as a real Nim widening (not a type error)":
    # If this ever stopped compiling, the whole scenario would be moot --
    # pin that the widening conversion this fix relies on is real.
    var a: int32 = 5
    let ok = a > 3_000_000_000
    check ok == false

  test "RED (pre-fix): symex must agree the target is UNSAT, not falsely SAT":
    let r = symexFind(reachOversizedLiteral, tLabel("hit"))
    check r.status == sxUnsat

  test "the mirror comparison direction agrees too":
    let r = symexFind(reachOversizedLiteralLe, tLabel("hit"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Non-regression: a literal that genuinely IS reachable at the operand's
# real (widened) width must still be found -- the fix must not overcorrect
# into banning every oversized literal outright.
# ---------------------------------------------------------------------------

proc reachViaWideParam(a: int) =
  ## `a` is a plain 64-bit `int` -- no hidden conversion at all here (both
  ## operands are already int64) -- must be unaffected by this fix.
  if a > 3_000_000_000:
    symexTarget("hit")

suite "#163 item 2 non-regression -- a same-width (no hidden conv) oversized literal comparison":

  test "oracle -- a plain 64-bit int can genuinely exceed 3 billion":
    check 4_000_000_000 > 3_000_000_000

  test "symex still finds it reachable":
    let r = symexFind(reachViaWideParam, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] > 3_000_000_000


# ---------------------------------------------------------------------------
# #163 item 2 follow-up (review round 9). The discrimination gate above only
# recognized width changes between a CLOSED set of plain fixed-width int
# spellings (`isIntFamilyName(valueTypeName(...))`). `valueTypeName` reads
# `getTypeInst`, which for a value whose DECLARED type is a named
# `range[lo..hi]` alias or an `enum` reports that alias/enum's own NAME (e.g.
# "SmallCount"), never a plain int spelling -- so a genuine width-changing
# hidden conversion on either shape fell to the untouched identity
# pass-through: structurally the exact same hazard the flagship case above
# closed for plain `int32`, just gated shut by name rather than by width.
#
# Empirically verified (scratchpad/probe_163item2b_*, not committed) BEFORE
# fixing the gate:
#   - A SIGNED range-alias TOP-LEVEL PARAM (`proc f(a: SmallCount)`) was
#     ALREADY sound despite the gap: `promoteSound` (issue #161) lifts a
#     signed, proven-range top-level param straight to Z3's unbounded Int
#     theory at allocation, bypassing the BV-width class of bug entirely.
#     Confirmed with both a narrow (0..100) and a near-full-width
#     (-2e9..2e9) range -- both already `sxUnsat`. Kept below as a
#     non-regression pin, not a repro.
#   - The SAME range-alias type used as an OBJECT FIELD reproduced the exact
#     false `sxSat` the flagship case closed for plain `int32` -- witness
#     `f = 0`, even though real Nim's `f > 3_000_000_000` is false for every
#     legal value 0..100 (`promoteSound` promotes only top-level params,
#     never a field).
#   - A LOCAL VARIABLE of the same range-alias type reproduced it too, for
#     the same reason.
#   - An UNSIGNED range-alias param (never `promoteSound`-eligible) happened
#     to stay sound only because 3_000_000_000 fits an unsigned 32-bit
#     window without wrapping -- not a proof the class was safe, just a
#     literal that didn't stress it. Included below as a non-regression pin.
#
# THE FIX: the shared `nnkHiddenStdConv`/`nnkHiddenSubConv`/`nnkHiddenAddr`
# arm now reads the width/signedness it needs directly off the `IRType`s
# `classifyType` already computes for both sides of the conversion
# (`outerTy`/`innerTy`) -- which correctly resolve a range alias's base
# width (`rangeBaseType`, issue #162) and an enum's lifted width
# (`enumOrdBitsNeeded`, issue #163 R2) -- instead of re-deriving them from a
# second, name-based lookup. A carve-out preserves the existing
# `promoteSound` safety net for the one shape it protects (a bare reference
# to the CURRENT proc's own signed, ranged, top-level PARAM): routing that
# shape through the width-conversion primitive too regressed a correct
# `sxUnsat` to `sxUnknown` (`mkConvIntWidth`'s walker assumes a raw BV
# operand, which a `promoteSound`-promoted param is not) -- confirmed
# empirically and left as the untouched identity pass-through.
#
# House rule: every symbolic expectation below is paired with an oracle
# computed by real Nim execution in this same file.

type SmallCount = range[0'i32..100'i32]
type USmallCount = range[0'u32..100'u32]

proc reachRangeAliasParam(a: SmallCount) =
  ## Non-regression: a signed ranged TOP-LEVEL PARAM is `promoteSound`-
  ## protected already -- must stay `sxUnsat` whether or not the
  ## discrimination gate itself recognizes the alias name.
  if a > 3_000_000_000:
    symexTarget("hit")

proc reachUnsignedRangeAliasParam(a: USmallCount) =
  ## Non-regression: an unsigned ranged param is never `promoteSound`-
  ## eligible, but 3_000_000_000 fits an unsigned 32-bit window without
  ## wrapping either way -- must stay `sxUnsat`.
  if a > 3_000_000_000'u32:
    symexTarget("hit")

type RangeFieldRec = object
  f: SmallCount

proc reachRangeAliasField(r: RangeFieldRec) =
  ## THE REPRO: a range-typed OBJECT FIELD is never `promoteSound`-eligible
  ## (only top-level params are), so before the fix this fell to the
  ## unconditional identity pass-through and produced a false `sxSat`.
  if r.f > 3_000_000_000:
    symexTarget("hit")

proc reachRangeAliasLocal(seed: int32) =
  ## THE REPRO, local-variable variant: a `let`/`var` local of a range-alias
  ## type is likewise never `promoteSound`-eligible.
  let x: SmallCount = 5'i32
  if x > 3_000_000_000:
    symexTarget("hit")

suite "#163 item 2 follow-up -- range-alias discrimination-gate gap":

  test "oracle -- no SmallCount (0..100, signed base int32) value satisfies a > 3_000_000_000":
    for a in [SmallCount(0'i32), SmallCount(1'i32), SmallCount(100'i32)]:
      check not (a.int64 > 3_000_000_000'i64)

  test "oracle -- no USmallCount (0..100, unsigned base uint32) value satisfies a > 3_000_000_000":
    for a in [USmallCount(0'u32), USmallCount(1'u32), USmallCount(100'u32)]:
      check not (a.uint64 > 3_000_000_000'u64)

  test "oracle -- no legal RangeFieldRec.f value satisfies f > 3_000_000_000":
    for fv in [0'i32, 1'i32, 100'i32]:
      let r = RangeFieldRec(f: SmallCount(fv))
      check not (r.f.int64 > 3_000_000_000'i64)

  test "non-regression -- a signed range-alias TOP-LEVEL PARAM stays sound (promoteSound)":
    let r = symexFind(reachRangeAliasParam, tLabel("hit"))
    check r.status == sxUnsat

  test "non-regression -- an unsigned range-alias param stays sound":
    let r = symexFind(reachUnsignedRangeAliasParam, tLabel("hit"))
    check r.status == sxUnsat

  test "RED (pre-fix): a range-typed OBJECT FIELD must agree the target is UNSAT":
    let r = symexFind(reachRangeAliasField, tLabel("hit"))
    check r.status == sxUnsat

  test "RED (pre-fix): a range-typed LOCAL VARIABLE must agree the target is UNSAT":
    let r = symexFind(reachRangeAliasLocal, tLabel("hit"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Non-regression: the fix must not disturb a genuinely SAME-WIDTH hidden
# conversion on a range-alias/enum-carrying value (subrange strip, an
# `nnkHiddenAddr` var-param, or an already-correct-width literal) -- those
# must still fall straight through untouched, exactly as the pre-existing
# `tsymex_163rev_parser_gaps.nim` char-range suite and
# `tsymex_163audit_range_domain.nim`'s enum-domain suite already pin.
# ---------------------------------------------------------------------------

type Color = enum
  cRed, cGreen, cBlue

proc reachEnumWidenViaOrd(c: Color) =
  ## `ord(c)` (a magic intrinsic, not this arm's hidden-stdconv path -- see
  ## this file's own header note below) already resolves to a native 64-bit
  ## `int` in the typed AST, so comparing it against a small in-range
  ## literal is a SAME-WIDTH case end to end and must stay reachable exactly
  ## as before.
  if ord(c) > 1:
    symexTarget("hit")

suite "#163 item 2 follow-up -- same-width pass-through stays untouched":

  test "oracle -- ord(cBlue) truly is 2, which is > 1, and no Color ordinal exceeds 1":
    check ord(cBlue) > 1
    check not (ord(cRed) > 1)
    check not (ord(cGreen) > 1)

  test "an enum ord() comparison within native-int width is still reachable":
    let r = symexFind(reachEnumWidenViaOrd, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == cBlue

# NOTE: probing the enum case above once surfaced a DIFFERENT false-`sxSat`
# -- not through this arm, and left as a recorded follow-up rather than
# fixed here. That follow-up is now closed by the fix below.

# ---------------------------------------------------------------------------
# #163 -- the ord() magic intercept identity-passes its argument at the
# ARGUMENT's own classified width, not ord's declared native-int RETURN
# width.
#
# `ord`'s declared signature is `proc ord*[T](x: T): int` -- its result is
# always native (64-bit signed) `int`. `dsl_parser.nim`'s `ord()` intercept
# used to `return parseExpr(n[1], ...)` unconditionally whenever the
# argument itself classified to `itInt` -- an identity pass-through at the
# ARGUMENT's own width. For a plain `int`/Rune argument that coincides with
# `ord`'s declared 64-bit return width, so no bug was visible there; an
# ENUM argument classifies at its own lifted, narrow width
# (`enumOrdBitsNeeded` -- e.g. 2 bits for a 3-member enum), and a `char`
# argument classifies at 8 bits.
#
# Reproduced empirically (scratchpad/probe_163ord_treerepr.nim,
# probe_163ord_types.nim, probe_163ord_fix.nim, not committed) BEFORE
# fixing: `treeRepr`/`getTypeInst` confirm the compiler wraps the whole
# `ord(c)` CALL in an `nnkHiddenStdConv` for the surrounding comparison, but
# that wrapper's own `getTypeInst` (`int64`) already MATCHES the Call
# node's own `getTypeInst` (`int`) -- so the generic `nnkHiddenStdConv`
# widening arm (the fix above in this file) sees no width mismatch at that
# level and recurses straight into the `ord()` "nnkCall" handling, which is
# where the bug actually lived. `symexFind` on the PARAM shape below
# returned `sxSat` with witness `cGreen`; the same false `sxSat` reproduced
# for an enum LOCAL, an enum OBJECT FIELD, and `ord()` bound to a `let`
# outside any comparison. A `char` argument reproduced it too (`ord(ch) >
# 3_000_000_000` -- no `char` can ever satisfy that; `ord` tops out at 255).
#
# THE FIX: the same site now reads `outerTy` off `classifyType` for the
# `ord(...)` CALL node `n` itself (which resolves `ord`'s declared `int`
# return type, always native width) and `innerTy` off the argument `n[1]`
# (the enum's own lifted width, or a range alias's own width via
# `rangeBaseType`). A genuine width change routes through the SAME
# `mkConvIntWidth` widening machinery the two fixes above use, sharing the
# identical `isPromoteSoundEligibleParam` carve-out -- now factored into one
# proc both call sites share, rather than two independent copies of the
# same rule that could drift: `ord` of a bare reference to the current
# proc's own signed, ranged, top-level param stays an untouched identity
# pass-through, because `promoteSound` (issue #161) already promoted it to
# an unbounded Z3 Int with no BV modulus to wrap against.
#
# House rule: every symbolic expectation below is paired with an oracle
# computed by real Nim execution in this same file.
# ---------------------------------------------------------------------------

type OrdRec = object
  c: Color

type SmallRange163 = range[0'i32..5'i32]

proc ordEnumParam(c: Color) =
  ## THE REPRO (param).
  if ord(c) > 3_000_000_000:
    symexTarget("hit")

proc ordEnumLocal() =
  ## THE REPRO (local).
  var c: Color = cGreen
  if ord(c) > 3_000_000_000:
    symexTarget("hit")

proc ordEnumField(r: OrdRec) =
  ## THE REPRO (object field).
  if ord(r.c) > 3_000_000_000:
    symexTarget("hit")

proc ordCharParam(ch: char) =
  ## THE REPRO (char) -- ord(char) tops out at 255, nowhere near 3e9.
  if ord(ch) > 3_000_000_000:
    symexTarget("hit")

proc ordRangeAliasParam(x: SmallRange163) =
  ## Non-regression: a signed ranged TOP-LEVEL PARAM stays sound via
  ## promoteSound, exactly like the analogous case in the hidden-stdconv
  ## fix above -- ord() of it must not be routed through mkConvIntWidth's
  ## BV-only walker.
  if ord(x) > 3_000_000_000:
    symexTarget("hit")

proc ordNonComparisonLet(c: Color) =
  ## THE REPRO (non-comparison context) -- the narrow width leaked into a
  ## `let` binding, not just an immediate comparison.
  let o = ord(c)
  if o > 3_000_000_000:
    symexTarget("hit")

proc ordEqualsOne(c: Color) =
  ## Non-regression: an ordinary IN-RANGE ord() comparison must still find
  ## its witness -- the fix must not overcorrect into declining every ord()
  ## comparison.
  if ord(c) == 1:
    symexTarget("hit")

suite "#163 -- ord() carries its declared native-int width, not the argument's":

  test "oracle -- no Color ordinal (0, 1, or 2) is ever > 3_000_000_000":
    for c in Color:
      check not (ord(c) > 3_000_000_000)

  test "oracle -- no char ordinal (0..255) is ever > 3_000_000_000":
    for ch in [char(0), 'a', char(255)]:
      check not (ord(ch) > 3_000_000_000)

  test "oracle -- no SmallRange163 value (0..5) is ever > 3_000_000_000":
    for v in [SmallRange163(0'i32), SmallRange163(5'i32)]:
      check not (v.int64 > 3_000_000_000'i64)

  test "oracle -- ord(cGreen) is 1, exactly":
    check ord(cGreen) == 1

  test "RED (pre-fix): an enum PARAM's ord() must agree the target is UNSAT":
    let r = symexFind(ordEnumParam, tLabel("hit"))
    check r.status == sxUnsat

  test "RED (pre-fix): an enum LOCAL's ord() must agree the target is UNSAT":
    let r = symexFind(ordEnumLocal, tLabel("hit"))
    check r.status == sxUnsat

  test "RED (pre-fix): an enum OBJECT FIELD's ord() must agree the target is UNSAT":
    let r = symexFind(ordEnumField, tLabel("hit"))
    check r.status == sxUnsat

  test "RED (pre-fix): a char's ord() must agree the target is UNSAT":
    let r = symexFind(ordCharParam, tLabel("hit"))
    check r.status == sxUnsat

  test "non-regression -- a signed range-alias TOP-LEVEL PARAM stays sound (promoteSound)":
    let r = symexFind(ordRangeAliasParam, tLabel("hit"))
    check r.status == sxUnsat

  test "RED (pre-fix): ord() bound to a let outside any comparison must agree UNSAT":
    let r = symexFind(ordNonComparisonLet, tLabel("hit"))
    check r.status == sxUnsat

  test "non-regression -- an ordinary in-range ord() comparison still finds its witness":
    let r = symexFind(ordEqualsOne, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == cGreen

suite "#163 item 2 -- walker version pin":

  test "walker version floor >= 138 (the round this fix lands in)":
    check parseInt(symexWalkerVersion) >= 140
