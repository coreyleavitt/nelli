## Issue #162 — a range subtype must carry its BASE TYPE, not just its bounds.
##
## `range[0'i32 .. 100_000'i32]` is a subtype of **int32**: Nim performs
## arithmetic on it in int32 and checks overflow against int32's window.
## `classifyType` discarded that, returning `tInt(64, signed = true)` for
## every `range[lo..hi]` regardless of the bounds' own type — so `a * b`
## reaching 1e10 was checked against a 64-bit window, where it fits, and a
## real reachable `OverflowDefect` vanished in BOTH integer modes.
##
## This is independent of #161's promotion bug: `isExact` was wrong here too,
## because the width is wrong before any promotion decision is made. #161
## stamps the width it is given; this issue is about the width it is given.
##
## Every symbolic expectation below is pinned against Nim's own runtime,
## executed in the same file — the oracle, not an assertion about it.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

const Exact = SymexSettings(integerSemantics: isExact)

# The issue's repro, verbatim. `a * b` reaches 1e10, which does not fit int32.
proc mul32(a, b: range[0'i32..100_000'i32]) =
  let c = a * b
  symexTarget("t")
  discard c

# Slice 2. An UNSIGNED base. Nim wraps unsigned arithmetic silently -- there
# is no OverflowDefect to find here -- so the obligation is not "prove no
# overflow", it is "reproduce the wrap". `a + b < a` holds exactly when the
# addition wrapped, which for uint8 it can: 200 + 100 = 44.
proc addU8(a, b: range[0'u8..255'u8]) =
  if a + b < a:
    symexTarget("wrapped")

# Slice 3. The NAMED-ALIAS route. `classifyType` reaches a range two ways --
# the instantiated formal (`getTypeInst`) and a named alias (`getImpl`) --
# and each had its own copy of the "every range is 64-bit signed" answer.
# Fixing only the formal would leave the identical defect one `type`
# declaration away.
type
  Px = range[0'i32..100_000'i32]
  Weight = range[0'u16..60_000'u16]

proc mulAlias(a, b: Px) =
  let c = a * b
  symexTarget("t")
  discard c

proc addAlias(a, b: Weight) =
  if a + b < a:
    symexTarget("wrapped")

# Slice 4. The obligation is about the base type's WIDTH, not about 32 bits.
proc mul8(a, b: range[-100'i8..100'i8]) =
  let c = a * b            # reaches 10_000 -- past int8.high
  symexTarget("t")
  discard c

proc mul16(a, b: range[0'i16..1000'i16]) =
  let c = a * b            # reaches 1e6 -- past int16.high
  symexTarget("t")
  discard c

# Slice 4. The non-regression anchor: a range over PLAIN `int` bounds. This
# is what every range in the suite looked like before this issue, and 1e10
# fits int64, so there is no defect here and there must not appear to be one.
proc mulPlain(a, b: range[0..100_000]) =
  let c = a * b
  symexTarget("t")
  discard c

# Slice 4. Range tightening has to keep working at the narrow width -- the
# declared bounds are asserted against a 32-bit sort now, not a 64-bit one.
proc tight32(x: range[0'i32..100'i32]) =
  if x > 100'i32:
    symexTarget("impossible")

suite "#162 — range subtypes carry their base type":

  test "the oracle — Nim itself raises OverflowDefect on an int32 range":
    ## Not a symex assertion. This is the ground truth the two tests below
    ## have to reproduce: arithmetic on `range[lo'i32..hi'i32]` happens in
    ## int32, so 1e10 overflows and the defect is real and reachable.
    proc rt(a, b: range[0'i32..100_000'i32]): int32 = a * b
    expect OverflowDefect:
      discard rt(100_000, 100_000)

  test "isExact finds the OverflowDefect in an int32 range subtype":
    ## The load-bearing property, and the half that proves this is not a
    ## promotion bug: `isExact` never promotes, so the only thing that can
    ## have hidden the defect is the declared width itself.
    let r = symexFind(mul32, tRaisedExn("OverflowDefect"), Exact)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "isOptimised finds it too":
    ## The other half. With the width corrected, #161's live obligation
    ## fires against the RIGHT window: interval arithmetic cannot discharge
    ## [0..1e10] inside int32, so the fork survives to Z3.
    let r = symexFind(mul32, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised

  test "the oracle — Nim wraps an unsigned range subtype silently":
    ## Ground truth for the two tests below. Unlike the signed case there is
    ## no defect: `200 + 100` over a uint8 base is 44, quietly.
    proc rt(a, b: range[0'u8..255'u8]): uint8 = a + b
    check rt(200, 100) == 44'u8

  test "isExact reproduces the unsigned wrap":
    ## Modelled as signed 64-bit, `a + b` could never be less than `a` and
    ## this path was unreachable. The base type is what makes it reachable.
    let r = symexFind(addU8, tLabel("wrapped"), Exact)
    check r.status == sxSat

  test "isOptimised agrees — an unsigned range must not promote":
    ## The load-bearing property for this slice, and the same ADR-0001
    ## argument #161 slice 3 made: an unbounded `Z3Int` cannot wrap, so a
    ## representation that wraps by construction is the only sound one for a
    ## type whose wrapping is DEFINED behaviour. Promotion is therefore
    ## refused outright for unsigned params rather than being made
    ## conditional -- unsigned has no raise fork that could keep the
    ## obligation live instead.
    let r = symexFind(addU8, tLabel("wrapped"))
    check r.status == sxSat

  test "an unsigned range raises no OverflowDefect":
    let r = symexFind(addU8, tRaisedExn("OverflowDefect"))
    check r.status != sxRaised

  test "the oracle — a named int32 alias behaves like the inline range":
    proc rt(a, b: Px): int32 = a * b
    expect OverflowDefect:
      discard rt(100_000, 100_000)

  test "a named int32 range alias carries its base type too":
    ## Same defect, one `type` declaration away. `Px` resolves through
    ## `getImpl` rather than `getTypeInst`, which is a separate arm.
    let r = symexFind(mulAlias, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    let e = symexFind(mulAlias, tRaisedExn("OverflowDefect"), Exact)
    check e.status == sxRaised

  test "a named unsigned range alias wraps":
    ## An unsigned alias did not merely classify wrongly — it did not match
    ## the alias arm's literal-kind guard at all, which admitted only the
    ## SIGNED literal kinds.
    proc rt(a, b: Weight): uint16 = a + b
    check rt(60_000, 60_000) == 54_464'u16
    let r = symexFind(addAlias, tLabel("wrapped"))
    check r.status == sxSat

  test "int8 and int16 bases carry their widths as well":
    ## 32 bits is not special; the fix reads the width it is given.
    proc rt8(a, b: range[-100'i8..100'i8]): int8 = a * b
    expect OverflowDefect:
      discard rt8(100, 100)
    proc rt16(a, b: range[0'i16..1000'i16]): int16 = a * b
    expect OverflowDefect:
      discard rt16(1000, 1000)
    check symexFind(mul8, tRaisedExn("OverflowDefect")).status == sxRaised
    check symexFind(mul16, tRaisedExn("OverflowDefect")).status == sxRaised

  test "a range over plain int bounds is untouched":
    ## The non-regression anchor. `int` bounds mean an int64 base, 1e10 fits,
    ## and there is no defect — exactly as before #162. Every pre-existing
    ## range in the suite is written this way, which is why the blast radius
    ## of this change is the narrow-width cases and nothing else.
    proc rt(a, b: range[0..100_000]): int = a * b
    check rt(100_000, 100_000) == 10_000_000_000
    let r = symexFind(mulPlain, tRaisedExn("OverflowDefect"))
    check r.status == sxUnsat

  test "declared bounds still tighten the path condition at 32 bits":
    let r = symexFind(tight32, tLabel("impossible"))
    check r.status == sxUnsat

  test "a narrow SIGNED range still promotes — the unsigned ban is not wider":
    ## Guards slice 2 against over-reach: refusing promotion for unsigned
    ## params must not cost the signed ones their `Z3Int` encoding.
    let r = symexFind(tight32, tLabel("impossible"))
    check r.abstractions.len == 1
    check r.abstractions[0].interval == interval(0'i64, 100'i64)

  test "version floor — this behaviour arrived at walker 129":
    ## Per CLAUDE.md: a walker SEMANTICS change bumps `symexWalkerVersion`
    ## and the round's test file pins the floor. 128 answered `sxUnsat`
    ## here in both modes; anything below 129 cannot have this fix.
    ##
    ## Compared numerically, not lexicographically: `symexWalkerVersion` is a
    ## string, and string comparison goes wrong once versions reach four
    ## digits (`"1000" < "129"`).
    check parseInt(symexWalkerVersion) >= 129

## ---------------------------------------------------------------------------
## Slice 5. Found by asking whether the fix reached every route into a range:
## it does — but the FIELD route revealed that a range-typed object field was
## never constrained at all. `ClassifiedType.range` was plumbed only into
## `IRParam`, so a field kept its bounds nowhere. The model then picked a
## value outside the declared range and witness construction crashed the
## caller's process with an unhandled `RangeDefect`.
##
## The fix moves the bounds onto `IRType` itself, where they belong: in Nim
## `range[0..100]` IS a type. Fields, nested objects, arrays and seq elements
## then inherit the constraint through `allocateSym`'s existing recursion
## rather than through per-container plumbing.

type
  Cfg32 = object
    w: range[0'i32..100_000'i32]
    h: range[0'i32..100_000'i32]

  Box = object
    lo: range[0..100]
    hi: range[0..100]

  Outer = object
    inner: Box

proc area32(c: Cfg32) =
  let a = c.w * c.h        # reaches 1e10 -- past int32.high
  symexTarget("t")
  discard a

proc beyond(b: Box) =
  if b.lo > 100:
    symexTarget("impossible")

proc beyondNested(o: Outer) =
  if o.inner.hi > 100:
    symexTarget("impossible")

proc withinBox(b: Box) =
  if b.lo == 100:
    symexTarget("reachable")

suite "#162 — range subtypes constrain object fields too":

  test "a range-typed field's bounds reach the path condition":
    ## Was `sxSat`: with no constraint on the field, `b.lo > 100` was
    ## satisfiable for a field declared `range[0..100]`.
    let r = symexFind(beyond, tLabel("impossible"))
    check r.status == sxUnsat

  test "the bounds are a refinement, not a ban — in-range targets survive":
    ## The complement, so the fix cannot be "constrain everything away".
    let r = symexFind(withinBox, tLabel("reachable"))
    check r.status == sxSat

  test "a nested object's field is constrained too":
    ## The reason the bounds belong on `IRType` rather than on a per-field
    ## side table: `allocateSym` already recurses, so nesting is free.
    let r = symexFind(beyondNested, tLabel("impossible"))
    check r.status == sxUnsat

  test "a field's witness stays inside its declared range":
    ## The crash. Unconstrained, Z3 returned an int32-scale value for a
    ## `range[0'i32..100_000'i32]` field and witness construction raised
    ## `RangeDefect` out of the user's own test process — a crash, not a
    ## wrong verdict.
    proc rt(c: Cfg32): int32 = c.w * c.h
    expect OverflowDefect:
      discard rt(Cfg32(w: 100_000, h: 100_000))
    let r = symexFind(area32, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised

  test "field bounds are part of the cache key":
    ## Two programs identical but for a field's declared bounds must not
    ## share a cached verdict. The bounds now live on `IRType`, and
    ## `canonicalize(IRType)` recurses through `itTuple`, so this holds by
    ## construction rather than by a parallel plumbing path.
    type Narrow = object
      v: range[0..10]
    type Wide = object
      v: range[0..1000]
    proc pN(n: Narrow) =
      if n.v > 10:
        symexTarget("over")
    proc pW(w: Wide) =
      if w.v > 10:
        symexTarget("over")
    check symexFind(pN, tLabel("over")).status == sxUnsat
    check symexFind(pW, tLabel("over")).status == sxSat

  test "version floor — field bounds arrived at walker 130":
    ## 129 answered `sxSat` for `b.lo > 100` over a `range[0..100]` field,
    ## and crashed the caller on witness construction.
    ##
    ## Compared numerically, not lexicographically: `symexWalkerVersion` is a
    ## string, and string comparison goes wrong once versions reach four
    ## digits (`"1000" < "130"`).
    check parseInt(symexWalkerVersion) >= 130
