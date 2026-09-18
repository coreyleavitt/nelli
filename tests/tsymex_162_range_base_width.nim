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

import std/unittest
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
    check symexWalkerVersion >= "129"
