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

  test "version floor — this behaviour arrived at walker 129":
    ## Per CLAUDE.md: a walker SEMANTICS change bumps `symexWalkerVersion`
    ## and the round's test file pins the floor. 128 answered `sxUnsat`
    ## here in both modes; anything below 129 cannot have this fix.
    check symexWalkerVersion >= "129"
