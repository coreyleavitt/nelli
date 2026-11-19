## RFC-0016 K9e: pins for the overflow / range / conversion survivors of the
## pin-strength run (docs/rfc-data/0016-k9e.md). Each test reaches an arm the
## eleven suites of `tests/0016-pinstrength.suites` left untouched, with an
## input that tells the arm from its mutant, and is judged against the native
## binary (`pinFind`: a witness is run natively, an `sxUnsat` is checked over
## the parameter's domain, a raise is compared by type).
##
## The arms:
##   overflowCond          signed `-` and `*` at 8 bits (the 64-bit shapes are
##                         pinned by `phase16_R16_4_overflow`)
##   lowerConvIntRange     a conversion to a range type: the check itself, the
##                         top of an unsigned 8-bit source, an unsigned 64-bit
##                         source, and a width-typed Int operand's two bounds
##   forkAssignRangeCheck  an assignment into a `range` local (`*=`: its live
##                         raise; an RHS of the range type: no raise)
##   lowerExpr uNeg        `-x` of a signed BV and of a width-typed Int
import std/unittest
import nelli/symex
import ./s8cu_helpers

const Exact = SymexSettings(integerSemantics: isExact)

# --- overflowCond: int8 sub / mul -------------------------------------------

proc sub8Raise(a, b: int8) =
  let c = a - b
  symexTarget("t")
  discard c

proc sub8Ok(a, b: int8) =
  let c = a - b
  if c == 0: symexTarget("hit")
  discard c

proc mul8Raise(a, b: int8) =
  let c = a * b
  symexTarget("t")
  discard c

proc mul8Ok(a, b: int8) =
  let c = a * b
  if c == 1: symexTarget("hit")
  discard c

suite "K9e overflow: signed 8-bit sub and mul":
  test "int8 a - b forks OverflowDefect":
    let r = pinFind(sub8Raise, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "int8 a - b = 0 is reachable without a raise":
    check pinFind(sub8Ok, tLabel("hit")).status == sxSat

  test "int8 a * b forks OverflowDefect":
    let r = pinFind(mul8Raise, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "int8 a * b = 1 is reachable without a raise":
    check pinFind(mul8Ok, tLabel("hit")).status == sxSat

# --- lowerConvIntRange ------------------------------------------------------

type
  R1 = range[1 .. 300]
  R10 = range[0 .. 10]

proc natNeg(x: int) =
  ## `Natural(x)` raises RangeDefect for a negative `x`: the check is made.
  let n = Natural(x)
  symexTarget("t")
  discard n

proc u8Top(x: uint8) =
  ## `R1(255'u8)` is in range: the unsigned 8-bit source's top is 255.
  if x == 255:
    let r = R1(x)
    symexTarget("t")
    discard r

proc u64Low(x: uint64) =
  if x == 5:
    let n = Natural(x)
    symexTarget("t")
    discard n

proc u64Top(x: uint64) =
  ## `Natural(uint64(high(int)))` is in range: a u64 source is clamped to
  ## `high(int64)`, not one below it.
  if x == uint64(high(int)):
    let n = Natural(x)
    symexTarget("t")
    discard n

proc u64Over(x: uint64) =
  ## above `high(int)` the conversion raises
  let n = Natural(x)
  symexTarget("t")
  discard n

proc intNatZero(x: range[-5 .. 20]) =
  ## a width-typed Int operand (a declared-range param is promoted to an Int
  ## sort): `Natural(0)` is in range
  if x == 0:
    let n = Natural(x)
    symexTarget("t")
    discard n

proc intR10Top(x: range[-5 .. 20]) =
  if x == 10:
    let r = R10(x)
    symexTarget("t")
    discard r

suite "K9e range: conversion to a range type":
  test "Natural(x) raises RangeDefect for x < 0":
    let r = pinFind(natNeg, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

  test "R1(x) of uint8 255 is in range":
    check pinFind(u8Top, tRaisedExn("RangeDefect")).status == sxUnsat

  test "Natural(x) of uint64 5 is in range":
    check pinFind(u64Low, tRaisedExn("RangeDefect")).status == sxUnsat

  test "Natural(x) of uint64 high(int) is in range":
    check pinFind(u64Top, tRaisedExn("RangeDefect")).status == sxUnsat

  test "Natural(x) of a uint64 above high(int) raises RangeDefect":
    check pinFind(u64Over, tRaisedExn("RangeDefect")).status == sxRaised

  test "Int operand: Natural(0) is in range (lower bound inclusive)":
    check pinFind(intNatZero, tRaisedExn("RangeDefect")).status == sxUnsat

  test "Int operand: range[0..10](10) is in range (upper bound inclusive)":
    check pinFind(intR10Top, tRaisedExn("RangeDefect")).status == sxUnsat

# --- forkAssignRangeCheck ---------------------------------------------------

proc asgRange(x, y: range[0 .. 100]) =
  ## x + y reaches 200: outside 1..100 (and 0 + 0 is below it)
  var v: range[1 .. 100] = 1
  v = x + y
  symexTarget("t")
  discard v

suite "K9e range: assignment into a range local":
  test "v = x + y raises RangeDefect outside 1..100":
    let r = pinFind(asgRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

# `v = x + y` takes Nim's hidden range conversion (`carriesRangeCheck`, so
# `isAssign.aty` stays nil and `forkAssignRangeCheck` is not called). An RHS
# of the target's own type has no conversion: the fork is built (its two
# bound conditions reached) and its raise side is unsatisfiable, since the
# value is already confined to the range.
#
# `v *= x` does reach the fork with a raise side Nim takes: `system.*=` is
# `x = x * y`, an `int` product stored into the range, so the store's own
# conversion raises `RangeDefect` (native: 3 * 4 raises, 3 * 3 does not).
# The parser lowers it to an assignment whose `aty` is the range (no
# conversion node), so this is the fork's live raise, and the pin that tells
# it from the arms behind the discharge (`conds.len == 0`, the `coRange`
# gate, the routed type).

proc mulAsgRange(x: range[0 .. 10]) =
  var v: range[0 .. 10] = 3
  v *= x
  symexTarget("t")
  discard v

suite "K9e range: `*=` on a range local":
  test "v *= x raises RangeDefect outside 0..10":
    let r = pinFind(mulAsgRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

type R100 = range[1 .. 100]
type RangeBox = ref object
  f: R100

proc idR100(x: R100): R100 = x

proc asgCall(x: R100) =
  var v: R100 = 1
  v = idR100(x)
  symexTarget("t")
  discard v

proc asgField(p: RangeBox) =
  if p == nil: return
  var v: R100 = 1
  v = p.f
  symexTarget("t")
  discard v

suite "K9e range: assignment of a value already of the range type":
  test "v = f(x) of the target's type cannot raise RangeDefect":
    check pinFind(asgCall, tRaisedExn("RangeDefect")).status == sxUnsat

  test "v = p.f of the target's type cannot raise RangeDefect":
    check pinFind(asgField, tRaisedExn("RangeDefect")).status == sxUnsat

# --- lowerExpr uNeg ---------------------------------------------------------

proc negBV(x: int) =
  let y = -x
  symexTarget("t")
  discard y

proc negBV32(x: int32) =
  let y = -x
  symexTarget("t")
  discard y

proc negInt(x: int) =
  let y = -x
  symexTarget("t")
  discard y

suite "K9e uNeg: -low(T) raises OverflowDefect":
  test "-x of a signed 64-bit BV":
    let r = pinFind(negBV, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "-x of a signed 32-bit BV":
    check pinFind(negBV32, tRaisedExn("OverflowDefect")).status == sxRaised

  test "-x of a width-typed Int (isExact)":
    let r = pinFind(negInt, tRaisedExn("OverflowDefect"), Exact)
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
