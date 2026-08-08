## Round-5, sello issue 1 — bv32/svBV64 width confusion in
## lowerArith/overflowCond. Two trigger shapes, one suspected root cause: a
## 64-bit-kinded SymVal minted at a branch merge (shape B) and along
## chained-call value flow (shape A), which 32-bit accessors (`bv32`
## FieldDefect) and width-strict binops (`binBV` width-mismatch doAssert)
## then trip over — surfacing post-v64 as classified
## sxUnknown/[weInternalWalkerFault]. Reported from sello's Curve25519
## harnesses (recodeScalarRadix16 per-step lemma, feCMove/feCSwap masks);
## validated on the 4990026 pin and re-confirmed on v0.3.2. The plain-int
## twin of shape A is clean, which localizes this to the BV width path.
import std/[unittest, strutils, sequtils]
import proptest/symex
import proptest/smt/canonicalize
import proptest/smt/types

# --- Shape A: chained nested int32 callees threading a carry ---------------

proc recodeStep(nibble, carryIn: int32; digitOut: var int32): int32 =
  symexAssume(nibble >= 0'i32 and nibble <= 15'i32)
  symexAssume(carryIn == 0'i32 or carryIn == 1'i32)
  var digit = nibble + carryIn
  let carryOut = (digit + 8'i32) shr 4'i32
  digit = digit - (carryOut shl 4'i32)
  digitOut = digit
  result = carryOut

proc chainedCarry(n0, n1, n2: int32) =
  ## One call alone is clean; the FieldDefect needs the callee's output
  ## threaded into the next call's input.
  var carry = 0'i32
  var d: int32
  carry = recodeStep(n0, carry, d)
  carry = recodeStep(n1, carry, d)
  carry = recodeStep(n2, carry, d)
  discard d

proc chainedCarryDigitRange(n0, n1: int32) =
  ## Non-vacuous UNSAT: the recode step's real invariant — the emitted digit
  ## is always in [-8, 7] — must PROVE through a chained carry.
  var carry = 0'i32
  var d: int32
  carry = recodeStep(n0, carry, d)
  carry = recodeStep(n1, carry, d)
  symexAssert(d >= -8'i32 and d <= 7'i32)

proc chainedCarryReachable(n0, n1: int32) =
  ## Non-vacuous SAT: a propagating carry is genuinely reachable.
  var carry = 0'i32
  var d: int32
  carry = recodeStep(n0, carry, d)
  carry = recodeStep(n1, carry, d)
  if carry == 1'i32:
    symexTarget("carry-propagates")

# --- Shape B: branch-merged int32 local in a binop with a symbolic operand -

proc maskAnd(bFlag: bool, rLimb: int32) =
  ## `rLimb and mask` tripped the binBV width-mismatch doAssert.
  let mask = if bFlag: -1'i32 else: 0'i32
  discard rLimb and mask

proc maskAdd(bFlag: bool, rLimb: int32) =
  ## `rLimb + mask` tripped the bv32 FieldDefect via overflowCond. With the
  ## width fixed, the HONEST verdict is a real OverflowDefect witness:
  ## int32.low + (-1) underflows in checked Nim.
  let mask = if bFlag: -1'i32 else: 0'i32
  discard rLimb + mask

proc maskAddBounded(bFlag: bool, rLimb: int32) =
  ## Bounded away from the underflow corner: must prove clean. The literal
  ## spelling of low(int32)+1 — `low`/`high` magics are a separate modeling
  ## question, not this suite's concern.
  symexAssume(rLimb >= -2147483647'i32)
  let mask = if bFlag: -1'i32 else: 0'i32
  discard rLimb + mask

proc maskReachable(bFlag: bool, rLimb: int32) =
  ## Non-vacuous SAT through the merged mask: `x and -1 == x` for any x, so
  ## the target is reachable exactly when bFlag drives the -1 arm.
  let mask = if bFlag: -1'i32 else: 0'i32
  if (rLimb and mask) == rLimb and bFlag:
    symexTarget("mask-identity")

suite "symex round-5 sello#1 — chained int32 callees (shape A)":

  test "carry chained across 3 int32 calls: clean sxUnsat, no walker fault":
    let r = symexFind(chainedCarry, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "digit-range invariant proves through the chain (non-vacuous UNSAT)":
    let r = symexFind(chainedCarryDigitRange, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "carry propagation is reachable (non-vacuous SAT)":
    let r = symexFind(chainedCarryReachable, tLabel("carry-propagates"))
    check r.status == sxSat

suite "symex round-5 sello#1 — branch-merged int32 mask (shape B)":

  test "`rLimb and mask` with branch-merged mask: clean, no walker fault":
    let r = symexFind(maskAnd, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "`rLimb + mask` unbounded: the REAL OverflowDefect is found (honesty)":
    ## Was FieldDefect 'bv32' on svBV64 inside overflowCond — the width bug
    ## crashed before the genuine underflow corner could be reported.
    let r = symexFind(maskAdd, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "`rLimb + mask` bounded above int32.low: clean, no walker fault":
    let r = symexFind(maskAddBounded, tRaisedExn("OverflowDefect"))
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "mask identity `x and -1 == x` reachable through the merge (SAT)":
    let r = symexFind(maskReachable, tLabel("mask-identity"))
    check r.status == sxSat

suite "symex round-5 sello — walker version pin":

  test "walker version floor >= 69 (literal-width protos + bool conv + svTuple bind)":
    check parseInt(symexWalkerVersion) >= 69
