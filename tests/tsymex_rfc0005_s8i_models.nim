## RFC-0005 (soundness channels) slice S8i -- S8g's different-mechanism
## remainder. Walker 156 -> 157.
##
## S8g fixed six model defects by construction and reported five more whose
## mechanism lay outside its design. Each one below is a claim the real SUT
## contradicts (a clean `sxSat` whose witness does something else, or a
## false `sxUnsat`), or an internal walker fault. Every expected value was
## probed against the real compiler (Nim 2.2.10, c and cpp identical, debug
## build: rangeChecks and overflowChecks on); the probe output is quoted
## beside the test.
##   (1) `low(T) div -1` raises `OverflowDefect` at every signed width, and
##       `low(T) mod -1` kills the process (SIGFPE) at widths 32 and 64.
##   (2) a `uint64` converts to float as unsigned.
##   (3) an int -> range / subrange / enum conversion range-checks
##       (`RangeDefect`), explicit or implicit.
##   (4) a symbolic discriminator reassignment of an object whose
##       construction was declined degrades through the recorded decline.
##   (5) the concolic `if` walker drains an `if` condition's scalar raises,
##       and routes only the raises the replay took.
##   (6) the walker version floor.
import std/[unittest, strutils, tables]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (1) div / mod by -1 at low(T) -------------------------------------------
#
# Probe (scratch probe, c and cpp identical; operands through a noinline
# identity so nothing folds):
#   low(int) div -1   -> OverflowDefect "over- or underflow"
#   low(int32) div -1 -> OverflowDefect;  low(int16) div -1 -> OverflowDefect
#   low(int8) div -1  -> OverflowDefect
#   low(int) mod -1   -> "SIGFPE: Arithmetic error." and exit 1, inside a
#                        `try: ... except Defect:` (not catchable)
#   low(int32) mod -1 -> SIGFPE (same)
#   low(int16) mod -1 == 0;  low(int8) mod -1 == 0 (C promotes to int)
#   low(int) + 1 mod -1 == 0;  5 mod -1 == 0
#   -7 mod 2 == -1;  7 mod -2 == 1;  -7 div 2 == -3 (C truncation: the
#   remainder takes the dividend's sign)

proc divOvf(x, y: int) =
  if y != 0:
    let q = x div y
    discard q

proc divOvf8(x, y: int8) =
  if y != 0:
    let q = x div y
    discard q

proc divOvf32(x, y: int32) =
  if y != 0:
    let q = x div y
    discard q

proc divNoOvf(x, y: int) =
  if y != 0 and x > low(int):
    let q = x div y
    discard q

proc modTrap(x, y: int) =
  if y == -1 and x == low(int):
    let r = x mod y
    if r == 0: symexTarget("s8i_mod_trap")

proc modTrap32(x, y: int32) =
  if y == -1 and x == low(int32):
    let r = x mod y
    if r == 0: symexTarget("s8i_mod_trap32")

proc modNoTrap8(x, y: int8) =
  if y == -1 and x == low(int8):
    let r = x mod y
    if r == 0: symexTarget("s8i_mod_notrap8")

proc modNearLow(x, y: int) =
  if y == -1 and x < -9223372036854775000:
    let r = x mod y
    if r == 0: symexTarget("s8i_mod_nearlow")

proc modSign(x, y: int) =
  if x == -7 and y == 2:
    if x mod y == -1: symexTarget("s8i_mod_sign")

proc modSignDivisor(x, y: int) =
  if x == 7 and y == -2:
    if x mod y == 1: symexTarget("s8i_mod_signdiv")

suite "S8i (1) low(T) div -1 raises OverflowDefect; low(T) mod -1 traps":
  test "low(int) div -1 raises OverflowDefect (was a false sxUnsat)":
    let r = symexFind(divOvf, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    if r.status == sxRaised:
      check r.raisedWitness[0] == low(int)
      check r.raisedWitness[1] == -1

  test "low(int8) div -1 raises OverflowDefect":
    let r = symexFind(divOvf8, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    if r.status == sxRaised:
      check r.raisedWitness[0] == low(int8)

  test "low(int32) div -1 raises OverflowDefect":
    let r = symexFind(divOvf32, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "a dividend above low(int) never overflows":
    let r = symexFind(divNoOvf, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "low(int) mod -1 does not continue (was a false sxSat: the SUT dies of SIGFPE)":
    let r = symexFind(modTrap, tLabel("s8i_mod_trap"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "low(int32) mod -1 does not continue":
    let r = symexFind(modTrap32, tLabel("s8i_mod_trap32"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "low(int8) mod -1 is 0 and continues":
    let r = symexFind(modNoTrap8, tLabel("s8i_mod_notrap8"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(modNoTrap8(r.witness[0], r.witness[1]), "s8i_mod_notrap8")

  test "a witness near low(int) avoids the trapping input":
    let r = symexFind(modNearLow, tLabel("s8i_mod_nearlow"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      # Running the SUT on `low(int)` would kill this test process.
      check r.witness[0] != low(int)
      if r.witness[0] != low(int):
        check reproduces(modNearLow(r.witness[0], r.witness[1]), "s8i_mod_nearlow")

  test "mod takes the dividend's sign: -7 mod 2 == -1 (was a false sxUnsat)":
    let r = symexFind(modSign, tLabel("s8i_mod_sign"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(modSign(r.witness[0], r.witness[1]), "s8i_mod_sign")

  test "mod ignores the divisor's sign: 7 mod -2 == 1 (was a false sxUnsat)":
    let r = symexFind(modSignDivisor, tLabel("s8i_mod_signdiv"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(modSignDivisor(r.witness[0], r.witness[1]), "s8i_mod_signdiv")

# ---- (2) uint64 -> float -------------------------------------------------------
#
# Probe (scratch probe, c and cpp identical):
#   float(9223372036854775808'u64) == 9.223372036854776e+18
#   float(high(uint64)) == 1.8446744073709552e+19
#   float32(9223372036854775808'u64) == 9.223372e+18
#   float(high(uint32)) == 4294967295.0

proc u64ToFloat(x: uint64) =
  if x >= 9223372036854775808'u64:
    if float(x) > 0.0: symexTarget("s8i_u64_float")

proc u64ToFloatNeg(x: uint64) =
  if float(x) < 0.0: symexTarget("s8i_u64_float_neg")

proc u64ToFloat32(x: uint64) =
  if x == high(uint64):
    if float32(x) > 1.0e19'f32: symexTarget("s8i_u64_float32")

suite "S8i (2) a uint64 converts to float as unsigned":
  test "float(x) of x >= 2^63 is positive (was a false sxUnsat)":
    let r = symexFind(u64ToFloat, tLabel("s8i_u64_float"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(u64ToFloat(r.witness[0]), "s8i_u64_float")

  test "float(x) of a uint64 is never negative (was a false sxSat)":
    let r = symexFind(u64ToFloatNeg, tLabel("s8i_u64_float_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "float32(high(uint64)) is about 1.8e19":
    let r = symexFind(u64ToFloat32, tLabel("s8i_u64_float32"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

# ---- (3) int -> range / subrange / enum conversion --------------------------------
#
# Probe (scratch probe, c and cpp identical):
#   Natural(-1)      -> RangeDefect "value out of range: -1 notin 0 .. 9223372036854775807"
#   Positive(0)      -> RangeDefect "value out of range: 0 notin 1 .. ..."
#   R(8), R = range[3..7] -> RangeDefect "value out of range: 8 notin 3 .. 7"
#   R(5) == 5
#   range[-2..2](3)  -> RangeDefect "value out of range: 3 notin -2 .. 2"
#   Natural(-1'i8)   -> RangeDefect
#   E(5), E = enum eA, eB, eC -> RangeDefect "value out of range: 5 notin 0 .. 2"

type
  S8iR = range[3..7]
  S8iE = enum eA, eB, eC

proc natConv(x: int) =
  let n = Natural(x)
  discard n

proc natConvOk(x: int) =
  if x > 10 and x < 20:
    let n = Natural(x)
    if n == 15: symexTarget("s8i_nat_ok")

proc subConv(x: int) =
  let r = S8iR(x)
  discard r

proc subConvHigh(x: int) =
  if x > 5:
    let r = S8iR(x)
    if r == 7: symexTarget("s8i_sub_high")

proc subConvCaught(x: int) =
  try:
    let r = S8iR(x)
    discard r
  except RangeDefect:
    if x == 9: symexTarget("s8i_sub_caught")

proc litRangeConv(x: int) =
  let r = range[-2..2](x)
  discard r

proc posConv8(x: int8) =
  let p = Positive(x)
  discard p

proc enumConv(x: int) =
  let e = S8iE(x)
  discard e

proc enumConvOk(x: int) =
  if x >= 0 and x <= 2:
    let e = S8iE(x)
    if e == eC: symexTarget("s8i_enum_ok")

suite "S8i (3) an int -> range conversion raises RangeDefect out of range":
  test "Natural(x) raises RangeDefect for x < 0 (was a pass-through)":
    let r = symexFind(natConv, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"
    if r.status == sxRaised: check r.raisedWitness[0] < 0

  test "Natural(x) in range is the value":
    let r = symexFind(natConvOk, tLabel("s8i_nat_ok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(natConvOk(r.witness[0]), "s8i_nat_ok")

  test "a subrange type conversion raises RangeDefect":
    let r = symexFind(subConv, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < 3 or r.raisedWitness[0] > 7

  test "a converted subrange value stays in range (x > 5 reaches r == 7)":
    let r = symexFind(subConvHigh, tLabel("s8i_sub_high"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7

  test "except RangeDefect around a subrange conversion is live (was a false sxUnsat)":
    let r = symexFind(subConvCaught, tLabel("s8i_sub_caught"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(subConvCaught(r.witness[0]), "s8i_sub_caught")

  test "an anonymous range[-2..2] conversion raises RangeDefect":
    let r = symexFind(litRangeConv, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < -2 or r.raisedWitness[0] > 2

  test "Positive(x) of an int8 raises RangeDefect for x < 1":
    let r = symexFind(posConv8, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedWitness[0] < 1

  test "an int -> enum conversion raises RangeDefect out of the enum's range":
    let r = symexFind(enumConv, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < 0 or r.raisedWitness[0] > 2

  test "an in-range int -> enum conversion is the ordinal":
    let r = symexFind(enumConvOk, tLabel("s8i_enum_ok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2

# The same check on an IMPLICIT conversion into a range type (Nim inserts
# a hidden conversion, then range-checks it). Probe (c and cpp identical,
# x = -1):
#   let q: R = x          -> RangeDefect "value out of range: -1 notin 3 .. 7"
#   var q: Natural = x    -> RangeDefect "value out of range: -1 notin 0 .. 9223372036854775807"
#   K(n: x), n: Natural   -> RangeDefect (same message)
#   let q: Natural = x8   -> RangeDefect (x8: int8)
#   let q: R = 5          -> no raise

type S8iNatObj = object
  n: Natural

proc hiddenLet(x: int) =
  let q: S8iR = x
  discard q

proc hiddenLetOk(x: int) =
  if x >= 3 and x <= 7:
    let q: S8iR = x
    if q == 4: symexTarget("s8i_hidden_ok")

proc hiddenVar(x: int) =
  var q: Natural = x
  discard q

proc hiddenField(x: int) =
  let k = S8iNatObj(n: x)
  discard k

proc hiddenInt8(x: int8) =
  let q: Natural = x
  discard q

suite "S8i (3b) an implicit conversion into a range type raises RangeDefect":
  test "let q: R = x raises out of range (was a false sxUnsat)":
    let r = symexFind(hiddenLet, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < 3 or r.raisedWitness[0] > 7

  test "let q: R = x in range is the value":
    let r = symexFind(hiddenLetOk, tLabel("s8i_hidden_ok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(hiddenLetOk(r.witness[0]), "s8i_hidden_ok")

  test "var q: Natural = x raises for x < 0 (was a false sxUnsat)":
    let r = symexFind(hiddenVar, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedWitness[0] < 0

  test "a Natural object field raises for x < 0 (was a false sxUnsat)":
    let r = symexFind(hiddenField, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedWitness[0] < 0

  test "an int8 into a Natural raises for x < 0 (was a false sxUnsat)":
    let r = symexFind(hiddenInt8, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedWitness[0] < 0

# ---- (4) symbolic reassignment of a declined construction ---------------------
#
# Nim (2.2.10): `S8iV(kind: t)` with a runtime `t` sets no arm field, so
# `a` is nil; the walker has no modelled default for a `ref` arm field and
# declines the construction (RFC-0005 S8f). The object
# is then unmodelled; a later `v.kind = u` must degrade on that decline,
# not assert inside the walker.

type
  S8iK = enum kA, kB
  S8iV = object
    case kind: S8iK
    of kA: a: ref int
    of kB: b: int

proc declinedReassign(t, u: S8iK) =
  var v = S8iV(kind: t)
  v.kind = u
  if v.kind == kB: symexTarget("s8i_declined_reassign")

proc declinedReassignLit(t: S8iK) =
  var v = S8iV(kind: t)
  v.kind = kB
  if v.kind == kB: symexTarget("s8i_declined_reassign_lit")

suite "S8i (4) reassigning a declined construction degrades, never faults":
  test "symbolic reassignment: a classified decline, not weInternalWalkerFault":
    let r = symexFind(declinedReassign, tLabel("s8i_declined_reassign"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check not r.errors.hasKind(weInternalWalkerFault)
    check r.errors.hasKind(feUnsupportedOp)

  test "literal reassignment: a classified decline, not weInternalWalkerFault":
    let r = symexFind(declinedReassignLit, tLabel("s8i_declined_reassign_lit"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check not r.errors.hasKind(weInternalWalkerFault)
    check r.errors.hasKind(feUnsupportedOp)

# ---- (5) the concolic if-walker drains its condition's raises -----------------
#
# Real Nim: `100 div 0` raises DivByZeroDefect, so with x == 0 the `if`
# decision is never made and control enters the handler, where `y > 3`
# is the one real decision.

proc concIfDiv(x, y: int) =
  try:
    if 100 div x > 5: symexTarget("s8i_conc_hi")
  except DivByZeroDefect:
    if y > 3: symexTarget("s8i_conc_handler")

suite "S8i (5) the concolic if-walker routes a raise in its condition":
  test "oracle: 100 div 0 raises DivByZeroDefect":
    var hit = false
    try:
      concIfDiv(0, 5)
    except DivByZeroDefect:
      hit = true
    check not hit   # caught inside the SUT

  test "a raising condition enters the handler":
    let trace = @[integerChoice(0, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concIfDiv, trace, bindings)
    checkpoint("branchTrace.len=" & $r.branchTrace.len)
    for b in r.branchTrace: checkpoint("armTaken=" & $b.armTaken)
    check r.pcSatByConcreteInputs
    # One real decision: the handler's `y > 3`, taken. The `if` whose
    # condition raised made no decision.
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

  test "a non-raising condition does not enter the handler":
    let trace = @[integerChoice(5, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concIfDiv, trace, bindings)
    checkpoint("branchTrace.len=" & $r.branchTrace.len)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

# A closure call is the raise channel an `if` condition keeps inline (A2a
# hoists arithmetic operands into `let` temps, drained at the `let`). Real
# Nim: `pred(0)` raises ValueError out of the condition, the handler runs
# and `y > 3` is its decision; `pred(7)` returns true and the handler never
# runs.

proc concIfClosure(x, y: int) =
  let pred = proc (v: int): bool =
    if v == 0: raise newException(ValueError, "zero")
    v > 5
  try:
    if pred(x): symexTarget("s8i_concc_hi")
  except ValueError:
    if y > 3: symexTarget("s8i_concc_handler")

suite "S8i (5b) the concolic if-walker routes a closure raise in its condition":
  test "oracle: pred(0) raises ValueError out of the condition":
    var hit = false
    try:
      concIfClosure(0, 5)
    except ValueError:
      hit = true
    check not hit   # caught inside the SUT

  test "a raising closure condition enters the handler (was dropped: an ambiguous stop, no handler decision)":
    let trace = @[integerChoice(0, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concIfClosure, trace, bindings)
    checkpoint("branchTrace.len=" & $r.branchTrace.len &
               " ambiguous=" & $r.counters.ambiguousBranches)
    check r.pcSatByConcreteInputs
    check r.counters.ambiguousBranches == 0
    # The closure body's `v == 0` (taken), then the handler's `y > 3`
    # (taken); the outer `if` made no decision.
    check r.branchTrace.len == 2
    if r.branchTrace.len == 2:
      check r.branchTrace[0].armTaken == 0
      check r.branchTrace[1].armTaken == 0

  test "a returning closure condition does not enter the handler":
    let trace = @[integerChoice(7, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concIfClosure, trace, bindings)
    checkpoint("branchTrace.len=" & $r.branchTrace.len)
    check r.pcSatByConcreteInputs
    # Only the closure body's `v == 0` (not taken): no handler decision.
    for b in r.branchTrace: check b.armTaken == -1

# ---- (6) walker version floor ---------------------------------------------------

suite "S8i (6) walker version":
  test "walker version is at least 157":
    check parseInt(symexWalkerVersion) >= 157
