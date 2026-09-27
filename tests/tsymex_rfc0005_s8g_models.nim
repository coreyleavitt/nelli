## RFC-0005 (soundness channels) slice S8g -- faithful scalar, string and
## defect models. Walker 154 -> 155.
##
## S8f's replay audit ran every clean `sxSat` against the real SUT. Six model
## defects survived it because they never produce a clean `sxSat` that
## replay could refute: each one makes the engine claim `sxUnsat` or
## `sxRaised` for something Nim does differently. Every expected value below
## was probed against the real compiler (Nim 2.2.10, c and cpp backends,
## debug build: rangeChecks and overflowChecks on); the probe output is
## quoted beside the test.
##   (1) float -> int conversion never raises. The walker modelled
##       `RangeDefect` for an out-of-range / NaN / Inf operand (ADR-0011
##       R16-2); Nim's generated C casts first and range-checks the CAST
##       value, which is tautological for a full-width target. The in-range
##       result is exact; out of range the value is C-level undefined, so it
##       is a fresh symbol on a `dcFreshSymbol` path (a replay-gated
##       candidate). A `range` target (`Natural(f)`) does raise.
##   (2) unary negation overflows: `-low(int)` (and `abs(low(int))`, whose
##       body is `-x`) raise `OverflowDefect`.
##   (3) `split(s, "")` is `@[s]`, not a byte-wise split.
##   (4) `new int` (a non-object pointee) is zero-initialised.
##   (5) slice / `del` defect classes: a negative slice length is a
##       `RangeDefect`, an empty slice never raises, `del(-1)` is a
##       `RangeDefect`; a string slice raises at all; `substr` clamps.
##   (6) a symbolic discriminator reassignment can select the `else:` arm.
##   (7) the walker version floor.
import std/[unittest, strutils]
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

# ---- (1) float -> int ---------------------------------------------------------
#
# Probe (scratch probe, c and cpp identical):
#   int(1e30) = int(-1e30) = int(NaN) = int(Inf) = int(-Inf)
#             = int(9.2233720368547758e18) = -9223372036854775808
#   int32(1e30) = int32(NaN) = 0; int32(1e10) = 1410065408
#   int8(300.0) = 44; int8(255.9) = -1; uint8(-3.7) = 253; uint8(256.0) = 0
#   none of them raise RangeDefect.
# The generated C (scratch probe) is `if ((NI)(f) < MIN || (NI)(f) > MAX)
# raiseRangeErrorI(...)`: the CAST value is checked, so the check never
# fires for a full-width target; a narrow one is `(NI8)((NI64)f)`, unchecked.
# A `range` target checks the cast value against the subrange:
#   Natural(-5.0) raises RangeDefect ("value out of range: -5 notin 0 .. ...").

proc f2iNever(f: float) =
  let i = int(f)
  discard i

proc f2iCaught(f: float) =
  try:
    let i = int(f)
    discard i
  except RangeDefect:
    symexTarget("s8g_f2i_caught")

proc f2iNanIsLow(f: float) =
  if f != f:
    let i = int(f)
    if i == low(int): symexTarget("s8g_f2i_nanlow")

proc f2iNanIs7(f: float) =
  if f != f:
    let i = int(f)
    if i == 7: symexTarget("s8g_f2i_nan7")

proc f2iExact(f: float) =
  if f > 2.0 and f < 3.0:
    if int(f) == 2: symexTarget("s8g_f2i_exact")

proc f2iExactMiss(f: float) =
  if f > 2.0 and f < 3.0:
    if int(f) == 3: symexTarget("s8g_f2i_exactmiss")

proc f2iI8Wrap(f: float) =
  if f >= 300.0 and f < 301.0:
    let b = int8(f)
    if b == 44: symexTarget("s8g_f2i_i8wrap")

proc f2iI8InRange(f: float) =
  if f > -2.0 and f < -1.0:
    let b = int8(f)
    if b == -1: symexTarget("s8g_f2i_i8inrange")

proc f2iU8Neg(f: float) =
  if f > -4.0 and f < -3.0:
    let b = uint8(f)
    if b == 253: symexTarget("s8g_f2i_u8neg")

proc f2iNatural(f: float) =
  let n = Natural(f)
  discard n

proc f2iNaturalOk(f: float) =
  if f > 5.0 and f < 6.0:
    let n = Natural(f)
    if n == 5: symexTarget("s8g_f2i_natok")

suite "S8g (1) float -> int: no RangeDefect, exact in range, fresh outside":
  test "int(f) never raises RangeDefect (was a false sxRaised)":
    let r = symexFind(f2iNever, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "an except RangeDefect around int(f) is dead (was a false sxSat)":
    let r = symexFind(f2iCaught, tLabel("s8g_f2i_caught"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "int(NaN) == low(int) is reachable: a replay-confirmed candidate":
    let r = symexFind(f2iNanIsLow, tLabel("s8g_f2i_nanlow"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(f2iNanIsLow(r.witness[0]), "s8g_f2i_nanlow")

  test "int(NaN) == 7 is a fresh-value candidate that replay refutes, never a claim":
    let r = symexFind(f2iNanIs7, tLabel("s8g_f2i_nan7"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feConvFloatToIntUndefined)

  test "in range, the conversion is exact and clean":
    let r = symexFind(f2iExact, tLabel("s8g_f2i_exact"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(f2iExact(r.witness[0]), "s8g_f2i_exact")
    let miss = symexFind(f2iExactMiss, tLabel("s8g_f2i_exactmiss"))
    checkpoint($miss.status & " " & show(miss.errors))
    check miss.status == sxUnsat

  test "int8(f) of an out-of-range f is not unreachable (was a false sxUnsat)":
    let r = symexFind(f2iI8Wrap, tLabel("s8g_f2i_i8wrap"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(f2iI8Wrap(r.witness[0]), "s8g_f2i_i8wrap")

  test "int8(f) in range is exact at width 8":
    let r = symexFind(f2iI8InRange, tLabel("s8g_f2i_i8inrange"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(f2iI8InRange(r.witness[0]), "s8g_f2i_i8inrange")

  test "uint8(f) of a negative f is not unreachable (was a false sxUnsat)":
    let r = symexFind(f2iU8Neg, tLabel("s8g_f2i_u8neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(f2iU8Neg(r.witness[0]), "s8g_f2i_u8neg")

  test "Natural(f) raises RangeDefect on a negative f (was a false sxUnsat)":
    let r = symexFind(f2iNatural, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

  test "Natural(f) in range converts exactly":
    let r = symexFind(f2iNaturalOk, tLabel("s8g_f2i_natok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(f2iNaturalOk(r.witness[0]), "s8g_f2i_natok")

  test "feConvFloatToIntUndefined is dcFreshSymbol":
    check classOf(feConvFloatToIntUndefined) == dcFreshSymbol

# ---- (2) unary negation overflow ----------------------------------------------
#
# Probe (scratch probe, c and cpp identical):
#   -low(int)   -> OverflowDefect ("over- or underflow")
#   -low(int32) -> OverflowDefect;  -low(int8) -> OverflowDefect
#   abs(low(int)) -> OverflowDefect; abs(low(int8)) -> OverflowDefect
#   (system's `abs` is `if x < 0: -x else: x`).

proc negOvf(x: int) =
  let y = -x
  discard y

proc negOvf8(x: int8) =
  let y = -x
  discard y

proc absOvf(x: int) =
  let y = abs(x)
  discard y

proc negSafe(x: int) =
  if x > -100 and x < 100:
    let y = -x
    discard y

proc negValue(x: int) =
  if x > 0 and -x == -5: symexTarget("s8g_neg_value")

suite "S8g (2) unary minus: -low(T) raises OverflowDefect":
  test "-x on int raises OverflowDefect at low(int) (was a false sxUnsat)":
    let r = symexFind(negOvf, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    if r.status == sxRaised: check r.raisedWitness[0] == low(int)

  test "-x on int8 raises OverflowDefect at low(int8)":
    let r = symexFind(negOvf8, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    if r.status == sxRaised: check r.raisedWitness[0] == low(int8)

  test "abs(x) raises OverflowDefect at low(int)":
    let r = symexFind(absOvf, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "-x of a bounded x never overflows":
    let r = symexFind(negSafe, tRaisedExn("OverflowDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "-x is still the negation":
    let r = symexFind(negValue, tLabel("s8g_neg_value"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5

# ---- (3) split(s, "") ---------------------------------------------------------
#
# Probe (scratch probes): "abc".split("") == @["abc"];
# "".split("") == @[""]; a runtime "xyz".split("") == @["xyz"]. strutils'
# `split` never matches an empty separator (`substrEq` of "" is false).

proc splitEmptySym(s: string) =
  let parts = s.split("")
  if parts.len == 1 and parts[0] == s: symexTarget("s8g_split_sym")

proc splitEmptyLit(s: string) =
  if s == "x":
    let parts = "abc".split("")
    if parts.len == 1 and parts[0] == "abc": symexTarget("s8g_split_lit")

proc splitEmptyTwo(s: string) =
  let parts = s.split("")
  if parts.len == 2: symexTarget("s8g_split_two")

suite "S8g (3) split(s, \"\") is @[s]":
  test "a symbolic receiver splits to itself (was a seZ3StringIncomplete decline)":
    let r = symexFind(splitEmptySym, tLabel("s8g_split_sym"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0

  test "a literal receiver splits to itself (was a byte-wise split: false sxUnsat)":
    let r = symexFind(splitEmptyLit, tLabel("s8g_split_lit"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

  test "two parts are unreachable":
    let r = symexFind(splitEmptyTwo, tLabel("s8g_split_two"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

# ---- (4) new(T) of a non-object pointee ----------------------------------------
#
# Probe (scratch probe): `new int` -> p[] == 0; `new float` -> 0.0;
# `new bool` -> false; `new string` -> ''.

proc newIntNonZero(x: int) =
  let p = new int
  if p[] != x and x == 0: symexTarget("s8g_new_int")

proc newBoolTrue() =
  let p = new bool
  if p[]: symexTarget("s8g_new_bool")

proc newIntWritten(x: int) =
  let p = new int
  p[] = x
  if p[] == 7: symexTarget("s8g_new_written")

suite "S8g (4) new(T) zero-initialises a non-object pointee":
  test "new int reads 0 (was a free cell: false sxSat)":
    let r = symexFind(newIntNonZero, tLabel("s8g_new_int"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "new bool reads false":
    let r = symexFind(newBoolTrue, tLabel("s8g_new_bool"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "a written cell reads the write":
    let r = symexFind(newIntWritten, tLabel("s8g_new_written"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(newIntWritten(r.witness[0]), "s8g_new_written")

# ---- (5) slice / del defect classes --------------------------------------------
#
# Probe (scratch probe, c and cpp identical), d = @[1, 2, 3], s = "abc":
#   d[4 .. ^1] -> RangeDefect "value out of range: -1 notin 0 .. ..." (the
#                 slice LENGTH hi-lo+1 is range-checked first)
#   d[2 .. 0]  -> RangeDefect (length -1);  d[5 .. 2] -> RangeDefect
#   d[3 .. ^1] -> no raise, len 0 (an EMPTY slice checks no index)
#   d[1 .. 7], d[-1 .. 1] -> IndexDefect
#   s[4 .. ^1] -> RangeDefect;  s[1 .. 7], s[-1 .. 1] -> IndexDefect
#   d.del(-1)  -> RangeDefect (`del`'s index is a `Natural`)
#   d.del(3)   -> IndexDefect
#   substr(s, -2, 1) == "ab"; substr(s, 1, 9) == "bc" (substr CLAMPS);
#   substr(s, 2, 0) == ""; substr(s, 5) == ""; substr(s, -1) == "abc"

proc sliceTail(data: seq[int]) =
  let payload = data[4 .. ^1]
  discard payload.len

proc sliceEmptyHigh(data: seq[int]) =
  if data.len == 3:
    let payload = data[5 .. 4]
    if payload.len == 0: symexTarget("s8g_slice_emptyhigh")

proc sliceOob(data: seq[int]) =
  if data.len == 3:
    let payload = data[1 .. 7]
    discard payload.len

proc delNeg(xs: seq[int], i: int) =
  if i < 0:
    var ys = xs
    ys.del(i)
    discard ys

proc delHigh(xs: seq[int], i: int) =
  if i >= 0:
    var ys = xs
    ys.del(i)
    discard ys

proc strSliceOob(s: string) =
  if s.len == 3:
    let t = s[1 .. 7]
    discard t

proc strSliceNeg(s: string) =
  if s.len == 3:
    let t = s[2 .. 0]
    discard t

proc strSliceOk(s: string) =
  if s.len == 3:
    let t = s[1 .. 2]
    if t == "bc": symexTarget("s8g_strslice_ok")

proc substrNeg(s: string) =
  if s == "abc":
    let t = substr(s, -2, 1)
    if t == "ab": symexTarget("s8g_substr_neg")

proc substrHigh(s: string) =
  if s == "abc":
    let t = substr(s, 1, 9)
    if t == "bc": symexTarget("s8g_substr_high")

proc strSliceBack(s: string) =
  if s == "abcd":
    if s[1 .. ^1] == "bcd" and s[^2 .. ^1] == "cd":
      symexTarget("s8g_strslice_back")

proc seqSliceBackLo(xs: seq[int]) =
  # Walker 154 read the low `^2` as 2: `xs[2 .. 4]`, length 3.
  if xs.len == 5 and xs[3] == 7:
    let t = xs[^2 .. ^1]
    if t.len == 2 and t[0] == 7: symexTarget("s8g_seqslice_backlo")

suite "S8g (5) slice and del defect classes":
  test "data[4 .. ^1] on a short seq raises RangeDefect (was IndexDefect)":
    let r = symexFind(sliceTail, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"
    if r.status == sxRaised: check r.raisedWitness[0].len < 4

  test "data[4 .. ^1] never raises IndexDefect":
    # The only reachable defect is RangeDefect; a reachable defect preempts
    # the search, so the IndexDefect target reports that one.
    let r = symexFind(sliceTail, tIndexError())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

  test "an empty slice past the end does not raise (was a false IndexDefect)":
    let r = symexFind(sliceEmptyHigh, tLabel("s8g_slice_emptyhigh"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

  test "data[1 .. 7] on a 3-seq raises IndexDefect":
    let r = symexFind(sliceOob, tIndexError())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "del(i) with i < 0 raises RangeDefect (was IndexDefect)":
    let r = symexFind(delNeg, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"
    if r.status == sxRaised: check r.raisedWitness[1] < 0

  test "del(i) with i >= len raises IndexDefect":
    let r = symexFind(delHigh, tIndexError())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    if r.status == sxRaised:
      check r.raisedWitness[1] >= r.raisedWitness[0].len

  test "a string slice past the end raises IndexDefect (was a clamp: no raise)":
    let r = symexFind(strSliceOob, tIndexError())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "a string slice of negative length raises RangeDefect":
    let r = symexFind(strSliceNeg, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

  test "an in-bounds string slice is exact":
    let r = symexFind(strSliceOk, tLabel("s8g_strslice_ok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(strSliceOk(r.witness[0]), "s8g_strslice_ok")

  test "a ^k string slice bound is len - k (was k itself: false sxUnsat)":
    # Walker 154 read `s[1 .. ^1]` of "abcd" as `s[1 .. 1]` == "b".
    let r = symexFind(strSliceBack, tLabel("s8g_strslice_back"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(strSliceBack(r.witness[0]), "s8g_strslice_back")

  test "a ^k low seq slice bound is len - k (was k itself)":
    let r = symexFind(seqSliceBackLo, tLabel("s8g_seqslice_backlo"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(seqSliceBackLo(r.witness[0]), "s8g_seqslice_backlo")

  test "substr clamps a negative first (was a false sxUnsat)":
    let r = symexFind(substrNeg, tLabel("s8g_substr_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

  test "substr clamps a last past the end":
    let r = symexFind(substrHigh, tLabel("s8g_substr_high"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

# ---- (6) symbolic discriminator reassignment into the else: arm ---------------
#
# Nim (2.2.10): a discriminator assignment that keeps the object in the same
# branch keeps its fields; `kC` and `kD` share the `else:` branch, so
# `box.kind = kD` from `kC` is legal and `box.c` survives.

type
  S8gK = enum kA, kB, kC, kD
  S8gBox = object
    case kind: S8gK
    of kA: a: int
    of kB: b: int
    else: c: int

proc elseArm(box: var S8gBox, t: S8gK) =
  if box.kind >= kC and t >= kC:
    box.kind = t
    if box.kind == kD and box.c == 9:
      symexTarget("s8g_else_arm")

proc elseFromA(box: var S8gBox, t: S8gK) =
  if box.kind == kA and t == kD:
    box.kind = t

suite "S8g (6) a symbolic discriminator reassignment reaches the else: arm":
  test "kC -> kD keeps the else: branch's field (was a false sxUnsat)":
    let r = symexFind(elseArm, tLabel("s8g_else_arm"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      var b = r.witness[0]
      check reproduces(elseArm(b, r.witness[1]), "s8g_else_arm")

  test "kA -> kD changes branch: FieldDefect (was no path at all)":
    # Nim: `box.kind = kD` from kA raises FieldDefect ("assignment to
    # discriminant changes object branch"). The pre-S8g walker forked only
    # explicit tags, so t == kD left no path and no defect.
    let r = symexFind(elseFromA, tRaisedExn("FieldDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check r.raisedTypeId == "FieldDefect"


# ---- (7) walker version floor ---------------------------------------------------

suite "S8g (7) walker version":
  test "walker version is at least 155":
    check parseInt(symexWalkerVersion) >= 155
