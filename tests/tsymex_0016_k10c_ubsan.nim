## RFC-0016 K10c -- the UBSan pin suite for the definedness axis.
##
## This file builds with `--overflowChecks:off` (its `.nim.cfg`), the profile
## `dpUnchecked`: signed `+`, `-`, `*` and the divisions are the bare C
## operation. For each arithmetic cell of `definednessTable` two things are
## pinned, and the table is what ties them:
##
##  * the WALKER, through `symexFind`: an undefined row halts at the operation
##    with its `UbKind` (`pinDecline`), a defined row is exact (`pinExact`);
##  * the C COMPILER, through a UBSan child (`ubsan_support`): inputs the row
##    calls undefined trip `-fsanitize=undefined`, inputs it calls defined
##    run clean.
## The expectation of each native input is derived from the table's answer
## for this profile (`definedness(op, class, dpUnchecked)`), so a row edited
## without the C evidence, or evidence that C does not bear out, fails here.
## `-fwrapv` (`dpFwrapv`) is the same sweep in a second child.
##
## Linux only for the UBSan half: mingw gcc and MSVC have no UBSan runtime,
## so those legs record a `skipCell` for each cell and keep the walker half,
## which does not depend on the C compiler.
import std/[unittest, strutils, os, options, math, sequtils]
import nelli
import nelli/symex
import nelli/smt/definedness
import nelli/smt/errorkind
import nelli/smt/buildprofile
import ./s8cu_helpers
import ./ubsan_support

# ---- the walker half --------------------------------------------------------
# Each unsafe SUT reaches its label only through the undefined side, which the
# walker halts: the verdict is untrusted and names the kind.

proc sutAddW(v: int) = (if v + 1 > v: discard else: symexTarget("hit"))
proc sutSubW(v: int) = (if v - 1 < v: discard else: symexTarget("hit"))
proc sutMulW(v: int) = (if v * 2 > v or v <= 0: discard else: symexTarget("hit"))
proc sutDivZS(a, b: int) = (if a div b == 12345 and b == 0: symexTarget("hit"))
proc sutModZS(a, b: int) = (if a mod b == 12345 and b == 0: symexTarget("hit"))
proc sutDivZU(a, b: uint64) =
  (if a div b == 12345'u64 and b == 0'u64: symexTarget("hit"))
proc sutModZU(a, b: uint64) =
  (if a mod b == 12345'u64 and b == 0'u64: symexTarget("hit"))
proc sutDivLow(a: int) =
  let r = a div -1
  if a == low(int) and r == 0: symexTarget("hit")
proc sutModLow(a: int) =
  let r = a mod -1
  if a == low(int) and r == 1: symexTarget("hit")

# The defined rows are exact, witness and all.
proc sutAddN(x: int8) = (if x == 127'i8 and x + 1'i8 == -128'i8: symexTarget("hit"))
proc sutSubN(x: int8) = (if x == -128'i8 and x - 1'i8 == 127'i8: symexTarget("hit"))
proc sutMulN(x: int8) = (if x == 127'i8 and x * 2'i8 == -2'i8: symexTarget("hit"))
proc sutDivLowN(a: int8) =
  let r = a div -1'i8
  if a == low(int8) and r == low(int8): symexTarget("hit")
proc sutModLowN(a: int8) =
  let r = a mod -1'i8
  if a == low(int8) and r == 0'i8: symexTarget("hit")

const narrowDom = sampled([low(int8), low(int8) + 1, -1'i8, 0'i8, 1'i8,
                           high(int8) - 1, high(int8)])

# ---- the native half: operands and the oracle --------------------------------

type
  V = enum vMin, vMinP1, vMax, vZero, vOne, vTwo, vM1, vThree, vSeven
  Row = object
    key: string
    op: ArithOp
    cls: OperandClass
    name: string                 ## the probe's op: "add" ..
    types: seq[string]
    pairs: seq[(V, V)]

func width(ty: string): int =
  case ty
  of "int64", "uint64": 64
  of "int32", "uint32": 32
  of "int16", "uint16": 16
  else: 8

func signed(ty: string): bool = ty.startsWith("int")

func value(ty: string; v: V): int64 =
  ## The operand as a number (signed types; unsigned `vMax` is read by `bits`).
  let w = width(ty)
  case v
  of vMin: (if signed(ty): -(1'i64 shl (w - 1)) else: 0'i64)
  of vMinP1: (if signed(ty): -(1'i64 shl (w - 1)) + 1 else: 1'i64)
  of vMax:
    if w == 64: (if signed(ty): high(int64) else: -1'i64)
    else: (if signed(ty): (1'i64 shl (w - 1)) - 1 else: (1'i64 shl w) - 1)
  of vZero: 0
  of vOne: 1
  of vTwo: 2
  of vM1: -1
  of vThree: 3
  of vSeven: 7

func bits(ty: string; v: V): uint64 = cast[uint64](value(ty, v))

{.push overflowChecks: on.}
proc overflows64(op: string; a, b: int64): bool =
  try:
    case op
    of "add": discard a + b
    of "sub": discard a - b
    else: discard a * b
    false
  except OverflowDefect:
    true
{.pop.}

proc inTypeOverflow(ty, op: string; a, b: V): bool =
  ## Whether the operation leaves the operand type's own range (independent of
  ## the table and of C). 64 bit: the checked operation; narrower: exact in
  ## `int64`.
  let x = value(ty, a)
  let y = value(ty, b)
  if width(ty) == 64: return overflows64(op, x, y)
  let r = case op
    of "add": x + y
    of "sub": x - y
    else: x * y
  let w = width(ty)
  r < -(1'i64 shl (w - 1)) or r > (1'i64 shl (w - 1)) - 1

proc condHolds(r: Row; ty: string; a, b: V): bool =
  ## The operand condition the row is about, decided without C.
  case r.cls
  of ocSignedWide, ocSignedNarrow: inTypeOverflow(ty, r.name, a, b)
  of ocZeroDivisorSigned, ocZeroDivisorUnsigned: b == vZero
  of ocLowByMinusOneWide, ocLowByMinusOneNarrow: a == vMin and b == vM1
  else: false

const
  addPairs = @[(vMax, vOne), (vMin, vM1), (vMax, vMax), (vOne, vTwo),
               (vMax, vZero), (vMin, vZero), (vMax, vM1), (vSeven, vThree)]
  subPairs = @[(vMin, vOne), (vMax, vM1), (vZero, vMin), (vZero, vZero),
               (vSeven, vThree), (vMin, vM1), (vMax, vOne)]
  mulPairs = @[(vMax, vTwo), (vMin, vM1), (vMin, vTwo), (vSeven, vThree),
               (vMax, vOne), (vMin, vOne), (vZero, vMax), (vM1, vM1)]
  zeroS = @[(vSeven, vZero), (vZero, vZero), (vMin, vZero), (vSeven, vTwo),
            (vSeven, vM1), (vMin, vOne)]
  zeroU = @[(vSeven, vZero), (vZero, vZero), (vMax, vZero), (vSeven, vTwo),
            (vMax, vOne)]
  lowM1 = @[(vMin, vM1), (vMin, vOne), (vMinP1, vM1), (vSeven, vM1),
            (vMin, vTwo)]
  wide = @["int64", "int32"]
  narrow = @["int16", "int8"]

func row(op: ArithOp; cls: OperandClass; name: string; types: seq[string];
         pairs: seq[(V, V)]): Row =
  Row(key: defKey(op, cls), op: op, cls: cls, name: name, types: types,
      pairs: pairs)

let rows = @[
  row(aoAdd, ocSignedWide, "add", wide, addPairs),
  row(aoAdd, ocSignedNarrow, "add", narrow, addPairs),
  row(aoSub, ocSignedWide, "sub", wide, subPairs),
  row(aoSub, ocSignedNarrow, "sub", narrow, subPairs),
  row(aoMul, ocSignedWide, "mul", wide, mulPairs),
  row(aoMul, ocSignedNarrow, "mul", narrow, mulPairs),
  row(aoDiv, ocZeroDivisorUnsigned, "div", @["uint64", "uint32", "uint16"], zeroU),
  row(aoMod, ocZeroDivisorUnsigned, "mod", @["uint64", "uint32", "uint16"], zeroU),
  row(aoDiv, ocZeroDivisorSigned, "div", wide & narrow, zeroS),
  row(aoMod, ocZeroDivisorSigned, "mod", wide & narrow, zeroS),
  row(aoDiv, ocLowByMinusOneWide, "div", wide, lowM1),
  row(aoMod, ocLowByMinusOneWide, "mod", wide, lowM1),
  row(aoDiv, ocLowByMinusOneNarrow, "div", narrow, lowM1),
  row(aoMod, ocLowByMinusOneNarrow, "mod", narrow, lowM1)]

proc casesFor(r: Row; p: DefProfile): seq[UbCase] =
  ## The row's native inputs with the expectation the TABLE gives for `p`.
  let undefined = definedness(r.op, r.cls, p).kind == dkUndefined
  for ty in r.types:
    for (a, b) in r.pairs:
      let cond = r.condHolds(ty, a, b)
      result.add UbCase(ty: ty, op: r.name, a: bits(ty, a), b: bits(ty, b),
                        expect: if undefined and cond: ueTrip else: ueClean,
                        cond: cond)

# The float -> int cells: operands are float64 bit patterns (op "f2i") or
# float32-representable ones (op "f32i"), the target an integer type.
#
# The ORACLE here does not read the table. Nim 2.2.10's C (read from the
# generated code, and what the cases below confirm) casts `int64`, `int` and
# every unsigned target straight to the target, and a signed target narrower
# than the operand's natural integer through `NI64` (`NI32` for a float32
# operand to int8/16): `(NI8)((NI64)f)`. The cast to the intermediate is
# undefined for NaN, an infinity or a truncation outside it; the integer
# conversion from the intermediate to the target is defined (gcc: modulo 2^n).
# `cond` is "the operand is outside the intermediate", decided without C.
const floatTargets = ["int64", "int32", "int16", "int8",
                      "uint64", "uint32", "uint16", "uint8"]

func isUnsigned(ty: string): bool = ty.startsWith("uint")

func interWidth(op, ty: string): int =
  ## The C type the value is cast to first, by the generated C above.
  let natural = if op == "f32i": 32 else: 64
  if not ty.isUnsigned and width(ty) < natural: natural else: width(ty)

func outsideIntermediate(op, ty: string; x: float): bool =
  if x != x or x == Inf or x == -Inf: return true
  let t = trunc(x)
  let iw = interWidth(op, ty)
  if ty.isUnsigned: t < 0.0 or t >= pow(2.0, float(iw))
  else: t < -pow(2.0, float(iw - 1)) or t >= pow(2.0, float(iw - 1))

func f2iOperands(op, ty: string): seq[float] =
  ## Just inside and outside the target's and the intermediate's range, NaN,
  ## infinities, -0.0 and the values between.
  let iw = interWidth(op, ty)
  let w = width(ty)
  let ihi = pow(2.0, float(if ty.isUnsigned: iw else: iw - 1))
  let ilo = if ty.isUnsigned: 0.0 else: -ihi
  result = @[0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 100.0, NaN, Inf, -Inf, 3.0e38,
             -3.0e38, ihi, ilo, ihi - 1.0, ihi - 0.5, ilo - 0.5, ilo - 1.0,
             ihi * 2.0, ilo * 2.0]
  if ty.isUnsigned:
    result.add [-1.0, 255.5, 256.0]
  elif w < iw:
    # past the TARGET but inside the intermediate: a defined wrap
    let thi = pow(2.0, float(w - 1))
    result.add [thi, thi + 44.0, -thi - 1.0, -thi - 100.0, thi * 4.0 + 7.0]
  if op == "f2i": result.add [1.0e30, -1.0e30, 9.223372036854775808e18,
                              9.2233720368547748e18, -9.223372036854775808e18]

func f2iCases(p: DefProfile; direct: bool): seq[UbCase] =
  ## The cases of one cell: `direct` is `convert/floatToInt`, else the narrowed
  ## `convert/floatToIntVia`. The expectation is the TABLE's, for the class the
  ## lowering function names, and its intermediate must be the oracle's.
  for op in ["f2i", "f32i"]:
    for ty in floatTargets:
      let low = floatToIntLowering(if op == "f32i": 32 else: 64, width(ty),
                                   not ty.isUnsigned)
      doAssert low.via == interWidth(op, ty), "the table's intermediate " &
        "disagrees with the C: " & op & " " & ty
      if (low.cls == ocFloatToInt) != direct: continue
      let undefined = convertDefinedness(low.cls, p).kind == dkUndefined
      for x0 in f2iOperands(op, ty):
        # the probe narrows a "f32i" operand to float32: judge that value
        let x = if op == "f32i": float64(float32(x0)) else: x0
        let cond = outsideIntermediate(op, ty, x)
        result.add UbCase(ty: ty, op: op, a: cast[uint64](x), b: 0,
                          expect: if undefined and cond: ueTrip else: ueClean,
                          cond: cond)

proc cellOf(r: Row): CellKey = parseCellKey("defined:" & r.key).get

# ---- the suite ---------------------------------------------------------------

suite "K10c: the walker half (checks-off profile)":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 300

  test "the build is the unchecked profile":
    check coOverflow notin buildSemantics.checks

  test "signed wide add, sub, mul: the overflow side halts":
    pinDecline(sutAddW, cellKey(axDefinedness, "add/signedWide"),
               definedness(aoAdd, ocSignedWide, dpUnchecked).ub)
    pinDecline(sutSubW, cellKey(axDefinedness, "sub/signedWide"),
               definedness(aoSub, ocSignedWide, dpUnchecked).ub)
    pinDecline(sutMulW, cellKey(axDefinedness, "mul/signedWide"),
               definedness(aoMul, ocSignedWide, dpUnchecked).ub)

  test "zero divisors halt, signed and unsigned":
    pinDecline(sutDivZS, cellKey(axDefinedness, "div/zeroDivisorSigned"),
               definedness(aoDiv, ocZeroDivisorSigned, dpUnchecked).ub)
    pinDecline(sutModZS, cellKey(axDefinedness, "mod/zeroDivisorSigned"),
               definedness(aoMod, ocZeroDivisorSigned, dpUnchecked).ub)
    pinDecline(sutDivZU, cellKey(axDefinedness, "div/zeroDivisorUnsigned"),
               definedness(aoDiv, ocZeroDivisorUnsigned, dpUnchecked).ub)
    pinDecline(sutModZU, cellKey(axDefinedness, "mod/zeroDivisorUnsigned"),
               definedness(aoMod, ocZeroDivisorUnsigned, dpUnchecked).ub)

  test "low(T) by -1 at 32 or 64 bits halts":
    pinDecline(sutDivLow, cellKey(axDefinedness, "div/lowByMinusOneWide"),
               definedness(aoDiv, ocLowByMinusOneWide, dpUnchecked).ub)
    pinDecline(sutModLow, cellKey(axDefinedness, "mod/lowByMinusOneWide"),
               definedness(aoMod, ocLowByMinusOneWide, dpUnchecked).ub)

  test "the narrow rows are defined: exact, the wrap included":
    for (op, cls) in [(aoAdd, ocSignedNarrow), (aoSub, ocSignedNarrow),
                      (aoMul, ocSignedNarrow), (aoDiv, ocLowByMinusOneNarrow),
                      (aoMod, ocLowByMinusOneNarrow)]:
      check definedness(op, cls, dpUnchecked).kind == dkDefined
    check pinExact(sutAddN, cellKey(axDefinedness, "add/signedNarrow"), domain = narrowDom).status == sxSat
    check pinExact(sutSubN, cellKey(axDefinedness, "sub/signedNarrow"), domain = narrowDom).status == sxSat
    check pinExact(sutMulN, cellKey(axDefinedness, "mul/signedNarrow"), domain = narrowDom).status == sxSat
    check pinExact(sutDivLowN, cellKey(axDefinedness, "div/lowByMinusOneNarrow"), domain = narrowDom).status == sxSat
    check pinExact(sutModLowN, cellKey(axDefinedness, "mod/lowByMinusOneNarrow"), domain = narrowDom).status == sxSat

suite "K10c: the table against C (UBSan)":
  test "the oracle: every cell has operands that meet its condition":
    for r in rows:
      var met, unmet = 0
      for ty in r.types:
        for (a, b) in r.pairs:
          if r.condHolds(ty, a, b): inc met else: inc unmet
      check met > 0
      check unmet > 0

  when defined(windows):
    test "no UBSan on this toolchain: each cell is declared, not run":
      for r in rows:
        skipCell(r.cellOf, "UBSan does not exist for mingw gcc or MSVC; the " &
          "cell is pinned by the walker half and by the Linux legs' UBSan run")
    test "no float-cast sanitizer on this toolchain: the float cell is declared":
      skipCell(parseCellKey("defined:convert/floatToInt").get,
        "UBSan does not exist for mingw gcc or MSVC; the cell is pinned by " &
        "the walker half (tsymex_0016_k10af_float) and by the Linux legs' " &
        "-fsanitize=float-cast-overflow run")
  else:
    test "the float -> int cells (-fsanitize=float-cast-overflow)":
      let p = buildFloatToIntProbe("K10c-f2i")
      defer: dispose(p)
      for (key, direct) in [("defined:convert/floatToInt", true),
                            ("defined:convert/floatToIntVia", false)]:
        let cases = f2iCases(dpUnchecked, direct)
        check cases.anyIt(it.expect == ueTrip)
        check cases.anyIt(it.expect == ueClean and it.cond == false)
        pinUbsanCell(parseCellKey(key).get, p, cases)
        # NaN, an infinity and a value outside the intermediate each trip; a
        # value inside it (the truncation, and for the narrowed cell the wrap,
        # included) does not.
        for c in cases:
          if c.cond: check c.expect == ueTrip
          else: check c.expect == ueClean

    test "the narrowed cell: a value past the target wraps, defined":
      # Inside the intermediate, outside the target: C converts modulo 2^n and
      # UBSan is silent. The values are what the walker models.
      let p = buildFloatToIntProbe("K10c-f2i-wrap")
      defer: dispose(p)
      for (ty, op, x, want) in [("int8", "f2i", 300.0, "44"),
                                ("int8", "f2i", -156.0, "100"),
                                ("int8", "f2i", 128.9, "-128"),
                                ("int16", "f2i", 65535.0, "-1"),
                                ("int32", "f2i", 4294967291.0, "-5"),
                                ("int32", "f2i", 9.0e18, "-494665728"),
                                ("int8", "f32i", 300.0, "44"),
                                ("int16", "f32i", 65535.0, "-1")]:
        let (rc, output) = p.runCase(UbCase(ty: ty, op: op,
          a: cast[uint64](x), b: 0, expect: ueClean))
        check rc == 0
        check "runtime error" notin output
        check output.strip == want
      check convertDefinedness(ocFloatToIntVia, dpUnchecked).kind == dkUndefined

    test "the default build profile (-fsanitize=undefined)":
      let p = buildUbsanProbe("K10c")
      defer: dispose(p)
      for r in rows:
        pinUbsanCell(r.cellOf, p, r.casesFor(dpUnchecked))
      pinNever(cellKey(axBuild, "cflags/sanitize"),
               cfSanitize in buildProvenance.assumedAbsent,
               "nelli assumes -fsanitize absent; all " & $rows.len &
               " arithmetic rows agree with C under -fsanitize=undefined")

    test "the -fwrapv profile: the wrap is defined, the divisions are not":
      let p = buildUbsanProbe("K10c-fwrapv", fwrapv = true)
      defer: dispose(p)
      for r in rows:
        pinUbsanCell(r.cellOf, p, r.casesFor(dpFwrapv), hardTrapOk = true)

    test "RED guard: a wrong claim is refused (an undefined input called clean)":
      let p = buildUbsanProbe("K10c-guard")
      defer: dispose(p)
      var bad = rows[0].casesFor(dpUnchecked)
      for c in bad.mitems:
        if c.expect == ueTrip: c.expect = ueClean
      expect PinFailure:
        pinUbsanCell(rows[0].cellOf, p, bad)
      var bad2 = rows[0].casesFor(dpUnchecked)
      for c in bad2.mitems:
        if c.expect == ueClean: c.expect = ueTrip
      expect PinFailure:
        pinUbsanCell(rows[0].cellOf, p, bad2)

suite "K10c: the C flags nelli assumes absent are rendered":
  test "the note names every flag assumed absent":
    let n = assumedAbsentNote()
    for f in buildProvenance.assumedAbsent: check $f in n

  test "docs/symex/README.md names every flag the provenance knows":
    let readme = readFile(currentSourcePath().parentDir.parentDir / "docs" /
                          "symex" / "README.md")
    for f in CFlag: check ("`" & $f) in readme

  test "an undefined halt carries the note":
    let r = symexFind(sutAddW, tLabel("hit"))
    var carried = false
    for e in r.errors:
      if e.kind == ubSignedOverflow and assumedAbsentNote() in e.msg:
        carried = true
    check carried
