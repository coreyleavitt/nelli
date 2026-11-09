## RFC-0016 PRC-07 (range half). This file builds with `--rangeChecks:off`
## (its `.nim.cfg`). With the check compiled out, a range conversion is the
## plain C cast and nothing else, so the walker models exactly that instead of
## declining every routine with `feCheckOption`.
##
## Native, read from the generated C of the pinned toolchain (c backend,
## `--rangeChecks:off`, a `noinline` identity feeding the operand), against the
## checks-on build, where each of the first six raises `RangeDefect`:
##   int8(300)         ((NI8) v)           44      signed narrowing: truncates
##   int32(5000000000) ((NI32) v)          705032704
##   chr(300)          ((NIM_CHAR) v)      44      (`char` is NU8)
##   R(300), R = range[0..10]   v          300     the value is kept, no store narrows
##   Natural(-3)       v                   -3      a range of `int`: kept
##   MyEnum(99)        ((tyEnum) v)        99      an enum is an NU8 typedef in C
##   uint8(300'u64)    ((NU8) v)           44      never checked, with or
##                                         without the option: control
## None is undefined in C (an out-of-range signed-to-narrower conversion is
## implementation-defined, and gcc, clang and cl.exe all wrap), so none belongs on
## the definedness axis. What an out-of-range value does LATER is the later
## operation's own check: `s[r]` on a seq still raises `IndexDefect`, but an
## array indexed by its own index type (`array[R, T]`, `array[MyEnum, T]`) has
## no bound check emitted at all, so `arr[MyEnum(99)] = 1` writes out of the
## array in C: undefined. That is the definedness row `index/unchecked`
## (`ubArrayOutOfBounds`): the out-of-array side halts at the access, the
## in-range side stays exact (UBSan `-fsanitize=bounds` pins the row below).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/definedness
import nelli/smt/errorkind
import ./s8cu_helpers
import ./ubsan_support

type
  MyEnum = enum meA, meB, meC
  R = range[0 .. 10]

const rk = cellKey(axBuild, "rangeChecks=off")
const ik = cellKey(axDefinedness, "index/unchecked")

proc sutInt8(v: int) =
  if v > 127 and int8(v) == 44'i8: symexTarget("hit")

proc sutInt32(v: int) =
  if v == 5000000000 and int32(v) == 705032704'i32: symexTarget("hit")

proc sutChr(v: int) =
  if v > 255 and ord(chr(v)) == 44: symexTarget("hit")

proc sutRangeKept(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")

proc sutNatural(v: int) =
  let n = Natural(v)
  if int(n) == -3: symexTarget("hit")

proc sutEnum(v: int) =
  let e = MyEnum(v)
  if ord(e) == 99: symexTarget("hit")

proc sutU8(v: uint64) =
  if v > 255'u64 and uint8(v) == 44'u8: symexTarget("hit")

proc sutRangeNoRaise(v: int) =
  ## The checks-on build raises here at 300; with the check off nothing does.
  discard R(v)

proc sutSeqIdx(v: int) =
  ## A seq index is checked against the length whatever the option says.
  var s = newSeq[int](3)
  let r = R(v)
  discard s[r]

proc sutArrGuarded(v: int) =
  var arr: array[R, int]
  if v >= 0 and v <= 10:
    arr[R(v)] = 1
    if v == 11: symexTarget("hit")

proc sutArrRead(v: int) =
  var arr: array[R, int]
  arr[2] = 7
  let r = R(v)
  if arr[r] == 7: symexTarget("hit")

proc sutArrOob(v: int) =
  ## The label is past the access, so only an out-of-range `v` could reach it:
  ## that side is undefined and the access halts.
  var arr: array[R, int]
  arr[R(v)] = 1
  if v < 0 or v > 10: symexTarget("hit")

proc sutArrReadOob(v: int) =
  var arr: array[R, int]
  arr[2] = 7
  let x = arr[R(v)]
  if x == 7 and (v < 0 or v > 10): symexTarget("hit")

proc sutEnumOob(v: int) =
  ## An enum is an `NU8` in C, so `MyEnum(v)` keeps the low byte: the ordinal,
  ## not `v`, is what leaves the array.
  var arr: array[MyEnum, int]
  let e = MyEnum(v)
  arr[e] = 1
  if ord(e) > 2: symexTarget("hit")

proc sutArrIdx(v: int) =
  var arr: array[R, int]
  arr[R(v)] = 1
  if v == 5: symexTarget("hit")

suite "PRC-07: range conversions with --rangeChecks:off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 309

  test "the build has the range check off and the others on":
    check coRange notin buildSemantics.checks
    check acRange notin arithChecksFor()
    check coOverflow in buildSemantics.checks

  test "int8(v) truncates":
    let r = pinExact(sutInt8, rk, domain = sampled([300, 44, 0]))
    check r.status == sxSat
    check r.trusted

  test "int32(v) truncates":
    let r = pinExact(sutInt32, rk, domain = sampled([5000000000, 0]))
    check r.status == sxSat
    check r.trusted

  test "chr(v) truncates":
    let r = pinExact(sutChr, rk, domain = sampled([300, 44, 0]))
    check r.status == sxSat
    check r.trusted

  test "range[0..10](v) keeps the out-of-range value":
    let r = pinExact(sutRangeKept, rk, domain = sampled([300, 5, 0]))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 300

  test "Natural(v) keeps a negative value":
    let r = pinExact(sutNatural, rk, domain = sampled([-3, 0]))
    check r.status == sxSat
    check r.trusted

  test "MyEnum(v) keeps an out-of-range ordinal":
    let r = pinExact(sutEnum, rk, domain = sampled([99, 1, 0]))
    check r.status == sxSat
    check r.trusted

  test "uint8(v) of a uint64 truncates (control: unchecked in every build)":
    let r = pinExact(sutU8, rk, domain = sampled([300'u64, 0'u64]))
    check r.status == sxSat
    check r.trusted

  test "no RangeDefect is reachable: an exact unsat":
    let r = pinExact(sutRangeNoRaise, rk, target = tRaisedExn("RangeDefect"),
                     domain = sampled([300, 5, -1]))
    check r.status == sxUnsat
    check r.trusted

  test "a seq index of the kept value still raises IndexDefect":
    let r = pinExact(sutSeqIdx, rk, target = tRaisedExn("IndexDefect"),
                     domain = sampled([300, 5, 1]))
    check r.status == sxRaised
    check r.trusted

  test "an array indexed by its own type, out of range, halts as undefined":
    # `arr[R(300)] = 1` writes outside the array: the out-of-range side ends
    # at the access with `ubArrayOutOfBounds`. It is not an `IndexDefect` and
    # not a `feCheckOption` decline.
    pinDecline(sutArrOob, ik, ubArrayOutOfBounds,
               excluding = {feCheckOption})
    let o = symexFind(sutArrOob, tRaisedExn("IndexDefect"))
    check o.status != sxRaised
    check not o.errors.named(feCheckOption)

  test "an array read at an out-of-range typed index halts too":
    pinDecline(sutArrReadOob, ik, ubArrayOutOfBounds,
               excluding = {feCheckOption})

  test "an enum-indexed array, out of range, halts too":
    pinDecline(sutEnumOob, ik, ubArrayOutOfBounds,
               excluding = {feCheckOption})

  test "unguarded, the in-range witness is exact and trusted":
    # The out-of-array side is reachable, and it is on the definedness axis,
    # so it does not taint the run: the witness is the native one and the
    # verdict stays trusted. The undefined side is a finding with its site.
    let r = symexFind(sutArrIdx, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 5
    check r.trusted
    check not r.errors.named(feCheckOption)
    check r.undefined.len == 1
    check r.undefined[0].kind == UbKind(ubArrayOutOfBounds)
    check "no bound check emitted" in r.undefined[0].site
    check "tsymex_0016_rangeoff" in r.undefined[0].site
    check r.undefined[0].witness[0] notin 0 .. 10

  test "tUndefined asks for the out-of-array input":
    let r = symexFind(sutArrIdx, tUndefined({UbKind(ubArrayOutOfBounds)}))
    check r.status == sxSat
    check r.witness[0] notin 0 .. 10
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubArrayOutOfBounds)}

  test "an in-range witness agrees with C (pinExact over in-range inputs)":
    let r = pinExact(sutArrIdx, rk, domain = sampled([5, 0, 10]))
    check r.status == sxSat
    check r.trusted

  test "a guard that rules the out-of-range side out leaves no halt":
    let r = pinExact(sutArrGuarded, rk, domain = sampled([-1, 0, 10, 11, 300]))
    check r.status == sxUnsat
    check r.trusted
    let g = symexFind(sutArrGuarded, tLabel("hit"))
    check g.undefined.len == 0

suite "PRC-07: index/unchecked against C (rangeChecks:off)":
  when defined(windows):
    test "no UBSan on this toolchain: the cell is declared, not run":
      skipCell(ik, "UBSan does not exist for mingw gcc or MSVC; the cell " &
        "is pinned by the walker half and by the Linux legs' " &
        "-fsanitize=bounds run")
  else:
    test "the table's row against -fsanitize=bounds":
      let p = buildIndexProbe("rangeoff-ubsan", indexBoundsFlags(
        ["--rangeChecks:off"]))
      defer: dispose(p)
      check definedness.admitDefined(aoIndex, ocUncheckedAccess,
        dsIndex).payload[dpChecked].kind == dkUndefined
      var cases: seq[UbCase]
      for (ty, lim) in [("arrR", 10), ("arrE", 2)]:
        for k in [-1, 0, 1, lim, lim + 1, lim + 290]:
          let outside = k < 0 or k > lim
          cases.add UbCase(ty: ty, op: "rd", a: cast[uint64](int64(k)), b: 0,
            expect: (if outside: ueTrip else: ueClean), cond: outside)
      for k in [-1, 5, 11, 300]:
        let outside = k < 0 or k > 10
        cases.add UbCase(ty: "arrR", op: "wr", a: cast[uint64](int64(k)),
          b: 0, expect: (if outside: ueTrip else: ueClean), cond: outside)
      pinUbsanCell(ik, p, cases)
