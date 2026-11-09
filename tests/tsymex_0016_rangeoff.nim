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
## array in C: undefined, and not modelled (the cell below declines it).
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type
  MyEnum = enum meA, meB, meC
  R = range[0 .. 10]

const rk = cellKey(axBuild, "rangeChecks=off")

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

proc sutArrIdx(v: int) =
  var arr: array[R, int]
  arr[R(v)] = 1
  if v == 5: symexTarget("hit")

suite "PRC-07: range conversions with --rangeChecks:off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 306

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

  test "an array indexed by its own type, out of range, is declined (UB in C)":
    # Not modelled: `arr[R(300)] = 1` writes outside the array. The out-of-range
    # side is declined with `feCheckOption`, never an `IndexDefect`.
    let o = symexFind(sutArrIdx, tRaisedExn("IndexDefect"))
    checkpoint show(o.errors)
    check o.status != sxRaised
    check not o.trusted
    check o.errors.named(feCheckOption)

  test "unguarded, the witness is the in-range one but the run stays untrusted":
    # The out-of-array side is reachable, and a reachable decline taints the
    # run: the witness itself is the native one. A guard (next test) makes the
    # verdict exact. Modelling the access as an undefined kind of the
    # definedness axis would keep the in-range witness trusted (remainder).
    let r = symexFind(sutArrIdx, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 5
    check not r.trusted
    check r.errors.named(feCheckOption)

  test "a guard that rules the out-of-range side out leaves no decline":
    let r = pinExact(sutArrGuarded, rk, domain = sampled([-1, 0, 10, 11, 300]))
    check r.status == sxUnsat
    check r.trusted

  test "an array read at an out-of-range typed index is declined too":
    let r = symexFind(sutArrRead, tLabel("hit"))
    checkpoint show(r.errors)
    check r.errors.named(feCheckOption)
