## RFC-0016 W1-g -- `x in a..b` / `x notin a..b` (W-31). Each SUT is run
## natively beside the walker's verdict by `pinExact`.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:  # keep a sweep-wide dir; else a private one
  putEnv("NELLI_PIN_DIR", getTempDir() / ("w1g_pins_" & $getCurrentProcessId()))

type E = enum eA = 0, eB = 1, eC = 5, eD = 6, eE = 9

proc inInt(x: int) =
  if x in 0 .. 10 and x == 7: symexTarget("t")

proc inIntFar(x: int) =
  if x in 0 .. 10 and x > 9: symexTarget("t")

proc notinInt(x: int) =
  if x notin 0 .. 10 and x == 11: symexTarget("t")

proc notinIntUnsat(x: int) =
  if x notin 0 .. 10 and x == 7: symexTarget("t")

proc inU8(x: uint8) =
  if x in 200'u8 .. 255'u8 and x == 250'u8: symexTarget("t")

proc inU8Hi(x: uint8) =
  if x in 10'u8 .. 20'u8 and x > 19'u8: symexTarget("t")

proc inChar(c: char) =
  if c in 'a' .. 'z' and c == 'q': symexTarget("t")

proc notinChar(c: char) =
  if c notin 'a' .. 'z' and c == 'A': symexTarget("t")

# eC..eD brackets no named value between eB and eC; the hole values 2..4 are
# not enum members but ordinal range membership never asks.
proc inEnum(e: E) =
  if e in eB .. eD and e == eC: symexTarget("t")

proc inEnumOut(e: E) =
  if e in eB .. eD and e == eE: symexTarget("t")

proc notinEnum(e: E) =
  if e notin eB .. eD and e == eE: symexTarget("t")

proc inExcl(x: int) =
  if x in 0 ..< 10 and x == 9: symexTarget("t")

proc inExclUnsat(x: int) =
  if x in 0 ..< 10 and x == 10: symexTarget("t")

proc inUnsat(x: int) =
  if x in 0 .. 10 and x == 11: symexTarget("t")

proc inVarBounds(x, a, b: int) =
  if a == 3 and b == 5 and x in a .. b and x == 5: symexTarget("t")

proc inVarBoundsEmpty(x, a, b: int) =
  if a == 5 and b == 3 and x in a .. b: symexTarget("t")

proc inExclVar(x, a, b: int) =
  if x in a ..< b and x == 5: symexTarget("t")

proc inExclVarU8(x, a, b: uint8) =
  if x in a ..< b and x == 5'u8: symexTarget("t")

suite "RFC-0016 W1-g: x in a..b":
  test "native ..< at the boundary":
    # int: pred(low(int)) overflows. uint8: `b - 1` wraps, so `0 ..< 0` is the
    # full range and contains 5.
    check nativeRun(inExclVar(5, 0, low(int))).raised == "OverflowDefect"
    check nativeRun(inExclVar(5, 0, 6)).hits.contains("t")
    check not nativeRun(inExclVar(5, 5, 5)).hits.contains("t")
    let r = nativeRun(inExclVarU8(5'u8, 0'u8, 0'u8))
    check r.raised == ""
    check r.hits.contains("t")

  test "version floor":
    check parseInt(symexWalkerVersion) >= 276

  test "int, in":
    let r = pinExact(inInt, cellKey(axConstruct, "in/slice/int"),
                     target = tLabel("t"))
    check r.status == sxSat
  test "int, in, upper":
    check pinExact(inIntFar, cellKey(axConstruct, "in/slice/int/upper"),
                   target = tLabel("t")).status == sxSat
  test "int, notin":
    check pinExact(notinInt, cellKey(axConstruct, "notin/slice/int"),
                   target = tLabel("t")).status == sxSat
  test "int, notin, unsat":
    check pinExact(notinIntUnsat, cellKey(axConstruct, "notin/slice/int/unsat"),
                   target = tLabel("t"),
                   domain = exhaustive(@[-1, 0, 7, 10, 11])).status == sxUnsat
  test "int, unsat":
    check pinExact(inUnsat, cellKey(axConstruct, "in/slice/int/unsat"),
                   target = tLabel("t"),
                   domain = exhaustive(@[-1, 0, 10, 11])).status == sxUnsat
  test "uint8":
    check pinExact(inU8, cellKey(axConstruct, "in/slice/uint8"),
                   target = tLabel("t"),
                   domain = sampled(@[0'u8, 199, 200, 250, 255])).status == sxSat
    check pinExact(inU8Hi, cellKey(axConstruct, "in/slice/uint8/hi"),
                   target = tLabel("t"),
                   domain = sampled(@[0'u8, 19, 20, 21, 255])).status == sxSat
  test "char":
    check pinExact(inChar, cellKey(axConstruct, "in/slice/char"),
                   target = tLabel("t"),
                   domain = sampled(@['a', 'q', 'z', 'A'])).status == sxSat
    check pinExact(notinChar, cellKey(axConstruct, "notin/slice/char"),
                   target = tLabel("t"),
                   domain = sampled(@['a', 'q', 'z', 'A'])).status == sxSat
  test "enum with a hole":
    check pinExact(inEnum, cellKey(axConstruct, "in/slice/enum"),
                   target = tLabel("t"),
                   domain = exhaustive(@[eA, eB, eC, eD, eE])).status == sxSat
    check pinExact(inEnumOut, cellKey(axConstruct, "in/slice/enum/out"),
                   target = tLabel("t"),
                   domain = exhaustive(@[eA, eB, eC, eD, eE])).status == sxUnsat
    check pinExact(notinEnum, cellKey(axConstruct, "notin/slice/enum"),
                   target = tLabel("t"),
                   domain = exhaustive(@[eA, eB, eC, eD, eE])).status == sxSat
  test "..<":
    check pinExact(inExcl, cellKey(axConstruct, "in/slice/excl"),
                   target = tLabel("t")).status == sxSat
    check pinExact(inExclUnsat, cellKey(axConstruct, "in/slice/excl/unsat"),
                   target = tLabel("t"),
                   domain = exhaustive(@[-1, 0, 9, 10, 11])).status == sxUnsat
  test "variable bounds":
    check pinExact(inVarBounds, cellKey(axConstruct, "in/slice/varbounds"),
                   target = tLabel("t"),
                   domain = sampled(@[3, 4, 5, 7])).status == sxSat
    check pinExact(inVarBoundsEmpty, cellKey(axConstruct, "in/slice/empty"),
                   target = tLabel("t"),
                   domain = sampled(@[3, 4, 5, 7])).status == sxUnsat

  test "..< with a variable bound: sat, boundary raise":
    check pinExact(inExclVar, cellKey(axConstruct, "in/slice/excl/var"),
                   target = tLabel("t")).status == sxSat
    check pinExact(inExclVar, cellKey(axConstruct, "in/slice/excl/var/lowRaise"),
                   target = tRaisedExn("OverflowDefect"),
                   domain = sampled(@[low(int), -1, 0, 5, 6, high(int)])).status == sxRaised
  test "..< with a variable uint8 bound":
    let dom = sampled(@[0'u8, 4, 5, 6, 255])
    check pinExact(inExclVarU8, cellKey(axConstruct, "in/slice/excl/var/u8"),
                   target = tLabel("t"), domain = dom).status == sxSat
    # b == 0 wraps natively rather than raising, so no run raises.
    check pinExact(inExclVarU8, cellKey(axConstruct, "in/slice/excl/var/u8/raise"),
                   target = tRaisedExn("OverflowDefect"),
                   domain = dom).status == sxUnsat
