## RFC-0016 K9e -- pin strength, the bounds / wrap / compare / arithmetic-
## lowering cluster. Each check below is a call the walker answers and the
## natively compiled proc confirms (`pinFind` / `pinExact`), chosen so that one
## mutant of `runtime.nim`'s Int-sorted encoding (`cmpInt`, `arithInt`,
## `intBounds`, `intWindow`, `wrapIntToWidth`), of the BV compare lowering
## (`lowerCmp`) or of the arithmetic lowering (`lowerArith`) changes the verdict:
## a witness the binary does not reach, or a hit the binary does reach lost.
##
## Where the mutant turns a hit into an `sxUnsat`, the native domain is named
## (`sampled`) so that it holds the input that reaches the label; where it
## turns an `sxUnsat` into a spurious `sxSat`, the witness replay catches it.
##
## An Int-sorted ("promoted") value is a signed `int`/`intN` parameter the
## suite bounds with a leading `symexAssume` (`collectAssertRanges`), or an
## `uint8(x)` / `s.len.uint` conversion of one; plain parameters are
## bit-vectors and reach the `lowerCmp` / `binBV` lines instead.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

# ---- Int-sorted compare (`cmpInt`) -----------------------------------------

proc sutIntLeGe(x, y: int) =
  ## `<=` and `>=` at equality: reached only if both are non-strict.
  symexAssume(x >= 0 and x <= 10)
  symexAssume(y >= 0 and y <= 10)
  if x <= y and x >= y: symexTarget("hit")

proc sutIntGtLe(x, y: int) =
  ## `>` is strict: `x > y and x <= y` has no solution.
  symexAssume(x >= 0 and x <= 10)
  symexAssume(y >= 0 and y <= 10)
  if x > y and x <= y: symexTarget("hit")

# ---- Int-sorted arithmetic (`arithInt`) ------------------------------------

proc sutIntMul(x, y: int) =
  symexAssume(x >= 0 and x <= 20)
  symexAssume(y >= 0 and y <= 20)
  if x * y == 35 and x < y: symexTarget("hit")

# ---- the width bounds (`intBounds`, width 8) -------------------------------

proc sutI8Low(x, y: int8) =
  ## `x + y` ranges over [-128, -90]: inside int8, so no overflow fork, and
  ## -128 is reachable.
  symexAssume(x >= -128 and x <= -100)
  symexAssume(y >= 0 and y <= 10)
  if x + y == -128: symexTarget("hit")

proc sutI8High(x, y: int8) =
  symexAssume(x >= 100 and x <= 127)
  symexAssume(y >= -10 and y <= 0)
  if x + y == 127: symexTarget("hit")

# ---- the unsigned window and its wrap (`intWindow`, `wrapIntToWidth`) ------

proc sutU8WrapZero(x: int) =
  ## `uint8(255) + 1` wraps to 0.
  symexAssume(x >= 0 and x <= 1000)
  let u = uint8(x)
  if u + 1'u8 == 0'u8: symexTarget("hit")

proc sutU8WrapOne(x: int) =
  ## `uint8(255) + 2` wraps to 1 (a wrap that lands off zero).
  symexAssume(x >= 0 and x <= 1000)
  let u = uint8(x)
  if u + 2'u8 == 1'u8: symexTarget("hit")

proc sutU8WrapRange(x: int) =
  ## `uint8(254) + 1` is 255, outside `range[0 .. 254]`: a RangeDefect.
  symexAssume(x >= 0 and x <= 1000)
  let u = uint8(x) + 1'u8
  var r: range[0 .. 254] = int(u)
  if r == 3: symexTarget("hit")

proc sutLenMinusOne(s: string) =
  ## `0'u - 1` wraps to `high(uint)`, far above 2^33.
  if s.len <= 4 and s.len.uint - 1'u > 20_000_000_000'u:
    symexTarget("hit")

proc sutLenPlusMax(s: string) =
  ## `1'u + high(uint)` is 2^64, which wraps to 0.
  if s.len <= 4 and s.len.uint + high(uint) == 0'u:
    symexTarget("hit")

# ---- the BV compare lowering (`lowerCmp`) ----------------------------------

proc sutBvLeGe(x, y: int) =
  if x <= y and x >= y: symexTarget("hit")

proc sutBvGtLe(x, y: int) =
  if x > y and x <= y: symexTarget("hit")

proc sutBvUGtLe(x, y: uint) =
  if x > y and x <= y: symexTarget("hit")

# ---- the BV subtraction (`lowerArith`) -------------------------------------

proc sutBvSub(x, y: int) =
  if x - y == 5 and x > 100: symexTarget("hit")

suite "K9e cmp: Int-sorted compare and arithmetic":
  test "<= and >= are non-strict":
    let r = pinFind(sutIntLeGe, tLabel("hit"))
    check r.status == sxSat

  test "> is strict":
    let r = pinFind(sutIntGtLe, tLabel("hit"))
    check r.status == sxUnsat

  test "* is a product":
    let r = pinFind(sutIntMul, tLabel("hit"))
    check r.status == sxSat

suite "K9e cmp: the width bounds":
  test "int8 low(T) is reachable by an in-window sum":
    let r = pinFind(sutI8Low, tLabel("hit"))
    check r.status == sxSat

  test "int8 high(T) is reachable by an in-window sum":
    let r = pinFind(sutI8High, tLabel("hit"))
    check r.status == sxSat

suite "K9e cmp: the unsigned window":
  test "uint8 255 + 1 wraps to 0":
    let r = pinExact(sutU8WrapZero, cellKey(faGeneric, "k9e/cmp/u8wrap0"),
                     domain = sampled([255, 0, 1, 300]))
    check r.status == sxSat

  test "uint8 255 + 2 wraps to 1":
    let r = pinExact(sutU8WrapOne, cellKey(faGeneric, "k9e/cmp/u8wrap1"),
                     domain = sampled([255, 0, 1, 300]))
    check r.status == sxSat

  test "a wrapped uint8 result is up to 255":
    let r = pinExact(sutU8WrapRange, cellKey(faGeneric, "k9e/cmp/u8range"),
                     target = tRaisedExn("RangeDefect"),
                     domain = sampled([254, 0, 5]))
    check r.status == sxRaised

  test "uint64 wraps at 2^64":
    let r = pinFind(sutLenMinusOne, tLabel("hit"))
    check r.status == sxSat

  test "uint64 window top is 2^64 - 1":
    let r = pinFind(sutLenPlusMax, tLabel("hit"))
    check r.status == sxSat

suite "K9e cmp: the BV compare and subtraction":
  test "signed <= and >= are non-strict":
    let r = pinFind(sutBvLeGe, tLabel("hit"))
    check r.status == sxSat

  test "signed > is strict":
    let r = pinFind(sutBvGtLe, tLabel("hit"))
    check r.status == sxUnsat

  test "unsigned > is strict":
    let r = pinFind(sutBvUGtLe, tLabel("hit"))
    check r.status == sxUnsat

  test "subtraction subtracts":
    let r = pinFind(sutBvSub, tLabel("hit"))
    check r.status == sxSat
