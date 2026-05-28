## A fixed 128-bit two's-complement signed integer.
##
## This is the value domain for proptest's integer choice primitive
## (`ChoiceInt`). 128 bits is the minimal fixed width that losslessly covers
## the entire range of *every* native Nim integer type — crucially the full
## `uint64` range, whose upper half does not fit in `int64`. It is a
## stack-allocated value type: no heap allocation, trivially copyable, and
## usable at compile time. Arbitrary precision (for a future bignum strategy)
## is deliberately *not* handled here; it belongs in a separate primitive so it
## never burdens the integer hot path.
##
## Only the operations the engine currently needs are implemented; arithmetic
## (add/sub/shift, used by the shrinker) is added when that code demands it.

import std/hashes

type
  Int128* = object
    hi*: int64   ## high 64 bits; the sign lives here
    lo*: uint64  ## low 64 bits

func toInt128*(x: SomeSignedInt): Int128 =
  ## Sign-extend a signed integer into 128 bits.
  let v = int64(x)
  Int128(hi: (if v < 0: -1'i64 else: 0'i64), lo: cast[uint64](v))

func toInt128*(x: SomeUnsignedInt): Int128 =
  ## Zero-extend an unsigned integer into 128 bits (preserves the top bit that
  ## `int64` would lose).
  Int128(hi: 0'i64, lo: uint64(x))

func toInt128*(x: int): Int128 =
  ## Concrete overload for the default literal type, so `toInt128(42)` is
  ## unambiguous (an `int` literal matches this exactly and prefers it over the
  ## signed/unsigned generics).
  toInt128(int64(x))

func `==`*(a, b: Int128): bool =
  a.hi == b.hi and a.lo == b.lo

func `<`*(a, b: Int128): bool =
  ## Two's-complement ordering: compare the high limb signed (sign lives there),
  ## then the low limb unsigned when the high limbs are equal.
  if a.hi != b.hi: a.hi < b.hi
  else: a.lo < b.lo

func `<=`*(a, b: Int128): bool =
  not (b < a)

func hash*(x: Int128): Hash =
  !$(0 !& hash(x.hi) !& hash(x.lo))

func toInt64*(x: Int128): int64 =
  ## Narrow to int64 (valid when the value is in int64 range; the low limb is the
  ## two's-complement representation). Values outside int64 wrap.
  cast[int64](x.lo)

func fitsInt64*(x: Int128): bool {.inline.} =
  ## True iff `x` is exactly representable in int64 — i.e. its sign-extension
  ## bit pattern matches the int64 two's-complement encoding (`hi == 0` for
  ## non-negative values up to `high(int64)`, or `hi == -1` for any negative
  ## value). Callers that need to narrow through `toInt64` should gate on this.
  (x.hi == 0 and x.lo <= uint64(high(int64))) or x.hi == -1

func `$`*(x: Int128): string =
  ## Decimal rendering. Every value produced from a native Nim integer has
  ## `hi` either 0 (a value in 0 .. 2^64-1) or -1 (a negative int64), so those
  ## render directly without 128-bit division. A genuine >64-bit value (not
  ## constructible through the current API) falls back to its limbs.
  if x.hi == 0: $x.lo
  elif x.hi == -1: $cast[int64](x.lo)
  else: "i128(" & $x.hi & ", " & $x.lo & ")"

func `+`*(a, b: Int128): Int128 =
  ## Two's-complement 128-bit addition with carry from the low limb.
  result.lo = a.lo + b.lo
  let carry = if result.lo < a.lo: 1'i64 else: 0'i64  # unsigned wrap ⇒ carry
  result.hi = a.hi + b.hi + carry

func `-`*(a, b: Int128): Int128 =
  ## Two's-complement 128-bit subtraction with borrow from the low limb.
  result.lo = a.lo - b.lo
  let borrow = if a.lo < b.lo: 1'i64 else: 0'i64
  result.hi = a.hi - b.hi - borrow

func clamp*(x, lo, hi: Int128): Int128 =
  ## Constrain `x` to the closed interval `[lo, hi]`.
  if x < lo: lo
  elif hi < x: hi
  else: x
