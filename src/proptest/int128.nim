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

func clamp*(x, lo, hi: Int128): Int128 =
  ## Constrain `x` to the closed interval `[lo, hi]`.
  if x < lo: lo
  elif hi < x: hi
  else: x
