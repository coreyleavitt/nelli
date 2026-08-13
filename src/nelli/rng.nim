## SplitMix64 — a small, fast, value-type PRNG.
##
## It is the entropy source the `DataSource` draws from during generation. As a
## plain value `object`, copying it yields an independent, identical stream,
## which is what lets the engine snapshot/replay generation deterministically
## without threading a global RNG. (The reproducibility *unit* is ultimately the
## recorded choice sequence, not the seed — but a deterministic RNG underpins it.)

type
  SplitMix64* = object
    state: uint64

func initSplitMix64*(seed: uint64): SplitMix64 =
  SplitMix64(state: seed)

func next*(r: var SplitMix64): uint64 =
  ## Advance the generator and return the next 64-bit value (the standard
  ## SplitMix64 mixing function; its high bits are well-distributed, unlike
  ## xoroshiro128+'s low bit).
  r.state = r.state + 0x9E3779B97F4A7C15'u64
  var z = r.state
  z = (z xor (z shr 30)) * 0xBF58476D1CE4E5B9'u64
  z = (z xor (z shr 27)) * 0x94D049BB133111EB'u64
  z = z xor (z shr 31)
  z

func bounded*(r: var SplitMix64, n: uint64): uint64 =
  ## Uniform in `[0, n)` for `n > 0`, using rejection to eliminate modulo bias.
  ## (`n == 0` is treated as the full `uint64` range — the caller's "2^64 values"
  ## case — and returns a raw draw.)
  if n == 0:
    return r.next
  let limit = (high(uint64) div n) * n  # largest multiple of n that fits
  while true:
    let x = r.next
    if x < limit:
      return x mod n

import ./int128

func bounded128*(r: var SplitMix64, n: Int128): Int128 =
  ## Uniform in `[0, n)` for a non-negative 128-bit `n`. Treats `n` as an
  ## unsigned 128-bit value (`n.hi * 2^64 + n.lo`). The fast path delegates
  ## to `bounded` when the range fits in u64. For wider ranges we draw two
  ## 64-bit words, mask down to the smallest power-of-two ceiling of `n`, and
  ## rejection-sample — accept rate ≥ 50%, so the expected number of draws
  ## per call is ≤ 2.
  doAssert n.hi >= 0, "bounded128 requires non-negative n"
  if n.hi == 0:
    return toInt128(bounded(r, n.lo))
  # Find k such that 2^(k-1) <= n < 2^k, with k in [65, 128].
  var k = 64
  var probe = uint64(n.hi)
  while probe > 0'u64:
    inc k
    probe = probe shr 1
  let topMask = if k < 128: (1'u64 shl (k - 64)) - 1'u64 else: high(uint64)
  let nHi = uint64(n.hi)
  while true:
    let xHi = r.next and topMask
    let xLo = r.next
    if xHi < nHi or (xHi == nHi and xLo < n.lo):
      return Int128(hi: int64(xHi), lo: xLo)
