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
