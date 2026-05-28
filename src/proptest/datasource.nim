## The DataSource: what strategies draw primitives from.
##
## Each draw both *produces* a value (in generation mode, sampled from the RNG;
## replay mode comes later) and *records* a matching `ChoiceNode` into `recorded`
## — the choice sequence the shrinker and example database operate on. A draw
## never violates its constraints, and the p=0/p=1 (and analogous) boundaries are
## honored exactly so dependent generation stays correct.

import ./rng, ./choice, ./int128

type
  DataSource* = object
    rng: SplitMix64
    recorded*: seq[ChoiceNode]  ## the choice sequence built up by draws

func newDataSource*(rng: SplitMix64): DataSource =
  ## A generation-mode source backed by `rng`.
  DataSource(rng: rng)

proc drawBoolean*(ds: var DataSource, p: float): bool =
  ## Draw a boolean that is true with probability `p`. p<=0 forces false and
  ## p>=1 forces true (recorded as forced, hence unshrinkable); otherwise the
  ## value is sampled from the RNG's high bits.
  var value: bool
  var forced = false
  if p <= 0.0:
    value = false; forced = true
  elif p >= 1.0:
    value = true; forced = true
  else:
    # 53 high bits → a uniform fraction in [0, 1)
    let frac = float(ds.rng.next shr 11) * (1.0 / 9007199254740992.0)
    value = frac < p
  ds.recorded.add booleanChoice(value, p, forced)
  value

proc drawInteger*(ds: var DataSource, min, max, shrinkTowards: Int128): Int128 =
  ## Draw a uniform integer in `[min, max]` and record it. For native-typed
  ## bounds the span fits in 64 bits; `span.lo + 1` wraps to 0 precisely when the
  ## range is the full 2^64, which `bounded` interprets as "any uint64" — so the
  ## whole int64/uint64 domain is covered with no overflow and no special-casing.
  ## A singleton range (`min == max`) is recorded as forced.
  let span = max - min
  let forced = span == toInt128(0)
  let offset = bounded(ds.rng, span.lo + 1'u64)
  let value = min + toInt128(offset)
  ds.recorded.add ChoiceNode(
    wasForced: forced, kind: ckInteger, intVal: value,
    intC: IntConstraints(min: min, max: max,
                         shrinkTowards: clamp(shrinkTowards, min, max)))
  value
