## Integer distribution biasing for `drawInteger` (#103).
##
## Extracted from `datasource.nim` so the bias policy is:
##
## 1. **Unit-testable** — `selectBoundaryValue` and `selectSmallWindowValue`
##    can be exercised in isolation with deterministic RNG seeds, instead
##    of inferred statistically from full-pipeline draws.
## 2. **Tunable** — `IntegerBiasConfig` exposes the previously-hardcoded
##    constants (boundary %, small-window %, window size, shrinkTowards
##    weight) so users can override per-test bias when the default isn't
##    aggressive enough for their domain (heavy arithmetic, parser fuzzing).
## 3. **Composable** — `DataSource` carries an `integerBias` field; the
##    engine can populate it from `Settings` (future hook).
##
## The default values match the long-standing behavior in `datasource.nim`
## before this extraction: 30% boundary, 30% small-window of ±64 around
## `shrinkTowards`, 40% uniform — with 50% shrinkTowards weight inside
## the boundary roll.

import ../int128, ../rng

type
  IntegerBiasConfig* = object
    ## Tunable biasing policy for `drawInteger`. The percentages must
    ## satisfy `boundaryPercent + smallWindowPercent <= 100`; the
    ## remainder falls through to the uniform draw.
    boundaryPercent*: int
      ## Probability (0-100) the draw goes through the boundary path
      ## (favoring `shrinkTowards`, ±1, ±0, min, max, near-min, near-max).
    smallWindowPercent*: int
      ## Probability (0-100) the draw lands in a small magnitude window
      ## around `shrinkTowards`.
    smallWindowSize*: int
      ## Window width: small-window draws fall in
      ## `[clamp(st - size, min, max), clamp(st + size, min, max)]`.
    shrinkTowardsWeight*: int
      ## Within the boundary path, the percentage (0-100) that
      ## short-circuits to `clamp(shrinkTowards, min, max)` directly
      ## (rather than picking from the full boundary set).

const defaultIntegerBias* = IntegerBiasConfig(
  boundaryPercent: 30,
  smallWindowPercent: 30,
  smallWindowSize: 64,
  shrinkTowardsWeight: 50)

proc resolved*(cfg: IntegerBiasConfig): IntegerBiasConfig =
  ## Treat an all-zero (zero-initialised) `IntegerBiasConfig` as the
  ## sentinel for "no explicit policy set; use the library default."
  ## This lets a caller construct `Settings(...)` as an object literal
  ## without listing `integerBias`, and still get the default 30/30/40
  ## bias semantics — without us having to invent an `Option`-typed
  ## field on Settings (which would change the literal construction
  ## ergonomics for every existing test).
  ##
  ## The "everything genuinely 0/0/0/0" config has no legitimate use
  ## (smallWindowSize=0 makes the small-window math degenerate; all
  ## three percentages at zero is already expressible via the default
  ## by setting `smallWindowSize: 1` or any nonzero token field).
  if cfg.boundaryPercent == 0 and cfg.smallWindowPercent == 0 and
     cfg.smallWindowSize == 0 and cfg.shrinkTowardsWeight == 0:
    defaultIntegerBias
  else:
    cfg

# --- the integer-boundary candidate set ---------------------------------------

proc integerBoundaries*(min, max, shrinkTowards: Int128): seq[Int128] =
  ## Bug-cluster values: shrinkTowards, 0, ±1, the constraint bounds, and
  ## one off-bound on each side. All filtered to `[min, max]`.
  let candidates = [shrinkTowards,
                    toInt128(0), toInt128(1), toInt128(-1),
                    min, max,
                    min + toInt128(1), max - toInt128(1)]
  for c in candidates:
    if min <= c and c <= max:
      result.add c
  if result.len == 0:
    result.add min

# --- the helpers ----------------------------------------------------------------

proc selectBoundaryValue*(rng: var SplitMix64,
                          min, max, shrinkTowards: Int128,
                          config: IntegerBiasConfig): Int128 =
  ## Draw one value from the boundary path: with `shrinkTowardsWeight%`
  ## probability return `clamp(shrinkTowards, min, max)` directly,
  ## otherwise pick uniformly from `integerBoundaries`.
  let subroll = rng.next mod 100'u64
  if subroll < uint64(config.shrinkTowardsWeight):
    return clamp(shrinkTowards, min, max)
  let cs = integerBoundaries(min, max, shrinkTowards)
  let idx = rng.next mod uint64(cs.len)
  cs[idx]

proc selectSmallWindowValue*(rng: var SplitMix64,
                             min, max, shrinkTowards: Int128,
                             config: IntegerBiasConfig): Int128 =
  ## Draw uniformly inside the small-magnitude window
  ## `[clamp(st - size, min, max), clamp(st + size, min, max)]`. The
  ## window collapses to a singleton if it falls entirely outside
  ## `[min, max]` — caller's responsibility to clamp the result.
  let st = clamp(shrinkTowards, min, max)
  let smallLo = clamp(st - toInt128(config.smallWindowSize), min, max)
  let smallHi = clamp(st + toInt128(config.smallWindowSize), min, max)
  let smallSpan = smallHi - smallLo
  smallLo + toInt128(bounded(rng, smallSpan.lo + 1'u64))
