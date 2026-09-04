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
    ##
    ## RFC-0010: the defaults are declared on the fields, so a partial literal
    ## carries them and an all-zero one means what it says -- an unbiased,
    ## uniform draw -- instead of being read as a sentinel for "use the
    ## defaults". That sentinel was `resolved()`, now retired.
    boundaryPercent*: int = 30
      ## Probability (0-100) the draw goes through the boundary path
      ## (favoring `shrinkTowards`, ±1, ±0, min, max, near-min, near-max).
    smallWindowPercent*: int = 30
      ## Probability (0-100) the draw lands in a small magnitude window
      ## around `shrinkTowards`.
    smallWindowSize*: int = 64
      ## Window width: small-window draws fall in
      ## `[clamp(st - size, min, max), clamp(st + size, min, max)]`.
    shrinkTowardsWeight*: int = 50
      ## Within the boundary path, the percentage (0-100) that
      ## short-circuits to `clamp(shrinkTowards, min, max)` directly
      ## (rather than picking from the full boundary set).

const defaultIntegerBias* = IntegerBiasConfig()
  ## RFC-0010: the values live on the type now, so this is the empty literal.
  ## Kept as a name for one release.

proc resolved*(cfg: IntegerBiasConfig): IntegerBiasConfig {.deprecated:
    "RFC-0010: IntegerBiasConfig declares its own field defaults, so a partial " &
    "literal already carries them and there is nothing left to resolve. An " &
    "all-zero config now means an unbiased uniform draw, which is what it " &
    "says. Removed at the next major.".} =
  ## Identity. This was the sentinel: an all-zero `IntegerBiasConfig` was read
  ## as "no explicit policy set; use the library default", so that a caller
  ## could write `Settings(...)` as an object literal without listing
  ## `integerBias` and still get 30/30/40.
  ##
  ## That was a bespoke fix for one field of one type, and RFC-0010 is the
  ## general one. Keeping it as identity for a release means the ~2 call sites
  ## and any downstream use keep compiling while the deprecation message
  ## explains the change.
  ##
  ## Note the behavioural consequence, which the audit has to carry: an
  ## EXPLICIT all-zero config used to be rescued to the defaults and is now
  ## honoured. That is the correct reading -- zero has to keep meaning what a
  ## caller wrote -- but it is a silent change for anyone who was relying on
  ## the sentinel.
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
