## The DataSource: what strategies draw primitives from.
##
## Each draw both *produces* a value and *records* a matching `ChoiceNode` into
## `recorded` — the choice sequence the shrinker and example database operate on.
##
## Two modes share one type:
## * **generation** (`newDataSource`) samples values from the RNG;
## * **replay** (`newReplaySource`) reads values from a previously recorded
##   sequence, so a stored failure regenerates identically.
##
## During replay, drawing past the end of the sequence — or drawing a different
## *kind* than was recorded at that position — raises `Overrun`. Per the
## conjecture model, "the only way a choice sequence can be invalid is for it to
## be too short," so the engine treats an overrun as a clean not-interesting
## outcome rather than an error.

import std/[math, unicode, options]
import ./rng, ./choice, ./int128

type
  Overrun* = object of CatchableError
    ## Raised when a replay draws past the recorded sequence or misaligns on kind.

  Span* = object
    ## A labeled, semantically-meaningful range `[start, finish)` of draw indices
    ## in `recorded`. Spans nest (depth-first) and give the shrinker structure-
    ## aware deletion boundaries. The `label` is opaque — spans with the same
    ## meaning share a label.
    label*: int
    start*, finish*: int

  DataSource* = object
    rng: SplitMix64
    prerecorded: seq[ChoiceNode]  ## replay source (empty in generation mode)
    cursor: int                   ## replay read position
    replaying: bool
    recorded*: seq[ChoiceNode]    ## the choice sequence built up by draws
    spans*: seq[Span]             ## completed spans over `recorded`
    spanStack: seq[tuple[label, start: int]]  ## open spans (depth-first)

func newDataSource*(rng: SplitMix64): DataSource =
  ## A generation-mode source backed by `rng`.
  DataSource(rng: rng, replaying: false)

func newReplaySource*(prerecorded: seq[ChoiceNode]): DataSource =
  ## A replay-mode source that yields the values in `prerecorded`.
  DataSource(prerecorded: prerecorded, replaying: true)

func isReplaying*(ds: DataSource): bool {.inline.} =
  ## Whether `ds` is replaying a prerecorded sequence. Strategies that do
  ## generation-only work (biased rolls, weighted picks) **must** gate it on
  ## this so replay reads cleanly from the recorded sequence — otherwise a
  ## replay would consume one node where generation consumed two, and the
  ## cursor walks out of alignment.
  ds.replaying

proc nextRoll*(ds: var DataSource): float64 =
  ## A generation-time uniform fraction in `[0, 1)` for strategy-side biasing
  ## decisions (weights, swarm). Pulled from `ds.rng` directly — *not* recorded
  ## as a choice node — so replay does not consult it. Strategies must gate use
  ## on `not ds.isReplaying`.
  float64(ds.rng.next shr 11) * (1.0 / 9007199254740992.0)

proc startSpan*(ds: var DataSource, label: int) =
  ## Open a span at the current draw position.
  ds.spanStack.add (label: label, start: ds.recorded.len)

proc endSpan*(ds: var DataSource) =
  ## Close the innermost open span, recording its `[start, finish)` range.
  let top = ds.spanStack.pop()
  ds.spans.add Span(label: top.label, start: top.start, finish: ds.recorded.len)

proc takeReplay(ds: var DataSource, kind: ChoiceKind): ChoiceNode =
  ## Consume the next recorded node, requiring it to match `kind`.
  if ds.cursor >= ds.prerecorded.len:
    raise newException(Overrun, "choice sequence exhausted")
  result = ds.prerecorded[ds.cursor]
  if result.kind != kind:
    raise newException(Overrun, "choice kind mismatch during replay")
  inc ds.cursor

proc drawBoolean*(ds: var DataSource, p: float): bool =
  ## Draw a boolean true with probability `p`. p<=0 forces false, p>=1 forces
  ## true (recorded forced); otherwise the value comes from the replay sequence
  ## or, in generation, the RNG's high bits.
  let forced = p <= 0.0 or p >= 1.0
  var value: bool
  if ds.replaying:
    let node = ds.takeReplay(ckBoolean)  # consume for alignment even when forced
    value = (if p <= 0.0: false elif p >= 1.0: true else: node.boolVal)
  elif forced:
    value = p >= 1.0
  else:
    # 53 high bits → a uniform fraction in [0, 1)
    value = (float(ds.rng.next shr 11) * (1.0 / 9007199254740992.0)) < p
  ds.recorded.add booleanChoice(value, p, forced)
  value

func coerceFloat(v, lo, hi, smallest: float64, allowNan: bool): float64 =
  ## Map an arbitrary float (possibly NaN/Inf/subnormal, as bit-pattern draws
  ## produce) onto a value permitted by the constraints: NaN passes only when
  ## allowed (else 0 clamped into range), values are clamped to [lo,hi], and a
  ## nonzero magnitude below `smallest` snaps to 0 (then re-clamped).
  if v != v:  # NaN
    if allowNan: return v
    return clamp(0.0, lo, hi)
  result = clamp(v, lo, hi)
  if result != 0.0 and abs(result) < smallest:
    result = clamp(0.0, lo, hi)

proc drawFloat*(ds: var DataSource, min, max: float64, allowNan: bool,
                smallestNonzeroMagnitude: float64): float64 =
  ## Draw a float and record it. In replay, the recorded bits are passed
  ## through `coerceFloat`. In generation, with ~30% probability we boundary-
  ## inject one of the "interesting" floats (±0, NaN if allowed, ±Inf, ±1,
  ## bounds) — these are where float bugs cluster. The remaining 70% draws a
  ## raw 64-bit pattern, so NaN/±Inf/subnormals still occur naturally. The
  ## chosen value is always passed through `coerceFloat` to land within
  ## constraints. A singleton range is forced.
  let forced = min == max
  var raw: float64
  if ds.replaying:
    raw = ds.takeReplay(ckFloat).floatVal
  elif forced:
    raw = min
  else:
    let roll = ds.rng.next mod 100'u64
    if roll < 30'u64:
      let subroll = ds.rng.next mod 100'u64
      if subroll < 40'u64:
        # Zero — both signs.
        raw = if (ds.rng.next mod 4'u64) == 0'u64: -0.0 else: 0.0
      elif allowNan and subroll < 70'u64:
        raw = NaN
      elif subroll < 80'u64:
        raw = Inf
      elif subroll < 90'u64:
        raw = NegInf
      else:
        let opts = [1.0, -1.0, min, max]
        raw = opts[int(ds.rng.next mod uint64(opts.len))]
    else:
      raw = cast[float64](ds.rng.next)
  let value = coerceFloat(raw, min, max, smallestNonzeroMagnitude, allowNan)
  ds.recorded.add ChoiceNode(
    wasForced: forced, kind: ckFloat, floatVal: value,
    floatC: FloatConstraints(min: min, max: max, allowNan: allowNan,
                             smallestNonzeroMagnitude: smallestNonzeroMagnitude))
  value

proc integerBoundaries(min, max, shrinkTowards: Int128): seq[Int128] =
  ## Candidate "interesting" values for boundary injection: shrinkTowards, 0,
  ## ±1, the bounds, and the near-bounds, filtered to those in range. Most
  ## integer bugs cluster around these values.
  let candidates = [shrinkTowards,
                    toInt128(0), toInt128(1), toInt128(-1),
                    min, max,
                    min + toInt128(1), max - toInt128(1)]
  for c in candidates:
    if min <= c and c <= max:
      result.add c
  if result.len == 0:
    result.add min

proc drawInteger*(ds: var DataSource, min, max, shrinkTowards: Int128,
                  forced: Option[Int128] = none(Int128)): Int128 =
  ## Draw an integer in `[min, max]` and record it. Replay clamps the recorded
  ## value. In generation, a caller-supplied `forced` value is used verbatim
  ## (preserves the original constraints for shrinkability — used by weighted
  ## strategies); otherwise distribution biasing kicks in: ~5% boundary
  ## injection (from `integerBoundaries`), ~30% small-magnitude window of
  ## ±64 around `shrinkTowards`, ~65% uniform fall-through. Bias is generation-
  ## only — replay reads one node per draw exactly as before.
  let span = max - min
  let isSingleton = span == toInt128(0)
  var value: Int128
  if ds.replaying:
    value = clamp(ds.takeReplay(ckInteger).intVal, min, max)
  elif forced.isSome:
    value = clamp(forced.get, min, max)
  elif isSingleton:
    value = min
  else:
    let roll = ds.rng.next mod 100'u64
    if roll < 30'u64:
      # Boundary injection. Within a boundary roll, weight `shrinkTowards`
      # heavily (50%) — most integer bugs cluster on the shrink target — and
      # spread the remaining 50% across the other candidates (0, ±1, bounds,
      # near-bounds).
      let subroll = ds.rng.next mod 100'u64
      if subroll < 50'u64:
        value = clamp(shrinkTowards, min, max)
      else:
        let cs = integerBoundaries(min, max, shrinkTowards)
        let idx = ds.rng.next mod uint64(cs.len)
        value = cs[idx]
    elif roll < 60'u64:
      const window = 64'i64
      let st = clamp(shrinkTowards, min, max)
      let smallLo = clamp(st - toInt128(window), min, max)
      let smallHi = clamp(st + toInt128(window), min, max)
      let smallSpan = smallHi - smallLo
      value = smallLo + toInt128(bounded(ds.rng, smallSpan.lo + 1'u64))
    else:
      # `count` is the number of admissible values in `[min, max]`. For
      # `span >= 2^64 - 1` the addition wraps in Int128 modular arithmetic
      # (which is exactly what bounded128 expects: `n.hi == 1, n.lo == 0`
      # represents `count = 2^64`, and so on for wider ranges).
      let count = span + toInt128(1)
      value = min + bounded128(ds.rng, count)
  ds.recorded.add ChoiceNode(
    wasForced: isSingleton or forced.isSome,
    kind: ckInteger, intVal: value,
    intC: IntConstraints(min: min, max: max,
                         shrinkTowards: clamp(shrinkTowards, min, max)))
  value

const
  maxBytesSize* = 1_048_576       ## 1 MB — hard cap on `drawBytes` length.
  maxStringRunes* = 65_536        ## 64 K codepoints — hard cap on `drawString`.

proc drawBytes*(ds: var DataSource, minSize, maxSize: int): seq[byte] =
  ## Draw a byte string whose length is in `[minSize, min(maxSize, maxBytesSize)]`
  ## and record it. `maxSize` is silently clamped: a hostile or programmer-error
  ## value like `high(int)` would otherwise overflow the `+1` width computation
  ## and drive an unbounded allocation. Replay raises `Overrun` if the recorded
  ## value's length is no longer admissible under the current bounds — the IR
  ## per-node invariant is preserved across constraint changes by treating
  ## the recording as stale rather than silently rewriting the value.
  var value: seq[byte]
  if ds.replaying:
    value = ds.takeReplay(ckBytes).bytesVal
    if value.len < minSize or value.len > maxSize:
      raise newException(Overrun,
        "recorded bytes length " & $value.len & " is no longer in [" &
        $minSize & ", " & $maxSize & "]")
  else:
    let cappedMax = min(maxSize, maxBytesSize)
    let cappedMin = min(minSize, cappedMax)
    let span = uint64(cappedMax - cappedMin) + 1'u64
    let n = cappedMin + int(bounded(ds.rng, span))
    value = newSeq[byte](n)
    for i in 0 ..< n:
      value[i] = byte(ds.rng.next and 0xFF'u64)
  ds.recorded.add ChoiceNode(
    wasForced: false, kind: ckBytes, bytesVal: value,
    bytesC: BytesConstraints(minSize: minSize, maxSize: maxSize))
  value

proc drawCodepoint(ds: var DataSource, iv: IntervalSet): int32 =
  ## Uniformly pick an allowed codepoint across the interval set's total span.
  var total = 0'u64
  for r in iv.ranges:
    total += uint64(r.hi - r.lo + 1)
  if total == 0:
    return 0'i32
  var k = bounded(ds.rng, total)
  for r in iv.ranges:
    let size = uint64(r.hi - r.lo + 1)
    if k < size:
      return r.lo + int32(k)
    k -= size
  iv.ranges[0].lo  # unreachable for a non-empty set

proc drawString*(ds: var DataSource, intervals: IntervalSet,
                 minSize, maxSize: int): string =
  ## Draw a string whose length (in codepoints) is in
  ## `[minSize, min(maxSize, maxStringRunes)]` and whose every codepoint lies
  ## in `intervals`, then record it. `maxSize` is silently clamped (see
  ## `drawBytes` for the same reason). Replay raises `Overrun` if the
  ## recorded value's codepoint length or character set are no longer
  ## admissible — same stale-recording semantics as `drawBytes`.
  var value: string
  if ds.replaying:
    value = ds.takeReplay(ckString).strVal
    let cpLen = value.runeLen
    if cpLen < minSize or cpLen > maxSize:
      raise newException(Overrun,
        "recorded string length " & $cpLen & " codepoints is no longer in [" &
        $minSize & ", " & $maxSize & "]")
    for r in value.runes:
      if int32(r) notin intervals:
        raise newException(Overrun,
          "recorded codepoint " & $int32(r) &
          " is no longer in the strategy's interval set")
  else:
    let cappedMax = min(maxSize, maxStringRunes)
    let cappedMin = min(minSize, cappedMax)
    let span = uint64(cappedMax - cappedMin) + 1'u64
    let n = cappedMin + int(bounded(ds.rng, span))
    for _ in 0 ..< n:
      value.add $Rune(drawCodepoint(ds, intervals))
  ds.recorded.add ChoiceNode(
    wasForced: false, kind: ckString, strVal: value,
    strC: StringConstraints(intervals: intervals, minSize: minSize, maxSize: maxSize))
  value
