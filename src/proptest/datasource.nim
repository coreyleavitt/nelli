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

import std/[math, unicode]
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
  ## Draw a float and record it. Generation draws a raw 64-bit pattern (so NaN,
  ## ±Inf, ±0 and subnormals all occur) and coerces it to a permitted value;
  ## the recorded value replays bit-exactly. A singleton range is forced.
  let forced = min == max
  let raw = if ds.replaying: ds.takeReplay(ckFloat).floatVal
            else: cast[float64](ds.rng.next)
  let value = coerceFloat(raw, min, max, smallestNonzeroMagnitude, allowNan)
  ds.recorded.add ChoiceNode(
    wasForced: forced, kind: ckFloat, floatVal: value,
    floatC: FloatConstraints(min: min, max: max, allowNan: allowNan,
                             smallestNonzeroMagnitude: smallestNonzeroMagnitude))
  value

proc drawInteger*(ds: var DataSource, min, max, shrinkTowards: Int128): Int128 =
  ## Draw a uniform integer in `[min, max]` and record it. Native-typed bounds
  ## have a span that fits in 64 bits; `span.lo + 1` wraps to 0 precisely when
  ## the range is the full 2^64, which `bounded` reads as "any uint64" — so the
  ## whole int64/uint64 domain is covered without overflow or special-casing. A
  ## singleton range is recorded as forced; replayed values are clamped into the
  ## current bounds so the draw is always permitted.
  let span = max - min
  let forced = span == toInt128(0)
  var value: Int128
  if ds.replaying:
    value = clamp(ds.takeReplay(ckInteger).intVal, min, max)
  else:
    value = min + toInt128(bounded(ds.rng, span.lo + 1'u64))
  ds.recorded.add ChoiceNode(
    wasForced: forced, kind: ckInteger, intVal: value,
    intC: IntConstraints(min: min, max: max,
                         shrinkTowards: clamp(shrinkTowards, min, max)))
  value

proc drawBytes*(ds: var DataSource, minSize, maxSize: int): seq[byte] =
  ## Draw a byte string whose length is in `[minSize, maxSize]` and record it.
  var value: seq[byte]
  if ds.replaying:
    value = ds.takeReplay(ckBytes).bytesVal
  else:
    let n = minSize + int(bounded(ds.rng, uint64(maxSize - minSize + 1)))
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
  ## Draw a string whose length (in codepoints) is in `[minSize, maxSize]` and
  ## whose every codepoint lies in `intervals`, then record it.
  var value: string
  if ds.replaying:
    value = ds.takeReplay(ckString).strVal
  else:
    let n = minSize + int(bounded(ds.rng, uint64(maxSize - minSize + 1)))
    for _ in 0 ..< n:
      value.add $Rune(drawCodepoint(ds, intervals))
  ds.recorded.add ChoiceNode(
    wasForced: false, kind: ckString, strVal: value,
    strC: StringConstraints(intervals: intervals, minSize: minSize, maxSize: maxSize))
  value
