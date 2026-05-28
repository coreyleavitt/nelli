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

import ./rng, ./choice, ./int128

type
  Overrun* = object of CatchableError
    ## Raised when a replay draws past the recorded sequence or misaligns on kind.

  DataSource* = object
    rng: SplitMix64
    prerecorded: seq[ChoiceNode]  ## replay source (empty in generation mode)
    cursor: int                   ## replay read position
    replaying: bool
    recorded*: seq[ChoiceNode]    ## the choice sequence built up by draws

func newDataSource*(rng: SplitMix64): DataSource =
  ## A generation-mode source backed by `rng`.
  DataSource(rng: rng, replaying: false)

func newReplaySource*(prerecorded: seq[ChoiceNode]): DataSource =
  ## A replay-mode source that yields the values in `prerecorded`.
  DataSource(prerecorded: prerecorded, replaying: true)

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
