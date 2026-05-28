## The shortlex shrinker.
##
## Given a falsifying choice sequence, repeatedly transform it to find a
## shortlex-smaller sequence that still falsifies the property — by *re-running*
## the strategy + property over candidate sequences. A candidate is "interesting"
## iff the property still raises when replayed through it; candidates that
## overrun, reject, or pass are uninteresting.
##
## This first slice implements **lexicographic lowering**: for each integer
## node, binary-search the smallest value (between `shrinkTowards` and the
## current value) that still falsifies. Span-directed deletion and the rest of
## the pass suite are next.

import std/unicode
import ./choice, ./datasource, ./strategy, ./int128

type
  ShrinkResult*[T] = object
    choices*: seq[ChoiceNode]
    example*: T
    flaky*: bool
      ## True when the final minimized candidate fails to reproduce the
      ## failure on replay — i.e. shrinking-time non-determinism slipped past
      ## the engine's pre-shrink retries. The engine reports this as `otFlaky`.

proc complexity*(n: ChoiceNode): Int128 =
  ## Per-node "complexity" used by `sortKeyLess`: distance from each kind's
  ## natural zero target. For ints it's `|value - shrinkTowards|`; for floats
  ## the raw bit pattern (so ±0 < ±1 < … < big magnitudes in absolute terms);
  ## for bools 0=false, 1=true; for bytes/strings a length-shifted byte/char
  ## sum (length dominates within equal sequence length).
  case n.kind
  of ckInteger:
    if n.intVal < n.intC.shrinkTowards:
      n.intC.shrinkTowards - n.intVal
    else:
      n.intVal - n.intC.shrinkTowards
  of ckFloat:
    # Magnitude-based: the IEEE-754 bit pattern of `abs(x)` is monotone in
    # magnitude for finite floats (±0 → 0, ±1.0 → 0x3FF0…, ±Inf → 0x7FF0…)
    # and places NaN above ±Inf (NaN bit pattern is 0x7FF…<nonzero>). Sign
    # is irrelevant for "simplicity" — `-1.0` and `+1.0` are equally far
    # from zero, and a signed cast made negative floats look *simpler* than
    # zero, breaking shortlex ordering.
    toInt128(cast[uint64](abs(n.floatVal)))
  of ckBoolean:
    if n.boolVal: toInt128(1) else: toInt128(0)
  of ckBytes:
    var sum: int64 = 0
    for b in n.bytesVal: sum += int64(b)
    toInt128((int64(n.bytesVal.len) shl 16) or sum)
  of ckString:
    # Count *codepoints*, not bytes — `runeLen` and `runes` so multi-byte
    # UTF-8 doesn't inflate both the length and the sum and skew shortlex.
    # Sum is over codepoint ordinals so "shorter codepoint sequence wins"
    # dominates within equal-length comparisons.
    var sum: int64 = 0
    for r in n.strVal.runes: sum += int64(int32(r))
    toInt128((int64(n.strVal.runeLen) shl 24) or sum)

proc sortKeyLess*(a, b: seq[ChoiceNode]): bool =
  ## Strict shortlex ordering over choice sequences: shorter is smaller; for
  ## equal length, lexicographic by per-node `complexity`. This is the
  ## ordering the shrinker minimizes against — exposed so callers can compare
  ## candidate sequences explicitly.
  if a.len != b.len:
    return a.len < b.len
  for i in 0 ..< a.len:
    let ca = complexity(a[i])
    let cb = complexity(b[i])
    if ca != cb: return ca < cb
  false

proc tryFalsifies*[T](s: Strategy[T], prop: proc(x: T),
                      candidate: seq[ChoiceNode]
                     ): tuple[fails: bool, x: T, spans: seq[Span]] =
  ## Replay `candidate` through `s`, then run `prop`. Returns `fails = true` iff
  ## the property still fails — any other outcome (rejection, overrun, pass) is
  ## "not interesting" and the candidate must not be kept. The recorded spans
  ## are returned so the deletion pass can target structural ranges.
  var ds = newReplaySource(candidate)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return (false, x, ds.spans)
  except CatchableError, Defect:
    # The strategy itself raised a falsifying error (e.g., a per-step invariant
    # inside a stateful strategy). Still a falsification.
    return (true, x, ds.spans)
  try:
    prop(x); (false, x, ds.spans)
  except Rejection:
    (false, x, ds.spans)
  except CatchableError, Defect:
    (true, x, ds.spans)

proc lowerStringAt[T](s: Strategy[T], prop: proc(x: T),
                      choices: var seq[ChoiceNode], idx: int) =
  ## Truncate the string to `minSize` codepoints (filled with the smallest
  ## allowed codepoint), then lower each remaining codepoint toward that
  ## smallest. The smallest codepoint is the first interval's `lo`.
  let node = choices[idx]
  if node.kind != ckString or node.wasForced: return
  let iv = node.strC.intervals
  if iv.ranges.len == 0: return
  let smallestCp = iv.ranges[0].lo
  let smallestRune = $Rune(smallestCp)
  let minSize = node.strC.minSize
  let curLen = node.strVal.runeLen
  if curLen > minSize:
    var truncated = ""
    for _ in 0 ..< minSize: truncated.add smallestRune
    var cand = choices
    cand[idx].strVal = truncated
    if tryFalsifies(s, prop, cand).fails:
      choices = cand
      return
  # Lower each codepoint toward smallestCp.
  var runes: seq[Rune]
  for r in choices[idx].strVal.runes: runes.add r
  for i in 0 ..< runes.len:
    if int32(runes[i]) == smallestCp: continue
    var newRunes = runes
    newRunes[i] = Rune(smallestCp)
    var ns = ""
    for r in newRunes: ns.add $r
    var cand = choices
    cand[idx].strVal = ns
    if tryFalsifies(s, prop, cand).fails:
      choices = cand
      runes = newRunes

proc lowerBytesAt[T](s: Strategy[T], prop: proc(x: T),
                     choices: var seq[ChoiceNode], idx: int) =
  ## Try truncating bytes to `minSize` (zero-filled) and then lower each byte
  ## toward 0. A `minSize`-length all-zero sequence is the zero form.
  let node = choices[idx]
  if node.kind != ckBytes or node.wasForced: return
  let cur = node.bytesVal
  let minSize = node.bytesC.minSize
  # Try truncation to minSize (all zero bytes).
  if cur.len > minSize:
    var cand = choices
    cand[idx].bytesVal = newSeq[byte](minSize)
    if tryFalsifies(s, prop, cand).fails:
      choices = cand
      return
  # Lower each byte to 0.
  for i in 0 ..< choices[idx].bytesVal.len:
    if choices[idx].bytesVal[i] == 0'u8: continue
    var cand = choices
    cand[idx].bytesVal[i] = 0'u8
    if tryFalsifies(s, prop, cand).fails:
      choices = cand

proc lowerBoolAt[T](s: Strategy[T], prop: proc(x: T),
                    choices: var seq[ChoiceNode], idx: int) =
  ## Try flipping an unforced `true` to `false` (the zero form). If the
  ## property still falsifies, accept the change. A `false` is already at the
  ## target; forced bools are immutable.
  let node = choices[idx]
  if node.kind != ckBoolean or node.wasForced: return
  if not node.boolVal: return
  var cand = choices
  cand[idx].boolVal = false
  if tryFalsifies(s, prop, cand).fails:
    choices = cand

proc lowerFloatAt[T](s: Strategy[T], prop: proc(x: T),
                     choices: var seq[ChoiceNode], idx: int) =
  ## Binary-search a failing float toward the in-range value closest to 0
  ## (sign preserved when possible). The *target floor* is `clamp(0, min,
  ## max)` — for an all-positive range this is `min`, for an all-negative
  ## range it's `max`. Writing 0.0 unconditionally would store a value that
  ## violates the node's `[min, max]` constraint and make `repro()` lie;
  ## replay would still reproduce (via `coerceFloat`) but the IR invariant
  ## would be broken. NaN is left alone (no useful order).
  let node = choices[idx]
  if node.kind != ckFloat or node.wasForced: return
  let cur = node.floatVal
  if cur != cur: return     # NaN — no ordering
  let lo = node.floatC.min
  let hi = node.floatC.max
  let floor = clamp(0.0, lo, hi)
  if cur == floor: return   # already at the in-range zero-equivalent

  # Try the floor directly first.
  var cand = choices
  cand[idx].floatVal = floor
  if tryFalsifies(s, prop, cand).fails:
    choices = cand
    return

  # Binary-search between `floor` and `cur` along the line `(1-t)*floor + t*cur`
  # (t in [0, 1]). Both endpoints are in `[min, max]` by construction, so every
  # interpolated candidate is too. Invariant: `tPass` passes, `tFail` fails.
  var tPass = 0.0
  var tFail = 1.0
  for _ in 0 ..< 60:
    if tFail - tPass <= 1e-12: break
    let tMid = (tPass + tFail) * 0.5
    let mid = (1.0 - tMid) * floor + tMid * cur
    cand = choices
    cand[idx].floatVal = mid
    if tryFalsifies(s, prop, cand).fails:
      tFail = tMid
      choices = cand
    else:
      tPass = tMid

proc lowerIntegerAt[T](s: Strategy[T], prop: proc(x: T),
                       choices: var seq[ChoiceNode], idx: int) =
  ## Binary-search the value closest to `shrinkTowards` (on the same side as
  ## `cur`) that still falsifies, and write it into `choices[idx]`. Works in
  ## both directions: `cur > target` shrinks down toward the target, `cur <
  ## target` shrinks up. Skips forced nodes, values already at the target,
  ## and values outside the native int64 range (rare for hand-written
  ## strategies; the binary search uses int64 arithmetic).
  let node = choices[idx]
  if node.kind != ckInteger or node.wasForced: return
  let target = node.intC.shrinkTowards
  let cur = node.intVal
  if cur == target: return
  if not fitsInt64(target) or not fitsInt64(cur): return

  # Try the target itself first — if it still falsifies, we're done.
  var cand = choices
  cand[idx].intVal = target
  if tryFalsifies(s, prop, cand).fails:
    choices = cand
    return

  # Binary-search on the half-open segment `(target, cur]` (or `[cur, target)`
  # if cur < target). Invariant: pred(`passSide`) = pass, pred(`failSide`) = fail.
  # `passSide` starts at target (just shown to pass), `failSide` at cur.
  var passSide = toInt64(target)
  var failSide = toInt64(cur)
  while (if passSide < failSide: failSide - passSide else: passSide - failSide) > 1:
    let mid = passSide + (failSide - passSide) div 2
    cand = choices
    cand[idx].intVal = toInt128(mid)
    if tryFalsifies(s, prop, cand).fails:
      failSide = mid
      choices = cand
    else:
      passSide = mid

proc deleteSpansPass[T](s: Strategy[T], prop: proc(x: T),
                        choices: var seq[ChoiceNode]) =
  ## Structure-respecting deletion: for each recorded span, try removing all of
  ## its nodes; keep the candidate when the property still fails. Restarts after
  ## each successful deletion so we work with fresh spans.
  var changed = true
  while changed:
    changed = false
    let res = tryFalsifies(s, prop, choices)
    if not res.fails: return  # defensive — caller hands us a falsifying seq
    for span in res.spans:
      if span.finish <= span.start: continue
      var cand = newSeqOfCap[ChoiceNode](choices.len - (span.finish - span.start))
      for j in 0 ..< choices.len:
        if j < span.start or j >= span.finish:
          cand.add choices[j]
      if tryFalsifies(s, prop, cand).fails:
        choices = cand
        changed = true
        break

proc shrink*[T](s: Strategy[T], prop: proc(x: T),
                choices: seq[ChoiceNode],
                maxShrinks = 500): ShrinkResult[T] =
  ## Apply the shrink passes to a falsifying sequence and return the minimized
  ## sequence with the example it regenerates. Passes are run to a fixed point
  ## (deletion shortens, lowering minimizes contents); `maxShrinks` caps the
  ## outer fixpoint iterations so a pathological case can't loop indefinitely.
  var best = choices
  var prev: seq[ChoiceNode]
  var iter = 0
  # `maxShrinks <= 0` means unlimited — preserves the old default for callers
  # that didn't know about the cap (e.g. explicit `Settings(…)` literals).
  while best != prev and (maxShrinks <= 0 or iter < maxShrinks):
    inc iter
    prev = best
    deleteSpansPass(s, prop, best)
    for i in 0 ..< best.len:
      case best[i].kind
      of ckInteger: lowerIntegerAt(s, prop, best, i)
      of ckFloat:   lowerFloatAt(s, prop, best, i)
      of ckBoolean: lowerBoolAt(s, prop, best, i)
      of ckBytes:   lowerBytesAt(s, prop, best, i)
      of ckString:  lowerStringAt(s, prop, best, i)
  let res = tryFalsifies(s, prop, best)
  # If the final candidate doesn't reproduce, the property was flaky at some
  # point during shrinking — flag it rather than asserting; the engine will
  # report `otFlaky` so the user knows their property is non-deterministic.
  ShrinkResult[T](choices: best, example: res.x, flaky: not res.fails)
