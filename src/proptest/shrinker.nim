## The shortlex shrinker.
##
## Given a falsifying choice sequence, repeatedly transform it to find a
## shortlex-smaller sequence that still falsifies the property — by *re-running*
## the strategy + property over candidate sequences. A candidate is "interesting"
## iff the property still raises when replayed through it; candidates that
## overrun, reject, or pass are uninteresting.
##
## The pass suite runs to fixpoint:
## * **`deleteSpansPass`** — drop whole spans (one list element, one Table
##   entry, etc.) at a time, restarting from fresh spans after each accept.
## * **`lowerIntegerAt`** — binary-search the closest-to-`shrinkTowards`
##   value that still falsifies (works in both directions: positive `cur`
##   shrinks down, negative `cur` shrinks up).
## * **`lowerFloatAt`** — interpolate between `cur` and the in-range floor
##   `clamp(0, min, max)`, binary-searching for the smallest magnitude still
##   falsifying. Stored value satisfies `floatC.min ≤ v ≤ floatC.max`.
## * **`lowerBoolAt`** — flip `true → false` when still falsifying.
## * **`lowerBytesAt`** — truncate then zero-fill.
## * **`lowerStringAt`** — truncate then lower each codepoint to the
##   interval-set's minimum.

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
  ## Binary-search a failing float toward the smallest-magnitude *permitted*
  ## value in the strategy's constraints (sign-preserving where possible).
  ## The floor is computed as: `0` when zero is in range, otherwise the
  ## min-magnitude end of the range, snapped above `smallestNonzeroMagnitude`
  ## if needed. Interpolated mid-values that fall in the forbidden window
  ## `(-smallestNonzero, smallestNonzero)` are not stored — they pass-direct
  ## the bisect so the loop makes progress without violating the IR
  ## invariant. NaN current value is left alone (no useful order).
  let node = choices[idx]
  if node.kind != ckFloat or node.wasForced: return
  let cur = node.floatVal
  if cur != cur: return     # NaN — no ordering
  let lo = node.floatC.min
  let hi = node.floatC.max
  let smallest = node.floatC.smallestNonzeroMagnitude

  # Smallest-magnitude permitted value in [lo, hi].
  let floor =
    if lo <= 0.0 and 0.0 <= hi: 0.0           # zero straddles the range
    elif lo > 0.0: max(lo, smallest)          # range entirely positive
    else: min(hi, -smallest)                  # range entirely negative
  if not node.floatC.permits(floor): return   # no permitted target — give up
  if cur == floor: return

  var cand = choices
  cand[idx].floatVal = floor
  if tryFalsifies(s, prop, cand).fails:
    choices = cand
    return

  # Binary-search between `floor` and `cur` along the line `(1-t)*floor + t*cur`.
  # Both endpoints are permitted by construction; *interpolated* mids may not
  # be (they can land in the smallestNonzeroMagnitude forbidden window). When
  # `permits` rejects a mid we treat it as "passes" — advancing `tPass`
  # toward `tFail` — so the search continues on the failing side.
  var tPass = 0.0
  var tFail = 1.0
  for _ in 0 ..< 60:
    if tFail - tPass <= 1e-12: break
    let tMid = (tPass + tFail) * 0.5
    let mid = (1.0 - tMid) * floor + tMid * cur
    if not node.floatC.permits(mid):
      tPass = tMid
      continue
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
  ## both directions. Distance/mid arithmetic is done in `Int128` so the
  ## difference `failSide - passSide` cannot overflow even at the int64
  ## extremes (e.g. `cur = low(int64), target = 0` gives a 2^63 distance).
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

  # Binary-search in `Int128` between `target` (passes) and `cur` (fails).
  var passSide = target
  var failSide = cur
  let one = toInt128(1)
  while true:
    let dist = if passSide < failSide: failSide - passSide
               else: passSide - failSide
    if not (dist > one): break
    # Mid = passSide + (failSide - passSide) / 2 in 128-bit arithmetic,
    # avoiding overflow at the int64 extremes. We compute `(failSide - passSide)
    # div 2` then add to `passSide`. Int128 division is not (yet) in the
    # library; for the common case `dist` fits in u64 we narrow and divide
    # there. Distance > uint64.max requires int128-spanning bounds, which
    # the public `integers(int, int)` API never produces.
    if dist.hi != 0:
      break  # 128-bit distance bisection not implemented; out of scope today
    let halfStep = dist.lo div 2'u64
    let mid = if passSide < failSide: passSide + toInt128(halfStep)
              else: passSide - toInt128(halfStep)
    cand = choices
    cand[idx].intVal = mid
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
