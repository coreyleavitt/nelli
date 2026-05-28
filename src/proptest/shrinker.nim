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

import ./choice, ./datasource, ./strategy, ./int128

type
  ShrinkResult*[T] = object
    choices*: seq[ChoiceNode]
    example*: T
    flaky*: bool
      ## True when the final minimized candidate fails to reproduce the
      ## failure on replay — i.e. shrinking-time non-determinism slipped past
      ## the engine's pre-shrink retries. The engine reports this as `otFlaky`.

proc fitsInt64(x: Int128): bool {.inline.} =
  ## True iff `x` is exactly representable in int64 (so `toInt64` is faithful).
  (x.hi == 0 and x.lo <= uint64(high(int64))) or x.hi == -1

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

proc lowerIntegerAt[T](s: Strategy[T], prop: proc(x: T),
                       choices: var seq[ChoiceNode], idx: int) =
  ## Binary-search the smallest value in `[shrinkTowards, current]` that still
  ## falsifies, and write it into `choices[idx]`. Skips forced nodes, values
  ## already at the target, and the rare native-out-of-int64 case.
  let node = choices[idx]
  if node.kind != ckInteger or node.wasForced: return
  let target = node.intC.shrinkTowards
  let cur = node.intVal
  if cur == target: return
  if not (target < cur): return                 # only lower direction here
  if not fitsInt64(target) or not fitsInt64(cur): return

  # First, try the target itself — if it falsifies, we're done.
  var cand = choices
  cand[idx].intVal = target
  if tryFalsifies(s, prop, cand).fails:
    choices = cand
    return

  # Otherwise binary-search the boundary. Invariant: pred(lo)=pass, pred(hi)=fail.
  var lo = toInt64(target)
  var hi = toInt64(cur)
  while hi - lo > 1:
    let mid = lo + (hi - lo) div 2
    cand = choices
    cand[idx].intVal = toInt128(mid)
    if tryFalsifies(s, prop, cand).fails:
      hi = mid
      choices = cand
    else:
      lo = mid

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
                choices: seq[ChoiceNode]): ShrinkResult[T] =
  ## Apply the shrink passes to a falsifying sequence and return the minimized
  ## sequence with the example it regenerates. Passes are run to a fixed point:
  ## deletion shortens, then lex-lowering minimizes contents at the new length;
  ## each iteration may enable further reductions in the next.
  var best = choices
  var prev: seq[ChoiceNode]
  while best != prev:
    prev = best
    deleteSpansPass(s, prop, best)
    for i in 0 ..< best.len:
      lowerIntegerAt(s, prop, best, i)
  let res = tryFalsifies(s, prop, best)
  # If the final candidate doesn't reproduce, the property was flaky at some
  # point during shrinking — flag it rather than asserting; the engine will
  # report `otFlaky` so the user knows their property is non-deterministic.
  ShrinkResult[T](choices: best, example: res.x, flaky: not res.fails)
