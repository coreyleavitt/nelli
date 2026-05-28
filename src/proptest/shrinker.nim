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

proc fitsInt64(x: Int128): bool {.inline.} =
  ## True iff `x` is exactly representable in int64 (so `toInt64` is faithful).
  (x.hi == 0 and x.lo <= uint64(high(int64))) or x.hi == -1

proc tryFalsifies*[T](s: Strategy[T], prop: proc(x: T),
                      candidate: seq[ChoiceNode]): tuple[fails: bool, x: T] =
  ## Replay `candidate` through `s`, then run `prop`. Returns `(true, x)` iff
  ## the property still fails — any other outcome (rejection, overrun, pass) is
  ## "not interesting" and the candidate must not be kept.
  var ds = newReplaySource(candidate)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return (false, x)
  try:
    prop(x); (false, x)
  except Rejection:
    (false, x)
  except CatchableError, Defect:
    (true, x)

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

proc shrink*[T](s: Strategy[T], prop: proc(x: T),
                choices: seq[ChoiceNode]): ShrinkResult[T] =
  ## Apply the shrink passes to a falsifying sequence and return the minimized
  ## sequence with the example it regenerates.
  var best = choices
  for i in 0 ..< best.len:
    lowerIntegerAt(s, prop, best, i)
  let (fails, x) = tryFalsifies(s, prop, best)
  doAssert fails, "shrinker invariant: the final candidate must still falsify"
  ShrinkResult[T](choices: best, example: x)
