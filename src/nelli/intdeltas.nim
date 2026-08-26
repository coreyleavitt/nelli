## Log-scaled `±2^k` integer-perturbation kernel, shared between the
## fuzz adapter and the targeted-PBT hill-climb (RFC-fuzzer-nextgen U1).
##
## A leaf module with NO dependencies (not even `nelli/int128` — callers
## narrow to `int64` before calling) — this is the crashinfo.nim/U0
## pattern applied to a second fuzz↔engine sharing problem. Before U1,
## `fuzzir.nim` and `engine/targeting.nim` each carried their OWN copy
## of this exact algorithm: `fuzzir.nim` needed to stay a leaf (no
## engine deps, so it can't import `engine/targeting`), and at the time
## there was no shared home that both could reach without either
## `fuzzir.nim` importing engine internals or `engine/targeting.nim`
## importing the fuzz layer. The E1 `Worker`/`Pool` seams (+ U0's
## `crashinfo.nim`) established the pattern for resolving exactly this
## shape of duplication: extract the shared piece into its own
## dependency-free leaf module that both sides import directly, with
## no coupling to either the fuzz or engine dependency graph.
proc logScaledIntDeltas*(width: int64): seq[int64] =
  ## ±2^k for k in `[0, log2(width)]`, big-to-small — a single sweep can
  ## cross a wide falsifying/interesting boundary before fine-tuning.
  ## `width` is the constraint range's width (`max - min`), used to
  ## bound `k`. `width <= 0` (a degenerate/singleton range) yields no
  ## deltas.
  if width <= 0: return @[]
  var k = 0
  while k < 62 and (1'i64 shl (k + 1)) <= width:
    inc k
  while k >= 0:
    let d = 1'i64 shl k
    result.add d
    result.add -d
    dec k
