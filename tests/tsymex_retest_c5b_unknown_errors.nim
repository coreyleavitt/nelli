## Chapulin 0.1.0 re-test triage — catalog #5(b) (Invariant 7 violation),
## walker v64. Every `sxUnknown` must carry at least one CLASSIFIED error.
## Before v64, two walk-budget degrade sites (`maxLoopUnwind` k-unroll
## exhaustion, `maxFrontierSize` frontier prune) set `w.sawUnknown` BARE —
## chapulin's re-test observed `sxUnknown, errors == @[]` for its chained
## dependent-scan and var-out-param-in-loop shapes, leaving the consumer no
## way to tell "solver couldn't decide" apart from "walker forgot to say
## why". v64 classifies both sites as `beBudgetExhausted` and adds a
## verdict-time backstop (an sxUnknown that would still escape with empty
## errors is stamped `weInternalWalkerFault` — a classification-gap signal,
## never an empty seq).
import std/[unittest, strutils, sequtils]
import proptest/symex
import proptest/smt/canonicalize
import proptest/smt/types

type ScanError = object of CatchableError

# ---- the chapulin catalog-#6 scanlen shape (empty-errors sxUnknown repro) --

proc scanLen(data: seq[int], offset: int): int =
  var i = offset
  while i < data.len:
    if ((data[i] mod 256) + 256) mod 256 == 0:
      return i + 1
    i.inc
  raise newException(ScanError, "Unterminated at " & $offset)

proc chainOnly(data: seq[int]) =
  let p1 = scanLen(data, 2)
  discard scanLen(data, p1)

# ---- minimal deterministic unwind-exhaustion shape -------------------------

proc symbolicTripCount(n: int) =
  ## Trip count is symbolic — the guard stays satisfiable past any finite
  ## k-unroll. The label is gated on a trip count far beyond `maxLoopUnwind`
  ## (default 5), so NO in-budget path can reach it: the only verdict route
  ## is through the budget bail — sxUnknown, and v64 requires it classified.
  var i = 0
  while i < n:
    inc i
  if i > 100:
    symexTarget("deep-loop")

suite "symex re-test C5b — Invariant 7: no sxUnknown with empty errors":

  test "symbolic-trip-count loop: sxUnknown carries beBudgetExhausted":
    let r = symexFind(symbolicTripCount, tLabel("deep-loop"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == beBudgetExhausted)

  test "chained dependent scans (chapulin #6 scanlen shape): errors no longer empty":
    let r = symexFind(chainOnly, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0

suite "symex re-test C5b — walker version pin":

  test "walker version floor >= 64 (budget-bail classification + Invariant-7 backstop)":
    check parseInt(symexWalkerVersion) >= 64
