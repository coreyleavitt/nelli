## RFC-fuzzer-nextgen R27 (code review, MEDIUM/design): the crash de-dup /
## stop-decision collaborator extracted from the `fuzz[T]` loop
## (`fuzz.nim`).
##
## Before this module, `fuzz[T]`'s `recordCrashIfInteresting` closure
## captured THREE loop-local mutable variables by hand (`seenCrashKeys`,
## `lastCrashIter`, plus the outer `iter` it read) to answer two questions
## every crash observation needs answered: is this a NEW finding (for
## de-dup, FUZZ_PLAN 6a), and should the campaign stop now (F4
## `stopOnFirstCrash`)? `CrashRecorder` owns the de-dup set and the
## `lastCrashIter` bookkeeping directly, and reduces to one call per
## observation.
##
## **Why this takes a pre-computed `key: string`, not a `Coverage`/
## `CrashInfo`/`Observation[T]`.** Crash-KEY computation
## (`settings.crashKey` override, or the loop's own `defaultCrashKey`
## fallback folding `Coverage`+message+`CrashInfo.kind`) is a fuzz.nim
## concern — it needs `Verdict`/`Observation[T]`, which are generic/loop-
## local types `fuzz.nim` itself defines, and pulling them in here would
## either duplicate `defaultCrashKey` or create an import cycle
## (`fuzz.nim` would need to import this module for the recorder, and this
## module would need `fuzz.nim` for `Verdict`). Splitting the boundary at
## "already-computed identity key in, dedup+stop decision out" keeps this
## module a pure, leaf, string-keyed policy — testable with nothing but
## plain strings — while `fuzz.nim` keeps owning what a crash's IDENTITY
## means.
##
## Byte-for-byte behavior preserved from the pre-R27 loop:
## - `observe` reproduces `not seenCrashKeys.containsOrIncl(key)` for
##   "is this new," `keepAllCrashes or isNewCrash` for "should the loop
##   record it," and `stopOnFirstCrash and isNewCrash` for "should the loop
##   stop" — the same three-way fold, in the same order, off the same
##   `containsOrIncl` call (recording the key exactly once, on first sight,
##   regardless of `keepAllCrashes`).
## - `lastCrashIter` is set on EVERY crash observation passed to `observe`
##   (dup or new), matching the pre-R27 loop's `lastCrashIter = iter`
##   assignment, which ran unconditionally before the dedup check.

import std/sets

type
  CrashRecorder* = object
    keepAllCrashes: bool
    stopOnFirstCrash: bool
    seenKeys: HashSet[string]
    lastCrashIterVal: int

proc newCrashRecorder*(keepAllCrashes = false; stopOnFirstCrash = false): CrashRecorder =
  CrashRecorder(keepAllCrashes: keepAllCrashes, stopOnFirstCrash: stopOnFirstCrash)

proc lastCrashIter*(r: CrashRecorder): int = r.lastCrashIterVal
  ## RFC-fuzzer-nextgen S5a: the `iter` value at the most recent crash
  ## observation passed to `observe` (any verdict in `{vInteresting,
  ## vTimedOut}`, dup or new) — `0` until the first one. Feeds
  ## `CampaignStats.sinceLastCrashIters` (`iter - lastCrashIter`).

proc observe*(r: var CrashRecorder; iter: int; key: string):
    tuple[recordable: bool, shouldStop: bool] =
  ## Call once per crash-verdict observation (`vInteresting`/`vTimedOut` —
  ## the caller filters non-crash verdicts out before calling this;
  ## `observe` itself has no verdict to check). `key` is the crash's
  ## identity fingerprint the caller already computed (`settings.crashKey`
  ## or the loop's `defaultCrashKey` fallback).
  ##
  ## `recordable`: whether the CALLER should append this observation to
  ## `FuzzReport.irCrashes` — true when `keepAllCrashes` is set, or this is
  ## the first time `key` has been seen this campaign.
  ## `shouldStop`: F4's `stopOnFirstCrash` gate — true only for a NEW
  ## (never-seen) key under `stopOnFirstCrash`; a duplicate never stops the
  ## loop even under `keepAllCrashes`.
  r.lastCrashIterVal = iter
  let isNewCrash = not r.seenKeys.containsOrIncl(key)
  (recordable: r.keepAllCrashes or isNewCrash,
   shouldStop: r.stopOnFirstCrash and isNewCrash)
