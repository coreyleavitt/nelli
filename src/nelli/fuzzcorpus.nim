## RFC-fuzzer-nextgen R27 (code review, MEDIUM/design): the corpus/schedule
## collaborator extracted from the `fuzz[T]` loop (`fuzz.nim`).
##
## Before this module, `fuzz[T]` carried FIVE parallel `seq`s by hand —
## `corpus`, `corpusCov`, `corpusNanos`, `corpusSlots`, `corpusCmpLog`, plus
## `energy` — and every site that added, culled, or read an entry (S1's
## per-tick energy refresh, S1's parent selection, S4's periodic cull, the
## mutation-admit growth path, G3's concolic-admit growth path) had to keep
## all five/six in lockstep by hand. `FuzzCorpusStore` owns that state
## directly: one `add` appends to every parallel array atomically, one
## `cull` filters all of them atomically, and `refreshEnergy`/`pickParent`
## read them without the caller ever touching an index into more than one
## array at a time.
##
## **What stayed in `fuzz.nim`.** Two things this store does NOT own, on
## purpose:
## - **Persistence** (`ExampleDatabase.saveCorpus`) and **report bookkeeping**
##   (`FuzzReport.corpus.irEntries`) are the LOOP's concerns, not the
##   store's — `add`/`cull` are pure in-memory operations with no I/O, so a
##   caller can drive them without a database at all (see
##   `tests/tfuzzcorpusstore.nim`). The loop still does its own
##   `saveCorpus`/`report.corpus.irEntries.add` immediately after `add`,
##   same call sites as before.
## - **The favored-set decision** (`favoredIndices`, unchanged, still in
##   `fuzz.nim`) stays a free function over this store's own read accessors
##   (`slotsOf`/`sizesOf`/`nanosOf`) rather than a store method — it is
##   already a pure function of exactly the store's own arrays plus
##   `FrontierStats` (an external input), so wrapping it in a method would
##   only rename the call, not change what owns what. `cull(keep)` is the
##   store's side of that split: given a decision, apply it.
##
## Byte-for-byte behavior preserved from the pre-R27 loop: `add` reproduces
## the five-array append (`energy` seeded at the `0.0` placeholder the loop
## always used, refreshed on the NEXT `refreshEnergy` call, never eagerly);
## `refreshEnergy`/`pickParent(uniform=true/false)` reproduce
## `entropicEnergy`/`energyWeightedIndex`/the uniform `rng.next mod
## corpus.len` fallback exactly, consuming `rng` identically either way;
## `cull` reproduces the loop's own five-array filter-by-`keep` (including
## resetting `energy` to a fresh zero seq afterward, refreshed by the next
## `refreshEnergy` tick, same as before).

import ./choice, ./datasource, ./coverage, ./rng

type
  CorpusEntry* = tuple[choices: seq[ChoiceNode], spans: seq[Span]]

  FuzzCorpusStore* = object
    ## Owns every per-entry array the schedule (S1) and culling (S4) read
    ## or mutate. All `seq`s below are always kept the same length —
    ## `add`/`cull` are the only two ways to change that length, and both
    ## touch every array together.
    entries: seq[CorpusEntry]
    cov: seq[Coverage]
    nanos: seq[int64]
    slots: seq[seq[int]]
    cmpLog: seq[seq[CmpLogEntry]]
    energy: seq[float]

proc len*(c: FuzzCorpusStore): int = c.entries.len

proc `[]`*(c: FuzzCorpusStore; i: int): CorpusEntry = c.entries[i]
  ## `corpus[i]` reads exactly as it did when `corpus` was a bare
  ## `seq[CorpusEntry]` — kept as an operator (not just `entryAt`) so the
  ## loop's existing `corpus[i].choices`/`corpus[parentIdx]` call sites
  ## needed no shape change, only a type change.

proc choicesAt*(c: FuzzCorpusStore; i: int): seq[ChoiceNode] = c.entries[i].choices
proc spansAt*(c: FuzzCorpusStore; i: int): seq[Span] = c.entries[i].spans
proc entryAt*(c: FuzzCorpusStore; i: int): CorpusEntry = c.entries[i]
proc cmpLogAt*(c: FuzzCorpusStore; i: int): seq[CmpLogEntry] = c.cmpLog[i]
proc covAt*(c: FuzzCorpusStore; i: int): Coverage = c.cov[i]
proc energyOf*(c: FuzzCorpusStore): seq[float] = c.energy

proc allChoices*(c: FuzzCorpusStore): seq[seq[ChoiceNode]] =
  ## The raw entry list in current (post-any-cull) order — what the loop's
  ## end-of-run report assembly reads before optionally minimizing.
  for e in c.entries: result.add e.choices

proc allCov*(c: FuzzCorpusStore): seq[Coverage] = c.cov

proc sizesChoices*(c: FuzzCorpusStore): seq[int] =
  ## `favoredIndices`' `sizeChoices` argument — each entry's IR length.
  result = newSeq[int](c.entries.len)
  for i, e in c.entries: result[i] = e.choices.len

proc slotsOf*(c: FuzzCorpusStore): seq[seq[int]] = c.slots
proc nanosOf*(c: FuzzCorpusStore): seq[int64] = c.nanos

proc add*(c: var FuzzCorpusStore; choices: seq[ChoiceNode]; spans: seq[Span];
         cov: Coverage; nanos: int64; cmpLog: seq[CmpLogEntry] = @[]) =
  ## Append one entry to every parallel array atomically. `energy` starts at
  ## `0.0` — a placeholder overwritten the next time `refreshEnergy` runs
  ## (the loop always calls it at the top of the next iteration under the
  ## adaptive schedule), never computed eagerly here, matching the pre-R27
  ## loop's `recordCorpusGrowth` exactly.
  c.entries.add (choices: choices, spans: spans)
  c.cov.add cov
  c.nanos.add nanos
  c.slots.add coveredSlots(cov)
  c.cmpLog.add cmpLog
  c.energy.add 0.0

proc addSeed*(c: var FuzzCorpusStore; choices: seq[ChoiceNode]; spans: seq[Span]) =
  ## Append a not-yet-run seed: placeholder `Coverage()`/`0` nanos/empty
  ## cmpLog — exactly what the pre-R27 loop produced for a freshly loaded
  ## seed before the F2 preload-replay pass (or the seed's first selection
  ## as a mutation parent) observes its real coverage. `setObserved` below
  ## backfills once that replay happens.
  add(c, choices, spans, Coverage(), 0'i64, @[])

proc setObserved*(c: var FuzzCorpusStore; i: int; cov: Coverage; nanos: int64;
                  cmpLog: seq[CmpLogEntry]) =
  ## F2: backfill a preloaded seed's real coverage/timing/cmpLog once the
  ## loop has replayed it (`orchestrator.run`) — the loop still owns the
  ## replay itself; this just folds the observation back into the store's
  ## arrays instead of four direct index assignments.
  c.cov[i] = cov
  c.nanos[i] = nanos
  c.slots[i] = coveredSlots(cov)
  c.cmpLog[i] = cmpLog

proc refreshEnergy*(c: var FuzzCorpusStore; stats: FrontierStats) =
  ## RFC-fuzzer-nextgen S1: recompute every entry's Entropic energy fresh
  ## from the frontier's LIVE `stats` — never maintained incrementally,
  ## since a slot's rarity denominator (`totalAdmitted`) moves on every
  ## admit, same as the pre-R27 loop.
  for i in 0 ..< c.entries.len:
    c.energy[i] = entropicEnergy(c.slots[i], stats, c.entries[i].choices.len, c.nanos[i])

proc pickParent*(c: FuzzCorpusStore; rng: var SplitMix64; uniform: bool): int =
  ## S1 parent selection: energy-weighted by default, or a uniform
  ## `rng.next mod len` fallback under `uniformSchedule` — consumes `rng`
  ## identically to the pre-R27 loop in both branches (same call shape,
  ## same order), so the mutation-sequence trajectory is unaffected by this
  ## extraction. Callers are expected to have called `refreshEnergy` first
  ## when `uniform` is false (this proc does not refresh itself, to keep
  ## the "recompute once per iteration, not once per pick" contract
  ## explicit at the call site — the same contract the original loop had).
  if uniform:
    return int(rng.next mod uint64(c.entries.len))
  var total = 0.0
  for e in c.energy: total += e
  if total <= 0.0: return int(rng.next mod uint64(c.entries.len))
  let r = (rng.next.float / 18446744073709551616.0) * total   # u64 range -> [0,total)
  var acc = 0.0
  for i, e in c.energy:
    acc += e
    if r < acc: return i
  c.entries.high

proc cull*(c: var FuzzCorpusStore; keep: seq[bool]) =
  ## Apply a favored-set decision (from `favoredIndices(c.slotsOf, ...)`,
  ## still a free function over this store's read accessors — see the
  ## module doc): filter every parallel array down to the kept indices,
  ## and reset `energy` to a fresh zero seq (refreshed by the next
  ## `refreshEnergy` tick), exactly the pre-R27 loop's S4 cull block.
  var newEntries: seq[CorpusEntry]
  var newCov: seq[Coverage]
  var newNanos: seq[int64]
  var newSlots: seq[seq[int]]
  var newCmpLog: seq[seq[CmpLogEntry]]
  for i in 0 ..< c.entries.len:
    if keep[i]:
      newEntries.add c.entries[i]
      newCov.add c.cov[i]
      newNanos.add c.nanos[i]
      newSlots.add c.slots[i]
      newCmpLog.add c.cmpLog[i]
  c.entries = newEntries
  c.cov = newCov
  c.nanos = newNanos
  c.slots = newSlots
  c.cmpLog = newCmpLog
  c.energy = newSeq[float](newEntries.len)
