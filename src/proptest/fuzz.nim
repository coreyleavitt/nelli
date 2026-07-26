## Fuzz integration — the bytes-as-DataSource entry point and (in a
## later issue) the coverage-guided runner.
##
## This module is the **partitioned-fuzz half** of proptest: it shares
## the choice-sequence IR, Strategy[T], DataSource, ExampleDatabase,
## and shrinker with the PBT runner, but lives behind its own entry
## points so a user who only wants property tests never touches the
## fuzz API. Per the M12 design discussion, the partitioning is the
## architecture that lets us combine PBT and structured fuzzing in
## one library without entangling them.
##
## The first capability here is `fuzzOnce(s, prop, bytes)`: run a
## strategy + property against an externally-supplied byte buffer.
## This is the integration point for libFuzzer / AFL / custom mutator
## harnesses — they hand us bytes, we hand them back a verdict.

import std/[options, times, monotimes, os, strutils, sets]
import ./strategy, ./datasource, ./engine, ./rng, ./coverage, ./choice, ./fuzzir, ./db
export fuzzir
# The coverage runtime + `{.cover.}` pragma live in a dedicated leaf
# module (`./coverage`) so the PBT engine can depend on them (for #107
# coverage-guided forAll) without a fuzz↔engine cycle. Re-exported here
# so existing `import proptest/fuzz` callers don't break.
export coverage

# --- fuzzOnce: bytes → value → property -------------------------------------

type
  FuzzOnceOutcome* = enum
    foOk,         ## strategy produced a value; property held
    foRejected,   ## the byte buffer was too short to satisfy the strategy
                  ## (or a `filter`/`assume` rejected the example); the
                  ## fuzzer should drop this input from its corpus
    foFalsified   ## the property raised `FalsifiedError`; the bytes
                  ## are a crash-reproducing input (libFuzzer keeps it)

  FuzzOnceResult*[T] = object
    outcome*: FuzzOnceOutcome
    value*: Option[T]
    message*: string

proc fuzzOnce*[T](s: Strategy[T], prop: proc(x: T),
                  bytes: seq[byte]): FuzzOnceResult[T] =
  ## Run `s` then `prop` against a byte buffer. Insufficient bytes or
  ## strategy-side rejection both map to `foRejected` — the fuzzer drops
  ## the input. A property failure (`foFalsified`) is what the fuzzer
  ## corpus retains.
  var ds = newReplaySourceFromBytes(bytes)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return FuzzOnceResult[T](outcome: foRejected)
  result.value = some(x)
  try:
    prop(x)
    result.outcome = foOk
  except Rejection:
    result.outcome = foRejected
  except FalsifiedError as e:
    result.outcome = foFalsified
    result.message = e.msg
  except CatchableError as e:
    result.outcome = foFalsified
    result.message = $e.name & ": " & e.msg
  except Defect as e:
    result.outcome = foFalsified
    result.message = "crashed: " & $e.name & ": " & e.msg

proc fuzzOnceIR*[T](s: Strategy[T], prop: proc(x: T),
                    choices: seq[ChoiceNode]): FuzzOnceResult[T] =
  ## IR-level peer of `fuzzOnce`. Replays `choices` through the strategy
  ## (no byte-decode in the loop) and runs the property. The architectural
  ## entry point for IR-aware mutation: a mutator hands us a mutated
  ## sequence directly and we check it without ever round-tripping through
  ## bytes. Insufficient/misaligned choices map to `foRejected` per the
  ## same convention as `fuzzOnce`.
  var ds = newReplaySource(choices)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return FuzzOnceResult[T](outcome: foRejected)
  result.value = some(x)
  try:
    prop(x)
    result.outcome = foOk
  except Rejection:
    result.outcome = foRejected
  except FalsifiedError as e:
    result.outcome = foFalsified
    result.message = e.msg
  except CatchableError as e:
    result.outcome = foFalsified
    result.message = $e.name & ": " & e.msg
  except Defect as e:
    result.outcome = foFalsified
    result.message = "crashed: " & $e.name & ": " & e.msg

# --- FuzzSettings / FuzzReport / fuzzWith ------------------------------------

type
  FuzzMutationMode* = enum
    ## Selects the mutation kernel. `fmIR` is enum-position 0 so an
    ## un-initialized `FuzzSettings` defaults to IR mode — the structural
    ## payoff of the M12 typed-IR decision (#110). `fmBytes` retains the
    ## libFuzzer/AFL byte path for harnesses that hand us raw bytes.
    fmIR,
    fmBytes

  FuzzCorpusKind* = enum fckIR, fckBytes

  FuzzCorpus* = object
    ## Sum type at the collection level: one corpus, one representation.
    ## Matches `FuzzMutationMode` so the type system enforces that a
    ## byte-mode run produces a byte corpus and IR-mode produces an IR
    ## corpus — no mixing, no parallel-field convention.
    case kind*: FuzzCorpusKind
    of fckIR:    irEntries*:   seq[seq[ChoiceNode]]
    of fckBytes: byteEntries*: seq[seq[byte]]

  FuzzSettings* = object
    ## Configuration for the coverage-guided fuzz runner. Deliberately
    ## distinct from PBT `Settings` per the M12 partitioning: a PBT user
    ## should never see fuzz fields, and a fuzz user shouldn't pay for
    ## PBT-only fields they don't need.
    maxIterations*: int
      ## Hard cap on `fuzzOnce` calls. `0` = no cap (controlled by
      ## `timeBudget` alone).
    timeBudget*: Duration
      ## Wall-clock budget. The loop exits when this is exceeded or
      ## when `maxIterations` is hit, whichever first. `0` (the default
      ## via `initDuration()`) means no wall-clock cap.
    seed*: uint64
      ## Master seed for the fuzzer's own RNG (drives random initial
      ## seeds and mutation choices). Deterministic in this seed when
      ## the SUT is deterministic.
    mutationMode*: FuzzMutationMode
      ## Selects byte vs IR mutation kernel. Defaults to `fmIR` (enum
      ## position 0) for the structural-validity payoff — #110.
    initialCorpus*: seq[seq[byte]]
      ## Seed inputs for `fmBytes` mode (e.g., from a previous AFL run).
      ## Ignored in `fmIR` mode; IR-mode seeds itself by generating one
      ## random input through the strategy.
    initialIRCorpus*: seq[seq[ChoiceNode]]
      ## Seed IR sequences for `fmIR` mode (e.g., persisted from a
      ## previous fuzz run, or hand-crafted regression seeds).
    initialInputSize*: int
      ## Bytes per random initial input in `fmBytes` mode. Defaults to 64.
    integerBias*: IntegerBiasConfig
      ## Distribution bias for `drawInteger` in the IR runner's seed
      ## input (#103 follow-up). Narrow effect by design: the byte-mode
      ## adapter draws via `bytesMode` (bias-irrelevant) and corpus
      ## entries after the seed come from IR mutators (which use their
      ## own log-scaled perturbation kernel, also bias-irrelevant).
      ## So this field only affects the one fresh-RNG seed input that
      ## `fuzzWithIR` generates when `initialIRCorpus` is empty.
      ## Zero-init resolves to `defaultIntegerBias` via `resolved()`.
    keepAllCrashes*: bool
      ## By default the loop de-dups crashes by `crashKey` (keep-first), so the
      ## same bug reached many ways is reported once (FUZZ_PLAN 6a). Set this to
      ## record every `vInteresting`/`vTimedOut` run, dupes included.
    crashKey*: proc(cov: Coverage; message: string): string {.closure.}
      ## Crash-identity fingerprint for de-dup. `nil` (the default) keys on the
      ## coverage edge-set plus the crash message — input-representation
      ## independent, so it is stable under shrinking. Override to key on, e.g.,
      ## a sanitizer stack hash parsed from the message.
    database*: ExampleDatabase
      ## Optional corpus persistence (FUZZ_PLAN 6b). When set (a non-nil backend),
      ## the loop loads any prior corpus as seeds on start and saves every
      ## new-coverage input, keyed by `fuzzCorpusKey(persistKey, frontier.targetId)`.
      ## Folding the `targetId` into the key means a changed binary re-keys cleanly:
      ## the stale corpus (tied to a now-invalid coverage map) is simply missed.
      ## Persists via `saveCorpus`/`loadCorpus` (F1, RFC-chapulin-hardening) — a
      ## dedicated, never-pruned DB section, so the corpus survives even a run
      ## that shares its testId with a `forAll` regression suite (`dbReusePhase`
      ## only ever reads/prunes the `primary` section).
    persistKey*: string
      ## User half of the persistence key — names the campaign (e.g. "nim-parser").
    corpusLimit*: int
      ## Cap on persisted corpus entries (keep-most-recent). `0` → 256.
    powerSchedule*: bool
      ## Opt-in (FUZZ_PLAN 6c): bias parent selection toward corpus entries with
      ## high "energy" — newly admitted inputs and lineages that keep growing
      ## coverage — instead of picking uniformly. Off by default, so the default
      ## trajectory (and `tfuzzir`) is unchanged.
    minimizeCorpus*: bool
      ## Opt-in (FUZZ_PLAN 6c): after the run, reduce the reported/persisted corpus
      ## to a minimal subset whose per-entry coverage still spans the same edges
      ## (greedy set cover). The frontier and `coverageHits` are unaffected.

  FuzzReport* = object
    iterations*: int
      ## Number of `fuzzOnce` / `fuzzOnceIR` calls performed before exit.
    coverageHits*: int
      ## Distinct edges discovered across the whole run. Approximates
      ## "what fraction of the SUT did we explore."
    corpus*: FuzzCorpus
      ## Inputs that found new coverage. Variant tag matches the run's
      ## `mutationMode`; persistent across runs.
    crashes*: seq[tuple[bytes: seq[byte], message: string]]
      ## Falsifying byte-mode inputs (carries the exact bytes for repro).
      ## IR-mode crashes go to `irCrashes` instead.
    irCrashes*: seq[tuple[choices: seq[ChoiceNode], message: string]]
      ## Falsifying IR-mode inputs (carries the choice sequence).
    timedOut*: bool
      ## True iff the loop exited because `timeBudget` was hit (vs.
      ## `maxIterations`).

  Verdict* = enum
    ## What the oracle made of one run (FUZZ_PLAN D14). Generic over in-process
    ## and external targets; an external `Oracle` maps exit/signal/stderr to it.
    vOk           ## ran, nothing of interest
    vRejected     ## the input was malformed/filtered — drop from corpus
    vInteresting  ## a finding (crash / sanitizer report / differential mismatch)
    vTimedOut     ## a hang — a first-class finding, not a drop

  RunResult* = object
    ## The raw mechanical result of one external run — the oracle's input (D14).
    ## Defined here (ahead of the execution contract) so `Observation` can carry it,
    ## which is what lets `differentialTarget` compose `Target`s on their raw results.
    exitCode*: int
    signal*: int            ## 0 == exited normally; else the terminating signal
    stdout*, stderr*: seq[byte]
    timedOut*: bool
    durationNs*: int64

  Observation*[T] = object
    ## The result of executing one value via a `Target` (D3): the verdict, the
    ## run's coverage, a message for crash retention, and (for external targets)
    ## the raw `RunResult` so composers like `differentialTarget` can compare children.
    verdict*: Verdict
    coverage*: Coverage
    message*: string
    runResult*: RunResult

  Target*[T] = object
    ## Execute-and-observe as one round trip (D3). `inProcessTarget` runs a `prop`;
    ## `externalTarget`/`differentialTarget` (Phase 5) run a child. Closed under
    ## composition, so the `fuzz` loop is target-agnostic.
    run*: proc(x: T): Observation[T] {.closure.}

proc mutateByteFlip(rng: var SplitMix64, base: seq[byte]): seq[byte] =
  ## One-bit-flip mutation. Picks a random bit position in `base` and
  ## flips it. The simplest AFL-style mutation; lots of crashes are
  ## one bit away from a benign input.
  result = base
  if result.len == 0: return
  let idx = int(rng.next mod uint64(result.len))
  let bit = uint64(rng.next mod 8'u64)
  result[idx] = result[idx] xor byte(1'u8 shl bit)

proc mutateByteReplace(rng: var SplitMix64, base: seq[byte]): seq[byte] =
  ## Replace a random byte with a random value. Bigger steps than
  ## bit-flip; useful for crossing wide integer thresholds.
  result = base
  if result.len == 0: return
  let idx = int(rng.next mod uint64(result.len))
  result[idx] = byte(rng.next and 0xff'u64)

proc randomBytes(rng: var SplitMix64, n: int): seq[byte] =
  result = newSeq[byte](n)
  for i in 0 ..< n:
    result[i] = byte(rng.next and 0xff'u64)

proc captureIR[T](s: Strategy[T], choices: seq[ChoiceNode]):
    tuple[ok: bool, choices: seq[ChoiceNode], spans: seq[Span]] =
  ## Replay `choices` through `s` to recover the structural spans the
  ## strategy emits. Used during corpus promotion: a mutator hands us a
  ## new choice sequence; before the loop can splice/delete against it
  ## later, it needs the spans the strategy *would* draw under those
  ## choices. Falls back to `(false, ...)` on misalignment (the mutant
  ## is structurally invalid for this strategy and gets dropped).
  var ds = newReplaySource(choices)
  try:
    discard s.generate(ds)
  except Rejection, Overrun:
    return (ok: false, choices: choices, spans: @[])
  except CatchableError, Defect:
    return (ok: false, choices: choices, spans: @[])
  (ok: true, choices: ds.recorded, spans: ds.spans)

proc inProcessTarget*[T](prop: proc(x: T)): Target[T] =
  ## A `Target` over an in-process property (FUZZ_PLAN D3). Per run: reset the
  ## {.cover.} bitmap (per-run isolation — the probe is `resetsPerRun`, D8), run
  ## `prop`, map the same exceptions `fuzzOnce` does to a `Verdict`, snapshot the
  ## bitmap, and restore the prior coverage mode. The default target for `fuzz`,
  ## preserving the in-process behavior of the shipped `fuzzWith*` loops.
  let probe = inProcessProbe()
  Target[T](run: proc(x: T): Observation[T] =
    let prior = currentCoverageMode()
    setCoverageMode(cmRecording)
    resetCoverage()
    var verdict = vOk
    var msg = ""
    try:
      prop(x)
    except Rejection:
      verdict = vRejected
    except FalsifiedError as e:
      verdict = vInteresting; msg = e.msg
    except CatchableError as e:
      verdict = vInteresting; msg = $e.name & ": " & e.msg
    except Defect as e:
      verdict = vInteresting; msg = "crashed: " & $e.name & ": " & e.msg
    let cov = probe.read()
    setCoverageMode(prior)
    Observation[T](verdict: verdict, coverage: cov, message: msg))

proc coverageFingerprint*(c: Coverage): string =
  ## A stable key over the SET of covered slots — the default `crashKey` (D11): two
  ## crashes reaching the same novel edges are likely one bug.
  var h = 2166136261'u32
  for i in 0 ..< c.counters.len:
    if c.counters[i] > 0'u8:
      h = (h xor uint32(i and 0xffff)) * 16777619'u32
      h = (h xor uint32((i shr 16) and 0xffff)) * 16777619'u32
  $h

proc defaultCrashKey(cov: Coverage; message: string): string =
  ## Crash identity (FUZZ_PLAN 6a) when the user supplies no `crashKey`: the
  ## coverage edge-set fingerprint plus the message. The message carries the
  ## crash signal/exit for external targets and the exception text in-process, so
  ## two genuinely different bugs at the same site (or with no coverage at all)
  ## still separate. Keyed on observable behavior, not input bytes → shrinker-safe.
  coverageFingerprint(cov) & "\x00" & message

proc energyWeightedIndex(rng: var SplitMix64; energy: seq[float]): int =
  ## Pick a corpus index with probability proportional to its energy (6c power
  ## schedule). Falls back to uniform if all energy is zero. Deterministic in `rng`.
  var total = 0.0
  for e in energy: total += e
  if total <= 0.0: return int(rng.next mod uint64(energy.len))
  let r = (rng.next.float / 18446744073709551616.0) * total   # u64 range → [0,total)
  var acc = 0.0
  for i, e in energy:
    acc += e
    if r < acc: return i
  energy.high

proc minimalCovering(entries: seq[seq[ChoiceNode]]; covs: seq[Coverage]): seq[seq[ChoiceNode]] =
  ## Greedy set cover (6c corpus minimization): the fewest entries whose covered
  ## edges still union to the whole corpus's edge set. Entries covering nothing
  ## (e.g. unrun seeds) drop out. Deterministic: ties break to the lowest index.
  var remaining = initHashSet[int]()
  for c in covs:
    for i in 0 ..< c.counters.len:
      if c.counters[i] > 0'u8: remaining.incl i
  var used = newSeq[bool](entries.len)
  while remaining.len > 0:
    var best = -1
    var bestGain = 0
    for k in 0 ..< entries.len:
      if used[k]: continue
      var gain = 0
      for i in 0 ..< covs[k].counters.len:
        if covs[k].counters[i] > 0'u8 and i in remaining: inc gain
      if gain > bestGain: bestGain = gain; best = k
    if best < 0: break
    used[best] = true
    result.add entries[best]
    for i in 0 ..< covs[best].counters.len:
      if covs[best].counters[i] > 0'u8: remaining.excl i

proc fuzzCorpusKey*(persistKey, targetId: string): string =
  ## The `ExampleDatabase` testId the fuzz loop persists its corpus under (6b):
  ## the campaign `persistKey` folded with the target's `targetId`. A changed
  ## binary carries a new `targetId`, so it misses the stale corpus and re-keys
  ## cleanly. Public so a caller can pre-seed (or inspect) the persisted corpus.
  persistKey & "#" & targetId

proc fuzz*[T](s: Strategy[T]; target: Target[T]; frontier: var CoverageFrontier;
              settings: FuzzSettings): FuzzReport =
  ## The coverage-guided fuzz loop, generalized over an arbitrary `Target` and a
  ## `CoverageFrontier` (FUZZ_PLAN D10). The corpus is choice-IR; each iteration
  ## mutates a parent, replays it to a value (split from the run, so any `Target`
  ## can execute it), runs the target, ADMITS the input iff its coverage raised a
  ## new edge bucket, and retains `vInteresting` findings. `fuzzWith*` is this loop
  ## with `inProcessTarget`; `externalTarget` (Phase 5) drives a child process.
  var rng = initSplitMix64(settings.seed)
  let dbActive = settings.database.saveImpl != nil
  let testId = fuzzCorpusKey(settings.persistKey, frontier.targetId)
  let corpusLimit = if settings.corpusLimit > 0: settings.corpusLimit else: 256
  var corpus: seq[tuple[choices: seq[ChoiceNode], spans: seq[Span]]]
  for seed in settings.initialIRCorpus:
    let cap = captureIR(s, seed)
    if cap.ok: corpus.add (choices: cap.choices, spans: cap.spans)
  if dbActive:                                   # resume: persisted corpus as seeds (6b)
    # F1: the fuzz corpus lives in the DB's dedicated `corpus` section, not
    # `primary` — `primary` is the regression-replay channel `dbReusePhase`
    # prunes on pass/reject, which is the wrong lifecycle for coverage seeds
    # that keep earning their keep even once they stop crashing.
    for choices in settings.database.loadCorpus(testId):
      let cap = captureIR(s, choices)
      if cap.ok: corpus.add (choices: cap.choices, spans: cap.spans)
  if corpus.len == 0:
    var ds = newDataSource(initSplitMix64(rng.next))
    ds.integerBias = resolved(settings.integerBias)
    try:
      discard s.generate(ds)
      corpus.add (choices: ds.recorded, spans: ds.spans)
    except CatchableError, Defect:
      discard
  result.corpus = FuzzCorpus(kind: fckIR, irEntries: @[])
  for entry in corpus: result.corpus.irEntries.add entry.choices

  # Parallel per-entry bookkeeping for the 6c scheduler/minimizer (cheap when unused).
  var energy = newSeq[float](corpus.len)       # power-schedule weight per entry
  for i in 0 ..< energy.len: energy[i] = 1.0
  var corpusCov = newSeq[Coverage](corpus.len) # coverage each entry produced (empty = seed)

  let started = getMonoTime()
  let hasDeadline = settings.timeBudget.inNanoseconds > 0
  var seenCrashKeys = initHashSet[string]()    # crash de-dup, keep-first (6a)
  var iter = 0
  while corpus.len > 0:
    if settings.maxIterations > 0 and iter >= settings.maxIterations: break
    if hasDeadline:
      let elapsed = getMonoTime() - started
      if elapsed.inNanoseconds > settings.timeBudget.inNanoseconds:
        result.timedOut = true
        break
    inc iter
    let parentIdx = if settings.powerSchedule: energyWeightedIndex(rng, energy)
                    else: int(rng.next mod uint64(corpus.len))
    let parent = corpus[parentIdx]
    let pick = rng.next mod 5'u64
    var mutant: seq[ChoiceNode]
    case pick
    of 0: mutant = mutateIRPerturbInteger(rng, parent.choices)
    of 1: mutant = mutateIRKindBoundary(rng, parent.choices)
    of 2:
      let donor = corpus[int(rng.next mod uint64(corpus.len))]
      mutant = mutateIRSpanSplice(rng, parent.choices, donor.choices,
                                  parent.spans, donor.spans)
    of 3: mutant = mutateIRSpanDelete(rng, parent.choices, parent.spans)
    else: mutant = mutateIRSpanDuplicate(rng, parent.choices, parent.spans)

    var ds = newReplaySource(mutant)             # replay the mutant to a value
    var val: T
    var generated = true
    try:
      val = s.generate(ds)
    except Rejection, Overrun:
      generated = false
    if not generated: continue

    let obs = target.run(val)
    if obs.verdict == vRejected: continue
    if frontier.admit(obs.coverage).interesting:
      let cap = captureIR(s, mutant)
      if cap.ok:
        corpus.add (choices: cap.choices, spans: cap.spans)
        corpusCov.add obs.coverage
        energy.add 2.0                           # a fresh grower starts hot (recency)
        if settings.powerSchedule: energy[parentIdx] += 1.0   # reward the lineage
        result.corpus.irEntries.add cap.choices
        if dbActive: settings.database.saveCorpus(testId, cap.choices, corpusLimit)
    if obs.verdict in {vInteresting, vTimedOut}:
      let key = if settings.crashKey != nil: settings.crashKey(obs.coverage, obs.message)
                else: defaultCrashKey(obs.coverage, obs.message)
      if settings.keepAllCrashes or not seenCrashKeys.containsOrIncl(key):
        result.irCrashes.add (choices: mutant, message: obs.message)
  if settings.minimizeCorpus:                    # 6c: reduce to a minimal covering subset
    var choices: seq[seq[ChoiceNode]]
    for entry in corpus: choices.add entry.choices
    result.corpus.irEntries = minimalCovering(choices, corpusCov)
  result.iterations = iter
  result.coverageHits = frontier.coveredEdges

proc fuzzWithBytes[T](s: Strategy[T], prop: proc(x: T),
                      settings: FuzzSettings): FuzzReport =
  ## The byte-mutation kernel. Retained for libFuzzer / AFL compatibility:
  ## when a harness mutates outside our process and feeds us raw bytes,
  ## we have no choice but to byte-fuzz. Internal callers should prefer
  ## the IR kernel (`fmIR`).
  let priorMode = currentCoverageMode()
  setCoverageMode(cmRecording)
  defer: setCoverageMode(priorMode)
  resetCoverage()
  var rng = initSplitMix64(settings.seed)
  let initSize = if settings.initialInputSize > 0: settings.initialInputSize
                 else: 64
  var corpus: seq[seq[byte]] = settings.initialCorpus
  if corpus.len == 0:
    corpus.add randomBytes(rng, initSize)
  result.corpus = FuzzCorpus(kind: fckBytes, byteEntries: corpus)

  let started = getMonoTime()
  let hasDeadline = settings.timeBudget.inNanoseconds > 0
  var iter = 0
  while true:
    if settings.maxIterations > 0 and iter >= settings.maxIterations: break
    if hasDeadline:
      let elapsed = getMonoTime() - started
      if elapsed.inNanoseconds > settings.timeBudget.inNanoseconds:
        result.timedOut = true
        break
    inc iter
    let parent = result.corpus.byteEntries[
      int(rng.next mod uint64(result.corpus.byteEntries.len))]
    let bytes = if rng.next mod 2'u64 == 0: mutateByteFlip(rng, parent)
                else: mutateByteReplace(rng, parent)
    let covBefore = currentCoverage()
    let r = fuzzOnce(s, prop, bytes)
    let covAfter = currentCoverage()
    if covAfter > covBefore:
      result.corpus.byteEntries.add bytes
    case r.outcome
    of foOk, foRejected: discard
    of foFalsified:
      result.crashes.add (bytes: bytes, message: r.message)
  result.iterations = iter
  result.coverageHits = currentCoverage()

proc fuzzWithIR[T](s: Strategy[T], prop: proc(x: T),
                   settings: FuzzSettings): FuzzReport =
  ## The IR-mutation kernel — #110's architectural payoff. Now the in-process
  ## instance of the generalized `fuzz` loop: `inProcessTarget(prop)` over a fresh
  ## in-process `CoverageFrontier`. Admission on a new edge bucket (in the 0/1
  ## {.cover.} bitmap a new slot is exactly a new distinct edge) is equivalent to
  ## the old `covAfter > covBefore` scalar — the shipped fuzz/coverage suites pin it.
  var frontier = newCoverageFrontier()
  fuzz(s, inProcessTarget(prop), frontier, settings)

proc fuzzWith*[T](s: Strategy[T], prop: proc(x: T),
                  settings: FuzzSettings): FuzzReport =
  ## Coverage-guided fuzz loop. Dispatches on `settings.mutationMode`:
  ## `fmIR` (default) uses the IR mutators — the architectural payoff
  ## of the typed-IR decision; `fmBytes` retains the libFuzzer/AFL
  ## byte path for harnesses that hand us raw bytes.
  ##
  ## The fuzz runner uses `recordEdge` calls from `{.cover.}`'d code,
  ## so for coverage signal to fire, the SUT must be instrumented.
  ## An uninstrumented SUT degrades gracefully to "random fuzzing".
  ## Saves and restores the caller's `CoverageMode` so the recording
  ## state is scoped to this call.
  case settings.mutationMode
  of fmIR:    fuzzWithIR(s, prop, settings)
  of fmBytes: fuzzWithBytes(s, prop, settings)


# --- external coverage probe: parse a dumped sancov map (FUZZ_PLAN D5/D9) ----

proc covLe32(s: string; off: int): uint32 {.inline.} =
  uint32(s[off].byte) or (uint32(s[off+1].byte) shl 8) or
  (uint32(s[off+2].byte) shl 16) or (uint32(s[off+3].byte) shl 24)

proc parseCoverageMap*(raw: string): Coverage =
  ## Parse the proptest_cov dump (docs/fuzz/INTERFACE.md wire format). Raises
  ## `ValueError` on any mismatch (bad magic / version / length / checksum) — a
  ## present-but-invalid map is NEVER returned as coverage (D5), so a torn write or
  ## a crash-poisoned counter section cannot be mistaken for a real observation.
  if raw.len < 20 or raw[0..3] != "PCOV":
    raise newException(ValueError, "coverage map: bad magic")
  let version = covLe32(raw, 4)
  if version != 1'u32:
    raise newException(ValueError, "coverage map: unsupported version " & $version)
  let length = int(covLe32(raw, 12))
  if raw.len != 16 + length + 4:
    raise newException(ValueError, "coverage map: truncated (length mismatch)")
  var counters = newSeq[uint8](length)
  var sum = 0'u32
  for i in 0 ..< length:
    counters[i] = raw[16 + i].byte
    sum += uint32(counters[i])
  if sum != covLe32(raw, 16 + length):
    raise newException(ValueError, "coverage map: checksum mismatch")
  Coverage(counters: counters)

proc sancovFileProbe*(path: string): CoverageProbe =
  ## A `CoverageProbe` reading a child's dumped sancov map from `path`. An ABSENT
  ## file → empty `Coverage` (no-coverage; D7 — absent is never stale); a
  ## present-but-invalid file raises (D5). `resetsPerRun = false`: each dump is a
  ## fresh-exec absolute snapshot (D2 [INV-fresh-exec]).
  CoverageProbe(
    read: proc(): Coverage =
      if not fileExists(path): Coverage(counters: @[])
      else: parseCoverageMap(readFile(path)),
    resetsPerRun: false)

# --- external-execution contract: delivery, oracle, limits (FUZZ_PLAN D13/D14/D16) ---
#
# Pure descriptions of how an input reaches a child and how its result is judged.
# `externalTarget` (Phase 5) executes them against a real subprocess; here they are
# data + closures, testable with no child.

type
  InputPlan* = object
    ## A complete, pure description of one external run: the argv to exec, stdin to
    ## feed, env to set, files to write before and clean after. Produced by an
    ## `InputDelivery` from (input bytes, base argv, a per-run dir).
    argv*: seq[string]
    stdin*: seq[byte]
    env*: seq[(string, string)]
    filesToWrite*: seq[tuple[path: string; content: seq[byte]]]
    filesToClean*: seq[string]

  InputDelivery* = object
    plan*: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan {.closure.}

  Oracle*[T] = object
    judge*: proc(r: RunResult; x: T): Verdict {.closure.}

  ResourceLimits* = object  ## per-run caps (D16), applied by externalTarget via setrlimit
    perRunTimeout*: Duration ## drives SIGTERM → grace → SIGKILL (D7); 0 == none
    addressSpaceBytes*: int  ## 0 == unset
    cpuSeconds*: int         ## 0 == unset
    stdoutBytes*: int        ## 0 == unset

proc bytesToStr(b: seq[byte]): string =
  result = newString(b.len)
  for i in 0 ..< b.len: result[i] = char(b[i])

proc strToBytes(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  for i in 0 ..< s.len: result[i] = byte(s[i])

# --- input delivery built-ins (D13) ---
proc stdinDelivery*(): InputDelivery =
  ## Feed the input on the child's stdin; argv unchanged (filters, codecs, jq...).
  InputDelivery(plan: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan =
    InputPlan(argv: baseArgv, stdin: bytes))

proc argvFileDelivery*(suffix = ""): InputDelivery =
  ## Write the input to a temp file in `runDir` and substitute it for the `@@`
  ## placeholder in argv (libFuzzer/AFL convention; hunt's "write a .nim, pass its
  ## path" is this with `suffix = ".nim"`). The file is listed for cleanup.
  InputDelivery(plan: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan =
    let path = runDir / ("ptinput" & suffix)
    var argv = baseArgv
    for i in 0 ..< argv.len:
      if argv[i] == "@@": argv[i] = path
    InputPlan(argv: argv, filesToWrite: @[(path, bytes)], filesToClean: @[path]))

proc envVarDelivery*(name: string): InputDelivery =
  ## Pass the input as the value of env var `name` (small configs).
  InputDelivery(plan: proc(bytes: seq[byte]; baseArgv: seq[string]; runDir: string): InputPlan =
    InputPlan(argv: baseArgv, env: @[(name, bytesToStr(bytes))]))

# --- oracle built-ins (D14) ---
proc signalOracle*[T](): Oracle[T] =
  ## The default crash oracle: a terminating signal or non-zero exit is a finding,
  ## a timeout is a hang. (An expected non-zero exit is NOT a bug for tools that
  ## use it as a status — those want `exitCodeOracle`.)
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: vTimedOut
    elif r.signal != 0 or r.exitCode != 0: vInteresting
    else: vOk)

proc sanitizerOracle*[T](): Oracle[T] =
  ## A finding iff stderr carries a sanitizer report (ASan/UBSan), regardless of
  ## exit code — sanitizers often exit 0 with the report on stderr (hunt's O2).
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: return vTimedOut
    let err = bytesToStr(r.stderr)
    if "==ERROR:" in err or "runtime error:" in err or "AddressSanitizer" in err: vInteresting
    else: vOk)

proc exitCodeOracle*[T](bugCodes: set[uint8]): Oracle[T] =
  ## A finding on a signal or an exit code in `bugCodes` — for tools where only
  ## *some* non-zero exits mean a bug.
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: vTimedOut
    elif r.signal != 0: vInteresting
    elif r.exitCode in 0..255 and uint8(r.exitCode) in bugCodes: vInteresting
    else: vOk)

proc stderrPatternOracle*[T](pattern: string): Oracle[T] =
  ## A finding iff `pattern` appears in stderr.
  Oracle[T](judge: proc(r: RunResult; x: T): Verdict =
    if r.timedOut: vTimedOut
    elif pattern in bytesToStr(r.stderr): vInteresting
    else: vOk)

# --- corpus interop: AFL/libFuzzer-style directories of one-file-per-input (6d) ---
proc importCorpusDir*(dir: string): seq[seq[byte]] =
  ## Read every regular file in `dir` as one raw byte input — the on-disk format
  ## AFL and libFuzzer use. Feed the result to `FuzzSettings.initialCorpus` (or to
  ## `fuzzBinary` as seeds). A missing directory yields no inputs.
  if not dirExists(dir): return
  for kind, path in walkDir(dir):
    if kind == pcFile: result.add strToBytes(readFile(path))

proc exportCorpusDir*(dir: string; inputs: seq[seq[byte]]) =
  ## Write each input as its own file under `dir` (created if absent), so an
  ## external fuzzer can pick up where a proptest run left off. Names are
  ## zero-padded indices for stable ordering.
  createDir(dir)
  for i, inp in inputs:
    writeFile(dir / ("input-" & align($i, 6, '0')), bytesToStr(inp))

proc replayInput*[T](s: Strategy[T]; choices: seq[ChoiceNode]): Option[T] =
  ## Re-materialize the value a recorded choice-sequence produces. Used to turn a
  ## report's IR-mode crash back into its concrete input for repro/export.
  var ds = newReplaySource(choices)
  try: some(s.generate(ds))
  except CatchableError, Defect: none(T)

proc exportCrashes*(dir: string; report: FuzzReport; s: Strategy[seq[byte]]) =
  ## Write each retained crash's bytes to `dir` (created if absent) for repro.
  ## Crashes are stored as choice-IR; replaying through `s` recovers the exact
  ## input that was delivered to the target.
  createDir(dir)
  for i, cr in report.irCrashes:
    let inp = replayInput(s, cr.choices)
    if inp.isSome:
      writeFile(dir / ("crash-" & align($i, 6, '0')), bytesToStr(inp.get))

# --- differential / N-target oracle (FUZZ_PLAN D15) ---
proc differentialTarget*[T](targets: seq[Target[T]];
                            compare: proc(rs: seq[RunResult]; x: T): Verdict): Target[T] =
  ## Fan one input across N child `Target`s and reduce their `RunResult`s to a single
  ## verdict via `compare` (D15) — the generic output-equivalence / differential oracle
  ## (two parsers, gcc-vs-clang, encode→decode round-trip). Still a `Target[T]`, so the
  ## `fuzz` loop is unchanged and this composes with everything. Corpus coverage is the
  ## children's maps concatenated in order, so each child's edges stay distinct frontier
  ## slots; a child's width is pinned on its first non-empty map so a later crash (absent
  ## map → zeros) keeps the joint vector aligned.
  var widths = newSeq[int](targets.len)
  Target[T](run: proc(x: T): Observation[T] =
    var rrs = newSeq[RunResult](targets.len)
    var covs = newSeq[Coverage](targets.len)
    for i, t in targets:
      let obs = t.run(x)
      rrs[i] = obs.runResult
      covs[i] = obs.coverage
    for i in 0 ..< covs.len:
      if widths[i] == 0 and covs[i].counters.len > 0: widths[i] = covs[i].counters.len
    var joint: seq[byte]
    for i in 0 ..< covs.len:
      let base = joint.len
      joint.setLen(base + widths[i])
      for j in 0 ..< min(widths[i], covs[i].counters.len): joint[base + j] = covs[i].counters[j]
    let verdict = compare(rrs, x)
    var msg = ""
    if verdict in {vInteresting, vTimedOut}:
      for i, rr in rrs: msg.add "child " & $i & " exit=" & $rr.exitCode & " sig=" & $rr.signal & "\n"
    Observation[T](verdict: verdict, coverage: Coverage(counters: joint), message: msg))

# --- external target: run an instrumented child process (FUZZ_PLAN D3/D5/D7/D16) ---
when defined(posix):
  import std/posix

  let
    PT_RLIMIT_AS {.importc: "RLIMIT_AS", header: "<sys/resource.h>".}: cint
    PT_RLIMIT_CPU {.importc: "RLIMIT_CPU", header: "<sys/resource.h>".}: cint
    PT_RLIMIT_CORE {.importc: "RLIMIT_CORE", header: "<sys/resource.h>".}: cint

  proc ptSetLimit(res: cint; cap: int) =
    var rl = RLimit(rlim_cur: cap, rlim_max: cap)
    discard setrlimit(res, rl)

  var ptChildCtr = 0
  proc runChild*(argv: seq[string]; env: seq[(string, string)]; stdin: seq[byte];
                 limits: ResourceLimits): RunResult =
    ## fork/exec `argv` with `stdin` fed from a temp file and stdout/stderr captured to
    ## temp files, under `limits`. On timeout: SIGTERM → ~200ms grace → SIGKILL, so a
    ## sancov-instrumented child still dumps its map (D7). Precise signal vs exit code.
    inc ptChildCtr
    let stem = getTempDir() / ("ptfz_" & $getCurrentProcessId() & "_" & $ptChildCtr)
    let inPath = stem & ".in"
    let outPath = stem & ".out"
    let errPath = stem & ".err"
    writeFile(inPath, bytesToStr(stdin))
    var envv: seq[string]
    for k, v in envPairs(): envv.add k & "=" & v
    for kv in env: envv.add kv[0] & "=" & kv[1]
    let ca = allocCStringArray(argv)              # alloc before fork (no malloc in the child)
    let ce = allocCStringArray(envv)
    let timeoutMs = int(limits.perRunTimeout.inMilliseconds)
    let t0 = epochTime()
    let pid = fork()
    if pid < 0:
      deallocCStringArray(ca); deallocCStringArray(ce)
      raiseOSError(osLastError(), "fork failed")
    if pid == 0:
      ptSetLimit(PT_RLIMIT_CORE, 0)
      if limits.addressSpaceBytes > 0: ptSetLimit(PT_RLIMIT_AS, limits.addressSpaceBytes)
      if limits.cpuSeconds > 0: ptSetLimit(PT_RLIMIT_CPU, limits.cpuSeconds)
      let ifd = posix.open(inPath.cstring, O_RDONLY)
      let ofd = posix.open(outPath.cstring, O_WRONLY or O_CREAT or O_TRUNC, 0o644)
      let efd = posix.open(errPath.cstring, O_WRONLY or O_CREAT or O_TRUNC, 0o644)
      discard dup2(ifd, 0); discard dup2(ofd, 1); discard dup2(efd, 2)
      discard close(ifd); discard close(ofd); discard close(efd)
      discard execvpe(argv[0].cstring, ca, ce)
      exitnow(127)                                # exec failed
    var status: cint = 0
    if timeoutMs <= 0:
      discard waitpid(pid, status, cint(0))
    else:
      let deadline = t0 + timeoutMs.float / 1000.0
      var reaped = false
      while not reaped:
        if waitpid(pid, status, WNOHANG) == pid:
          reaped = true
        elif epochTime() >= deadline:
          discard kill(pid, SIGTERM)              # let proptest_cov.c dump
          let graceEnd = epochTime() + 0.2
          while epochTime() < graceEnd:
            if waitpid(pid, status, WNOHANG) == pid: reaped = true; break
            sleep(5)
          if not reaped:
            discard kill(pid, SIGKILL)
            discard waitpid(pid, status, cint(0))
            reaped = true
          result.timedOut = true
        else:
          sleep(5)
    deallocCStringArray(ca); deallocCStringArray(ce)
    result.durationNs = int64((epochTime() - t0) * 1e9)
    if WIFSIGNALED(status):
      result.signal = int(WTERMSIG(status))
      result.exitCode = -1
    else:
      result.exitCode = int(WEXITSTATUS(status))
    result.stdout = strToBytes(if fileExists(outPath): readFile(outPath) else: "")
    result.stderr = strToBytes(if fileExists(errPath): readFile(errPath) else: "")
    removeFile(inPath); removeFile(outPath); removeFile(errPath)

  var ptRunCtr = 0
  proc externalTarget*[T](argv: seq[string]; delivery: InputDelivery; oracle: Oracle[T];
                          limits = ResourceLimits();
                          encode: proc(x: T): seq[byte]): Target[T] =
    ## A `Target` over an instrumented external binary (D3). Per input: encode → `delivery`
    ## plans the run → write its files + set a per-run `$PROPTEST_COV_FILE` → `runChild` under
    ## `limits` → `oracle` judges the `RunResult` → read the dumped sancov map (absent or
    ## torn/poisoned → empty, advisory; D7) → clean up.
    Target[T](run: proc(x: T): Observation[T] =
      inc ptRunCtr
      let runDir = getTempDir() / ("ptrun_" & $getCurrentProcessId() & "_" & $ptRunCtr)
      createDir(runDir)
      let covFile = runDir / "cov.bin"
      let plan = delivery.plan(encode(x), argv, runDir)
      for fw in plan.filesToWrite: writeFile(fw.path, bytesToStr(fw.content))
      var env = plan.env
      env.add ("PROPTEST_COV_FILE", covFile)
      let rr = runChild(plan.argv, env, plan.stdin, limits)
      let verdict = oracle.judge(rr, x)
      var cov = Coverage(counters: @[])
      if fileExists(covFile):
        try: cov = parseCoverageMap(readFile(covFile))
        except ValueError: discard            # crash-poisoned / torn → advisory empty (D7)
      var msg = ""
      if verdict in {vInteresting, vTimedOut}:
        # Lead with the crash descriptor so a bare signal (no stderr, no coverage)
        # still keys distinctly per crash type for de-dup (6a).
        msg = "exit=" & $rr.exitCode & " signal=" & $rr.signal &
              (if rr.timedOut: " timedout" else: "") & "\n" & bytesToStr(rr.stderr)
      try: removeDir(runDir)
      except CatchableError: discard
      Observation[T](verdict: verdict, coverage: cov, message: msg, runResult: rr))

  proc fuzzBinary*(s: Strategy[seq[byte]]; argv: seq[string];
                   settings = FuzzSettings(); limits = ResourceLimits()): FuzzReport =
    ## The 1-line happy path: fuzz `argv`, feeding each generated input on stdin, treating a
    ## crash / non-zero exit as a finding. For a structured target, build an `externalTarget`
    ## with a custom delivery / oracle / encode instead.
    var frontier = newCoverageFrontier()
    let target = externalTarget[seq[byte]](argv, stdinDelivery(), signalOracle[seq[byte]](),
                                           limits, proc(x: seq[byte]): seq[byte] = x)
    fuzz(s, target, frontier, settings)
