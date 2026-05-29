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

import std/[options, times, monotimes]
import ./strategy, ./datasource, ./engine, ./rng, ./coverage, ./choice, ./fuzzir
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
  ## The IR-mutation kernel — #110's architectural payoff.
  ##
  ## Mutates `seq[ChoiceNode]` directly via the `mutateIR*` suite. Every
  ## mutation respects the kind/range constraints the strategy declared,
  ## so the mutated IR replays through `fuzzOnceIR` with near-zero
  ## structural rejection. Span-aware splice/delete/duplicate produce
  ## cross-input recombinations that no byte-mutator can express.
  let priorMode = currentCoverageMode()
  setCoverageMode(cmRecording)
  defer: setCoverageMode(priorMode)
  resetCoverage()
  var rng = initSplitMix64(settings.seed)

  # Internal corpus carries (choices, spans). spans are an internal cache
  # for the structural mutators; the public report exposes only the
  # choice sequences.
  var corpus: seq[tuple[choices: seq[ChoiceNode], spans: seq[Span]]]
  for seed in settings.initialIRCorpus:
    let cap = captureIR(s, seed)
    if cap.ok: corpus.add (choices: cap.choices, spans: cap.spans)
  if corpus.len == 0:
    # Seed from one fresh random generation.
    var ds = newDataSource(initSplitMix64(rng.next))
    try:
      discard s.generate(ds)
      corpus.add (choices: ds.recorded, spans: ds.spans)
    except CatchableError, Defect:
      discard  # degenerate strategy; we'll loop with empty corpus
  result.corpus = FuzzCorpus(kind: fckIR, irEntries: @[])
  for entry in corpus: result.corpus.irEntries.add entry.choices

  let started = getMonoTime()
  let hasDeadline = settings.timeBudget.inNanoseconds > 0
  var iter = 0
  while corpus.len > 0:
    if settings.maxIterations > 0 and iter >= settings.maxIterations: break
    if hasDeadline:
      let elapsed = getMonoTime() - started
      if elapsed.inNanoseconds > settings.timeBudget.inNanoseconds:
        result.timedOut = true
        break
    inc iter
    let parentIdx = int(rng.next mod uint64(corpus.len))
    let parent = corpus[parentIdx]
    # Uniform random over the five IR mutators. Weighted scheduling
    # is a separate concern; first ship the uniform baseline so the
    # diversity is observable, then tune.
    let pick = rng.next mod 5'u64
    var mutant: seq[ChoiceNode]
    case pick
    of 0: mutant = mutateIRPerturbInteger(rng, parent.choices)
    of 1: mutant = mutateIRKindBoundary(rng, parent.choices)
    of 2:
      let donorIdx = int(rng.next mod uint64(corpus.len))
      let donor = corpus[donorIdx]
      mutant = mutateIRSpanSplice(rng, parent.choices, donor.choices,
                                  parent.spans, donor.spans)
    of 3: mutant = mutateIRSpanDelete(rng, parent.choices, parent.spans)
    else: mutant = mutateIRSpanDuplicate(rng, parent.choices, parent.spans)

    let covBefore = currentCoverage()
    let r = fuzzOnceIR(s, prop, mutant)
    let covAfter = currentCoverage()
    if covAfter > covBefore:
      let cap = captureIR(s, mutant)
      if cap.ok:
        corpus.add (choices: cap.choices, spans: cap.spans)
        result.corpus.irEntries.add cap.choices
    case r.outcome
    of foOk, foRejected: discard
    of foFalsified:
      result.irCrashes.add (choices: mutant, message: r.message)
  result.iterations = iter
  result.coverageHits = currentCoverage()

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

