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

import std/[options, macros, hashes, times, monotimes]
import ./strategy, ./datasource, ./engine, ./rng

# --- coverage runtime ---------------------------------------------------------
#
# A fixed-size bitmap of edge hits, keyed by the (file, line, column) hash
# of the instrumented branch. AFL-style: collisions are tolerated; the
# tradeoff is a small false-equivalence rate for vastly simpler runtime
# semantics than a perfect-hash scheme. 2^13 = 8192 edges is plenty for
# any single SUT we'll fuzz under unit tests; promote to a configurable
# bound when real codebases push past it.

const coverageEdgeCount* = 8192
const coverageEdgeMask = coverageEdgeCount - 1

var coverageBitmap {.threadvar.}: array[coverageEdgeCount, uint8]
var coverageHitsCached {.threadvar.}: int

proc resetCoverage*() =
  ## Zero the per-thread coverage bitmap and hit count. The fuzz runner
  ## calls this before each example so coverage growth measures *this
  ## example's* contribution, not the whole run's.
  for i in 0 ..< coverageEdgeCount:
    coverageBitmap[i] = 0
  coverageHitsCached = 0

proc recordEdge*(id: int) {.inline.} =
  ## Mark edge `id` as hit. `id mod coverageEdgeCount` is the bitmap
  ## slot; collisions are tolerated (AFL convention). Only the first
  ## hit of an edge updates the count, so re-hits in a tight loop
  ## don't inflate the score.
  let slot = id and coverageEdgeMask
  if coverageBitmap[slot] == 0:
    coverageBitmap[slot] = 1
    inc coverageHitsCached

proc currentCoverage*(): int =
  ## Number of distinct edges hit since the last `resetCoverage`.
  ## O(1) — we maintain a running cached count.
  coverageHitsCached

# --- {.cover.} macro pragma --------------------------------------------------
#
# Walks a proc's body AST and injects `recordEdge(id)` at the start of
# every branch arm (the `then` and `else` of an `if`, every arm of a
# `case`, the body of a `while`). Edge IDs are the source location hash
# (file + line + column) modulo `coverageEdgeCount`, so they're stable
# across runs and don't require a global counter — but collisions are
# tolerated per the AFL convention.

proc edgeIdFromLineInfo(n: NimNode): int =
  let li = n.lineInfoObj
  let h = hash(li.filename) !& hash(li.line) !& hash(li.column)
  abs(!$h) and (coverageEdgeCount - 1)

proc instrumentNode(n: NimNode): NimNode =
  ## Recursive AST rewrite. Branch nodes (`if`, `case`, `while`) get
  ## `recordEdge` injected into each arm; all other nodes are walked
  ## structurally so nested branches deeper in the body are also
  ## instrumented.
  case n.kind
  of nnkIfStmt, nnkIfExpr, nnkWhenStmt:
    result = n.copyNimNode
    for branch in n:
      let edgeId = edgeIdFromLineInfo(branch)
      case branch.kind
      of nnkElifBranch, nnkElifExpr:
        let cond = branch[0]
        let body = instrumentNode(branch[1])
        let wrapped = newStmtList(
          newCall(bindSym"recordEdge", newLit(edgeId)), body)
        result.add nnkElifBranch.newTree(cond, wrapped)
      of nnkElse, nnkElseExpr:
        let body = instrumentNode(branch[0])
        let wrapped = newStmtList(
          newCall(bindSym"recordEdge", newLit(edgeId)), body)
        result.add nnkElse.newTree(wrapped)
      else:
        result.add branch  # unexpected; preserve verbatim
  of nnkCaseStmt:
    result = n.copyNimNode
    # The selector (first child) is not a branch; pass it through unmodified.
    result.add n[0]
    for i in 1 ..< n.len:
      let branch = n[i]
      let edgeId = edgeIdFromLineInfo(branch)
      let newBranch = branch.copyNimNode
      # nnkOfBranch / nnkElse: last child is the body, preceding children
      # are the match patterns (for nnkOfBranch) or absent (for nnkElse).
      for j in 0 ..< branch.len - 1:
        newBranch.add branch[j]
      let body = instrumentNode(branch[^1])
      newBranch.add newStmtList(
        newCall(bindSym"recordEdge", newLit(edgeId)), body)
      result.add newBranch
  of nnkWhileStmt:
    let edgeId = edgeIdFromLineInfo(n)
    let cond = n[0]
    let body = instrumentNode(n[1])
    let wrapped = newStmtList(
      newCall(bindSym"recordEdge", newLit(edgeId)), body)
    result = nnkWhileStmt.newTree(cond, wrapped)
  else:
    result = n.copyNimNode
    for child in n:
      result.add instrumentNode(child)

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

# --- FuzzSettings / FuzzReport / fuzzWith ------------------------------------

type
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
    initialCorpus*: seq[seq[byte]]
      ## Seed inputs (e.g., from a previous AFL run, hand-curated edge
      ## cases). The runner mutates from these instead of starting from
      ## empty buffers. Optional; empty default is fine.
    initialInputSize*: int
      ## Bytes per random initial input when the corpus is exhausted.
      ## Defaults to 64 if 0.

  FuzzReport* = object
    iterations*: int
      ## Number of `fuzzOnce` calls performed before exit.
    coverageHits*: int
      ## Distinct edges discovered across the whole run. Approximates
      ## "what fraction of the SUT did we explore."
    corpus*: seq[seq[byte]]
      ## Inputs that found new coverage. Persistent across runs (the
      ## next fuzz session can pass these in as `initialCorpus`).
    crashes*: seq[tuple[bytes: seq[byte], message: string]]
      ## Inputs that triggered a property failure or exception. Each
      ## carries the exact bytes that reproduce the crash and the
      ## exception message for triage.
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

proc fuzzWith*[T](s: Strategy[T], prop: proc(x: T),
                  settings: FuzzSettings): FuzzReport =
  ## Coverage-guided fuzz loop. Mutates from a corpus of
  ## coverage-rewarding inputs; each iteration runs `fuzzOnce` and
  ## either grows the corpus (new edges) or appends to crashes
  ## (property failure). Exits at `maxIterations` or `timeBudget`,
  ## whichever first.
  ##
  ## The fuzz runner uses `recordEdge` calls from `{.cover.}`'d code,
  ## so for coverage signal to fire, the SUT must be instrumented.
  ## An uninstrumented SUT degrades gracefully to "random fuzzing"
  ## (all inputs report zero new coverage; the corpus stays minimal).
  resetCoverage()
  var rng = initSplitMix64(settings.seed)
  let initSize = if settings.initialInputSize > 0: settings.initialInputSize
                 else: 64
  # Seed the corpus: explicit inputs first, then one random.
  var corpus: seq[seq[byte]] = settings.initialCorpus
  if corpus.len == 0:
    corpus.add randomBytes(rng, initSize)
  result.corpus = corpus

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
    # Pick a corpus parent and mutate.
    let parent = result.corpus[int(rng.next mod uint64(result.corpus.len))]
    let bytes = if rng.next mod 2'u64 == 0: mutateByteFlip(rng, parent)
                else: mutateByteReplace(rng, parent)
    let covBefore = currentCoverage()
    let r = fuzzOnce(s, prop, bytes)
    let covAfter = currentCoverage()
    if covAfter > covBefore:
      # New edge(s) found via this input — promote to corpus.
      result.corpus.add bytes
    case r.outcome
    of foOk, foRejected: discard
    of foFalsified:
      result.crashes.add (bytes: bytes, message: r.message)
  result.iterations = iter
  result.coverageHits = currentCoverage()

macro cover*(procDef: untyped): untyped =
  ## Pragma macro: rewrite the proc's body so each branch point records
  ## an edge hit. Use as `proc f(x: int) {.cover.} = ...`. The
  ## instrumentation is source-level (Nim's compiler doesn't expose a
  ## sanitizer-coverage hook); each `if` / `case` / `while` branch gets
  ## a unique ID derived from its source location.
  expectKind procDef, {nnkProcDef, nnkFuncDef, nnkLambda}
  result = procDef
  result[^1] = instrumentNode(procDef[^1])

