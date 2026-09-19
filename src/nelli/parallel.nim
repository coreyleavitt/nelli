## Parallel state-machine testing — linearisability checking.
##
## Given a recorded concurrent history of operations (each with an
## `invokeTime`, a `responseTime`, the operation tag, and the value the
## SUT actually returned), determine whether there exists a sequential
## ordering of those operations — respecting real-time happens-before
## — that is consistent with a sequential model.
##
## This is the most powerful concurrency-bug-finding technique in PBT:
## `quickcheck-state-machine` (Haskell) and PropEr (Erlang) have it;
## most other PBT libraries don't. The algorithm here is the Wing-Gong
## definition implemented as a happens-before-respecting backtracking
## search. Worst case `O(n!)` but in practice prunes hard — the
## practical bug-finding regime (≤ 10 ops, 2-3 threads) runs in
## milliseconds.
##
## **Current scope.** This module ships the algorithmic core
## (`isLinearisable`). A user with a real concurrent SUT records the
## `(threadId, invokeTime, responseTime, opId, observedRet)` of each
## operation — typically with `getMonoTime().ticks` before and after
## the call — and hands the resulting `seq[LinEvent]` to
## `isLinearisable`. A thread-based runner that *generates* concurrent
## histories automatically (spawning suffixes, recording timestamps,
## then handing the history to the checker) is the natural follow-up;
## the algorithmic core ships first so the Wing-Gong definition is
## in place and tested independent of the thread-orchestration layer.

import std/[options, hashes, sets, locks, monotimes, times]
import ./strategy, ./datasource, ./int128, ./choice

when defined(windows):
  # `SwitchToThread` has no `winlean` wrapper -- declared directly here,
  # matching the raw-FFI precedent in fuzzworker.nim/fuzz.nim for a syscall
  # the stdlib doesn't already expose. Returns nonzero iff it actually
  # switched to another ready thread; we don't care which, so it's discarded
  # at the call site.
  proc winSwitchToThread(): int32 {.stdcall, dynlib: "kernel32",
                                     importc: "SwitchToThread".}
else:
  import std/posix

type
  LinEvent*[OpId, Ret] = object
    ## One recorded operation invocation. `invokeTime` < `responseTime`
    ## by construction; ops on different threads can have overlapping
    ## intervals (they ran concurrently); ops on the same thread are
    ## totally ordered (one ended before the next began).
    threadId*: int
    invokeTime*, responseTime*: int
    opId*: OpId          ## the model-dispatch tag (often `int` or an enum)
    observedRet*: Ret    ## what the SUT returned for this invocation

  LinResult*[OpId, Ret] = object
    ## Outcome of a linearisability check.
    linearisable*: bool
      ## True iff a valid sequential ordering exists.
    witness*: seq[LinEvent[OpId, Ret]]
      ## When `linearisable`, an ordering that the model accepts.
      ## Empty when `linearisable = false`.
    partialWitness*: seq[LinEvent[OpId, Ret]]
      ## When NOT linearisable, the longest prefix of *any* attempted
      ## ordering that the model accepted. This is debug gold: it
      ## tells the user "these ops linearized fine; the next one is
      ## where the SUT broke." Empty when `linearisable = true` (use
      ## `witness` instead).
    divergingOp*: Option[OpId]
      ## The opId of the first event whose observed return value
      ## diverged from every model trajectory consistent with the
      ## ops placed before it. `none` when `linearisable = true`.
    failureReason*: string
      ## When not linearisable, a short explanation: the operation we
      ## couldn't place + the divergence between model and SUT.

proc isLinearisable*[State, OpId, Ret](
    history: seq[LinEvent[OpId, Ret]],
    initial: State,
    applyModel: proc(s: var State, opId: OpId): Ret,
    retEq: proc(a, b: Ret): bool): LinResult[OpId, Ret] =
  ## Search for a sequential ordering of `history` that (a) respects
  ## real-time happens-before — if op A's response precedes op B's
  ## invocation, A must precede B — and (b) is consistent with
  ## `applyModel` starting from `initial`.
  ##
  ## `retEq` lets the user choose what counts as "the SUT's return
  ## value matches the model's" — strict equality for total functions,
  ## a relaxed check (e.g. set membership) for nondeterministic specs.
  if history.len == 0:
    result.linearisable = true
    return

  # Real-time precedence: for each op `o`, the set of ops that must
  # precede it (everything whose responseTime < o.invokeTime). Reduces
  # the search: an op is only eligible to be placed next if every
  # required-predecessor is already placed.
  var precedes = newSeq[seq[int]](history.len)
  for i in 0 ..< history.len:
    for j in 0 ..< history.len:
      if i != j and history[j].responseTime < history[i].invokeTime:
        precedes[i].add j

  var placed = newSeq[bool](history.len)
  var placedMask: uint64 = 0
  var witness: seq[LinEvent[OpId, Ret]]
  var found = false
  # Wing-Gong memoization: cache (placedSet, stateHash) of explored
  # configurations that *dead-ended*. On revisit we skip the recursion
  # but still update bestPartial — partial-witness quality isn't
  # compromised. Bitmask encoding works up to 64 ops (history.len ≤
  # 64); past that, fall back to no memoization. Real bug-finding
  # regime is ≤ 10 ops per thread per round, so 64 is comfortably wide.
  let useMemo = history.len <= 64
  var deadEnds: HashSet[(uint64, Hash)]
  # Track the longest valid prefix seen across all branches — what
  # we return as `partialWitness` if no full witness exists. Also
  # track the *event* immediately after the longest prefix's end —
  # the first op whose model return disagreed with the SUT.
  var bestPartial: seq[LinEvent[OpId, Ret]]
  var divergingOp: Option[OpId]

  proc backtrack(state: State) =
    if found: return
    if witness.len == history.len:
      found = true
      return
    # Update best-partial: we've successfully placed `witness.len`
    # ops along *this* branch. If that beats the running maximum,
    # remember the prefix.
    if witness.len > bestPartial.len:
      bestPartial = witness
    # Wing-Gong: have we already explored this exact (placed, state)
    # configuration and learned it dead-ends? Skip the work.
    if useMemo and (placedMask, hash(state)) in deadEnds: return
    # Try every eligible op. Track which ones the model rejected so,
    # if every option dies here, the *first* rejected op is the one
    # we report as diverging.
    var anyEligible = false
    var firstRejected: Option[OpId]
    for i in 0 ..< history.len:
      if placed[i]: continue
      var eligible = true
      for p in precedes[i]:
        if not placed[p]:
          eligible = false
          break
      if not eligible: continue
      anyEligible = true
      var newState = state
      let modelRet = applyModel(newState, history[i].opId)
      if not retEq(modelRet, history[i].observedRet):
        if firstRejected.isNone:
          firstRejected = some(history[i].opId)
        continue
      placed[i] = true
      placedMask = placedMask or (1'u64 shl i)
      witness.add history[i]
      backtrack(newState)
      if found: return
      placed[i] = false
      placedMask = placedMask and not (1'u64 shl i)
      discard witness.pop()
    # If this branch dead-ended (every eligible op was rejected) and
    # we've gone deeper than any prior dead-end, capture the diverging
    # op at *this* depth.
    if anyEligible and firstRejected.isSome and witness.len >= bestPartial.len:
      divergingOp = firstRejected
    # Record this config as a dead end so sibling subtrees that arrive
    # via permuted prefix can skip it.
    if useMemo and not found:
      deadEnds.incl (placedMask, hash(state))

  backtrack(initial)
  if found:
    result.linearisable = true
    result.witness = witness
  else:
    result.linearisable = false
    result.partialWitness = bestPartial
    result.divergingOp = divergingOp
    result.failureReason =
      "no sequential ordering consistent with the model — SUT diverged" &
      (if divergingOp.isSome:
        " at opId " & $divergingOp.get & " after " & $bestPartial.len &
        " op(s) placed"
       else: "")

# --- The thread-based parallel runner (#101) ----------------------------------

type
  LinOpDef*[State, SUT, Ret] = object
    ## One operation in a parallel state-machine spec. `applySUT` is
    ## executed against the real (possibly shared, possibly racy)
    ## system under test from worker threads; `applyModel` is the
    ## sequential reference, executed from the main thread when
    ## checking linearisability. Both must be `gcsafe` so they can
    ## be invoked from worker threads under `--threads:on`.
    opId*: int
    applySUT*: proc(sut: SUT): Ret {.gcsafe, closure.}
    applyModel*: proc(s: var State): Ret {.gcsafe, closure.}

  LinSpec*[State, SUT, Ret] = object
    ## A parallel state-machine specification. `newSUT` is called once
    ## per repetition to materialize a fresh SUT (typically allocates
    ## shared memory + initializes locks). `ops` enumerates the
    ## operations the runner may schedule; opIds index into this list.
    modelInitial*: State
    newSUT*: proc(): SUT {.gcsafe, closure.}
    ops*: seq[LinOpDef[State, SUT, Ret]]

  ScheduledOp* = object
    ## One scheduled operation within a parallel plan: which op to run,
    ## plus how many real scheduler-yield calls (`spinJitter`) to spend
    ## immediately BEFORE invoking it — never during the op's own body.
    ## See `parallelCheck`'s doc comment for exactly what that can and
    ## cannot catch, and `parallelJitterPoint` for perturbing INSIDE an
    ## op. Jitter delays are drawn from the choice sequence, so they
    ## *shrink* — if a race only manifests at a specific delay
    ## pattern, the engine can pull it toward the minimal pattern
    ## that still exposes the bug.
    opIdx*: int
    jitter*: int

  ParallelPlan* = object
    ## A generated plan: sequential prefix (run on the main thread)
    ## plus N parallel suffixes (one per worker thread). Plans are
    ## values; nothing about them is thread-bound until the runner
    ## hands a suffix to a worker.
    prefix*: seq[ScheduledOp]
    suffixes*: seq[seq[ScheduledOp]]

  # --- private runner state ---

  WorkerCtx[State, SUT, Ret] = object
    ## Per-worker scratch passed into each thread by pointer. Each
    ## worker writes only to its own slot in `histories` — no shared
    ## mutation. The barrier and clock pointer are shared.
    threadId: int
    sut: SUT
    ops: ptr seq[LinOpDef[State, SUT, Ret]]
    suffix: ptr seq[ScheduledOp]
    history: ptr seq[LinEvent[int, Ret]]
    barrierMu: ptr Lock
    barrierCv: ptr Cond
    barrierCount: ptr int
    barrierTarget: int

proc schedulerYield() {.inline.} =
  ## Ask the OS scheduler to run a different ready thread right now, if
  ## one exists. A real syscall (`sched_yield` / `SwitchToThread`) that
  ## can produce an actual context switch — unlike a busy no-op spin,
  ## which never leaves this thread's own timeslice and so can never
  ## influence which thread the kernel schedules next.
  when defined(windows):
    discard winSwitchToThread()
  else:
    discard posix.sched_yield()

proc spinJitter(n: int) {.inline.} =
  ## `n` scheduler-yield calls (see `schedulerYield`), spent before an
  ## op is invoked. `n = 0` costs nothing — the loop body never runs —
  ## so `maxJitter = 0` remains a true no-op fast path.
  ##
  ## This used to be a counted busy spin (`var k = 0; while k < n: inc
  ## k`): a pure no-op loop that never asked the OS for anything and so
  ## ran in nanoseconds — several orders of magnitude below a real
  ## scheduling quantum (~1-15ms on Linux) and therefore structurally
  ## incapable of influencing which thread actually runs next. `n`'s
  ## UNIT is unchanged (still "how many jitter units", same integer
  ## range every existing caller already passes); only the mechanism
  ## each unit spends its time on changed, from spinning to yielding.
  for _ in 0 ..< n:
    schedulerYield()

proc parallelJitterPoint*(n = 1) =
  ## Call this from INSIDE an `applySUT` op body, at the exact point
  ## you want the OS scheduler to reconsider which thread runs next —
  ## e.g. between the read and the write of an unsynchronized
  ## read-modify-write. `ScheduledOp.jitter` / `maxJitter` can only
  ## insert delay BETWEEN ops (see `parallelCheck`'s doc comment); it
  ## never runs while an op's body is executing, so it structurally
  ## cannot widen a race window that lives inside a single op. This
  ## proc performs the same real scheduler-yield `spinJitter` uses,
  ## just reachable from wherever inside the op the SUT author needs
  ## it — the library's answer to "hand-roll a `sleep` in the SUT" for
  ## exposing an intra-op race.
  for _ in 0 ..< n:
    schedulerYield()

proc workerProc[State, SUT, Ret](
    ctx: ptr WorkerCtx[State, SUT, Ret]) {.thread, nimcall.} =
  # Barrier: wait until every worker has arrived, then all release
  # together so the parallel phase actually overlaps in wall time.
  acquire(ctx[].barrierMu[])
  inc ctx[].barrierCount[]
  if ctx[].barrierCount[] >= ctx[].barrierTarget:
    broadcast(ctx[].barrierCv[])
  else:
    while ctx[].barrierCount[] < ctx[].barrierTarget:
      wait(ctx[].barrierCv[], ctx[].barrierMu[])
  release(ctx[].barrierMu[])

  for sched in ctx[].suffix[]:
    spinJitter(sched.jitter)
    let invokeTime = int(getMonoTime().ticks)
    let ret = ctx[].ops[][sched.opIdx].applySUT(ctx[].sut)
    let responseTime = int(getMonoTime().ticks)
    ctx[].history[].add LinEvent[int, Ret](
      threadId: ctx[].threadId,
      invokeTime: invokeTime,
      responseTime: responseTime,
      opId: ctx[].ops[][sched.opIdx].opId,
      observedRet: ret)

proc runPlan[State, SUT, Ret](
    spec: LinSpec[State, SUT, Ret],
    plan: ParallelPlan): seq[LinEvent[int, Ret]] =
  ## One execution of a plan: build SUT, run prefix on main thread,
  ## spawn workers, join, merge histories. The SUT is materialized
  ## fresh per call (callers loop for repetitions).
  let sut = spec.newSUT()
  # Prefix: run sequentially on main thread; record events as we go.
  for sched in plan.prefix:
    spinJitter(sched.jitter)
    let invokeTime = int(getMonoTime().ticks)
    let ret = spec.ops[sched.opIdx].applySUT(sut)
    let responseTime = int(getMonoTime().ticks)
    result.add LinEvent[int, Ret](
      threadId: 0, invokeTime: invokeTime, responseTime: responseTime,
      opId: spec.ops[sched.opIdx].opId, observedRet: ret)

  if plan.suffixes.len == 0: return

  # Parallel phase. Barrier sync across workers + main-thread waiter.
  var barrierMu: Lock; initLock(barrierMu)
  var barrierCv: Cond; initCond(barrierCv)
  var barrierCount = 0
  let target = plan.suffixes.len
  # Per-worker history slots, allocated outside the threads.
  var perThreadHistories = newSeq[seq[LinEvent[int, Ret]]](plan.suffixes.len)
  # Suffix value-copies — we pass pointers into stable storage so
  # the worker threads don't see moving seq buffers.
  var suffixesLocal = plan.suffixes
  var opsLocal = spec.ops
  var ctxs = newSeq[WorkerCtx[State, SUT, Ret]](plan.suffixes.len)
  for i in 0 ..< plan.suffixes.len:
    ctxs[i] = WorkerCtx[State, SUT, Ret](
      threadId: i + 1,           # prefix is thread 0; workers are 1..N
      sut: sut,
      ops: addr opsLocal,
      suffix: addr suffixesLocal[i],
      history: addr perThreadHistories[i],
      barrierMu: addr barrierMu,
      barrierCv: addr barrierCv,
      barrierCount: addr barrierCount,
      barrierTarget: target)
  var threads = newSeq[Thread[ptr WorkerCtx[State, SUT, Ret]]](plan.suffixes.len)
  for i in 0 ..< plan.suffixes.len:
    createThread(threads[i], workerProc[State, SUT, Ret], addr ctxs[i])
  joinThreads(threads)
  deinitLock(barrierMu)
  deinitCond(barrierCv)
  for h in perThreadHistories:
    for ev in h: result.add ev

proc parallelCheck*[State, SUT, Ret](
    spec: LinSpec[State, SUT, Ret],
    retEq: proc(a, b: Ret): bool {.closure.},
    prefixSteps = 3,
    parallelSteps = 3,
    threads = 2,
    repetitions = 5,
    maxJitter = 100): Strategy[LinResult[int, Ret]] =
  ## The thread-based parallel runner. Generates a `ParallelPlan` from
  ## the choice sequence (op indices + jitter delays — both shrinkable),
  ## executes the plan `repetitions` times on real threads with a
  ## start-barrier, builds a history, and runs `isLinearisable`.
  ##
  ## **Repetitions**: racy bugs are scheduler-dependent. The same plan
  ## may pass on one execution and fail on the next. The strategy
  ## short-circuits on the *first* non-linearisable result among the
  ## repetitions — that result is what the engine sees.
  ##
  ## **Jitter from the choice sequence**: each scheduled op carries an
  ## integer in `[0, maxJitter]` drawn from the source, spent as real
  ## OS scheduler-yield calls (`spinJitter`) immediately BEFORE that op
  ## is invoked. The shrinker can pull jitter values toward 0, finding
  ## the minimal scheduling perturbation that still reproduces a bug.
  ##
  ## **What jitter can and cannot catch.** Jitter only ever runs
  ## BETWEEN ops — it perturbs which thread the scheduler picks to run
  ## next and how a thread's suffix is staggered relative to its
  ## siblings. It NEVER runs while an op's body (`applySUT`) is
  ## executing. So it can help expose bugs that hinge on ordering or
  ## timing BETWEEN two ops, but it structurally CANNOT widen a race
  ## window that lives INSIDE a single op's body — most concretely, an
  ## unsynchronized read-modify-write (read a field, compute, write it
  ## back) racing against another thread's read-modify-write of the
  ## same field. No value of `maxJitter` catches that shape of bug:
  ## there is no op boundary between the read and the write for jitter
  ## to land on.
  ##
  ## If your SUT has that shape of race and you want the harness —
  ## rather than a hand-rolled `sleep` inside the SUT itself — to widen
  ## the window, call `parallelJitterPoint()` from inside `applySUT` at
  ## the specific point you want the scheduler to reconsider (e.g.
  ## between the read and the write). It performs the same real
  ## scheduler-yield mechanism as `maxJitter`, just reachable from
  ## inside an op body instead of only between ops.

  let spec = spec   # capture by value
  let retEq = retEq
  let ops = spec.ops
  let opCount = ops.len

  newStrategy(proc(src: var DataSource): LinResult[int, Ret] =
    # 1. Draw the plan. Inline the draw to avoid a nested closure
    # capturing `var src` (Nim forbids capturing var by reference).
    var plan: ParallelPlan
    if opCount > 0:
      for _ in 0 ..< prefixSteps:
        let opIdx = toInt64(src.drawInteger(
          toInt128(0), toInt128(opCount - 1), toInt128(0))).int
        let jitter = if maxJitter <= 0: 0
                     else: toInt64(src.drawInteger(
                       toInt128(0), toInt128(maxJitter), toInt128(0))).int
        plan.prefix.add ScheduledOp(opIdx: opIdx, jitter: jitter)
      for t in 0 ..< threads:
        var suffix: seq[ScheduledOp]
        for _ in 0 ..< parallelSteps:
          let opIdx = toInt64(src.drawInteger(
            toInt128(0), toInt128(opCount - 1), toInt128(0))).int
          let jitter = if maxJitter <= 0: 0
                       else: toInt64(src.drawInteger(
                         toInt128(0), toInt128(maxJitter), toInt128(0))).int
          suffix.add ScheduledOp(opIdx: opIdx, jitter: jitter)
        plan.suffixes.add suffix

    # 2. Run repetitions; short-circuit on first non-linearisable.
    var lastResult: LinResult[int, Ret]
    lastResult.linearisable = true
    let reps = max(1, repetitions)
    for _ in 0 ..< reps:
      let history = runPlan(spec, plan)
      let r = isLinearisable(
        history, spec.modelInitial,
        proc(s: var State, opId: int): Ret =
          # Map opId → op by linear scan (small spec.ops; not a hot path).
          for op in ops:
            if op.opId == opId: return op.applyModel(s)
          # Unreachable if the runner only emits opIds from the spec.
          default(Ret),
        retEq)
      lastResult = r
      if not r.linearisable: return r
    lastResult)
