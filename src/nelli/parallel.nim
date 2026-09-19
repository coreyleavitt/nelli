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

import std/[options, hashes, sets, locks, monotimes, times, macros]
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
    ## cannot catch, and `{.jitterPoints.}` (or the lower-level
    ## `parallelJitterPoint`) for perturbing INSIDE an op. Jitter delays
    ## are drawn from the choice sequence, so they
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
  ## The low-level primitive: call this from INSIDE an `applySUT` op
  ## body, at the exact point you want the OS scheduler to reconsider
  ## which thread runs next — e.g. between the read and the write of an
  ## unsynchronized read-modify-write. `ScheduledOp.jitter` / `maxJitter`
  ## can only insert delay BETWEEN ops (see `parallelCheck`'s doc
  ## comment); it never runs while an op's body is executing, so it
  ## structurally cannot widen a race window that lives inside a single
  ## op. This proc performs the same real scheduler-yield `spinJitter`
  ## uses, just reachable from wherever inside the op the SUT author
  ## needs it.
  ##
  ## **Prefer `{.jitterPoints.}` (below) unless you specifically want
  ## one yield at one hand-chosen point.** Calling this directly asks
  ## the author to already know exactly where the race window is —
  ## which partly defeats the point of automated concurrency testing —
  ## and it puts a call into `nelli/parallel` inside the code under
  ## test, giving production code a dependency on a test harness for no
  ## other reason. `{.jitterPoints.}` is the recommended surface for
  ## "instrument this proc for the harness"; this proc remains public
  ## and supported as the primitive it's built on, for the case where
  ## you genuinely do want a single yield at a single point you've
  ## already identified.
  ##
  ## **Measured reliability**: placed at the read/write boundary of the
  ## same unsynchronized-increment race `parallelCheck`'s doc comment
  ## describes, this hook (default `n = 1`, no `sleep` anywhere in the
  ## op) caught the race in 20/20 idle runs and 10/10 CPU-contended runs
  ## -- see "lock-free wrong counter is detected via parallelJitterPoint
  ## (no sleep)" in `tests/tparallelcheck.nim`. As with every catch-rate
  ## figure in this module, that is a one-time measurement taken when
  ## the hook was introduced (round 10), not a property re-verified by
  ## every sweep -- the single seeded run in that test is what actually
  ## runs on every sweep, and it guards the basic catch (an
  ## `otFalsified`/`otFlaky` outcome), not the specific ratio.
  for _ in 0 ..< n:
    schedulerYield()

proc insertJitterBoundaries(n: NimNode; count: var int; procName: string): NimNode
  ## Forward declaration — mutually recursive with `instrumentStmtList`
  ## below (each statement list splits its children via
  ## `insertJitterBoundaries`; each control-flow node recurses into its
  ## nested statement list(s) via `instrumentStmtList`). See
  ## `insertJitterBoundaries`'s own doc comment further down for what it
  ## actually does. `procName` is threaded through purely so the
  ## self-reporting fallback warning (see that doc comment) can name the
  ## annotated proc; it plays no role in the rewrite itself.

proc instrumentStmtList(list: NimNode; count: var int; procName: string): NimNode =
  ## Split every adjacent-statement boundary of `list` with a
  ## `parallelJitterPoint()` call — but NEVER after the final statement.
  ## That asymmetry is deliberate and load-bearing: if `list` is (or
  ## ends up nested inside) a proc's own top-level body, or a branch
  ## body sitting in the proc's implicit-return position, its last
  ## statement can be the proc's/branch's implicit `result` — appending
  ## a void call after it would silently change what the proc returns.
  ## Each element is additionally recursed into via `insertJitterBoundaries`
  ## so control-flow nested inside a single statement (an `if` inside a
  ## `for` body, etc.) is instrumented too. `count` accumulates the
  ## number of `parallelJitterPoint()` calls actually inserted, across
  ## the whole recursion — the macro reads it back to detect a total
  ## no-op rather than guessing from any one list's length.
  result = list.copyNimNode
  for i in 0 ..< list.len:
    result.add insertJitterBoundaries(list[i], count, procName)
    if i < list.len - 1:
      result.add newCall(bindSym"parallelJitterPoint")
      inc count

## Nested-callable node kinds `insertJitterBoundaries` must never recurse
## into or warn about, even though several of them carry an `nnkStmtList`
## body: a `proc`/`func`/`lambda`/etc. declared inside the annotated proc's
## body is a SEPARATE callable with its own statement lists, not part of
## this proc's control flow. Instrumenting it (or warning that it was
## skipped) would be incorrect attribution — the "unhandled construct"
## fallback warning below exists to catch REAL gaps like round 13's
## `nnkDefer`/`nnkWhenStmt`, not to fire on every nested `proc` a SUT
## happens to declare.
const jitterNestedCallableKinds = {
  nnkProcDef, nnkFuncDef, nnkLambda, nnkIteratorDef, nnkTemplateDef,
  nnkMacroDef, nnkConverterDef, nnkMethodDef, nnkDo}

proc hasStmtListChild(n: NimNode): bool =
  ## True if `n` has a direct child that is itself an `nnkStmtList` —
  ## i.e. `n` is (or looks like) a statement-holding construct rather
  ## than a plain expression or leaf. Used only by the fallback arm
  ## below to decide whether a node kind `insertJitterBoundaries` has no
  ## dedicated arm for is nonetheless the kind of thing that SHOULD have
  ## one. Deliberately shallow (direct children only): `nnkIfExpr` and
  ## `nnkCaseStmt`-as-expression wrap their branch bodies in
  ## `nnkElifExpr`/`nnkOfBranch` first, not a bare `nnkStmtList`, so this
  ## check does not mistake a genuine expression position for a
  ## statement list the way a deep search would.
  for child in n:
    if child.kind == nnkStmtList:
      return true
  false

proc insertJitterBoundaries(n: NimNode; count: var int; procName: string): NimNode =
  ## AST rewrite used by `{.jitterPoints.}`: insert a
  ## `parallelJitterPoint()` call between every pair of adjacent
  ## statements reachable through `n`'s control-flow structure — not
  ## just `n`'s own top-level statement list. An N-statement list has
  ## N-1 boundaries between them; every boundary gets a yield, so
  ## whichever boundary the real race lives at — the SUT author does
  ## not need to know which — a yield lands there. This generalises the
  ## read/write-boundary case `parallelJitterPoint` asks the author to
  ## hand-locate: an unsynchronized read-modify-write is, at the Nim
  ## source level, two adjacent statements (read into a local, then
  ## write back), so splitting every statement boundary covers that
  ## shape without the author pointing at it — including when those two
  ## statements sit inside an `if`/`while`/`for`/`case`/`block`/`try`/
  ## `defer`/`when` body rather than directly in the proc's own
  ## top-level list (round 12 finding Q3: a race inside a loop body is
  ## arguably the *commoner* shape for a concurrent counter, and
  ## pre-recursion this hook missed it entirely, silently).
  ##
  ## Follows `instrumentNode` (coverage.nim)'s shape: dispatch on the
  ## node kinds that carry a nested statement-list body, rewrite each
  ## such body, and recurse. Two differences from `instrumentNode`, both
  ## deliberate:
  ## - `instrumentNode`'s fallback arm recurses into *every* child of
  ##   *every* node it doesn't special-case, because a coverage branch
  ##   can be nested arbitrarily deep inside an expression. A jitter
  ##   boundary, in contrast, only ever exists between two STATEMENTS in
  ##   a statement list — there is nowhere to put a void
  ##   `parallelJitterPoint()` call inside a genuine expression position
  ##   (`nnkIfExpr` branches, call arguments, ...) without either
  ##   producing an invalid AST or silently changing an expression's
  ##   value. So the fallback here does NOT recurse further — only the
  ##   explicitly listed statement-holding constructs (top-level list,
  ##   `if`/`elif`/`else`, `case`, `while`, `for`, `block`,
  ##   `try`/`except`/`finally`, `defer`, `when`/`elif`/`else`) are
  ##   walked.
  ##   NOTE (round 13 finding R13-6 corrected a prior version of this
  ##   comment): `nnkWhenStmt` used to be lumped in with `nnkIfExpr` here
  ##   as an "expression position with nowhere to put a call", which was
  ##   simply wrong — a `when` in STATEMENT position (the only position
  ##   this macro ever sees, since it rewrites a proc BODY) has ordinary
  ##   `nnkStmtList` branch bodies via `nnkElifBranch`/`nnkElse`,
  ##   structurally identical to `nnkIfStmt`'s. It gets its own arm
  ##   below, sharing that shape. `jitterPoints` is an `untyped` macro
  ##   running pre-semantic-analysis, so an untaken `when` branch (and
  ##   any jitter call inserted into it) is discarded before codegen —
  ##   the same reasoning `instrumentNode` already relies on in
  ##   production for its combined `nnkIfStmt, nnkIfExpr, nnkWhenStmt`
  ##   arm.
  ## - For the same "no callable is part of this proc's own control
  ##   flow" reason, this rewrite never descends into a nested
  ##   `proc`/`func`/`lambda`/`iterator`/`template`/`macro`/`converter`/
  ##   `method`/`do` block declared inside the annotated proc's body —
  ##   see `jitterNestedCallableKinds`.
  ##
  ## The never-insert-after-the-last-statement rule (see
  ## `instrumentStmtList`) is applied at EVERY statement list this
  ## recurses into, not just the proc's own top-level one — so it holds
  ## for a branch body sitting in implicit-return position too (Nim
  ## treats each branch of a top-level-position `if`/`case` as
  ## separately contributing an implicit result).
  ##
  ## **Self-reporting fallback (round 13 finding R13-2/R13-6).** Round 12
  ## added six arms; round 13's review found two more missing
  ## (`nnkDefer`, `nnkWhenStmt`) — both silent, because the zero-insertion
  ## guard on the macro only fires when the TOTAL count across the whole
  ## proc is zero, and any other statement boundary in the same proc
  ## keeps that count positive. An allow-list of "constructs we thought
  ## of" will always be one review round behind whatever construct
  ## nobody thought of yet. So the `else` arm below does not just fall
  ## through: if the node it was handed is itself a statement-holding
  ## construct (`hasStmtListChild`) and not a nested callable
  ## (`jitterNestedCallableKinds`, which legitimately have a body but
  ## aren't part of this proc's control flow), it emits a compile-time
  ## `warning` naming the node kind, the proc, and that a nested body was
  ## left uninstrumented. This is a `warning`, not the `{.error.}` the
  ## macro itself uses for zero total insertions (see `jitterPoints`):
  ## a proc that partially instruments — every OTHER statement boundary
  ## still gets a yield — is still useful, and hard-failing the build
  ## every time a SUT author reaches for some exotic statement kind this
  ## module hasn't special-cased yet would be worse than the gap it
  ## reports.
  case n.kind
  of nnkStmtList:
    result = instrumentStmtList(n, count, procName)
  of nnkIfStmt:
    result = n.copyNimNode
    for branch in n:
      case branch.kind
      of nnkElifBranch:
        result.add nnkElifBranch.newTree(
          branch[0], insertJitterBoundaries(branch[1], count, procName))
      of nnkElse:
        result.add nnkElse.newTree(
          insertJitterBoundaries(branch[0], count, procName))
      else:
        result.add branch  # unexpected; preserve verbatim
  of nnkWhenStmt:
    # Same shape as nnkIfStmt (see the doc comment above): branch[0] is
    # the (untouched) condition, branch[1]/branch[0] the StmtList body.
    result = n.copyNimNode
    for branch in n:
      case branch.kind
      of nnkElifBranch:
        result.add nnkElifBranch.newTree(
          branch[0], insertJitterBoundaries(branch[1], count, procName))
      of nnkElse:
        result.add nnkElse.newTree(
          insertJitterBoundaries(branch[0], count, procName))
      else:
        result.add branch  # unexpected; preserve verbatim
  of nnkCaseStmt:
    result = n.copyNimNode
    result.add n[0]  # selector
    for i in 1 ..< n.len:
      let branch = n[i]
      let newBranch = branch.copyNimNode
      for j in 0 ..< branch.len - 1:
        newBranch.add branch[j]
      newBranch.add insertJitterBoundaries(branch[^1], count, procName)
      result.add newBranch
  of nnkWhileStmt:
    result = nnkWhileStmt.newTree(
      n[0], insertJitterBoundaries(n[1], count, procName))
  of nnkForStmt:
    result = n.copyNimNode
    for i in 0 ..< n.len - 1:
      result.add n[i]  # loop var(s) + iterable, unchanged
    result.add insertJitterBoundaries(n[^1], count, procName)
  of nnkBlockStmt:
    result = n.copyNimNode
    for i in 0 ..< n.len - 1:
      result.add n[i]  # label (possibly empty), unchanged
    result.add insertJitterBoundaries(n[^1], count, procName)
  of nnkTryStmt:
    result = n.copyNimNode
    for child in n:
      case child.kind
      of nnkExceptBranch:
        let newBranch = child.copyNimNode
        for j in 0 ..< child.len - 1:
          newBranch.add child[j]
        newBranch.add insertJitterBoundaries(child[^1], count, procName)
        result.add newBranch
      of nnkFinally:
        result.add nnkFinally.newTree(
          insertJitterBoundaries(child[0], count, procName))
      else:
        # the try body itself
        result.add insertJitterBoundaries(child, count, procName)
  of nnkDefer:
    # `defer: stmt1; stmt2` parses as a single-child node whose child is
    # the StmtList making up the defer body (verified via `dumpTree`,
    # since this shape isn't spelled out in the manual). A
    # `parallelJitterPoint()` call inserted between two statements INSIDE
    # that body is a plain void call like any other statement — it does
    # not raise, allocate, or otherwise interact with unwinding, so it
    # cannot change what the surrounding `defer` guarantees. It is never
    # inserted after the body's last statement (instrumentStmtList's
    # invariant, same as everywhere else), so a `defer` body ending in an
    # expression used as its final statement is unaffected. Before this
    # arm existed, `nnkDefer` fell to the `else` branch below and was
    # skipped outright — R13-2: a read-modify-write race entirely inside
    # a `defer:` body got zero jitter points, silently, because the
    # proc's OTHER statements kept the total insertion count positive.
    result = nnkDefer.newTree(instrumentStmtList(n[0], count, procName))
  else:
    if n.kind notin jitterNestedCallableKinds and hasStmtListChild(n):
      warning(
        "{.jitterPoints.}: proc `" & procName & "` has a nested `" &
        $n.kind & "` construct that insertJitterBoundaries has no arm " &
        "for -- its statement-list body was left uninstrumented, so any " &
        "race living inside it will NOT be widened by this pragma. Add " &
        "an `of " & $n.kind & ":` arm to insertJitterBoundaries " &
        "(parallel.nim) that recurses into its body via " &
        "instrumentStmtList/insertJitterBoundaries, the same way the " &
        "existing arms do.",
        n)
    result = n

macro jitterPoints*(procDef: untyped): untyped =
  ## Pragma macro: rewrite the proc's body so a real scheduler-yield
  ## (`parallelJitterPoint`) runs between every pair of adjacent
  ## statements reachable through the proc's control flow — its own
  ## top-level list AND every `if`/`elif`/`else`, `when`/`elif`/`else`,
  ## `case`, `while`, `for`, `block`, `try`/`except`/`finally`, and
  ## `defer` body nested inside it, at any depth. Use as
  ## `proc f(c: ptr T): int {.gcsafe, jitterPoints.} = ...`.
  ##
  ## This is the RECOMMENDED way to widen an intra-op race window for
  ## `parallelCheck`. Unlike calling `parallelJitterPoint()` by hand, it
  ## asks the SUT author to locate nothing: annotate the proc once and
  ## every statement boundary its control flow can reach gets a chance
  ## to yield, including whichever boundary the actual race lives at —
  ## even one nested inside a loop, branch, or `defer` body. It also
  ## keeps the instrumentation OUT of the function body text, the same
  ## reason this codebase already reaches for a body-rewriting macro
  ## pragma rather than a hand-inserted call for "instrument this proc"
  ## — see `{.cover.}` / `{.covercmp.}` in coverage.nim, whose structure
  ## (`expectKind` the proc, rewrite `procDef[^1]`, return `procDef`)
  ## this macro follows directly; `insertJitterBoundaries`'s own doc
  ## comment lists where the recursion here deliberately parts ways with
  ## `instrumentNode`'s, and documents the self-reporting fallback that
  ## flags any FUTURE statement-holding construct nobody has added an
  ## arm for yet.
  ##
  ## **Never a silent no-op.** If the rewrite inserts zero jitter points
  ## anywhere in the proc — the body (and everything nested in it) has
  ## no statement boundary to widen at all, e.g. a single bare statement
  ## like `inc(c[].count)` — this is a COMPILE-TIME `{.error.}`, naming
  ## the proc, rather than compiling clean and doing nothing.
  ##
  ## This was a `warning` through round 12 (finding L12-2: before any
  ## check existed at all, `proc f(c: ptr Counter) {.gcsafe,
  ## jitterPoints.} = inc(c[].count)` — the single most natural way to
  ## write the exact race this pragma targets — compiled clean and
  ## instrumented nothing). Round 13 (finding R13-1) found the warning
  ## itself insufficient: `scripts/sweep.sh` runs every test through
  ## `dt-bounded.sh ... >/dev/null 2>&1`, so compiler stderr — where a
  ## `warning` lands — is discarded by the only harness that runs these
  ## tests on every sweep. A diagnostic the gate cannot see cannot carry
  ## a correctness guarantee. Annotating a proc `{.jitterPoints.}` that
  ## structurally cannot hold even one jitter point is also, unlike the
  ## partial-coverage case the fallback `warning` in
  ## `insertJitterBoundaries` reports, not a legitimate thing to leave in
  ## place: there is no valid reason to keep the pragma on a proc it can
  ## never do anything for, so failing the build is both actionable (the
  ## message says exactly what to do) and the one channel the gate
  ## cannot swallow. (The OTHER warning — the self-reporting fallback for
  ## a construct with no dispatch arm, see `insertJitterBoundaries` —
  ## deliberately stays a `warning`: a proc that instruments everywhere
  ## EXCEPT one exotic nested construct still yields real jitter points
  ## everywhere else, so erroring there could break a legitimate proc
  ## over a partial gap instead of just flagging it.)
  ##
  ## **Measured reliability**: applied to the same unsynchronized-increment
  ## race `parallelJitterPoint`'s own figure is based on (`racyIncPragma`,
  ## with no `sleep` and no hand-placed `parallelJitterPoint()` call
  ## anywhere in the SUT), this pragma caught the race in 20/20 idle runs
  ## and 10/10 CPU-contended runs -- see "lock-free wrong counter is
  ## detected via {.jitterPoints.} (no sleep, no hand-placed call)" in
  ## tests/tparallelcheck.nim. The SAME race relocated entirely inside a
  ## `for` loop body (`racyIncPragmaLoop`, proving the round-12 recursion
  ## fix actually reaches nested bodies, not just the top level) was
  ## caught in 20/20 idle runs and 20/20 CPU-contended runs (two
  ## independent contended sweeps, both 20/20) — see "lock-free wrong
  ## counter nested in a for loop is detected via {.jitterPoints.}" in the
  ## same file. The same race relocated inside a `defer:` body
  ## (`racyIncPragmaDefer`, round 13 finding R13-2) and inside a `when
  ## true:` body in statement position (`racyIncPragmaWhen`, round 13
  ## finding R13-6) were each measured in a smaller idle-only run — see
  ## those tests in tparallelcheck.nim for the exact counts. As with
  ## every catch-rate figure in this module, these are one-time
  ## measurements, not re-verified by every sweep; the single seeded run
  ## in each test is what runs on every sweep, and it guards the basic
  ## catch, not the ratio.
  expectKind procDef, {nnkProcDef, nnkFuncDef, nnkLambda}
  let nameNode = procDef[0]
  let procName = (if nameNode.kind == nnkPostfix: nameNode[^1] else: nameNode).repr
  var count = 0
  procDef[^1] = insertJitterBoundaries(procDef[^1], count, procName)
  if count == 0:
    error(
      "{.jitterPoints.}: proc `" & procName & "` would have zero jitter " &
      "points inserted -- its body (including everything nested in " &
      "if/when/case/while/for/block/try/defer bodies) has fewer than two " &
      "statements in every reachable statement list, so there is no " &
      "statement boundary anywhere for this pragma to widen. A compound " &
      "read-modify-write like `inc(x)` or `x += 1` must be split into a " &
      "separate read and write statement, or call parallelJitterPoint() " &
      "directly inside it, for the race window to be wideable by this " &
      "pragma at all. Annotating a proc `{.jitterPoints.}` that cannot " &
      "hold a single jitter point has no valid use case, so this is a " &
      "hard error rather than a warning (round 13 finding R13-1: a " &
      "warning is discarded by scripts/sweep.sh, which redirects " &
      "dt-bounded.sh's stderr to /dev/null, so it cannot carry a " &
      "correctness guarantee here).",
      procDef)
  result = procDef

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
  ## the window, annotate the op proc `{.jitterPoints.}` (see that
  ## pragma's doc comment). It rewrites the proc's body to yield between
  ## every statement boundary its control flow reaches — the proc's own
  ## top-level list AND every nested `if`/`case`/`while`/`for`/`block`/
  ## `try` body, at any depth — including whichever one the real
  ## read/write race sits at, without you having to locate the boundary
  ## yourself or add a call inside the function text. If NO boundary
  ## exists anywhere in the proc (e.g. its whole body is one bare
  ## statement like `inc(c[].count)`), the pragma warns at compile time
  ## rather than compiling clean and instrumenting nothing. This is a
  ## measured recommendation, not a hopeful one: see `{.jitterPoints.}`'s
  ## own doc comment for the catch-rate tests that back it.
  ##
  ## `parallelJitterPoint()` remains available as the low-level
  ## primitive `{.jitterPoints.}` is built on, for the narrower case
  ## where you already know the exact point and want exactly one yield
  ## there — see its own doc comment.

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
