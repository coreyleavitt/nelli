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

import std/[options]

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
  var witness: seq[LinEvent[OpId, Ret]]
  var found = false

  proc backtrack(state: State) =
    if found: return
    if witness.len == history.len:
      found = true
      return
    for i in 0 ..< history.len:
      if placed[i]: continue
      var eligible = true
      for p in precedes[i]:
        if not placed[p]:
          eligible = false
          break
      if not eligible: continue
      var newState = state
      let modelRet = applyModel(newState, history[i].opId)
      if not retEq(modelRet, history[i].observedRet): continue
      placed[i] = true
      witness.add history[i]
      backtrack(newState)
      if found: return
      placed[i] = false
      discard witness.pop()

  backtrack(initial)
  if found:
    result.linearisable = true
    result.witness = witness
  else:
    result.linearisable = false
    result.failureReason =
      "no sequential ordering consistent with the model — " &
      "SUT returned values no model trajectory produces"
