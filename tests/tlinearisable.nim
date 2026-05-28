import std/[unittest]
import proptest

# Linearisability checking: given a recorded concurrent history of
# operations (each with invoke/response timestamps + observed return
# value), does there exist a sequential ordering of those ops —
# respecting real-time happens-before — that's consistent with a
# sequential model? If yes → safe (per Wing-Gong definition). If no →
# race condition.
#
# This is the algorithmic heart. The parallel runner (separate suite
# below) generates plans, runs them on threads, and feeds histories
# into this checker.

type
  CounterState = object
    count: int

const opInc = 0
const opGet = 1

proc applyCounter(s: var CounterState, opId: int): int =
  case opId
  of opInc: inc s.count; s.count
  of opGet: s.count
  else: 0

proc intEq(a, b: int): bool = a == b

suite "isLinearisable: trivial cases":
  test "empty history is linearisable":
    let r = isLinearisable(
      newSeq[LinEvent[int, int]](),
      CounterState(),
      applyCounter,
      intEq)
    check r.linearisable

  test "sequential history that matches the model is linearisable":
    # All ops on thread 0, total order, return values match the counter.
    # inc → 1, inc → 2, get → 2.
    let history = @[
      LinEvent[int, int](threadId: 0, invokeTime: 0, responseTime: 1,
                        opId: opInc, observedRet: 1),
      LinEvent[int, int](threadId: 0, invokeTime: 1, responseTime: 2,
                        opId: opInc, observedRet: 2),
      LinEvent[int, int](threadId: 0, invokeTime: 2, responseTime: 3,
                        opId: opGet, observedRet: 2),
    ]
    let r = isLinearisable(history, CounterState(), applyCounter, intEq)
    check r.linearisable
    check r.witness.len == 3

  test "sequential history with a wrong return value is NOT linearisable":
    # inc → claimed 5 (should be 1) → no model trajectory matches.
    let history = @[
      LinEvent[int, int](threadId: 0, invokeTime: 0, responseTime: 1,
                        opId: opInc, observedRet: 5),
    ]
    let r = isLinearisable(history, CounterState(), applyCounter, intEq)
    check not r.linearisable
    check r.failureReason.len > 0

suite "isLinearisable: concurrent histories":
  test "concurrent inc + get with consistent return values is linearisable":
    # T0.inc and T1.get overlap in time. T0.inc returned 1, T1.get
    # returned 0. The ordering [get, inc] explains: get observed 0
    # (initial state), then inc went 0→1 and returned 1. Real-time
    # is respected because the intervals overlap (no happens-before
    # forces inc < get).
    let history = @[
      LinEvent[int, int](threadId: 0, invokeTime: 1, responseTime: 4,
                        opId: opInc, observedRet: 1),
      LinEvent[int, int](threadId: 1, invokeTime: 2, responseTime: 3,
                        opId: opGet, observedRet: 0),
    ]
    let r = isLinearisable(history, CounterState(), applyCounter, intEq)
    check r.linearisable
    check r.witness.len == 2
    # The valid witness puts get first (it returned 0).
    check r.witness[0].opId == opGet

  test "real-time precedence is enforced — non-overlapping ops keep order":
    # T0.inc fully precedes T1.get (T0 responds at time 2; T1 invokes
    # at time 3 — strict happens-before). So the order MUST be
    # [inc, get]. If get observed 0 (impossible after inc), no
    # ordering exists.
    let history = @[
      LinEvent[int, int](threadId: 0, invokeTime: 0, responseTime: 2,
                        opId: opInc, observedRet: 1),
      LinEvent[int, int](threadId: 1, invokeTime: 3, responseTime: 4,
                        opId: opGet, observedRet: 0),  # impossible
    ]
    let r = isLinearisable(history, CounterState(), applyCounter, intEq)
    check not r.linearisable

  test "a lost-update race is detected":
    # Classic non-atomic increment bug: two concurrent inc's both saw
    # `count = 1` (each read 0, wrote 1) and a subsequent get returned
    # 1 (only one effective increment). No sequential ordering of
    # `inc; inc; get` produces (1, 1, 1) — under sequential semantics
    # the two incs must produce (1, 2) or (2, 1), and a subsequent
    # get must return 2. The witness is impossible → rejected.
    let history = @[
      LinEvent[int, int](threadId: 0, invokeTime: 1, responseTime: 3,
                        opId: opInc, observedRet: 1),
      LinEvent[int, int](threadId: 1, invokeTime: 2, responseTime: 4,
                        opId: opInc, observedRet: 1),
      LinEvent[int, int](threadId: 0, invokeTime: 5, responseTime: 6,
                        opId: opGet, observedRet: 1),
    ]
    let r = isLinearisable(history, CounterState(), applyCounter, intEq)
    check not r.linearisable
    check r.failureReason.len > 0
