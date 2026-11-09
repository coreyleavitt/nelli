## RFC-0016 K10a-concolic, the checks-off half (`--overflowChecks:off`, see
## the `.nim.cfg`): a signed 32 bit `+` that overflows is undefined behaviour
## in C, so a flip must not hand it to the native run as a seed.
import std/unittest
import nelli/symex
import nelli/int128
import nelli/smt/errorkind
import ./s8cu_helpers

const lo32 = -2147483648'i64
const hi32 = 2147483647'i64

proc addGate(a, b: int32) =
  if a > 0'i32:
    if b > 0'i32:
      if a + b < 0'i32:         # only the overflow makes this true
        symexTarget("wrapped")

proc addPrefix(a, b: int32) =
  let s = a + b                 # on the prefix of the flipped decision
  if a > 0'i32:
    if b > 0'i32:
      if s < 0'i32:
        symexTarget("wrapped")

let bs = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
           ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]

proc seed(a, b: int64): seq[ChoiceNode] =
  @[integerChoice(a, lo32, hi32, 0), integerChoice(b, lo32, hi32, 0)]

proc overflows(s: seq[ChoiceNode]): bool =
  let a = toInt64(s[0].intVal)
  let b = toInt64(s[1].intVal)
  a + b > hi32 or a + b < lo32

suite "K10a-concolic, checks off: a seed never overflows":

  test "the overflow in the target's own condition is a finding, not a seed":
    let r = concolicFlip(addGate, seed(1, 1), bs, 2, pinSettingsConst)
    check r.outcome != cfoSolvedExact
    if r.materialized.len == 2:
      check not overflows(r.materialized)   # a relaxed seed is still defined
    check r.undefinedReached.len == 1
    if r.undefinedReached.len == 1:
      check r.undefinedReached[0].kind == ubSignedOverflow
      check overflows(r.undefinedReached[0].input)

  test "a relaxed attempt does not drop the prefix operation's definedness":
    let r = concolicFlip(addPrefix, seed(1, 1), bs, 2, pinSettingsConst)
    if r.materialized.len == 2:
      check not overflows(r.materialized)
