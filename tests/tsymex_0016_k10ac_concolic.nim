## RFC-0016 K10a-concolic (section 9.1 item 1): the concolic flip solve carries
## the definedness disjunction. A flip's seed is run natively, so it must keep
## every operation of the target decision's condition and its prefix defined;
## an input that instead drives one undefined is reported on
## `ConcolicFlipResult.undefinedReached`, never used as a seed.
##
## Unsigned `div` by zero is undefined in every build profile
## (`defined:div/zeroDivisorUnsigned`), so this file pins the default build;
## `tsymex_0016_k10ac_concolic_checksoff` pins the signed overflow row.
import std/unittest
import nelli/symex
import nelli/int128
import nelli/smt/errorkind
import ./s8cu_helpers

const u32max = 4294967295'i64

proc divGate(a, b: uint32) =
  if a > 0'u32:
    if a div b > a:             # only an undefined division makes this true
      symexTarget("wrapped")

proc divWindow(a, b: uint32) =
  if a > 0'u32:
    if a div b > 2'u32:
      symexTarget("big")

let bs = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
           ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]

proc seed(a, b: int64): seq[ChoiceNode] =
  @[integerChoice(a, 0, u32max, 0), integerChoice(b, 0, u32max, 0)]

suite "K10a-concolic: the flip solve keeps the prefix defined":

  test "a flip only a zero divisor satisfies is not solved; the zero is a finding":
    let r = concolicFlip(divGate, seed(5, 2), bs, 1, pinSettingsConst)
    check r.outcome == cfoUnsat
    check r.materialized.len == 0
    check r.undefinedReached.len == 1
    if r.undefinedReached.len == 1:
      check r.undefinedReached[0].kind == ubUnsignedDivZero
      check r.undefinedReached[0].input[1].intVal == toInt128(0)
    check r.flipCounters.undefinedReached == 1

  test "a flip with a defined solution keeps the divisor nonzero":
    let r = concolicFlip(divWindow, seed(5, 5), bs, 1, pinSettingsConst)
    check r.outcome == cfoSolvedExact
    check r.materialized.len == 2
    if r.materialized.len == 2:
      check r.materialized[1].intVal != toInt128(0)
    # the zero is still reported: it is reachable on the same prefix
    check r.undefinedReached.len == 1

  test "a flip whose target condition has no undefined side reports nothing":
    let r = concolicFlip(divGate, seed(5, 2), bs, 0, pinSettingsConst)
    check r.undefinedReached.len == 0
