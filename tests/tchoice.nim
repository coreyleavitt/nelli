import std/unittest
import proptest

suite "ChoiceNode: integer":
  test "constructing an integer choice exposes its kind, value, and constraints":
    let n = integerChoice(value = 42, min = 0, max = 100, shrinkTowards = 0)
    check n.kind == ckInteger
    check n.intVal == toInt128(42)
    check n.intC.min == toInt128(0)
    check n.intC.max == toInt128(100)
    check n.intC.shrinkTowards == toInt128(0)
    check not n.wasForced

suite "IntConstraints: permits":
  test "permits values within [min,max] and rejects those outside":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100),
                           shrinkTowards: toInt128(0))
    check c.permits(toInt128(0))     # lower bound inclusive
    check c.permits(toInt128(100))   # upper bound inclusive
    check c.permits(toInt128(42))
    check not c.permits(toInt128(-1))
    check not c.permits(toInt128(101))

  test "constructor clamps shrinkTowards into [min,max]":
    check integerChoice(value = 5, min = 0, max = 10,
                        shrinkTowards = -100).intC.shrinkTowards == toInt128(0)
    check integerChoice(value = 5, min = 0, max = 10,
                        shrinkTowards = 100).intC.shrinkTowards == toInt128(10)
    check integerChoice(value = 5, min = 0, max = 10,
                        shrinkTowards = 3).intC.shrinkTowards == toInt128(3)

suite "ChoiceInt: full integer-type coverage":
  test "represents and orders the full uint64 range int64 cannot hold":
    let maxU = toInt128(high(uint64))
    let aboveI64 = toInt128(uint64(high(int64)) + 1'u64)  # 2^63, beyond int64
    check toInt128(high(int64)) < aboveI64                # ordering across boundary
    check aboveI64 < maxU
    let c = IntConstraints(min: toInt128(0'u64), max: maxU,
                           shrinkTowards: toInt128(0))
    check c.permits(maxU)
    check c.permits(aboveI64)
    check not c.permits(toInt128(-1))
