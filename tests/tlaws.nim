import std/[unittest, strutils]
import nelli

# Algebraic-laws library: pre-baked named properties for the common
# typeclasses. The user writes
#   for law in monoidLaws(s, op, id): test law.name: check law.check()
# and gets associativity + identity tests for free. Each law family
# emits one NamedProperty per *named law* so a failure points exactly
# at which law is broken — not "the monoid laws failed" but
# "associativity failed."

suite "eqLaws":
  test "produces the three eq laws (reflexivity, symmetry, transitivity)":
    let laws = eqLaws(integers(0, 100))
    check laws.len == 3
    var names: seq[string]
    for l in laws: names.add l.name
    check "reflexivity" in names
    check "symmetry" in names
    check "transitivity" in names

  test "all three eq laws pass for integers (default ==)":
    for law in eqLaws(integers(0, 100)):
      check law.check()

suite "semigroupLaws":
  test "associativity passes for (integers, +)":
    let s = integers(-1000, 1000)
    let add = proc(a, b: int): int = a + b
    let laws = semigroupLaws(s, add)
    check laws.len == 1
    check laws[0].name == "associativity"
    check laws[0].check()

  test "a non-associative op fails the law":
    # Subtraction: (a - b) - c != a - (b - c) in general.
    # The first failing example surfaces via the diagnostic.
    let s = integers(0, 100)
    let sub = proc(a, b: int): int = a - b
    let laws = semigroupLaws(s, sub)
    check not laws[0].check()
    check "ensure" in laws[0].diagnostic()

suite "monoidLaws":
  test "produces associativity + left/right identity":
    let laws = monoidLaws(integers(-100, 100),
                          proc(a, b: int): int = a + b,
                          0)
    check laws.len == 3
    var names: seq[string]
    for l in laws: names.add l.name
    check "associativity" in names
    check "left identity" in names
    check "right identity" in names

  test "all three monoid laws pass for (integers, +, 0)":
    for law in monoidLaws(integers(-100, 100),
                          proc(a, b: int): int = a + b, 0):
      check law.check()

  test "identity laws fail for the wrong unit":
    # Wrong unit: 1 is not a left/right identity for +.
    let laws = monoidLaws(integers(1, 100),
                          proc(a, b: int): int = a + b, 1)
    var fails = 0
    for law in laws:
      if not law.check(): inc fails
    check fails >= 1   # at least the identity laws fail

suite "ordLaws":
  test "produces eq laws plus ord-specific laws":
    let laws = ordLaws(integers(0, 100))
    var names: seq[string]
    for l in laws: names.add l.name
    # eq laws are inherited.
    check "reflexivity" in names
    check "symmetry" in names
    check "transitivity" in names
    # ord-specific laws.
    check "antisymmetry" in names
    check "totality" in names
    check "transitivity of <=" in names

  test "all ord laws pass for integers (default <=)":
    for law in ordLaws(integers(0, 100)):
      check law.check()
