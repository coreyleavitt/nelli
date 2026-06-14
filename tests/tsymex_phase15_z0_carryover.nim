import std/unittest
import std/[tables, sets]
import proptest
import proptest/[rng, datasource]

# Phase 15 — Z0 carryover close-out (reconciled; see
# docs/symex/RFC-phase15-reconciliation.md §C).
#   item 1: named-field tuple strategies via a keyword generalization of `map`
#   item 2: non-empty constraintDigest on floats/strings/lists/tables/sets
#   item 3: NO :unk skip-load guard (struck — :unk is the live suffix); doc only.

suite "symex Phase 15 — Z0 carryover":

  test "z0 item1: map(name = strat, ...) builds a NAMED-field tuple strategy":
    let s = map(x = integers(0, 9), y = strings(minLen = 0, maxLen = 4))
    var ds = newDataSource(initSplitMix64(1))
    let v = s.generate(ds)
    # field access by name proves it is a named tuple, not positional
    check v.x >= 0 and v.x <= 9
    check v.y.len >= 0
    check (v is tuple[x: int, y: string])

  test "z0 item1: positional map(sa, sb) still yields a positional tuple":
    let s = map(integers(0, 9), strings(maxLen = 4))
    var ds = newDataSource(initSplitMix64(2))
    let v = s.generate(ds)
    check v[0] >= 0 and v[0] <= 9
    check (v is (int, string))

  test "z0 item1: unary map(s, f) functor still works":
    let s = integers(0, 9).map(proc(x: int): int = x * 2)
    var ds = newDataSource(initSplitMix64(3))
    let v = s.generate(ds)
    check v mod 2 == 0

  test "z0 item2: five strategies have a non-empty constraintDigest":
    check floats(0.0, 1.0).constraintDigest != ""
    check strings(0, 10).constraintDigest != ""
    check lists(integers(0, 9), 0, 8).constraintDigest != ""
    check tables(integers(0, 9), integers(0, 9), 0, 8).constraintDigest != ""
    check sets(integers(0, 9), 0, 8).constraintDigest != ""

  test "z0 item2: distinct parameterizations -> distinct digests":
    check floats(0.0, 1.0).constraintDigest != floats(-1.0, 1.0).constraintDigest
    check strings(0, 10).constraintDigest != strings(0, 20).constraintDigest
    check lists(integers(0, 9), 0, 8).constraintDigest !=
          lists(integers(0, 9), 0, 16).constraintDigest
    check tables(integers(0, 9), integers(0, 9), 0, 8).constraintDigest !=
          tables(integers(0, 9), integers(0, 9), 0, 16).constraintDigest
    check sets(integers(0, 9), 0, 8).constraintDigest !=
          sets(integers(0, 9), 0, 16).constraintDigest

  test "z0 item2: container digest reflects element digest":
    # lists over differently-bounded elements must not collide
    check lists(integers(0, 9), 0, 8).constraintDigest !=
          lists(integers(0, 99), 0, 8).constraintDigest
