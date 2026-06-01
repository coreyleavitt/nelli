## Phase 5 — Table[K, V] via two Z3 arrays (data + presence map).
import std/unittest
import std/tables
import proptest/symex

proc adultByAge(t: Table[string, int]) =
  if t["age"] >= 18:
    symexTarget("adult")

suite "symex Phase 5 — Table read":
  test "read int value from a Table[string, int]":
    let r = symexFind(adultByAge, tLabel("adult"))
    check r.status == sxSat
    check r.witness[0]["age"] >= 18

  test "`in` membership test on Table":
    proc requireKey(t: Table[string, int]) =
      if "age" in t and t["age"] >= 21:
        symexTarget("legal")
    let r = symexFind(requireKey, tLabel("legal"))
    check r.status == sxSat
    check "age" in r.witness[0]
    check r.witness[0]["age"] >= 21
