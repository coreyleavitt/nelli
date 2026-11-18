## Phase 5 — HashSet[T] via `Z3Array[T, Z3Bool]`.
import std/unittest
import std/sets
import nelli/symex
import ./s8cu_helpers

proc setHas42(s: HashSet[int]) =
  if 42 in s:
    symexTarget("has42")

suite "symex Phase 5 — HashSet":
  test "`in` membership test on HashSet":
    let r = pinFind(setHas42, tLabel("has42"))
    check r.status == sxSat
    check 42 in r.witness[0]
