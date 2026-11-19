## Rectify #144 — Table.len / HashSet.len cardinality counters.
##
## Each `svTable` / `svSet` carries a `Z3Int` counter alongside the
## present/members array. The counter is `>= 0` initially; mutations
## (cycle #145) update both the data and the counter atomically.
import std/unittest
import std/tables
import std/sets
import nelli/symex
import ./s8cu_helpers

suite "symex cardinality #144":
  test "Table.len visible to the SUT":
    proc bigTable(t: Table[string, int]) =
      if t.len >= 3:
        symexTarget("big")
    let r = pinFind(bigTable, tLabel("big"))
    check r.status == sxSat

  test "HashSet.len visible to the SUT":
    proc bigSet(s: HashSet[int]) =
      if s.len >= 5:
        symexTarget("big")
    let r = pinFind(bigSet, tLabel("big"))
    check r.status == sxSat
