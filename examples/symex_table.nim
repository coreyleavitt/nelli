## examples/symex_table.nim
##
## Symex over `Table[string, int]` — Phase 5's dynamic-container
## fragment. The walker models the table as a Z3 array (uninterpreted
## function `key → value`) plus a parallel `present` array tracking
## which keys are mapped. Reads compile to `select`; `contains`
## compiles to `present[key]`.
##
## The interesting bit: symex finds *what the table contains* to
## satisfy a path condition. You don't supply test fixtures — Z3
## constructs the table.

import std/[strformat, tables]
import proptest/symex

proc score(t: Table[string, int]) =
  # The walker needs to find a `t` such that `t.hasKey("alice")`
  # AND `t["alice"] > 100`. Both are constraints on the table's
  # symbolic representation; Z3 solves them jointly.
  if t.hasKey("alice") and t["alice"] > 100:
    symexTarget("hi-alice")

let r = symexFind(score, tLabel("hi-alice"))
doAssert r.status == sxSat, "expected SAT"

let t = r.witness[0]
echo &"symex constructed table: {t}"
doAssert t.hasKey("alice"), "witness must contain key alice"
doAssert t["alice"] > 100, "alice's value must exceed 100"

# Round-trip verification.
assertCoveredBy(score, tLabel("hi-alice"))
echo "assertCoveredBy: the constructed table reaches the target — good."
