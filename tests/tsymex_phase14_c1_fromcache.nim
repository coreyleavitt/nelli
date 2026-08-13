## Phase 14 cycle C1 — `SymexResult.fromCache` flag.
##
## RFC §C1 introduces `fromCache: bool` on `SymexResult[T]` so
## consumers can distinguish a cold `runSymex` result from a
## cache-served one. The full cache cascade for `symexFind`
## (witness/verdict cache → cold) is reserved for a follow-up
## cycle that extends the macro's signature with an
## `ExampleDatabase` argument; this RED test pins the field's
## existence + cold-run default (`false`) so the type shape is
## stable for L1/L2 consumers that already do the cascade.
import std/unittest
import nelli/symex

proc trivial(x: int) =
  if x == 7: symexTarget("seven")

suite "symex Phase 14 cycle C1 — SymexResult.fromCache":
  test "cold symexFind result has fromCache = false":
    let r = symexFind(trivial, tLabel("seven"))
    check r.status == sxSat
    check r.fromCache == false

  test "cold UNSAT result has fromCache = false":
    let r = symexFind(trivial, tLabel("not-a-marker"))
    # `tLabel("not-a-marker")` isn't in the SUT body; the parser
    # zero-targets fallback short-circuits to sxUnknown. Either way,
    # the cold run sets fromCache = false.
    check r.fromCache == false
