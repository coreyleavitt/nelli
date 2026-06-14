import std/unittest
import std/macros
import proptest/symex

# Phase 15 — Cluster L cycle L3: getAst / quote do macros (verification).

# (a) quote-do macro emitting a `len` call, beside a hand-written twin.
macro withLenCheck(sutName: untyped): untyped =
  quote do:
    proc `sutName`(s: seq[int]) =
      if s.len > 3: symexTarget("long")
withLenCheck(quoteSut)

proc handWritten(s: seq[int]) =
  if s.len > 3: symexTarget("long")

# (b) quote-do macro emitting a call to a user-defined generic proc. The parser
# monomorphizes generics before walking, so the inlined `doubleOrd[int]` body
# (`v + v`) is symexed concretely.
proc doubleOrd[T: Ordinal](v: T): T = v + v
macro withDouble(sutName: untyped): untyped =
  quote do:
    proc `sutName`(n: int) =
      if doubleOrd(n) == 10: symexTarget("doubled")   # reachable at n == 5
withDouble(genericSut)

suite "symex Phase 15 — L3 getAst/quote do macros":

  test "quote-do `len` SUT is walker-identical to hand-written (both sxSat)":
    let rq = symexFind(quoteSut, tLabel("long"))
    let rh = symexFind(handWritten, tLabel("long"))
    check rq.status == sxSat
    check rh.status == sxSat
    check rq.status == rh.status

  test "quote-do macro emitting a generic call monomorphizes and symexes -> sxSat":
    # doubleOrd(n) == 10 is reachable at n == 5; monomorphization + inlining
    # of the quote-do-emitted generic call must find it.
    let r = symexFind(genericSut, tLabel("doubled"))
    check r.status == sxSat
