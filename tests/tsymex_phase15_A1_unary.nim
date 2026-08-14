## RFC-parser-normalization Cluster A, slice A1 — context 6: UNARY compound
## operands (prefix `not`, unary `-`).
##
## Same discipline as tsymex_phase15_A1_bitwise.nim (read that file's header
## for the twin-equality helper convention and the hoist-after-assume
## caution). Mechanism census (RFC "Mechanism" block): round 1 MISSED both
## `nnkPrefix` arms — `not` -> `mkUnop(uNot, parseExpr(...))` and unary minus
## -> `mkUnop(uNeg, ...)` — and `uNot` "matters doubly": prefix `not` carries
## the SAME boolean/bitwise overload as `and`/`or` (the v64-hardened D1c
## walker arm), so constraint 1 (never atomize across a short-circuit
## boundary) applies to a `uNot` operand that is itself such an infix, too.
## This file includes the RFC's own named cell
## (`not ((cap and (cap - 1)) == 0)`) and a `not`-over-fault-bearing-boolean
## pin (no eager evaluation of the RHS fork).
import std/[unittest]
import nelli/symex

proc checkTwins[T](rInline, rHoisted: SymexResult[T]) =
  check rInline.status == rHoisted.status
  if rInline.status == sxSat and rHoisted.status == sxSat:
    check rInline.witness == rHoisted.witness
  if rInline.status == sxRaised and rHoisted.status == sxRaised:
    check rInline.raisedTypeId == rHoisted.raisedTypeId
    check rInline.raisedWitness == rHoisted.raisedWitness

# ---------------------------------------------------------------------------
# Cell 1 — atomic coverage (no twin): plain `not` on an atomic bool.
# ---------------------------------------------------------------------------
proc unaryAtomicNot(a: bool) =
  if not a:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — the RFC's named cell: `not ((cap and (cap - 1)) == 0)`, i.e. "cap
# is NOT a power of two". Reachable (e.g. cap == 3).
# ---------------------------------------------------------------------------
proc unaryNotBitwise(cap: int) =
  symexAssume(cap > 0)
  if not ((cap and (cap - 1)) == 0):
    symexTarget("notPow2")

proc unaryNotBitwiseHoisted(cap: int) =
  symexAssume(cap > 0)
  let capm1 = cap - 1
  if not ((cap and capm1) == 0):
    symexTarget("notPow2")

# ---------------------------------------------------------------------------
# Cell 3 — unary minus over inline-arith: `-(x - y)`, reachable when x > y.
# ---------------------------------------------------------------------------
proc unaryNegInline(x, y: int) =
  symexAssume(x > y and x < 1_000 and y > -1_000)
  if -(x - y) < 0:
    symexTarget("hit")

proc unaryNegInlineHoisted(x, y: int) =
  symexAssume(x > y and x < 1_000 and y > -1_000)
  let diff = x - y
  if -diff < 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 4 — unary minus over a call-result operand.
# ---------------------------------------------------------------------------
func absDiff(a, b: int): int {.inline.} =
  a - b

proc unaryNegCallResult(a, b: int) =
  symexAssume(a > b and a < 1_000 and b > -1_000)
  if -absDiff(a, b) < 0:
    symexTarget("hit")

proc unaryNegCallResultHoisted(a, b: int) =
  symexAssume(a > b and a < 1_000 and b > -1_000)
  let d = absDiff(a, b)
  if -d < 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 5 — `not` over a short-circuit boolean with an inline defect fork (no
# twin: this cell itself IS the pin). Round-2 extension of constraint 1:
# "eagerly hoisting `a and b` under `not` deposits the RHS fork
# unconditionally — the same violation" as hoisting a bare `and`/`or`.
# `i < 0` makes the whole `and` false WITHOUT ever evaluating `s[i]` in real
# Nim — this pins that the walker does not eagerly force that evaluation.
# ---------------------------------------------------------------------------
proc unaryNotShortCircuitFault(s: string, i: int) =
  symexAssume(i < 0)               ## forces the ONLY reachable path through
                                    ## the short-circuit, never through `s[i]`
  if not (i >= 0 and i < s.len and s[i] == 'x'):
    symexTarget("miss")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — unary (not / unary minus) operand-shape characterization corpus":

  test "cell 1 (atomic NOT, coverage): reachable, sxSat":
    let r = symexFind(unaryAtomicNot, tLabel("hit"))
    check r.status == sxSat

  test "cell 2 (#149-named: not pow2-mask, inline-arith): twin-identical, sxSat":
    let rInline  = symexFind(unaryNotBitwise, tLabel("notPow2"))
    let rHoisted = symexFind(unaryNotBitwiseHoisted, tLabel("notPow2"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 3 (unary minus, inline-arith): twin-identical, sxSat":
    let rInline  = symexFind(unaryNegInline, tLabel("hit"))
    let rHoisted = symexFind(unaryNegInlineHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 4 (unary minus, call-result operand): twin-identical, sxSat":
    let rInline  = symexFind(unaryNegCallResult, tLabel("hit"))
    let rHoisted = symexFind(unaryNegCallResultHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 5 (not over short-circuit fault, no twin): sxSat, no eager evaluation":
    let r = symexFind(unaryNotShortCircuitFault, tLabel("miss"))
    check r.status == sxSat
    check r.witness[1] < 0                    ## i < 0: real Nim never evaluates s[i]
