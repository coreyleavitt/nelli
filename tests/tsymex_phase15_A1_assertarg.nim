## RFC-parser-normalization Cluster A, slice A1 — context 8: compound
## conditions as DIRECT `symexAssume`/`symexAssert` arguments.
##
## Same discipline as tsymex_phase15_A1_bitwise.nim (read that file's header
## for the twin-equality helper convention and the hoist-after-assume
## caution). Like call-argument position (context 7), a `symexAssume`/
## `symexAssert` argument slot is itself out of the binop-operand chokepoint
## scope — but the compound condition it carries still routes through
## whatever atomization its OWN inner infix arms use, so this file pins that
## composition directly at the entry-macro boundary rather than through an
## intermediate `if`.
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
# Cell 1 — atomic coverage (no twin): a direct atomic `symexAssert` argument.
# ---------------------------------------------------------------------------
proc assertArgAtomic(a: bool) =
  symexAssert(a or not a)

# ---------------------------------------------------------------------------
# Cell 2 — the RFC's named cell: `symexAssert((cap and (cap - 1)) == 0)` as a
# DIRECT macro argument, with the SAME compound condition also assumed
# (so no violation is reachable). depth: 0.
# ---------------------------------------------------------------------------
proc assertArgBitwiseDirect(cap: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0)
  symexAssert((cap and (cap - 1)) == 0)

proc assertArgBitwiseDirectHoisted(cap: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0)
  let capm1 = cap - 1
  symexAssert((cap and capm1) == 0)

# ---------------------------------------------------------------------------
# Cell 3 — boolean short-circuit WITH a fault, as a DIRECT `symexAssert`
# argument (no intermediate `if`): the classic bound-check-then-use idiom
# `i < 0 or i >= s.len or s[i] == s[i]` (the last disjunct is a trivial
# tautology once safely evaluated) is unconditionally true, and short-
# circuits BEFORE the fault-bearing disjunct whenever `i` is out of range.
# The twin hoists only the two fault-FREE disjuncts.
# ---------------------------------------------------------------------------
proc assertArgBoolFaultDirect(s: string, i: int) =
  symexAssert(i < 0 or i >= s.len or s[i] == s[i])

proc assertArgBoolFaultDirectHoisted(s: string, i: int) =
  let neg = i < 0
  let oob = i >= s.len
  symexAssert(neg or oob or s[i] == s[i])

# ---------------------------------------------------------------------------
# Cell 4 — compound arithmetic condition as a DIRECT `symexAssume` argument,
# followed by a reachability query.
# ---------------------------------------------------------------------------
proc assumeArgArithDirect(x, y: int) =
  symexAssume((x + y) > 0 and (x - y) < 100)
  if x > 0 or y > 0:
    symexTarget("hit")

proc assumeArgArithDirectHoisted(x, y: int) =
  let s = x + y
  let d = x - y
  symexAssume(s > 0 and d < 100)
  if x > 0 or y > 0:
    symexTarget("hit")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — assert/assume direct-argument-position operand-shape characterization corpus":

  test "cell 1 (atomic direct assert, coverage): sxUnsat, no violation":
    let r = symexFind(assertArgAtomic, tAssertionViolation())
    check r.status == sxUnsat

  test "cell 2 (#149-named: direct assert of pow2-mask condition): sxUnsat, twin-identical":
    let rInline  = symexFind(assertArgBitwiseDirect, tAssertionViolation())
    let rHoisted = symexFind(assertArgBitwiseDirectHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 3 (direct assert, boolean short-circuit with fault): sxUnsat, twin-identical":
    let rInline  = symexFind(assertArgBoolFaultDirect, tAssertionViolation())
    let rHoisted = symexFind(assertArgBoolFaultDirectHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 4 (direct assume, compound arithmetic condition): sxSat, twin-identical":
    let rInline  = symexFind(assumeArgArithDirect, tLabel("hit"))
    let rHoisted = symexFind(assumeArgArithDirectHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)
