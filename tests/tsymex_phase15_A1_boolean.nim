## RFC-parser-normalization Cluster A, slice A1 — context 4: BOOLEAN
## compound operands under SHORT-CIRCUIT `and`/`or` (bool-typed).
##
## Same discipline as tsymex_phase15_A1_bitwise.nim (read that file's header
## for the twin-equality helper convention). This file is the D1c-invariance
## net referenced by the RFC (A2b depends on D1c's fast path continuing to
## fire identically post-restructure): it pins that a compound operand under
## `and`/`or` composes correctly with D1c's short-circuit modeling, and —
## per Mechanism constraint 1 — that hoisting NEVER crosses a short-circuit
## boundary. Twins here hoist ONLY the fault-free operand (typically the
## LHS); a defect-bearing RHS is never hoisted (that would deposit its fork
## unconditionally, exactly the violation constraint 1 forbids), so those
## cells stand alone with no twin.
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
# Cell 1 — atomic coverage (no twin): plain `and` on two atomic bools.
# ---------------------------------------------------------------------------
proc boolAtomicAnd(a, b: bool) =
  if a and b:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — compound (inline-arith) LHS under `and`, safe RHS with an inline
# defect fork left untouched. The twin hoists ONLY the LHS (`i + 0`, no
# fault potential) — the RHS index (`s[i]`) stays inline, guarded by the
# preceding `and`-chain conjuncts, per constraint 1.
# ---------------------------------------------------------------------------
proc boolAndLhsCompoundRhsFault(s: string, i: int) =
  if (i + 0) >= 0 and i < s.len and s[i] == 'x':
    symexTarget("hit")

proc boolAndLhsCompoundRhsFaultHoisted(s: string, i: int) =
  let ii = i + 0
  if ii >= 0 and i < s.len and s[i] == 'x':
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 3 — RHS defect fork, D1c fast-path baseline (no twin: hoisting the
# fault-bearing RHS is exactly what constraint 1 forbids). Pins that a
# guarded index read under `and` stays a real, reachable `sxSat` (D1c does
# not over-degrade a legitimately in-bounds continuation).
# ---------------------------------------------------------------------------
proc boolAndRhsFaultPin(a: array[5, int], i: int) =
  if i >= 0 and i < 5 and a[i] == 7:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 4 — `or` short-circuit with a fault-bearing final disjunct, guarded by
# the preceding out-of-range checks (the common bound-check idiom). Twin
# hoists the safe first disjunct (`i < 0`, no fault potential).
# ---------------------------------------------------------------------------
proc boolOrGuardThenFault(s: string, i: int) =
  if i < 0 or i >= s.len or s[i] != 'x':
    discard
  else:
    symexTarget("hit")

proc boolOrGuardThenFaultHoisted(s: string, i: int) =
  let neg = i < 0
  if neg or i >= s.len or s[i] != 'x':
    discard
  else:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 5 — nested boolean compound: LHS is itself a fault-free `and`-chain,
# nested inside an `or`. Hoisting a whole fault-free bool sub-expression is
# safe (no fork inside it).
# ---------------------------------------------------------------------------
proc boolNestedAndUnderOr(x, y, z: int) =
  if (x > 0 and y > 0) or z > 0:
    symexTarget("hit")

proc boolNestedAndUnderOrHoisted(x, y, z: int) =
  let both = (x > 0) and (y > 0)
  if both or z > 0:
    symexTarget("hit")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — boolean (short-circuit and/or) operand-shape characterization corpus":

  test "cell 1 (atomic AND, coverage): reachable, sxSat":
    let r = symexFind(boolAtomicAnd, tLabel("hit"))
    check r.status == sxSat

  test "cell 2 (compound LHS under AND, fault-bearing RHS untouched): twin-identical, sxSat":
    let rInline  = symexFind(boolAndLhsCompoundRhsFault, tLabel("hit"))
    let rHoisted = symexFind(boolAndLhsCompoundRhsFaultHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 3 (RHS defect fork, D1c fast-path baseline, no twin): sxSat, in-bounds witness":
    let r = symexFind(boolAndRhsFaultPin, tLabel("hit"))
    check r.status == sxSat

  test "cell 4 (OR guard-then-fault idiom): twin-identical, sxSat":
    let rInline  = symexFind(boolOrGuardThenFault, tLabel("hit"))
    let rHoisted = symexFind(boolOrGuardThenFaultHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 5 (nested AND-under-OR, fault-free): twin-identical, sxSat":
    let rInline  = symexFind(boolNestedAndUnderOr, tLabel("hit"))
    let rHoisted = symexFind(boolNestedAndUnderOrHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)
