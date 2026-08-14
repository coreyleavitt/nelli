## RFC-parser-normalization Cluster A, slice A1 — context 7: compound
## expressions in CALL-ARGUMENT position.
##
## The RFC is explicit that call-argument position is OUT of chokepoint
## scope: "an argument is not a binop operand; inner infix arms still route
## through it" — `parseAtomicOperand` atomizes operands of `mkBinop`/
## `mkUnop`/`mkStrOp`/`mkBorrowOp`, not the generic argument list of an
## ordinary call. This file's rows pin that the boundary guarantee still
## COMPOSES into call-argument position (a compound argument's own inner
## infix gets atomized on ITS way to being an operand of ITS OWN op — it is
## the outer call-argument slot itself that stays untouched), so the
## absence from the Mechanism block is a documented decision, not an
## oversight. Same twin-equality helper convention as
## tsymex_phase15_A1_bitwise.nim.
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
# Cell 1 — atomic coverage (no twin): a plain atomic argument.
# ---------------------------------------------------------------------------
func idInt(x: int): int {.inline.} =
  x

proc callArgAtomic(a: int) =
  if idInt(a) == 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — `f(a and b)`, bitwise compound argument, depth 1.
# ---------------------------------------------------------------------------
proc callArgBitwiseD1(a, b: int) =
  if idInt(a and b) == 0:
    symexTarget("hit")

proc callArgBitwiseD1Hoisted(a, b: int) =
  let ab = a and b
  if idInt(ab) == 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 3 — SAME shape, depth 2 (the callee itself calls another callee).
# ---------------------------------------------------------------------------
func idInt2(x: int): int {.inline.} =
  idInt(x)

proc callArgBitwiseD2(a, b: int) =
  if idInt2(a and b) == 0:
    symexTarget("hit")

proc callArgBitwiseD2Hoisted(a, b: int) =
  let ab = a and b
  if idInt2(ab) == 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 4 — `f(x > 0 and y < 10)`, boolean (fault-free short-circuit)
# compound argument.
# ---------------------------------------------------------------------------
func idBool(x: bool): bool {.inline.} =
  x

proc callArgBoolean(x, y: int) =
  if idBool(x > 0 and y < 10):
    symexTarget("hit")

proc callArgBooleanHoisted(x, y: int) =
  let cond = x > 0 and y < 10
  if idBool(cond):
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 5 — `f(s[i])`, a DEFECT-BEARING argument, unguarded. Baseline
# recorded: `i` is unconstrained, so a real in-bounds witness for "hit" IS
# reachable (unlike the arithmetic file's div-by-zero cell, where the assert
# itself is the ONLY target and every path passes through the fault) — the
# search finds that genuine `sxSat` witness rather than reporting the
# incidentally-reachable `IndexDefect` for an out-of-bounds `i`. Constraint 2
# (defect-fork ordering preserved) still applies to whichever witness the
# hoisted twin finds: it must match the inline form exactly.
# ---------------------------------------------------------------------------
func idChar(c: char): char {.inline.} =
  c

proc callArgDefectUnguarded(s: string, i: int) =
  if idChar(s[i]) == 'x':
    symexTarget("hit")

proc callArgDefectUnguardedHoisted(s: string, i: int) =
  let c = s[i]
  if idChar(c) == 'x':
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 6 — SAME shape, GUARDED (bound-checked before the call). The twin
# hoists the argument value INSIDE the already-safe guard branch, preserving
# the guard-before-fault ordering (constraint 2/3) rather than hoisting
# across it.
# ---------------------------------------------------------------------------
proc callArgDefectGuarded(s: string, i: int) =
  if i >= 0 and i < s.len and idChar(s[i]) == 'x':
    symexTarget("hit")

proc callArgDefectGuardedHoisted(s: string, i: int) =
  if i >= 0 and i < s.len:
    let c = s[i]
    if idChar(c) == 'x':
      symexTarget("hit")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — call-argument-position operand-shape characterization corpus":

  test "cell 1 (atomic arg, coverage): reachable, sxSat":
    let r = symexFind(callArgAtomic, tLabel("hit"))
    check r.status == sxSat

  test "cell 2 (bitwise compound arg, depth 1): twin-identical, sxSat":
    let rInline  = symexFind(callArgBitwiseD1, tLabel("hit"))
    let rHoisted = symexFind(callArgBitwiseD1Hoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 3 (bitwise compound arg, depth 2): twin-identical, sxSat":
    let rInline  = symexFind(callArgBitwiseD2, tLabel("hit"))
    let rHoisted = symexFind(callArgBitwiseD2Hoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 4 (boolean compound arg): twin-identical, sxSat":
    let rInline  = symexFind(callArgBoolean, tLabel("hit"))
    let rHoisted = symexFind(callArgBooleanHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell 5 (defect-bearing arg, unguarded): twin-identical, sxSat via a real in-bounds witness":
    let rInline  = symexFind(callArgDefectUnguarded, tLabel("hit"))
    let rHoisted = symexFind(callArgDefectUnguardedHoisted, tLabel("hit"))
    check rInline.status == sxSat
    check rInline.witness[1] >= 0 and rInline.witness[1] < rInline.witness[0].len
    checkTwins(rInline, rHoisted)

  test "cell 6 (defect-bearing arg, guarded): twin-identical, sxSat":
    let rInline  = symexFind(callArgDefectGuarded, tLabel("hit"))
    let rHoisted = symexFind(callArgDefectGuardedHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)
