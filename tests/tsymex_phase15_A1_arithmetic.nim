## RFC-parser-normalization Cluster A, slice A1 — context 3: ARITHMETIC
## compound operands (`+`, `-`, `*`, `div`, `mod`) feeding an assertion.
##
## Same discipline as tsymex_phase15_A1_bitwise.nim (read that file's header
## for the twin-equality helper convention and the hoist-after-assume
## caution). This file covers: the truncating-division identity as an
## inline-arith compound operand, the guarded-vs-unguarded `div` DEFECT-FORK
## pin (a deliberate NON-twin pair — the two procs differ in whether
## `symexAssume(y != 0)` guards the division, so they are expected to
## produce DIFFERENT verdicts; that divergence IS the pin), a call-result
## operand at depth 1, and the `{.borrow.}` bypass-site class (RFC Mechanism:
## "the `{.borrow.}` intercept ~1192 — a compound operand of a borrowed op is
## exactly the #149 shape class") with a NESTED borrowed-`+` operand.
##
## Domains are bounded via `symexAssume` wherever the natural (unbounded int)
## shape would make `OverflowDefect` reachable and dominate the verdict
## (Phase 15 E6: a reachable Defect raise always dominates the search target)
## — that would test overflow-fork behavior instead of the intended
## compound-operand shape. Bounded ranges are chosen comfortably clear of
## `int` overflow.
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
# Cell 1 — atomic coverage (no twin): plain `+` on two atomic int operands.
# ---------------------------------------------------------------------------
proc arithAtomicAdd(a, b: int) =
  if a + b == 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — inline-arith: the truncating-division identity
# `x == (x div y) * y + (x mod y)`, true for all `y != 0` in real Nim
# (T-division). Domain restricted to NON-NEGATIVE `x` — this is deliberate,
# not merely an overflow guard.
#
# INVESTIGATION NOTE (out of A1/Cluster-A scope, recorded here so it is not
# silently lost): the identity ALSO fails to hold for NEGATIVE `x` at HEAD,
# but not because of operand-shape/hoisting sensitivity — with x, y BOTH
# concretely fixed (no search, no twin involved) the engine already computes
# `x div y` via truncating semantics (matches Nim: e.g. `-64 div 519 == 0`)
# while `x mod y` is computed via Z3's native EUCLIDEAN `Z3_mk_mod`
# (`-64 mod 519 == 455` in-engine, vs Nim's real `-64 mod 519 == -64`) — a
# pre-existing `bMod` modeling gap for negative dividends, independent of
# this RFC's ANF chokepoint. Confirmed via `scratchpad` probes (not
# committed): `x div y` alone resolves correctly (truncating); `x mod y`
# alone resolves to the Euclidean value, not Nim's. This produces a
# `sxRaised(AssertionDefect)` false positive whose reported counterexample
# additionally differs between the inline and hoisted phrasing (both
# individually unsound, Z3 non-determinism over an equisatisfiable-but-
# differently-shaped false query picks different concrete models) — flagged
# for separate follow-up, not folded into this corpus's baseline.
# ---------------------------------------------------------------------------
proc arithDivModIdentity(x, y: int) =
  symexAssume(y > 0 and y < 1_000 and x >= 0 and x < 1_000)
  symexAssert(x == (x div y) * y + (x mod y))

proc arithDivModIdentityHoisted(x, y: int) =
  symexAssume(y > 0 and y < 1_000 and x >= 0 and x < 1_000)
  let rhs = (x div y) * y + (x mod y)
  symexAssert(x == rhs)

# ---------------------------------------------------------------------------
# Cell 3 — DEFECT-FORK PIN (deliberate non-twin pair): `x div y` as a
# compound operand, guarded by `symexAssume(y != 0)` vs unguarded. Ground
# truth item 5: inline defect forks already deposit into `preamble` during
# `parseExpr`, so the unguarded form's div-by-zero fork is expected to
# DOMINATE the verdict (Phase 15 E6) — this pins TODAY's fork-ordering
# behavior, not a hoist-equivalence claim.
# ---------------------------------------------------------------------------
proc arithDivGuarded(x, y: int) =
  symexAssume(y != 0 and x > -1_000 and x < 1_000)
  symexAssert((x div y) + 1 > (x div y))

proc arithDivUnguarded(x, y: int) =
  symexAssume(x > -1_000 and x < 1_000)          ## deliberately NO y != 0 guard
  symexAssert((x div y) + 1 > (x div y))

# ---------------------------------------------------------------------------
# Cell 4 — call-result operand, depth 1: `tripleIt(n) >= n` for bounded
# non-negative `n`.
# ---------------------------------------------------------------------------
func tripleIt(n: int): int {.inline.} =
  n * 3

proc arithCallResultD1(n: int) =
  symexAssume(n >= 0 and n < 1_000)
  symexAssert(tripleIt(n) >= n)

proc arithCallResultD1Hoisted(n: int) =
  symexAssume(n >= 0 and n < 1_000)
  let t = tripleIt(n)
  symexAssert(t >= n)

# ---------------------------------------------------------------------------
# Cell 5 — borrow-op bypass site: a NESTED borrowed `+` operand
# (`(m1 + m1) + m2`) on a `distinct int` — the `{.borrow.}` intercept
# constructs `mkBorrowOp` directly from `parseExpr` results, bypassing the
# general infix arm entirely (RFC Mechanism census).
# ---------------------------------------------------------------------------
type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}    ## needed for tuple-witness equality in checkTwins

proc borrowNestedArith(m1, m2: Meters) =
  if (m1 + m1) + m2 < Meters(1_000_000_000):
    symexTarget("hit")

proc borrowNestedArithHoisted(m1, m2: Meters) =
  let m1x2 = m1 + m1
  if m1x2 + m2 < Meters(1_000_000_000):
    symexTarget("hit")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — arithmetic operand-shape characterization corpus":

  test "cell 1 (atomic +, coverage): reachable, sxSat":
    let r = symexFind(arithAtomicAdd, tLabel("hit"))
    check r.status == sxSat

  test "cell 2 (div/mod identity, inline-arith): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(arithDivModIdentity, tAssertionViolation())
    let rHoisted = symexFind(arithDivModIdentityHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 3a (div, guarded y != 0): sxUnsat — no violation reachable":
    let r = symexFind(arithDivGuarded, tAssertionViolation())
    check r.status == sxUnsat

  test "cell 3b (div, UNGUARDED): sxRaised(DivByZeroDefect) dominates (fork-ordering pin)":
    let r = symexFind(arithDivUnguarded, tAssertionViolation())
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

  test "cell 4 (call-result operand, depth 1): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(arithCallResultD1, tAssertionViolation())
    let rHoisted = symexFind(arithCallResultD1Hoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 5 (borrow-op bypass site, nested borrowed +): twin-identical baseline":
    let rInline  = symexFind(borrowNestedArith, tLabel("hit"))
    let rHoisted = symexFind(borrowNestedArithHoisted, tLabel("hit"))
    checkTwins(rInline, rHoisted)
    check rInline.status in {sxSat, sxUnsat, sxRaised, sxUnknown}
    if rInline.status == sxUnknown:
      check rInline.errors.len > 0
