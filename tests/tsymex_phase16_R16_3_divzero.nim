import std/unittest
import nelli/symex

# Phase 16 R16-3 — div/mod-by-zero DivByZeroDefect raise fork.
#
# The engine now forks a `DivByZeroDefect` raise-path when `a div b` or
# `a mod b` is applied to a divisor `b` that may be zero. This mirrors the
# R16-2 float→int RangeDefect mechanism but for integer division, using a
# parallel sink `divByZeroConds` drained by `drainDivByZeroRaises`.
#
# Design: divisor==0 predicate is captured in `lowerArith` for bDiv/bMod ops
# (both svInt and BV paths) and pushed to the `divByZeroConds` sink.
# `drainDivByZeroRaises` (called via `drainScalarRaiseForks`) forks each
# predicate as a DivByZeroDefect raise and returns the surviving non-zero
# continuation. A short-circuit guard in dsl_parser prevents false positives
# when div appears in an `and`/`or` RHS guarded by `b != 0`.
#
# RED state for each test: before R16-3, tRaisedExn("DivByZeroDefect") yields
# sxUnsat because no raise fork is opened.

# ---------------------------------------------------------------------------
# Behavior 1: div — unconstrained divisor → sxRaised(DivByZeroDefect)
# ---------------------------------------------------------------------------

proc sd(a, b: int) =
  ## Unconstrained `b` — b==0 is satisfiable → DivByZeroDefect raise fork.
  let q = a div b
  symexTarget("td")
  discard q

suite "symex Phase 16 R16-3 — div DivByZeroDefect raise fork":

  test "R16-3-1: unconstrained a div b → sxRaised(DivByZeroDefect)":
    ## Before R16-3: tRaisedExn("DivByZeroDefect") yields sxUnsat.
    ## After R16-3: the raise fork is opened → sxRaised.
    let r = symexFind(sd, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# Behavior 2: mod — unconstrained divisor → sxRaised(DivByZeroDefect)
# ---------------------------------------------------------------------------

proc sm(a, b: int) =
  ## Unconstrained `b` — b==0 is satisfiable for mod too.
  let q = a mod b
  symexTarget("tm")
  discard q

suite "symex Phase 16 R16-3 — mod DivByZeroDefect raise fork":

  test "R16-3-2: unconstrained a mod b → sxRaised(DivByZeroDefect)":
    let r = symexFind(sm, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# Behavior 3: Caught — DivByZeroDefect inside try/except is catchable
# ---------------------------------------------------------------------------

proc sc_caught(a, b: int) =
  ## div inside try/except DivByZeroDefect: the defect is caught.
  try:
    let q = a div b
    discard q
  except DivByZeroDefect:
    symexTarget("tcaught")

suite "symex Phase 16 R16-3 — DivByZeroDefect catchability":

  test "R16-3-3: div in try/except DivByZeroDefect is caught → sxSat":
    ## The raise-fork enters the except handler; handler body reaches the target.
    let r = symexFind(sc_caught, tLabel("tcaught"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Behavior 4: Guarded short-circuit — b != 0 and a div b should NOT fork
# ---------------------------------------------------------------------------

proc sg(a, b: int) =
  ## `b != 0` guards the div in the RHS — DivByZeroDefect is NOT reachable.
  if b != 0 and a div b > 5:
    symexTarget("tg")

suite "symex Phase 16 R16-3 — guarded short-circuit (primary acceptance gate)":

  test "R16-3-4: b != 0 and a div b > 5 → NO DivByZeroDefect (guard eliminates b==0)":
    ## Before step 5 (rhsHasInlineDefectFork fix): false-positive sxRaised.
    ## After step 5: b==0 is short-circuit-guarded → sxUnsat for tRaisedExn.
    let r = symexFind(sg, tRaisedExn("DivByZeroDefect"))
    check r.status != sxRaised

# ---------------------------------------------------------------------------
# Behavior 5: LHS div still raises — not over-guarded
# ---------------------------------------------------------------------------

proc sl(a, b: int) =
  ## div is LHS of `and` — evaluated unconditionally by Nim. DivByZeroDefect IS
  ## reachable because there is no prior guard on `b`.
  if a div b > 5 and b != 0:
    symexTarget("tl")

suite "symex Phase 16 R16-3 — LHS div raises (not over-guarded)":

  test "R16-3-5: a div b > 5 and b != 0 → DivByZeroDefect still reachable (LHS div)":
    ## div is in the LHS — evaluated unconditionally → raise is reachable.
    let r = symexFind(sl, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# Behavior 6: acDivByZero off — no DivByZeroDefect when gate disabled
# ---------------------------------------------------------------------------

proc sd_off(a, b: int) =
  ## Same shape as sd, but tested with acDivByZero excluded.
  let q = a div b
  symexTarget("toff")
  discard q

proc noAcDivByZeroSettings(): SymexSettings =
  ## Settings with acDivByZero excluded from arithChecks.
  result = defaultSymexSettings()
  result.arithChecks = {acOverflow, acRange}

suite "symex Phase 16 R16-3 — acDivByZero gate":

  test "R16-3-6: acDivByZero off → no DivByZeroDefect raise (honest-incomplete)":
    let r = symexFind(sd_off, tRaisedExn("DivByZeroDefect"), noAcDivByZeroSettings())
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Behavior 7: Constant nonzero divisor — no DivByZeroDefect
# ---------------------------------------------------------------------------

proc sc_const(a: int) =
  ## `a div 2` — divisor is the constant 2, never zero.
  let q = a div 2
  symexTarget("tc")
  discard q

suite "symex Phase 16 R16-3 — constant nonzero divisor":

  test "R16-3-7: a div 2 → NO DivByZeroDefect (2 == 0 is UNSAT)":
    ## The divisor==0 predicate is `2 == 0` which Z3 can immediately refute.
    let r = symexFind(sc_const, tRaisedExn("DivByZeroDefect"))
    check r.status == sxUnsat
