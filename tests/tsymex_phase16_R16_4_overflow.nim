import std/unittest
import nelli/symex

# Phase 16 R16-4 — signed integer OverflowDefect raise fork.
#
# The engine now forks an `OverflowDefect` raise-path when signed integer
# arithmetic (+/-/*) may overflow. This mirrors the R16-3 DivByZeroDefect
# mechanism but uses Z3 BV overflow predicates (addNoOverflow/addNoUnderflow/
# subNoOverflow/subNoUnderflow/mulNoOverflow/mulNoUnderflow) to build the
# "this op overflows" condition, pushed to the `overflowConds` sink and
# drained by `drainOverflowRaises` (chained in `drainScalarRaiseForks`).
#
# Key correctness rules:
#   Signed BV (int, int8..int64) → fork OverflowDefect (raises in Nim).
#   Unsigned BV (uint, uint8..uint64) → NO fork (Nim wraps silently).
#   svInt (unbounded Z3Int) → NO fork (BV predicates on Int hang Z3).
#
# Short-circuit guard (step 6): rhsHasInlineDefectFork now covers bAdd/bSub/bMul,
# so `a < 100 and a+1 > 50` does NOT false-positive (a<100 ⇒ a+1 safe).

# ---------------------------------------------------------------------------
# Behavior 1: signed add — unconstrained a + b → OverflowDefect
# ---------------------------------------------------------------------------

proc sa(a, b: int) =
  ## Unconstrained signed ints — a+b may overflow → OverflowDefect raise fork.
  let c = a + b
  symexTarget("ta")
  discard c

suite "symex Phase 16 R16-4 — signed add OverflowDefect raise fork":

  test "R16-4-1: unconstrained a + b (signed) → sxRaised(OverflowDefect)":
    ## Before R16-4: tRaisedExn("OverflowDefect") yields sxUnsat.
    ## After R16-4: the raise fork is opened → sxRaised.
    let r = symexFind(sa, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

# ---------------------------------------------------------------------------
# Behavior 2: signed sub — unconstrained a - b → OverflowDefect
# ---------------------------------------------------------------------------

proc ss(a, b: int) =
  ## Unconstrained signed ints — a-b may overflow.
  let c = a - b
  symexTarget("ts")
  discard c

suite "symex Phase 16 R16-4 — signed sub OverflowDefect raise fork":

  test "R16-4-2: unconstrained a - b (signed) → sxRaised(OverflowDefect)":
    let r = symexFind(ss, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

# ---------------------------------------------------------------------------
# Behavior 3: signed mul — unconstrained a * b → OverflowDefect
# ---------------------------------------------------------------------------

proc sm(a, b: int) =
  ## Unconstrained signed ints — a*b may overflow.
  let c = a * b
  symexTarget("tm")
  discard c

suite "symex Phase 16 R16-4 — signed mul OverflowDefect raise fork":

  test "R16-4-3: unconstrained a * b (signed) → sxRaised(OverflowDefect)":
    let r = symexFind(sm, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

# ---------------------------------------------------------------------------
# Behavior 4: Caught — OverflowDefect inside try/except is catchable
# ---------------------------------------------------------------------------

proc sc_caught(a, b: int) =
  ## signed add inside try/except OverflowDefect: the defect is caught.
  try:
    let c = a + b
    discard c
  except OverflowDefect:
    symexTarget("tcaught")

suite "symex Phase 16 R16-4 — OverflowDefect catchability":

  test "R16-4-4: a+b in try/except OverflowDefect is caught → sxSat":
    ## The raise-fork enters the except handler; handler body reaches the target.
    let r = symexFind(sc_caught, tLabel("tcaught"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Behavior 5: UNSIGNED does NOT fork (Nim wraps silently)
# ---------------------------------------------------------------------------

proc su(a, b: uint) =
  ## Unsigned arithmetic wraps silently in Nim — no OverflowDefect.
  let c = a + b
  symexTarget("tu")
  discard c

suite "symex Phase 16 R16-4 — unsigned wraps (no OverflowDefect)":

  test "R16-4-5: a + b (unsigned) → NO OverflowDefect (Nim wraps silently)":
    ## Unsigned BV: no overflow fork. Critical Nim-semantics gate.
    let r = symexFind(su, tRaisedExn("OverflowDefect"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Behavior 6: Guarded short-circuit — a < 100 and a+1 > 50 must NOT false-positive
# ---------------------------------------------------------------------------

proc sg(a: int) =
  ## a<100 guards the RHS. a+1 overflow is only reachable when a could be
  ## near high::int, but a<100 makes that impossible. Must NOT sxRaised.
  if a < 100 and a + 1 > 50:
    symexTarget("tg")

suite "symex Phase 16 R16-4 — guarded short-circuit (primary acceptance gate)":

  test "R16-4-6: a < 100 and a+1 > 50 → NO OverflowDefect (a<100 guards)":
    ## Without the rhsHasInlineDefectFork bAdd guard: false-positive sxRaised.
    ## With the guard: a+1 is in the guarded path where a<100 constrains it.
    let r = symexFind(sg, tRaisedExn("OverflowDefect"))
    check r.status != sxRaised

# ---------------------------------------------------------------------------
# Behavior 7: LHS arith still raises — not over-guarded
# ---------------------------------------------------------------------------

proc sl(a: int) =
  ## a+1 is LHS of `and`, evaluated unconditionally. OverflowDefect IS reachable.
  if a + 1 > 50 and a < 100:
    symexTarget("tl")

suite "symex Phase 16 R16-4 — LHS arith raises (not over-guarded)":

  test "R16-4-7: a+1 > 50 and a < 100 → OverflowDefect still reachable (LHS arith)":
    ## a+1 is in the LHS — evaluated unconditionally → raise is reachable.
    let r = symexFind(sl, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

# ---------------------------------------------------------------------------
# Behavior 8: acOverflow off — no OverflowDefect when gate disabled
# ---------------------------------------------------------------------------

proc sa_off(a, b: int) =
  ## Same shape as sa, but tested with acOverflow excluded.
  let c = a + b
  symexTarget("toff")
  discard c

proc noAcOverflowSettings(): SymexSettings =
  ## Settings with acOverflow excluded from arithChecks.
  result = defaultSymexSettings()
  result.arithChecks = {acDivByZero, acRange}

suite "symex Phase 16 R16-4 — acOverflow gate":

  test "R16-4-8: acOverflow off → no OverflowDefect raise (honest-incomplete)":
    let r = symexFind(sa_off, tRaisedExn("OverflowDefect"), noAcOverflowSettings())
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Behavior 9: Bounded operands — no false positive when in-range
# ---------------------------------------------------------------------------

proc sb(a: int) =
  ## a is bounded to [0,10) by nested-if guards before the add.
  ## a+1 ∈ [1,11) — nowhere near overflow — so no OverflowDefect.
  ## Named target is reachable → sxSat (the target IS reachable in the
  ## non-overflow survivor path).
  if a >= 0 and a < 10:
    let c = a + 1
    symexTarget("tb")
    discard c

suite "symex Phase 16 R16-4 — bounded operands no false positive":

  test "R16-4-9: a in [0,10) → a+1 cannot overflow → NO OverflowDefect":
    ## Confirms in-range arithmetic stays clean.
    let r = symexFind(sb, tRaisedExn("OverflowDefect"))
    check r.status == sxUnsat

  test "R16-4-9b: a in [0,10) → named target tb is reachable (sxSat)":
    ## The non-overflow survivor path reaches the target.
    let r = symexFind(sb, tLabel("tb"))
    check r.status == sxSat
