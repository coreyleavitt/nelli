## Phase 16 — RFC Cluster 3 slice M5: `nnkIfExpr` in `parseExpr` (synthetic
## let+read) + `min`/`max` (via if-expression-bodied proc inlining).
##
## Before this slice, an if-EXPRESSION used as a SUB-EXPRESSION — nested as a
## `+` operand, or as the direct RHS of a `let` — was NOT covered by
## `parseExpr`'s `case` (only `parseStmtInner` handled `nnkIfStmt`/`nnkIfExpr`,
## at STATEMENT position); it fell into the CR-2a catch-all and degraded to a
## classified `sxUnknown`. M5 adds an `nnkIfExpr` arm to `parseExpr` that
## A-normalises via synthetic let+read: a fresh temp is bound to the chosen
## arm's value (each arm rebinds the SAME temp name — safe, because
## `runtime.nim`'s `isIf` walker forks `paths` per-arm BEFORE running the arm
## body, so sibling arms can never collide), the if is emitted as a statement
## into the caller's preamble, and a read of the temp is returned in the
## if-expression's place.
##
## `min`/`max` on `int` need NO separate modeling: `system.min`/`system.max`'s
## `int` overloads carry a `{.magic: "MinI"/"MaxI".}` pragma but ALSO a real,
## parseable body (`if x <= y: x else: y` / `if y <= x: x else: y`,
## `system/comparisons.nim`) — `getImpl` resolves it, and `parseCalleeImpl`'s
## single-`result = expr` rewrite (`resultRhs`) detects the whole body as one
## expression and calls `parseExpr` directly on its `nnkIfExpr`. That routes
## straight through this slice's new arm via ordinary proc-inlining. (The
## FLOAT overloads are intercepted earlier by `mathInterception` — Phase 15
## F6/A5 — and never reach this path; this file only exercises the int form.)
##
## Bumps `symexWalkerVersion` 50->51 (verdict-surface change: if-expr-subexpr
## and min/max SUTs move from `sxUnknown` to a real verdict).
## `renderAsChoicesVersion` stays "5" — no new witness shape (plain int/bool).
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---------------------------------------------------------------------------
# If-expression as a sub-expression (nested as a `+` operand)
# ---------------------------------------------------------------------------

proc ifExprSubExprHit1(x: int) =
  ## (if x > 0: 1 else: 2) + 1 == 2  <=>  x > 0
  let y = (if x > 0: 1 else: 2) + 1
  if y == 2:
    symexTarget("hit1")

proc ifExprSubExprHit2(x: int) =
  ## (if x > 0: 1 else: 2) + 1 == 3  <=>  x <= 0
  let y = (if x > 0: 1 else: 2) + 1
  if y == 3:
    symexTarget("hit2")

proc ifExprSubExprUnsat(x: int) =
  ## Neither branch of the if-expr can ever make y == 10 — proves the value
  ## is genuinely constrained (not a free/uninterpreted stand-in).
  let y = (if x > 0: 1 else: 2) + 1
  if y == 10:
    symexTarget("unsat")

# ---------------------------------------------------------------------------
# If-expression as the direct RHS of a `let`
# ---------------------------------------------------------------------------

proc ifExprDirectLet(x: int) =
  let y = if x > 0: 1 else: 2
  if y == 1:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# min / max (int) — via if-expression-bodied proc inlining
# ---------------------------------------------------------------------------

proc maxHitAtBound(x: int) =
  if max(x, 5) == 5:
    symexTarget("hit")

proc maxUnsat(x: int) =
  ## max(x, 5) is never < 5 for any x — soundness UNSAT.
  if max(x, 5) < 5:
    symexTarget("unsat")

proc minHitAtBound(x: int) =
  if min(x, 5) == 5:
    symexTarget("hit")

proc minUnsat(x: int) =
  ## min(x, 5) is never > 5 for any x — soundness UNSAT.
  if min(x, 5) > 5:
    symexTarget("unsat")

proc maxSymbolicVsSymbolic(a, b: int) =
  ## Both operands symbolic — proves inlining isn't special-cased to a
  ## literal second argument.
  if max(a, b) == a and a > b:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening M5 — if-expr sub-expression":

  test "M5-1: (if x>0:1 else:2)+1 == 2 <=> x>0, exact witness":
    let r = symexFind(ifExprSubExprHit1, tLabel("hit1"))
    check r.status == sxSat
    check r.witness[0] > 0

  test "M5-2: (if x>0:1 else:2)+1 == 3 <=> x<=0, exact witness (BOTH arms modeled)":
    let r = symexFind(ifExprSubExprHit2, tLabel("hit2"))
    check r.status == sxSat
    check r.witness[0] <= 0

  test "M5-3: if-expr sub-expression soundness UNSAT":
    let r = symexFind(ifExprSubExprUnsat, tLabel("unsat"))
    check r.status == sxUnsat

  test "M5-4: if-expr as direct let-rhs — sxSat with x>0 witness":
    let r = symexFind(ifExprDirectLet, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] > 0

suite "symex RFC-chapulin-hardening M5 — min/max":

  test "M5-5: max(x, 5) == 5 <=> x <= 5, exact witness":
    let r = symexFind(maxHitAtBound, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] <= 5

  test "M5-6: max(x, 5) < 5 is UNSAT (max(x,5) >= 5 always)":
    let r = symexFind(maxUnsat, tLabel("unsat"))
    check r.status == sxUnsat

  test "M5-7: min(x, 5) == 5 <=> x >= 5, exact witness":
    let r = symexFind(minHitAtBound, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] >= 5

  test "M5-8: min(x, 5) > 5 is UNSAT (min(x,5) <= 5 always)":
    let r = symexFind(minUnsat, tLabel("unsat"))
    check r.status == sxUnsat

  test "M5-9: max(a, b) == a and a > b — symbolic-vs-symbolic form":
    let r = symexFind(maxSymbolicVsSymbolic, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] > r.witness[1]

suite "symex RFC-chapulin-hardening M5 — walker version pin":

  test "walker version floor >= 51 (M5 introduced at 51)":
    check parseInt(symexWalkerVersion) >= 51
