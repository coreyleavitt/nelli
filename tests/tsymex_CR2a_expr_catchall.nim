## RFC-chapulin-hardening CR-2a — expression-position `error()` →
## preamble-`mkUnsupported` + dummy (Cluster 2 — Crash-totality).
##
## `parseExpr`'s catch-all (`dsl_parser.nim`, the final `else:` arm of its
## `case n.kind`) used to `error()` at MACRO-EXPANSION time whenever it
## reached a NimNode `kind` not covered by any of the arms above — aborting
## COMPILATION of the whole test file outright. That is strictly worse than
## `sxUnknown` (Invariant 3): the SUT could not be analysed at all.
##
## CR-2a converts that catch-all to the existing in-repo degrade idiom
## (precedent: the A7-S3 `runeLen(symbolic)` site in the same file): it
## registers a classified `sevError` parseError (`feUnsupportedExprKind`),
## appends `mkUnsupported(reason)` to the preamble, and returns a
## type-correct dummy resolved via `classifyType(n).ty` (works regardless of
## `n.kind`). Soundness rides on SND-1 (LANDED, walker v38+): `of
## isUnsupported` taints `Path.uncertain`, so any witness produced downstream
## of the dummy is demoted to `sxUnknown` at the chokepoints — the dummy can
## NEVER produce a false witness. The parseError also makes this Class-A, so
## `capForcedUnknown` backstops it independently of SND-1.
##
## ## RFC M5 migration (walker v50→51)
##
## M5 (RFC-chapulin-hardening Cluster 3) added an `nnkIfExpr` arm to
## `parseExpr`, so an if-EXPRESSION used as a sub-expression — this file's
## original RED repro for the catch-all — is no longer unsupported: it now
## resolves to a REAL verdict instead of degrading. Per the same migration
## principle M4 used for the SND-1 `&=` tests (flip the now-modeled case to
## its real verdict; retarget the mechanism-demonstration case to a
## still-unsupported construct), this file now:
##
##   * Flips `sutIfExprSubExpr` (if-expr nested as a `+` operand) to its
##     REAL verdict: `y` is always 2 or 3 (never 1), so `y == 1` is a genuine
##     `sxUnsat` now (not a dummy-taint `sxUnknown`).
##   * Flips `sutIfExprDirectLet` (if-expr as direct let-rhs) to its REAL
##     verdict: `y == 1` is reachable exactly when `x > 0`, a genuine `sxSat`
##     with witness `x > 0`.
##   * Retargets the catch-all-MECHANISM demonstration (formerly CR-2a-2,
##     riding on the if-expr dummy) to `sutCastSubExpr`: `cast[int32](x)` as
##     a `+` operand. `parseExpr` has no `nnkCast` arm outside the R11
##     pointer-materialisation guard (`unsafeCastReason`, which matches only
##     `cast[ptr T]`/`addr`, and only at LET-RHS classification, not inside
##     `parseExpr`'s own dispatch) — empirically verified (2026-07-22) to
##     still hit the catch-all post-M5: `sxUnknown` + `feUnsupportedExprKind`.
##     Reuses the SAME "dummy_would_sat" framing (`y == 1`, where a leaked
##     dummy of 0 would make `0 + 1 == 1` trivially true for every `x`) to
##     keep proving SND-1 soundness at this new site.
##
## `sutPlainIfStmt` (statement-position `if`, already supported) and
## `sutPlainArith` (plain arithmetic regression) are UNCHANGED.
##
## Walker version: v43 → v44 introduced this catch-all; v50 → v51 (M5) is
## what necessitates this migration.
##
## No new ADR: CR-2a reuses the existing `mkUnsupported`-degrade mechanism at
## a new site; it introduces no new mechanism (per RFC judgment call).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

# SUT 1 (was the RED repro for the catch-all; post-M5 a genuine `sxUnsat`):
# an if-EXPRESSION nested as an operand of `+`. `y` is always 2 (x > 0) or 3
# (x <= 0) — `y == 1` is never reachable. Pre-M5 this degraded to a
# dummy-tainted `sxUnknown` (the dummy value 0 would make `0 + 1 == 1` look
# trivially true for every x, a false witness SND-1 had to block); post-M5 it
# is REALLY modeled and REALLY unsat, for the real reason.
proc sutIfExprSubExpr(x: int) =
  let y = (if x > 0: 1 else: 2) + 1
  if y == 1:
    symexTarget("if_expr_subexpr")

# SUT 2 (post-M5 a genuine `sxSat`): an if-EXPRESSION as the DIRECT rhs of a
# `let`. Pre-M5 this hit the same catch-all as SUT 1 one recursion level
# shallower (no wrapping `nnkInfix`); post-M5 it is really modeled —
# reachable exactly when `x > 0`.
proc sutIfExprDirectLet(x: int) =
  let y = if x > 0: 1 else: 2
  if y == 1:
    symexTarget("direct_let_if")

# SUT 3 (RFC M5 migration — retargeted catch-all-MECHANISM demonstration):
# `cast[int32](x)` as a `+` operand. `parseExpr` has no `nnkCast` arm outside
# the R11 pointer-materialisation guard (which matches only `cast[ptr T]`/
# `addr`, and only at let-rhs classification) — this still lands on the
# catch-all post-M5. Same "dummy_would_sat" framing as the original SUT 1: a
# leaked dummy of 0 would make `y == 1` trivially true for every x.
proc sutCastSubExpr(x: int64) =
  let y = cast[int32](x) + 1
  if y == 1:
    symexTarget("dummy_would_sat")

# SUT 4 (genuine regression guard): `if` used directly at STATEMENT
# position (no let-binding) is handled by `parseStmtInner`'s `nnkIfStmt`/
# `nnkIfExpr` arm directly and never reaches `parseExpr` at all — CR-2a must
# not affect this already-supported shape.
proc sutPlainIfStmt(x: int) =
  if x > 0:
    symexTarget("plain_if_stmt")

# SUT 5 (genuine regression guard): ordinary arithmetic — no unsupported
# node kind anywhere — must still resolve exactly as before.
proc sutPlainArith(x: int) =
  let y = x + 1
  if y == 5:
    symexTarget("plain_arith")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening CR-2a/M5 — if-expr sub-expr now real (migrated)":

  test "CR-2a-1: if-expr nested as sub-expr is now a REAL sxUnsat (M5 models it)":
    ## Pre-M5 this was a dummy-tainted `sxUnknown`; post-M5 (walker v51) the
    ## if-expression is genuinely modeled and `y` (2 or 3) can never equal 1.
    let r = symexFind(sutIfExprSubExpr, tLabel("if_expr_subexpr"))
    check r.status == sxUnsat

  test "CR-2a-2: if-expr as direct let-rhs is now a REAL sxSat with x>0 witness (M5)":
    let r = symexFind(sutIfExprDirectLet, tLabel("direct_let_if"))
    check r.status == sxSat
    check r.witness[0] > 0

suite "symex RFC-chapulin-hardening CR-2a — catch-all MECHANISM still degrades (retargeted)":

  test "CR-2a-3: cast[int32](x) nested as sub-expr still compiles and degrades to sxUnknown + feUnsupportedExprKind":
    ## Strong form: assert the classified KIND, not just the verdict.
    let r = symexFind(sutCastSubExpr, tLabel("dummy_would_sat"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2a-4: dummy never produces a false witness (SND-1 soundness, retargeted site)":
    ## Even though the synthesized dummy (0) would make `y == 1` look
    ## trivially reachable for every x if it were actually read, the SND-1
    ## taint forces sxUnknown — never a false sxSat.
    let r = symexFind(sutCastSubExpr, tLabel("dummy_would_sat"))
    check r.status != sxSat

suite "symex RFC-chapulin-hardening CR-2a — regression guard":

  test "CR-2a-5: plain if-statement (unbound, statement position) unaffected — sxSat":
    let r = symexFind(sutPlainIfStmt, tLabel("plain_if_stmt"))
    check r.status == sxSat
    check r.witness[0] > 0

  test "CR-2a-6: plain arithmetic unaffected — sxSat with exact witness":
    let r = symexFind(sutPlainArith, tLabel("plain_arith"))
    check r.status == sxSat
    check r.witness[0] == 4

suite "symex RFC-chapulin-hardening CR-2a — walker version pin":

  test "walker version floor >= 44 (CR-2a introduced at 44)":
    ## CR-2a converts parseExpr's compile-abort catch-all to a classified
    ## sxUnknown degrade; bump 43->44 rotates any stale cache entries (there
    ## are none for the compile-abort case — a compile failure has no cache
    ## entry — but SUTs newly reachable through this path must not collide
    ## with any unrelated pre-44 cache key).
    check parseInt(symexWalkerVersion) >= 44
