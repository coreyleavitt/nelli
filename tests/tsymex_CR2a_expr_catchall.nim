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
## Concrete repro (RED before this slice, GREEN after): an `if`-EXPRESSION
## nested as a sub-expression — e.g. an operand of `+` — is NOT covered by
## `parseExpr`'s `case` (nnkIfStmt/nnkIfExpr are only handled at STATEMENT
## position, in `parseStmtInner`, including the direct `let x = if ...`
## shape). Once nested one level deeper (`(if c: 1 else: 2) + 1`), the `+`'s
## operand recurses through `parseExpr` and lands on the catch-all. Before
## this slice: `nim c tests/tsymex_CR2a_expr_catchall.nim` FAILED to compile
## with `Error: symex: unsupported expression kind nnkIfExpr in ...`. After:
## it compiles and the SUT resolves to a classified `sxUnknown`.
##
## Walker version: v43 → v44 (compile-abort → sxUnknown is a verdict change).
##
## No new ADR: CR-2a reuses the existing `mkUnsupported`-degrade mechanism at
## a new site; it introduces no new mechanism (per RFC judgment call).

import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

# SUT 1 (RED repro / strong-form): an if-EXPRESSION nested as an operand of
# `+` hits parseExpr's catch-all. The dummy value it degrades to is
# `mkIntLit(0)` (int is the classified type of the if-expression). If the
# dummy were ever actually CONSUMED by the walker (soundness bug), `y` would
# equal `0 + 1 == 1` for EVERY `x` — `y == 1` would look trivially reachable,
# producing a false `sxSat` witness for ALL x (including x <= 0, where the
# "real" if-expression value is 2, so `y` would really be 3, never 1). SND-1
# must taint this path to `sxUnknown` instead, proving the dummy is never
# read as a real value.
proc sutIfExprSubExpr(x: int) =
  let y = (if x > 0: 1 else: 2) + 1
  if y == 1:
    symexTarget("dummy_would_sat")

# SUT 2 (additional catch-all coverage, NOT a regression case): an
# if-EXPRESSION as the DIRECT rhs of a `let` ALSO hits parseExpr's catch-all
# — `nnkLetSection`'s binding handler (line ~2742) unconditionally calls
# `parseExpr(valNode, ...)` on the RHS regardless of its kind, so this is the
# SAME catch-all as SUT 1, just one recursion level shallower (no wrapping
# `nnkInfix`). `parseStmtInner`'s `nnkIfStmt`/`nnkIfExpr` arm only covers `if`
# used directly at STATEMENT position (bare, unbound) — see SUT 3.
proc sutIfExprDirectLet(x: int) =
  let y = if x > 0: 1 else: 2
  if y == 1:
    symexTarget("direct_let_if")

# SUT 3 (genuine regression guard): `if` used directly at STATEMENT
# position (no let-binding) is handled by `parseStmtInner`'s `nnkIfStmt`/
# `nnkIfExpr` arm directly and never reaches `parseExpr` at all — CR-2a must
# not affect this already-supported shape.
proc sutPlainIfStmt(x: int) =
  if x > 0:
    symexTarget("plain_if_stmt")

# SUT 4 (genuine regression guard): ordinary arithmetic — no unsupported
# node kind anywhere — must still resolve exactly as before.
proc sutPlainArith(x: int) =
  let y = x + 1
  if y == 5:
    symexTarget("plain_arith")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening CR-2a — expr-position catch-all degrade":

  test "CR-2a-1: if-expr nested as sub-expr compiles and degrades to sxUnknown + feUnsupportedExprKind":
    ## Strong form: assert the classified KIND, not just the verdict.
    let r = symexFind(sutIfExprSubExpr, tLabel("dummy_would_sat"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2a-2: dummy never produces a false witness (SND-1 soundness)":
    ## Even though the synthesized dummy (0) would make `y == 1` look
    ## trivially reachable for every x if it were actually read, the SND-1
    ## taint forces sxUnknown — never a false sxSat.
    let r = symexFind(sutIfExprSubExpr, tLabel("dummy_would_sat"))
    check r.status != sxSat

  test "CR-2a-3: if-expr as direct let-rhs also compiles and degrades to sxUnknown + feUnsupportedExprKind":
    ## Same catch-all as CR-2a-1, reached one recursion level shallower
    ## (no wrapping nnkInfix) — additional coverage that the fix isn't
    ## sensitive to nesting depth.
    let r = symexFind(sutIfExprDirectLet, tLabel("direct_let_if"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex RFC-chapulin-hardening CR-2a — regression guard":

  test "CR-2a-4: plain if-statement (unbound, statement position) unaffected — sxSat":
    let r = symexFind(sutPlainIfStmt, tLabel("plain_if_stmt"))
    check r.status == sxSat
    check r.witness[0] > 0

  test "CR-2a-5: plain arithmetic unaffected — sxSat with exact witness":
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
