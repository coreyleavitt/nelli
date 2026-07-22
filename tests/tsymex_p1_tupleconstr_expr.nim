## RFC-chapulin-hardening P1 — general `nnkTupleConstr` in EXPRESSION
## position (Cluster 4 — Parser expression coverage).
##
## Before this slice, `parseExpr` had NO general case for a tuple
## constructor used as an expression (`let t = (a, b)`, a value-returning
## proc's `result = (a, b, c)`, an anonymous named-field tuple `(x: a, y:
## b)`). Only the narrow `yield (e1, e2)` A3-S2a special-case in
## `parseIterBodyStmt` recognised `nnkTupleConstr`, and ONLY to destructure
## it directly into per-loop-var `let`s — it never built a tuple SymVal.
## Any OTHER tuple-constructor expression fell through to CR-2a's
## expression-position catch-all, which taints the whole run to a
## classified `sxUnknown` via SND-1 (the dummy zero-value for an `itTuple`
## is `nil`, so the catch-all's `zeroValueForType` returns `mkIntLit(0)`
## as an unreachable fallback protected by the taint).
##
## P1 adds a general N-ary `of nnkTupleConstr:` arm to `parseExpr` that
## builds a new `iekTupleLit` IR node (lowering to `svTuple`), reusing the
## ALREADY-EXISTING itTuple/svTuple witness/runtime machinery built for
## variant/object values (`emitTyAndReader`'s `itTuple` arm,
## `isRenderableWitnessTy`'s `itTuple` recursion, and every existing
## `svTuple` runtime dispatch) — this slice is purely the CONSTRUCTION
## path. Reading a tuple field (`t[0]` / `t.x`) was ALREADY fully
## supported (`nnkBracketExpr`/`nnkDotExpr`'s `itTuple` arms) — the gap was
## only ever on the construction side.
##
## Each tuple element is parsed via the ORDINARY `parseExpr` recursion, so
## an individually-unsupported field expression independently hits the
## CR-2a catch-all and taints the whole run via SND-1 — a tuple with one
## unsupported field can never manufacture a false `sxSat` from that
## field's dummy zero-value (Invariant 3); see the SND-1 soundness suite
## below.
##
## Bumps `symexWalkerVersion` 51->52 (verdict-surface change: SUTs
## constructing a tuple as an expression move from a classified
## `sxUnknown` to a real verdict). `renderAsChoicesVersion` STAYS "5" — see
## the version-pin test suite below for the evidence.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

# Basic 2-tuple construction as a `let`-rhs, then field-constrained. This is
# the RFC's headline example (`let t = (x, x+1); if t[0]==3 and t[1]==4: …`).
proc sutTupleBasicHit(x: int) =
  let t = (x, x + 1)
  if t[0] == 3 and t[1] == 4:
    symexTarget("basic_hit")

# UNSAT soundness: t[1] is ALWAYS t[0]+1 by construction — `t[1] == t[0]+2`
# can never hold. Proves REAL modeling (a dummy/free-symbol tuple could
# satisfy this), not a degrade. `x` is range-bounded so `x+1`/`x+2` are
# provably non-overflowing — an UNBOUNDED int param would make `x+1`
# itself reachably overflow near `int64.high`, and the resulting
# OverflowDefect finding (a real, unrelated, but also-reachable path) would
# win the search over the genuine logical UNSAT, masking exactly what this
# test is meant to prove.
proc sutTupleUnsat(x: range[0..1000]) =
  let t = (x, x + 1)
  if t[1] == t[0] + 2:
    symexTarget("basic_unsat")

# N-ary (3 elements) — proves the arm is genuinely N-ary, not a clone of the
# 2-element `yield` special-case.
proc sutTupleTriple(x: int) =
  let t = (x, x + 1, x + 2)
  if t[0] == 5 and t[1] == 6 and t[2] == 7:
    symexTarget("triple_hit")

proc sutTupleTripleUnsat(x: range[0..1000]) =
  ## t[2] is always t[0]+2 — t[2] == t[0]+3 is impossible. Range-bounded for
  ## the same overflow-avoidance reason as `sutTupleUnsat`.
  let t = (x, x + 1, x + 2)
  if t[2] == t[0] + 3:
    symexTarget("triple_unsat")

# Named-field tuple constructor `(a: expr, b: expr)` — the typed AST wraps
# each field as `nnkExprColonExpr[name, valueExpr]`.
proc sutNamedTupleHit(x: int) =
  let t = (a: x, b: x + 1)
  if t.a == 3 and t.b == 4:
    symexTarget("named_hit")

proc sutNamedTupleUnsat(x: range[0..1000]) =
  ## Range-bounded for the same overflow-avoidance reason as `sutTupleUnsat`.
  let t = (a: x, b: x + 1)
  if t.b == t.a + 2:
    symexTarget("named_unsat")

# NOTE on the RFC's `return (a, b, c)` framing: a value-returning helper
# whose body is a single `result = (a, b)` expression DOES route its RHS
# through this slice's new `parseExpr` arm (`parseCalleeImpl`'s `resultRhs`
# single-expression rewrite calls `parseExpr` directly on the
# tuple-constructor node, same mechanism M5 used for `min`/`max`) — so the
# CONSTRUCTION side works. But binding the CALL'S RESULT back at the call
# site (`let t = makePair(x)`) hits a SEPARATE, pre-existing, unrelated gap:
# `retBindEq` (`runtime.nim`) raises "composite-typed proc return not yet
# wired — got svTuple" (caught by CR-1c's `weInternalWalkerFault` catch-all,
# degrading soundly to `sxUnknown` — never a crash). This is the call/
# return-value BINDING path for a callee with a non-scalar return type, a
# DIFFERENT locus than `parseExpr`'s tuple-CONSTRUCTION arm this slice
# targets, and pre-dates P1 (verified: `retBindEq` is untouched by this
# slice's diff). Out of scope for P1 per the RFC's own scoping ("mainly the
# CONSTRUCTION path in parseExpr, reusing this [existing witness]
# machinery") — documented here as a discovered follow-up, not a P1 DoD
# item (the DoD's own examples are all `let`-bound constructions, never a
# helper-proc call).

# SND-1 soundness: one field is a STILL-unsupported expression
# (`cast[int32](x)` — `parseExpr` has no `nnkCast` arm outside the R11
# pointer-materialisation guard, verified elsewhere (tsymex_CR2a_expr_catchall)
# to still hit the CR-2a catch-all post-M5). The catch-all's dummy for an
# itInt field is `0`; if that dummy leaked through unprotected, `t[1] == 0`
# would look trivially SAT for every `x`. SND-1's taint on `isUnsupported`
# must force `sxUnknown` instead.
proc sutTupleUnsupportedField(x: int64) =
  let t = (x, cast[int32](x))
  if t[1] == 0:
    symexTarget("dummy_would_sat")

# Regression: an ordinary (non-tuple) expression is completely unaffected.
proc sutPlainArithRegression(x: int) =
  let y = x + 1
  if y == 5:
    symexTarget("plain_arith")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening P1 — tuple construction as expression":

  test "P1-1: let t=(x,x+1); t[0]==3 and t[1]==4 -> sxSat, exact witness x==3":
    let r = symexFind(sutTupleBasicHit, tLabel("basic_hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "P1-2: UNSAT soundness — t[1] == t[0]+2 is impossible (real modeling)":
    let r = symexFind(sutTupleUnsat, tLabel("basic_unsat"))
    check r.status == sxUnsat

  test "P1-3: N-ary (3-elem) tuple — exact witness x==5":
    let r = symexFind(sutTupleTriple, tLabel("triple_hit"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "P1-4: N-ary (3-elem) UNSAT soundness":
    let r = symexFind(sutTupleTripleUnsat, tLabel("triple_unsat"))
    check r.status == sxUnsat

  test "P1-5: named-field tuple (a: x, b: x+1) — exact witness x==3":
    let r = symexFind(sutNamedTupleHit, tLabel("named_hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "P1-6: named-field tuple UNSAT soundness":
    let r = symexFind(sutNamedTupleUnsat, tLabel("named_unsat"))
    check r.status == sxUnsat

suite "symex RFC-chapulin-hardening P1 — SND-1 soundness (unsupported field)":

  test "P1-8: tuple with cast[int32](x) field compiles and degrades to sxUnknown + feUnsupportedExprKind":
    ## Strong form: assert the classified KIND, not just the verdict.
    let r = symexFind(sutTupleUnsupportedField, tLabel("dummy_would_sat"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

  test "P1-9: the dummy field value never produces a false sxSat (SND-1 taint)":
    ## Even though a leaked dummy (0) would make `t[1] == 0` look trivially
    ## reachable for every x, SND-1's taint forces sxUnknown — never sxSat.
    let r = symexFind(sutTupleUnsupportedField, tLabel("dummy_would_sat"))
    check r.status != sxSat

suite "symex RFC-chapulin-hardening P1 — regression guard":

  test "P1-10: plain (non-tuple) arithmetic unaffected — exact witness x==4":
    let r = symexFind(sutPlainArithRegression, tLabel("plain_arith"))
    check r.status == sxSat
    check r.witness[0] == 4

suite "symex RFC-chapulin-hardening P1 — version pins":

  test "walker version floor >= 52 (P1 introduced at 52)":
    check parseInt(symexWalkerVersion) >= 52

  test "renderAsChoicesVersion floor >= 5 (P1 does NOT bump RC — see canonicalize.nim note)":
    ## P1 introduces no new witness shape: `renderAsChoices*[T]` (symex.nim)
    ## is built ONLY from the SUT's top-level parameter list, never from an
    ## internal `let`-bound or returned value, and its `elif T is tuple:`
    ## branch already existed untouched before this slice.
    check parseInt(renderAsChoicesVersion) >= 5
