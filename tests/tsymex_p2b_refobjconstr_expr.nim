## RFC-chapulin-hardening P2b — `ref object` construction (expression-position
## allocation), Cluster 4 — Parser expression coverage. ADR-0021.
##
## Before this slice, a `ref object` constructor used as an EXPRESSION (`let p
## = Node(val: x, next: nil)`, `Node = ref object`) reached the SAME
## `nnkObjConstr` arm P2a introduced for plain value objects (`classifyType`
## unwraps a NAMED ref-object alias to the identical `itTuple` shape) — but
## EVERY ref/ptr-typed field degraded: a bare `nnkNilLit` field value has no
## general `parseExpr` arm, and an omitted ref-typed field has no
## `zeroValueForType` encoding. P2b closes that gap by hardening the SAME
## value-tuple arm (see ADR-0021, `docs/SYMEX_PLAN.md`, for the full
## investigation, including why the RFC's original `isNew`/heap-allocation
## sketch was EMPIRICALLY REJECTED — it crashes for a NAMED ref-object alias
## and is architecturally incompatible with Phase 16 D1a's bare-symbol
## value-modelling).
##
## Bumps `symexWalkerVersion` 53->54 (verdict-surface change). `renderAs-
## ChoicesVersion` stays "5" (construction-only, same P1/P2a argument — see
## the version-pin suite below).
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

type
  Node = ref object
    val: int
    next: Node

  Rec = ref object
    a: int
    b: uint8
    c: int

  Point2 = object          ## plain value object (for the `new T` regression)
    x, y: int

  CastNode = ref object    ## SND-1 soundness fixture
    x: int64
    y: int32

  VNode = ref object        ## variant ref object (negative DoD)
    case kind: bool
    of true: a: int
    of false: b: int

# --- Headline DoD: basic construction + nil field -----------------------------
proc sutBasicHit(x: int) =
  let p = Node(val: x, next: nil)
  if p.val == 3:
    symexTarget("basic_hit")

# --- Load-bearing UNSAT soundness (proves REAL modeling, not a free dummy) ---
# p.val is ALWAYS x+1 by construction; p.val == x is impossible for any x
# (range-bounded so x+1 never overflows).
proc sutBasicUnsat(x: range[0..1000]) =
  let p = Node(val: x + 1, next: nil)
  if p.val == x:
    symexTarget("basic_unsat")

# --- nil field reads back as a genuine nil (comparable via the existing nil
# machinery) ------------------------------------------------------------------
proc sutNilFieldHit(x: int) =
  let p = Node(val: x, next: nil)
  if p.next == nil and p.val == 7:
    symexTarget("nil_field_hit")

# --- Multi-field construction; out-of-order; heterogeneous widths ------------
proc sutMultiFieldHit(x: int) =
  let r = Rec(c: x + 2, a: x, b: 5'u8)
  if r.a == 9 and r.b == 5 and r.c == 11:
    symexTarget("multi_hit")

# UNSAT soundness on the multi-field construction: c is ALWAYS a+2 by
# construction — c == a+3 is impossible.
proc sutMultiFieldUnsat(x: range[0..1000]) =
  let r = Rec(c: x + 2, a: x, b: 5'u8)
  if r.c == r.a + 3:
    symexTarget("multi_unsat")

# --- Omitted ref-typed field: sound zero (nil) — ground-truthed against
# real Nim `ref object` construction semantics (an omitted ref field really
# IS nil) ----------------------------------------------------------------------
proc sutOmittedFieldHit(x: int) =
  let p = Node(val: x)
  if p.val == 5 and p.next == nil:
    symexTarget("omitted_hit")

# Omitted-field UNSAT soundness: `next` is ALWAYS nil (never set) —
# `p.next != nil` is impossible. Proves the nil zero-init is REAL (a free/
# dummy ref could satisfy `!= nil`).
proc sutOmittedFieldUnsat(x: int) =
  let p = Node(val: x)
  if p.next != nil:
    symexTarget("omitted_unsat")

# --- Recursive field: non-nil, from a genuinely ref-valued (non-bare-symbol)
# source expression — cleanly expressible and must resolve to a real verdict,
# not a spurious degrade. -------------------------------------------------------
proc sutRecursiveFromDerivedRefHit(a: Node, x: int) =
  let p = Node(val: x, next: a.next)
  if p.val == 3:
    symexTarget("recursive_derived_hit")

# --- Recursive field: FROM an existing BARE-symbol node (`next: a`) is NOT
# cleanly expressible under this parser's value-model (D1a: `a` is
# value-modelled, no address to store) — must degrade SOUNDLY (sxUnknown,
# never a crash, never a false sxSat), per ADR-0021. -----------------------
proc sutRecursiveFromBareNode(a: Node, x: int) =
  let p = Node(val: x, next: a)
  if p.val == 3:
    symexTarget("recursive_bare_hit")

# --- SND-1 soundness: one field is a STILL-unsupported expression ------------
# The catch-all's dummy for an itInt32 field is `0`; if that dummy leaked
# through unprotected, `p.y == 0` would look trivially SAT for every `x`.
# SND-1's taint must force `sxUnknown` instead.
proc sutUnsupportedField(x: int64) =
  let p = CastNode(x: x, y: cast[int32](x))
  if p.y == 0:
    symexTarget("dummy_would_sat")

# --- Negative: variant ref-object construction stays sxUnknown (no crash,
# no false sxSat) — round-2 exclusion decision. -------------------------------
proc sutVariantConstr(x: int) =
  let v = VNode(kind: true, a: x)
  if v.a == 3:
    symexTarget("variant_hit")

# --- Regression: `new T` at LET-STATEMENT level (the existing R1a/R2 path,
# INLINE ref) still works, untouched by P2b. ----------------------------------
proc sutNewStmtRegression(x: int) =
  let p = new(Point2)
  p.x = x
  if p.x == 8:
    symexTarget("new_regression")

# Regression: an ordinary (non-object) expression is completely unaffected.
proc sutPlainArithRegression(x: int) =
  let y = x + 1
  if y == 5:
    symexTarget("plain_arith")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening P2b — ref-object construction as expression":

  test "P2b-1: let p=Node(val:x,next:nil); p.val==3 -> sxSat, exact witness x==3":
    let r = symexFind(sutBasicHit, tLabel("basic_hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "P2b-2: UNSAT soundness — p.val == x is impossible (p.val is always x+1)":
    let r = symexFind(sutBasicUnsat, tLabel("basic_unsat"))
    check r.status == sxUnsat

  test "P2b-3: nil field reads back as genuine nil — exact witness x==7":
    let r = symexFind(sutNilFieldHit, tLabel("nil_field_hit"))
    check r.status == sxSat
    check r.witness[0] == 7

  test "P2b-4: multi-field, out-of-order, heterogeneous widths — exact witness x==9":
    let r = symexFind(sutMultiFieldHit, tLabel("multi_hit"))
    check r.status == sxSat
    check r.witness[0] == 9

  test "P2b-5: multi-field UNSAT soundness — r.c == r.a+3 is impossible (always +2)":
    let r = symexFind(sutMultiFieldUnsat, tLabel("multi_unsat"))
    check r.status == sxUnsat

  test "P2b-6: omitted ref field defaults to nil — exact witness x==5":
    let r = symexFind(sutOmittedFieldHit, tLabel("omitted_hit"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "P2b-7: omitted-field UNSAT soundness — p.next != nil is impossible (never set)":
    let r = symexFind(sutOmittedFieldUnsat, tLabel("omitted_unsat"))
    check r.status == sxUnsat

  test "P2b-8: recursive field from a derived (non-bare) ref expr resolves cleanly — witness x==3":
    let r = symexFind(sutRecursiveFromDerivedRefHit, tLabel("recursive_derived_hit"))
    check r.status == sxSat
    check r.witness[1] == 3

suite "symex RFC-chapulin-hardening P2b — recursive-from-bare-node soundness (ADR-0021)":

  test "P2b-9: `next: a` (bare Node param) degrades to sxUnknown, never a crash":
    let r = symexFind(sutRecursiveFromBareNode, tLabel("recursive_bare_hit"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

  test "P2b-10: `next: a` never produces a false sxSat despite p.val==3 alone being trivially satisfiable":
    let r = symexFind(sutRecursiveFromBareNode, tLabel("recursive_bare_hit"))
    check r.status != sxSat

suite "symex RFC-chapulin-hardening P2b — SND-1 soundness (unsupported field)":

  test "P2b-11: ref-object with cast[int32](x) field compiles and degrades to sxUnknown + feUnsupportedExprKind":
    let r = symexFind(sutUnsupportedField, tLabel("dummy_would_sat"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

  test "P2b-12: the dummy field value never produces a false sxSat (SND-1 taint)":
    let r = symexFind(sutUnsupportedField, tLabel("dummy_would_sat"))
    check r.status != sxSat

suite "symex RFC-chapulin-hardening P2b — variant ref-object negative (round-2 exclusion)":

  test "P2b-13: variant ref-object constructor stays sxUnknown (no crash, no false sxSat)":
    let r = symexFind(sutVariantConstr, tLabel("variant_hit"))
    check r.status == sxUnknown
    check r.status != sxSat
    ## The degrade mechanism (ADR-0021) returns a reference to a fresh,
    ## deliberately-UNBOUND synthetic var — the FIRST read of `v` (already at
    ## the `let v = …` binding itself) is expected to hit either (a) my
    ## classified `feUnsupportedExprKind` parse-time error, if the unbound-var
    ## read is never actually reached, or (b) the safe missing-key path
    ## (`env[name]` -> `KeyError` -> ADR-0020's CR-1c safety net ->
    ## `weInternalWalkerFault`), if it IS reached before anything consumes it.
    ## EMPIRICALLY, which of the two fires is backend-dependent (C: (a); C++:
    ## (b)) — a benign cross-backend divergence in exception-timing, the same
    ## class ADR-0020 itself documents (the b7258f7/CR-1c precedent). Both are
    ## SOUND classified degrades to `sxUnknown`; the load-bearing invariant is
    ## the status assertions above (never a crash, never a false `sxSat`), not
    ## which specific error kind happens to surface.
    var sawKind = false
    for e in r.errors:
      if e.kind in {feUnsupportedExprKind, weInternalWalkerFault} and
         e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex RFC-chapulin-hardening P2b — regressions":

  test "P2b-14: `let p = new(Point2); p.x = x` (R1a/R2 let-statement path) still works":
    let r = symexFind(sutNewStmtRegression, tLabel("new_regression"))
    check r.status == sxSat
    check r.witness[0] == 8

  test "P2b-15: plain (non-object) arithmetic unaffected — exact witness x==4":
    let r = symexFind(sutPlainArithRegression, tLabel("plain_arith"))
    check r.status == sxSat
    check r.witness[0] == 4

suite "symex RFC-chapulin-hardening P2b — version pins":

  test "walker version floor >= 54 (P2b introduced at 54)":
    check parseInt(symexWalkerVersion) >= 54

  test "renderAsChoicesVersion floor >= 5 (P2b does NOT bump RC — see canonicalize.nim note)":
    ## P2b introduces no new witness shape: `renderAsChoices*[T]` (symex.nim)
    ## is built ONLY from the SUT's top-level parameter list, never from an
    ## internal `let`-bound or returned value.
    check parseInt(renderAsChoicesVersion) >= 5
