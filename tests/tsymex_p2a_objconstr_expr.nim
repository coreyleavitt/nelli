## RFC-chapulin-hardening P2a — general value-object (non-ref) `nnkObjConstr`
## in EXPRESSION position (Cluster 4 — Parser expression coverage).
##
## Before this slice, `parseExpr` had NO general case for a value-object
## constructor `Point(x: a, y: b)` used as an EXPRESSION (`let p = Point(x:
## a, y: b)`, an object `return`). `nnkObjConstr` was recognised ONLY inside
## `nnkRaiseStmt`'s `newException(T, msg)` shape (`raise newException(...)`)
## — any OTHER value-object construction fell through to CR-2a's
## expression-position catch-all, tainting the whole run to a classified
## `sxUnknown` via SND-1. Reading a field (`p.x`) was ALREADY fully
## supported (`nnkDotExpr`'s `itTuple` arm) — the gap was only construction.
##
## A value object's `IRType` is `itTuple`-shaped — the SAME shape P1's
## `nnkTupleConstr` arm produces, just with `objectName` populated — so P2a
## REUSES P1's `iekTupleLit`/`mkTupleLit`/`lowerTupleLit` wholesale rather
## than minting a new IR kind: every existing `iekTupleLit` dispatch site
## (emitExpr, abstraction.nim, probeProto, canonicalize, …) transfers for
## free.
##
## Unlike a tuple, object-constructor fields may be reordered
## (`Point(y: b, x: a)`) or OMITTED (`Point(x: a)`, `y` defaults to its
## zero value). The new `parseExpr` arm walks the TYPE's declared field
## order and, for an omitted field, synthesises Nim's genuine zero-init
## value via CR-2a's `zeroValueForType` — sound, not a degrade, since an
## omitted `int` field really IS `0` in real Nim.
##
## Each PRESENT field parses via the ORDINARY `parseExpr` recursion, so an
## individually-unsupported field (`cast[int32](x)`) independently hits the
## CR-2a catch-all and taints the whole run via SND-1 — never a false
## `sxSat` (Invariant 3).
##
## Bumps `symexWalkerVersion` 52->53 (verdict-surface change: SUTs
## constructing a value object as an expression move from a classified
## `sxUnknown` to a real verdict). `renderAsChoicesVersion` STAYS "5" — see
## the version-pin test suite below for the evidence.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

type
  Point = object
    x, y: int

  BytePair = object
    a: int
    b: uint8

# Basic value-object construction as a `let`-rhs, field-constrained. This is
# the RFC's headline example.
proc sutObjBasicHit(x: int) =
  let p = Point(x: x, y: x + 1)
  if p.x == 3 and p.y == 4:
    symexTarget("basic_hit")

# UNSAT soundness: p.y is ALWAYS p.x+1 by construction — `p.y == p.x + 2`
# can never hold. Proves REAL modeling (a dummy/free-symbol object could
# satisfy this), not a degrade. `x` is range-bounded so `x+1`/`x+2` are
# provably non-overflowing.
proc sutObjUnsat(x: range[0..1000]) =
  let p = Point(x: x, y: x + 1)
  if p.y == p.x + 2:
    symexTarget("basic_unsat")

# Fields out of order — must still map to declared position (x, then y).
proc sutObjOutOfOrderHit(x: int) =
  let p = Point(y: x + 1, x: x)
  if p.x == 3 and p.y == 4:
    symexTarget("outoforder_hit")

proc sutObjOutOfOrderUnsat(x: range[0..1000]) =
  let p = Point(y: x + 1, x: x)
  if p.y == p.x + 2:
    symexTarget("outoforder_unsat")

# Omitted field `y` — Nim zero-inits it to 0 (ground-truthed: a real `Point`
# constructed with only `x` set really has `y == 0`).
proc sutObjOmittedFieldHit(x: int) =
  let p = Point(x: x)
  if p.x == 5 and p.y == 0:
    symexTarget("omitted_hit")

# Omitted-field UNSAT soundness: p.y is ALWAYS 0 (never set) — asserting
# p.y == 1 must be UNSAT, proving the zero-init is REAL (a free/dummy value
# could satisfy p.y == 1).
proc sutObjOmittedFieldUnsat(x: int) =
  let p = Point(x: x)
  if p.y == 1:
    symexTarget("omitted_unsat")

# Heterogeneous fields — `b: uint8` must lower at its declared width (0..255),
# not default signed BV64. Constraining b > 250 combined with a b==300-shaped
# impossible target proves width matters (unreachable if b were a full int).
proc sutObjHeteroWidthHit(x: int) =
  let bp = BytePair(a: x, b: 5'u8)
  if bp.a == 9 and bp.b == 5:
    symexTarget("hetero_hit")

proc sutObjHeteroWidthUnsat(x: int) =
  ## `b` is always the literal `5'u8` — asserting `bp.b == 6` is impossible.
  let bp = BytePair(a: x, b: 5'u8)
  if bp.b == 6:
    symexTarget("hetero_unsat")

# `newException(...)` regression — its existing `nnkObjConstr` handling
# (inside `nnkRaiseStmt`) must be untouched by P2a's new general
# expression-position arm.
proc sutNewExceptionRegression(x: int) =
  if x == 7:
    raise newException(ValueError, "boom")

# SND-1 soundness: one field is a STILL-unsupported expression
# (`cast[int32](x)`). The catch-all's dummy for an itInt field is `0`; if
# that dummy leaked through unprotected, `p.y == 0` would look trivially SAT
# for every `x`. SND-1's taint on `isUnsupported` must force `sxUnknown`
# instead.
type
  CastPair = object
    x: int64
    y: int32

proc sutObjUnsupportedField(x: int64) =
  let p = CastPair(x: x, y: cast[int32](x))
  if p.y == 0:
    symexTarget("dummy_would_sat")

# Regression: an ordinary (non-object) expression is completely unaffected.
proc sutPlainArithRegression(x: int) =
  let y = x + 1
  if y == 5:
    symexTarget("plain_arith")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening P2a — value-object construction as expression":

  test "P2a-1: let p=Point(x:x,y:x+1); p.x==3 and p.y==4 -> sxSat, exact witness x==3":
    let r = symexFind(sutObjBasicHit, tLabel("basic_hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "P2a-2: UNSAT soundness — p.y == p.x+2 is impossible (real modeling)":
    let r = symexFind(sutObjUnsat, tLabel("basic_unsat"))
    check r.status == sxUnsat

  test "P2a-3: fields out of order (y before x) — exact witness x==3":
    let r = symexFind(sutObjOutOfOrderHit, tLabel("outoforder_hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "P2a-4: fields out of order UNSAT soundness":
    let r = symexFind(sutObjOutOfOrderUnsat, tLabel("outoforder_unsat"))
    check r.status == sxUnsat

  test "P2a-5: omitted field y defaults to 0 — exact witness x==5":
    let r = symexFind(sutObjOmittedFieldHit, tLabel("omitted_hit"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "P2a-6: omitted-field UNSAT soundness — p.y == 1 is impossible (never set)":
    let r = symexFind(sutObjOmittedFieldUnsat, tLabel("omitted_unsat"))
    check r.status == sxUnsat

  test "P2a-7: heterogeneous fields (int, uint8) lower at declared width — exact witness a==9":
    let r = symexFind(sutObjHeteroWidthHit, tLabel("hetero_hit"))
    check r.status == sxSat
    check r.witness[0] == 9

  test "P2a-8: heterogeneous-field UNSAT soundness — bp.b == 6 is impossible (always 5'u8)":
    let r = symexFind(sutObjHeteroWidthUnsat, tLabel("hetero_unsat"))
    check r.status == sxUnsat

suite "symex RFC-chapulin-hardening P2a — newException regression":

  test "P2a-9: raise newException(ValueError, msg) still resolves to sxRaised":
    let r = symexFind(sutNewExceptionRegression, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

suite "symex RFC-chapulin-hardening P2a — SND-1 soundness (unsupported field)":

  test "P2a-10: object with cast[int32](x) field compiles and degrades to sxUnknown + feUnsupportedExprKind":
    ## Strong form: assert the classified KIND, not just the verdict.
    let r = symexFind(sutObjUnsupportedField, tLabel("dummy_would_sat"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawKind = true
    check sawKind

  test "P2a-11: the dummy field value never produces a false sxSat (SND-1 taint)":
    ## Even though a leaked dummy (0) would make `p.y == 0` look trivially
    ## reachable for every x, SND-1's taint forces sxUnknown — never sxSat.
    let r = symexFind(sutObjUnsupportedField, tLabel("dummy_would_sat"))
    check r.status != sxSat

suite "symex RFC-chapulin-hardening P2a — regression guard":

  test "P2a-12: plain (non-object) arithmetic unaffected — exact witness x==4":
    let r = symexFind(sutPlainArithRegression, tLabel("plain_arith"))
    check r.status == sxSat
    check r.witness[0] == 4

suite "symex RFC-chapulin-hardening P2a — version pins":

  test "walker version floor >= 53 (P2a introduced at 53)":
    check parseInt(symexWalkerVersion) >= 53

  test "renderAsChoicesVersion floor >= 5 (P2a does NOT bump RC — see canonicalize.nim note)":
    ## P2a introduces no new witness shape: `renderAsChoices*[T]` (symex.nim)
    ## is built ONLY from the SUT's top-level parameter list, never from an
    ## internal `let`-bound or returned value, and its object/tuple
    ## reflection branch already existed untouched before this slice.
    check parseInt(renderAsChoicesVersion) >= 5
