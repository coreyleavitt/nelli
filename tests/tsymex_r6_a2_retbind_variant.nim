## Round-6 A2 — `retBindEq` svVariant arm: the GENERAL encoding.
##
## ADR-0029 (`docs/SYMEX_PLAN.md`). A1 (walker v75) landed `iekVariantLit`
## construction; the `retBindEq` binding that links a call's fresh `retSym`
## placeholder to what a variant-returning callee actually returns was still
## unwired (falls through `retBindEq`'s composite catch-all, degrading the
## caller's path to classified `sxUnknown`). A2 wires it with the GENERAL
## encoding the ADR specifies:
##
##   discEq ∧ (⋀ over declared arms: (disc == tag) → per-field eq for that
##   arm) ∧ plain-field eq
##
## This must be sound for BOTH a freshly-pinned literal construction (A1's
## `iekVariantLit` — "active arm" is host-selectable there) AND a
## pass-through return of a variant-typed PARAMETER, where the discriminator
## reaching `retBindEq` is genuinely symbolic and no arm is distinguished at
## bind time — the per-arm IMPLICATION guard is what keeps the encoding
## sound in that case (an unguarded all-arms-equated encoding would be
## unsound: it would force every arm's fields equal even for arms the
## discriminant never selects).
##
## Bumps `symexWalkerVersion` 75->76: verdict-surface change (previously
## `sxUnknown` variant-returning callees now resolve to real `sxSat`/
## `sxUnsat`).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

type
  ShapeKind = enum skCircle, skSquare
  Shape = object
    tag: int                       ## plain field, shared across arms
    case kind: ShapeKind
    of skCircle: radius: int
    of skSquare: side: int

# --- Test 1: tracer — callee constructs (literal disc, A1 machinery) and
# returns a variant; caller binds it and constrains the active arm's field --
proc makeCircle(r: int): Shape =
  Shape(kind: skCircle, radius: r, tag: 42)

proc sutCalleeConstructedHit(r: int) =
  let s = makeCircle(r)
  if s.radius == 7 and s.tag == 42:
    symexTarget("callee_circle_radius_7")

# --- Test 2: UNSAT companion — soundness, not a free/unconstrained value ---
proc makeCirclePlusOne(r: range[0 .. 1000]): Shape =
  Shape(kind: skCircle, radius: r + 1, tag: 42)

proc sutCalleeConstructedUnsat(r: range[0 .. 1000]) =
  let s = makeCirclePlusOne(r)
  if s.radius == r:
    symexTarget("callee_radius_unsat")

# --- Test 3: pass-through pin — callee returns its variant PARAM unchanged
# (genuinely symbolic discriminant, no literal to host-select an "active"
# arm from). The general encoding must bind through this shape exactly as
# it binds a literal construction. ------------------------------------------
proc identityShape(s: Shape): Shape = s

proc sutPassThroughFieldMatchSat(s: Shape) =
  ## The bound result's active-arm field, constrained the SAME way as the
  ## param's own field, proves — the pass-through binding threads s's field
  ## through to r's, not just a literal-pinned construction (A1 territory).
  let r = identityShape(s)
  if s.kind == skCircle and r.kind == skCircle and s.radius == 5 and r.radius == 5:
    symexTarget("passthrough_field_match")

proc sutPassThroughFieldMismatchUnsat(s: Shape) =
  ## Soundness companion: r IS s (identity pass-through), so if the field
  ## binding is genuinely wired (not a vacuous/unconstrained retSym), this
  ## contradictory pair — same arm, different literal values — must be
  ## unreachable exactly as it would be constraining s twice directly.
  let r = identityShape(s)
  if s.kind == skCircle and r.kind == skCircle and s.radius == 5 and r.radius == 6:
    symexTarget("passthrough_field_mismatch")

# --- Test 4: guarded-arm soundness — the shape a naive UNGUARDED
# all-arms-equated (or disc-unlinked) encoding would get wrong. -------------
proc sutGuardedDiscMismatchUnsat(s: Shape) =
  ## r IS s (identity), so r's discriminant can NEVER take a different tag
  ## than s's — this is only true if `discEq` genuinely links retSym's
  ## disc back to the callee's returned disc. An encoding that dropped (or
  ## mis-wired) that link would let r's disc float free of s's, making this
  ## falsely reachable.
  let r = identityShape(s)
  if s.kind == skCircle and r.kind == skSquare:
    symexTarget("guarded_disc_mismatch")

proc sutGuardedCircleArmReachable(s: Shape) =
  ## Companion positive pin (paired with the Square arm below): EACH arm's
  ## field must bind to its OWN source field under its OWN guard — a
  ## partial/hardcoded guard (e.g. one that only wires the first declared
  ## arm) would make this arm's bind wrong or unreachable.
  let r = identityShape(s)
  if r.kind == skCircle and r.radius == 7:
    symexTarget("guarded_circle_reachable")

proc sutGuardedSquareArmReachable(s: Shape) =
  let r = identityShape(s)
  if r.kind == skSquare and r.side == 11:
    symexTarget("guarded_square_reachable")

# --- Test 5: plain-field (non-case field) equation — the `∧ plain-field eq`
# conjunct, unconditional (no disc guard, shared across every arm). --------
proc sutPlainFieldBindsUnconditionally(s: Shape) =
  ## `tag` is a plain field: present and equated regardless of which arm is
  ## active — constraining it on the bound result alone (no disc guard
  ## needed) must prove.
  let r = identityShape(s)
  if r.tag == 99:
    symexTarget("plain_field_binds")

suite "symex round-6 A2 — retBindEq svVariant general encoding":

  test "A2-1: callee constructs Shape(kind: skCircle, radius: r); r==7 reachable -> sxSat, witness r==7":
    let res = symexFind(sutCalleeConstructedHit, tLabel("callee_circle_radius_7"))
    check res.status == sxSat
    check res.witness[0] == 7

  test "A2-2: UNSAT companion — callee's returned s.radius is always r+1, s.radius==r is impossible":
    let res = symexFind(sutCalleeConstructedUnsat, tLabel("callee_radius_unsat"))
    check res.status == sxUnsat

  test "A2-3a: pass-through param, symbolic disc — matching field constraint on the bound result -> sxSat":
    let res = symexFind(sutPassThroughFieldMatchSat, tLabel("passthrough_field_match"))
    check res.status == sxSat

  test "A2-3b: pass-through UNSAT companion — mismatched field constraint on the SAME identity is impossible":
    let res = symexFind(sutPassThroughFieldMismatchUnsat, tLabel("passthrough_field_mismatch"))
    check res.status == sxUnsat

  test "A2-4a: guarded-arm soundness — r's disc can never diverge from s's through pure identity -> sxUnsat":
    let res = symexFind(sutGuardedDiscMismatchUnsat, tLabel("guarded_disc_mismatch"))
    check res.status == sxUnsat

  test "A2-4b: guarded-arm soundness — the Circle arm binds correctly through pass-through -> sxSat, witness radius==7":
    let res = symexFind(sutGuardedCircleArmReachable, tLabel("guarded_circle_reachable"))
    check res.status == sxSat
    check res.witness[0].kind == skCircle
    check res.witness[0].radius == 7

  test "A2-4c: guarded-arm soundness — the OTHER (Square) arm ALSO binds correctly, independently -> sxSat, witness side==11":
    let res = symexFind(sutGuardedSquareArmReachable, tLabel("guarded_square_reachable"))
    check res.status == sxSat
    check res.witness[0].kind == skSquare
    check res.witness[0].side == 11

  test "A2-5: plain (non-case) field binds unconditionally through the pass-through, no disc guard needed -> sxSat, witness tag==99":
    let res = symexFind(sutPlainFieldBindsUnconditionally, tLabel("plain_field_binds"))
    check res.status == sxSat
    check res.witness[0].tag == 99

suite "symex round-6 A2 — walker version pin":

  test "walker version floor >= 76 (retBindEq svVariant general encoding)":
    check parseInt(symexWalkerVersion) >= 76
