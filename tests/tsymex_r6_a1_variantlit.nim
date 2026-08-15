## Round-6 A1 — `iekVariantLit`: literal-discriminant variant construction.
##
## ADR-0029 (`docs/SYMEX_PLAN.md`). Before this slice, `dsl_parser.nim`'s
## `nnkObjConstr` arm declined EVERY variant-object constructor (both
## `itVariant` single-discriminator and `itMultiVariant` multi-`case`
## shapes) through one combined `of itVariant, itMultiVariant:` arm (P2b) —
## the field-split heap's `heRefVariantUnsupported` justification for that
## decline never actually applied to VALUE (non-ref) variant construction,
## which builds an ordinary `svVariant` the same way `allocateSym(itVariant)`
## already does for a top-level param. A1 SPLITS that combined arm: a
## LITERAL-discriminant `itVariant` constructor now builds a real
## `svVariant` (the discriminator PINNED to the literal tag — a Z3 CONST,
## not a fresh symbol with a disjunction constraint — with the active arm's
## fields taken from the parsed constructor exprs and every OTHER arm
## allocated FRESH-UNCONSTRAINED, per the ADR's soundness note: real Nim
## raises `FieldDefect` on an out-of-arm read before any value is
## observable, so a zero-filled inactive field would let a buggy twin
## "read" a value real Nim never yields — reading one is a FINDING via the
## existing `isVariantField` fork, not a modeling gap).
##
## Kept declining cleanly (classified `sxUnknown`, never a crash):
##   * `itMultiVariant` (multi-`case` object) construction — its own
##     retained `of itMultiVariant:` arm, message updated to cite this
##     ADR's "ships as its own slice only if a consumer needs it first".
##   * A SYMBOLIC discriminant at a construction site — fork-per-tag
##     construction is A3's job (`isVariantConstructSym`), not A1's.
##   * A ref-object-ALIASED variant constructor (`VNode = ref object; case
##     kind: ...`) — `classifyType` collapses it to the SAME `itVariant`
##     IRType as a plain value object (ADR-0022 sub-decision #1: variant
##     ref objects stay value-modeled everywhere), so A1 detects the
##     ref-alias directly on the constructor's callee type symbol (mirrors
##     `dsl_typebridge.classifyType`'s own `impl[2].kind in {nnkRefTy,
##     nnkPtrTy}` detection) to keep this ADR-0029 "deliberately not
##     covered" shape excluded — the pre-existing `tsymex_p2b_
##     refobjconstr_expr.nim` P2b-13 pin (`sutVariantConstr`) must stay
##     green, unaffected by this slice.
##
## Bumps `symexWalkerVersion` 74->75: verdict-surface change (previously
## `sxUnknown` value-variant constructors now resolve to real `sxSat`/
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

  KindA = enum kaX, kaY
  KindB = enum kbP, kbQ
  TwoAxis = object                 ## itMultiVariant (two `nnkRecCase` axes)
    case axis1: KindA
    of kaX: a1: int
    of kaY: a2: int
    case axis2: KindB
    of kbP: b1: int
    of kbQ: b2: int

  RVKind = enum rvA, rvB
  RVNode = ref object               ## ref-aliased variant (ADR-0022 D#1 shape)
    case kind: RVKind
    of rvA: a: int
    of rvB: b: int

# --- Test 1: construct + read the active arm's field (+ a plain shared
# field, exercising both the arm-field and plain-field construction paths) -
proc sutCircleRadiusHit(r: int) =
  let s = Shape(kind: skCircle, radius: r, tag: 42)
  if s.radius == 7 and s.tag == 42:
    symexTarget("circle_radius_7")

# --- Test 2: UNSAT companion (soundness — not a free/unconstrained value) -
proc sutCircleRadiusUnsat(r: range[0 .. 1000]) =
  let s = Shape(kind: skCircle, radius: r + 1)
  if s.radius == r:
    symexTarget("circle_radius_unsat")

# --- Test 3: a constraint on the constructed discriminant ITSELF proves --
proc sutCircleDiscProves(r: int) =
  let s = Shape(kind: skCircle, radius: r)
  if s.kind != skCircle:
    symexTarget("disc_mismatch_unreachable")

# --- Test 4: the OTHER active arm ----------------------------------------
proc sutSquareSideHit(sd: int) =
  let s = Shape(kind: skSquare, side: sd)
  if s.side == 11:
    symexTarget("square_side_11")

# --- Test 5: itMultiVariant construction — mandatory regression pin ------
proc sutMultiVariantConstrDeclines(x: int) =
  let t = TwoAxis(axis1: kaX, a1: x, axis2: kbP, b1: x)
  if t.a1 == 3:
    symexTarget("multivariant_hit")

# --- Test 6 (bonus, trivial): symbolic discriminant at construction ------
# Nim itself only accepts a RUNTIME discriminant in constructor syntax when
# no arm-specific field is set (it cannot prove which arm's storage is safe
# to initialize otherwise) — so this SUT sets only the plain `tag` field,
# the Nim-legal shape ADR-0029 cites for `protocol.nim:166`'s symbolic-disc
# constructor (there, only fields common to the branch-narrowed tag set).
proc sutSymbolicDiscDeclines(k: ShapeKind, t: int) =
  let s = Shape(kind: k, tag: t)
  if s.tag == 7:
    symexTarget("symbolic_disc_reached")

# --- Test 7 (bonus): ref-aliased variant constructor stays excluded ------
proc sutRefVariantConstrDeclines(x: int) =
  let v = RVNode(kind: rvA, a: x)
  if v.a == 3:
    symexTarget("ref_variant_hit")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex round-6 A1 — iekVariantLit literal-discriminant construction":

  test "A1-1: Shape(kind: skCircle, radius: r); r==7 reachable -> sxSat, witness r==7":
    let res = symexFind(sutCircleRadiusHit, tLabel("circle_radius_7"))
    check res.status == sxSat
    check res.witness[0] == 7

  test "A1-2: UNSAT companion — s.radius is always r+1, s.radius==r is impossible":
    let res = symexFind(sutCircleRadiusUnsat, tLabel("circle_radius_unsat"))
    check res.status == sxUnsat

  test "A1-3: the constructed discriminant equals the literal tag — s.kind != skCircle is unreachable":
    let res = symexFind(sutCircleDiscProves, tLabel("disc_mismatch_unreachable"))
    check res.status == sxUnsat

  test "A1-4: the OTHER active arm — Shape(kind: skSquare, side: sd); sd==11 -> sxSat":
    let res = symexFind(sutSquareSideHit, tLabel("square_side_11"))
    check res.status == sxSat
    check res.witness[0] == 11

suite "symex round-6 A1 — itMultiVariant construction regression pin":

  test "A1-5: multi-case-object constructor still declines cleanly — classified sxUnknown, not a crash":
    let res = symexFind(sutMultiVariantConstrDeclines, tLabel("multivariant_hit"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    for e in res.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        hasClassified = true
    check hasClassified

suite "symex round-6 A1 — out-of-scope shapes keep declining cleanly":

  test "A1-6: a SYMBOLIC discriminant at construction declines cleanly (A3 territory, not A1)":
    let res = symexFind(sutSymbolicDiscDeclines, tLabel("symbolic_disc_reached"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    for e in res.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        hasClassified = true
    check hasClassified

  test "A1-7: a ref-aliased variant constructor stays excluded (ADR-0029 'deliberately not covered')":
    let res = symexFind(sutRefVariantConstrDeclines, tLabel("ref_variant_hit"))
    check res.status == sxUnknown
    check res.status != sxSat

suite "symex round-6 A1 — walker version pin":

  test "walker version floor >= 75 (iekVariantLit literal-discriminant construction)":
    check parseInt(symexWalkerVersion) >= 75
