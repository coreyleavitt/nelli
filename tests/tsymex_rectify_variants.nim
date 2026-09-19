## Rectify #141 — variant (case) objects.
##
## History:
##   * Phase 5 cycle (rectify round 2) — variants flat-tuple lowered,
##     witness stubbed as `default(Object)`. This file's
##     `isLargeCircle` test only asserted `r.status == sxSat` because
##     the stub didn't carry meaningful field values.
##   * Phase 11 (cycles 1-10) — variants are first-class `itVariant`,
##     walker forks at arm-field access, witness is constructed via
##     case dispatch. This file is the migration point: every
##     assertion now reflects the new contract.
##
## The plain enum test (Color) stays unchanged — enums classify as
## `itInt(8, unsigned)`, never `itVariant`.
import std/unittest
import nelli/symex

type Color = enum red, green, blue

proc isRed(c: Color) =
  if c == red:
    symexTarget("hit-red")

type
  ShapeKind = enum skCircle, skSquare
  Shape = object
    case kind: ShapeKind
    of skCircle: radius: int
    of skSquare: side: int

proc isLargeCircle(s: Shape) =
  # Phase 16 D1c: restored flat-and form.
  if s.kind == skCircle and s.radius > 100:
    symexTarget("big-circle")

proc isMatchingSquare(s: Shape) =
  # Phase 16 D1c: restored flat-and form.
  if s.kind == skSquare and s.side == 42:
    symexTarget("forty-two-square")

suite "symex variant objects #141 + Phase 11 migration":
  test "enum-typed param dispatch":
    let r = symexFind(isRed, tLabel("hit-red"))
    check r.status == sxSat
    # Issue #163: the witness reader now emits a correctly-typed `Color`
    # value directly (see `IRType.enumName`), so `r.witness[0]` is already
    # `Color` rather than a raw ordinal -- compare via `ord()` instead of
    # a bare uint8 equality.
    check ord(r.witness[0]) == ord(red)

  test "variant — discriminator-gated arm-field constraint reaches target":
    let r = symexFind(isLargeCircle, tLabel("big-circle"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.kind == skCircle
    check s.radius > 100

  test "variant — different arm tag also works (skSquare)":
    let r = symexFind(isMatchingSquare, tLabel("forty-two-square"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.kind == skSquare
    check s.side == 42
