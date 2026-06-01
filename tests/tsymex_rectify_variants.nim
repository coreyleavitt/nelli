## Rectify #141 — variant (case) objects.
##
## Modelled as `svTuple` with the discriminator + all-variant fields
## as parallel members. A constraint links discriminator-value to
## which variant fields are observable; witness extraction picks the
## right variant based on the discriminator's solved value.
import std/unittest
import proptest/symex

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
  if s.kind == skCircle and s.radius > 100:
    symexTarget("big-circle")

suite "symex variant objects #141":
  test "enum-typed param dispatch":
    let r = symexFind(isRed, tLabel("hit-red"))
    check r.status == sxSat
    check r.witness[0] == ord(red).uint8

  test "variant object — discriminator + variant field reachable":
    let r = symexFind(isLargeCircle, tLabel("big-circle"))
    check r.status == sxSat
    # The flat-tuple witness exposes discriminator + all variant fields;
    # downstream code can dispatch on the discriminator. Variant-aware
    # witness construction (yielding `Shape(kind: skCircle, radius: …)`)
    # lands as a follow-up if a consumer needs it.
