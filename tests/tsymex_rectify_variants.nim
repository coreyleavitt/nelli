## Rectify #141 — variant (case) objects.
##
## Modelled as `svTuple` with the discriminator + all-variant fields
## as parallel members. A constraint links discriminator-value to
## which variant fields are observable; witness extraction picks the
## right variant based on the discriminator's solved value.
import std/unittest
import proptest/symex

type
  ShapeKind = enum skCircle, skSquare
  Shape = object
    case kind: ShapeKind
    of skCircle: radius: int
    of skSquare: side: int

proc isLargeShape(s: Shape) =
  case s.kind
  of skCircle:
    if s.radius > 100:
      symexTarget("big-circle")
  of skSquare:
    if s.side > 100:
      symexTarget("big-square")

suite "symex variant objects #141":
  test "variant with enum discriminator: big-circle":
    let r = symexFind(isLargeShape, tLabel("big-circle"))
    check r.status == sxSat
    check r.witness[0].kind == skCircle
    check r.witness[0].radius > 100
