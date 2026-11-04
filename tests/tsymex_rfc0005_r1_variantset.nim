## RFC-0005 review R1-13 -- a variant field write after a declined
## constructor.
##
## `lowerVariantFieldSet` (`v.f = x` on a value variant) keeps the old value
## when the receiver has no slot for `f`: a construction that already
## declined bound a non-variant stand-in. It recorded that dropped write as
## `seVariantFieldOnDeclinedCtor`, a HALT kind (`dcOmitted`, no path taint),
## although the path goes on without the write. It now records
## `feUnsupportedOp` (`dcSubstituted`), the kind every other dropped write
## records, so the path that goes on carries the taint itself.
##
## No program was found that reaches the write on a clean path: every
## constructor that binds the stand-in declines first, with
## `feUnsupportedExprKind` (`dcNoAnswer`), which taints the path with both
## bits. The rows pin that the write after such a constructor never
## produces a clean verdict, and that an `else`-covered tag, which the walk
## now builds, decides.
import std/[unittest]
import nelli
import nelli/symex
import ./s8cu_helpers

type
  K = enum ka, kb, kc
  V = object
    tag: int
    case kind: K
    of ka: a: int
    else: b: int

proc elseCtorWrite(x: int) =
  var v = V(kind: kc, b: 1)
  v.tag = x
  if v.tag == 7: symexTarget("hit")

# The discriminator omitted (Nim defaults it): the A1 missing-discriminant
# decline binds a non-variant stand-in.
proc noDiscWrite(x: int) =
  var v = V(tag: 1)
  v.tag = x
  if v.tag == 7: symexTarget("hit")

suite "R1-13: a variant field write after a declined constructor":

  test "an else-covered tag decides":
    check native(elseCtorWrite(7)) == "hit"
    decides(elseCtorWrite, sxSat)

  test "the write after a constructor with no discriminator":
    check native(noDiscWrite(7)) == "hit"
    let r = symexFind(noDiscWrite, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feUnsupportedExprKind)
