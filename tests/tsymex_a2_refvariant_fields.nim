## A2 Slice 2 (ADR-0013) — arm-specific field READ + FieldDefect + full witness
## through a ref-to-variant pointee.
##
## Slice 1 modelled the discriminant (and plain fields) of an `itVariant`
## pointee behind a `ref`/`ptr`; arm-specific field reads (`p.<armField>`) still
## raised `SymexRefVariantUnsupportedError` → `sxUnknown`. Slice 2 lifts that:
## `isDeref` now materialises the disc heap, FieldDefect-forks the out-of-arm
## side (D1a, mirroring the value-variant `isVariantField` arm) and binds an
## ite-chain over the matching arms' per-(arm,field) heaps. The witness
## serializer (D5, `currentVariantHeaps`) emits the active arm's observed
## fields.
##
## RED before Slice 2 (walker v27): every arm-field read below raised the
## deferred error → `sxUnknown` (so the SAT tests were `sxUnknown`, not `sxSat`,
## and the FieldDefect tests were `sxUnknown`, not `sxRaised`). GREEN at v28.
import std/unittest
import proptest/symex

# ---- bool-discriminant variant: read an ARM field through a ref --------------
type
  VNode = object
    case tag: bool
    of true:  val: int
    of false: other: int

# `p.val` is the `tag == true` arm's field; gated by `p.tag` so the SAT path is
# the in-arm side.
proc readArmField(p: ref VNode) =
  if p.tag and p.val == 42:
    symexTarget("hit")

# Nil-guarded but NOT disc-gated arm-field read: `p.val` with no `tag` gate →
# FieldDefect on the `tag == false` arm. The `p != nil` guard isolates the
# FieldDefect (it short-circuits the NilAccessDefect fork) so the target finds
# the arm-mismatch defect, not a nil deref.
proc wrongArmRead(p: ref VNode) =
  if p != nil:
    let x = p.val
    discard x

# ---- enum-discriminant variant, 3 arms (exercises D4.5 on a NON-bool disc) ---
# A bool disc makes the disc-range disjunction a tautology (Slice 1 could not
# test D4.5). A 3-arm enum disc makes it load-bearing: Z3 must never pick an
# ordinal outside {0,1,2}, so the FieldDefect witness's disc is a LEGAL,
# non-matching arm rather than an impossible ordinal.
type
  Color = enum cRed, cGreen, cBlue
  CNode = object
    case col: Color
    of cRed:   r: int
    of cGreen: g: int
    of cBlue:  b: int

# Disc-gated arm-field read: the SAT path pins `col == cGreen` and `g == 7`.
proc readGreenArm(p: ref CNode) =
  if p.col == cGreen and p.g == 7:
    symexTarget("green")

# Unconditional read of the cGreen-arm field on an enum disc → FieldDefect when
# col != cGreen. The defect witness's disc MUST be a legal ordinal (cRed/cBlue),
# which is exactly the D4.5 disc-range guarantee.
proc enumWrongArm(p: ref CNode) =
  if p != nil:
    let x = p.g
    discard x

# ---- D4.5 multi-address: the disc-range clause must bind EVERY ref-to-variant
# address, not just the FIRST to materialise the per-type disc heap. Two refs of
# the same variant type share ONE disc heap array; `p.col` materialises it and
# `q.col` then finds it already present. If the range disjunction is gated on
# first-materialisation, `q`'s discriminant is left UNCONSTRAINED and Z3 may pick
# an ordinal matching no arm — so the "matches no arm" branch below becomes a
# FALSE POSITIVE (`sxSat`) for a label that is unreachable at runtime. D4.5
# requires the clause per ADDRESS, so this target must be `sxUnsat`.
proc twoNodeNoArm(p: ref CNode, q: ref CNode) =
  if p != nil and q != nil and p.col == cRed and
     q.col != cRed and q.col != cGreen and q.col != cBlue:
    symexTarget("impossible")

suite "A2 Slice 2 — ref-to-variant arm-field read + FieldDefect + witness (v28)":

  test "arm-field read SAT — witness consistent (tag arm, val == 42)":
    let r = symexFind(readArmField, tLabel("hit"))
    check r.status == sxSat
    check not r.witness[0].isNil
    # The in-arm path: the disc selects the `true` arm and the arm field is 42.
    check r.witness[0][].tag == true
    check r.witness[0][].val == 42     ## D5: active-arm field observed value

  test "wrong-arm read — FieldDefect found (disc selects the other arm)":
    let r = symexFind(wrongArmRead, tFieldDefect())
    check r.status == sxRaised
    check r.raisedTypeId == "FieldDefect"
    # Z3 chose the OUT-of-arm side: the disc is NOT the `val`-bearing arm.
    check r.raisedWitness[0][].tag == false

  test "enum-disc arm-field read SAT — witness disc is a LEGAL ordinal (D4.5)":
    let r = symexFind(readGreenArm, tLabel("green"))
    check r.status == sxSat
    check not r.witness[0].isNil
    let node = r.witness[0][]
    # The disc-range mechanism (D4.5) on a 3-arm enum yields a sound witness:
    # the discriminant is a legal ordinal and the in-arm path pins it to cGreen.
    check ord(node.col) >= ord(low(Color))
    check ord(node.col) <= ord(high(Color))
    check node.col == cGreen
    check node.g == 7                  ## D5: active-arm field observed value

  test "enum-disc wrong-arm read — FieldDefect witness disc is a LEGAL non-matching ordinal (D4.5)":
    let r = symexFind(enumWrongArm, tFieldDefect())
    check r.status == sxRaised
    check r.raisedTypeId == "FieldDefect"
    let node = r.raisedWitness[0][]
    # Without the disc-range disjunction Z3 could pick an ordinal matching no arm
    # (an unsound, impossible discriminant). With D4.5 the defect witness's disc
    # is a legal enum ordinal that is simply not the cGreen arm.
    check ord(node.col) >= ord(low(Color))
    check ord(node.col) <= ord(high(Color))
    check node.col != cGreen

  test "D4.5 multi-address — disc-range binds the SECOND ref too (no false positive)":
    # `impossible` is reachable only if `q.col` is an ordinal matching no arm.
    # With the per-address disc-range clause that is UNSAT; without it (range
    # gated on first-materialisation) `q`'s disc is free and the label is a
    # spurious `sxSat` — an Invariant-3 violation.
    let r = symexFind(twoNodeNoArm, tLabel("impossible"))
    check r.status == sxUnsat
