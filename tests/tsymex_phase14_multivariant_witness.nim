## Phase 14 cycle A1d — witness emitter for `itMultiVariant`.
##
## A1a left `emitTyAndReader` returning `default(ObjectName)` for
## multi-axis objects: it compiles, but the symex witness
## doesn't reflect what Z3 actually picked. A1d replaces the stub
## with nested case statements (outer `case axis1`, inner
## `case axis2` per axis-1 arm) that read each axis-disc + active-
## arm fields at the SAME witness paths `extractFromSymVal`
## writes (`<base>.<discName>` and `<base>.<discName>.@<tagOrd>.<f>`).
##
## RFC critical invariant: the constructed object, fed through
## `fields(w)`, MUST yield choices in the same order that
## `renderAsChoices` will later emit them — disc1, arm1 fields,
## disc2, arm2 fields. Otherwise the seed-replay path silently
## corrupts witnesses.
import std/unittest
import proptest/symex
import proptest/smt/types
import proptest/choice
import proptest/int128

type
  KindA = enum kaX, kaY
  KindB = enum kbP, kbQ
  TwoAxis = object
    case axis1: KindA
    of kaX: a1: int
    of kaY: a2: int
    case axis2: KindB
    of kbP: b1: int
    of kbQ: b2: int

proc gatedTwoAxis(obj: TwoAxis) =
  # Force the only SAT witness: axis1 = kaX (so `a1` is live),
  # a1 == 42, axis2 = kbQ (so `b2` is live), b2 == 7. Z3 has no
  # other path that reaches the target.
  # Phase 16 D1c: restored flat-and chain; D1c short-circuit prevents
  # spurious FieldDefect forks from arm-field accesses guarded by disc checks.
  if obj.axis1 == kaX and obj.a1 == 42 and
     obj.axis2 == kbQ and obj.b2 == 7:
    symexTarget("pinned-witness")

suite "symex Phase 14 cycle A1d — multi-axis witness emitter":
  test "witness reflects per-axis tags + arm fields chosen by Z3":
    let r = symexFind(gatedTwoAxis, tLabel("pinned-witness"))
    check r.status == sxSat
    let w = r.witness[0]
    check w.axis1 == kaX
    check w.a1 == 42
    check w.axis2 == kbQ
    check w.b2 == 7

  test "renderAsChoices yields choices in fields(w) order":
    # RFC A1d critical invariant: rendering the constructed witness
    # via `renderAsChoices` (which uses Nim's `fields(w)` iterator —
    # symex.nim ~115-122 for objects) must produce choices in the
    # same order in which the choice sequence will be replayed by
    # any consumer. For TwoAxis with axis1=kaX and axis2=kbQ,
    # active-arm fields(w) order is: axis1, a1, axis2, b2 — 4
    # choices total, with the disc choices at positions 0 and 2
    # holding their enum ordinals.
    let r = symexFind(gatedTwoAxis, tLabel("pinned-witness"))
    check r.status == sxSat
    let choices = renderAsChoices(r.witness[0])
    check choices.len == 4
    # Position 0 is axis1, position 2 is axis2 — both rendered as
    # integerChoice with the enum ordinal as the value.
    check choices[0].kind == ckInteger
    check choices[0].intVal == toInt128(ord(kaX))
    check choices[2].kind == ckInteger
    check choices[2].intVal == toInt128(ord(kbQ))
    check choices[1].kind == ckInteger
    check choices[1].intVal == toInt128(42)
    check choices[3].kind == ckInteger
    check choices[3].intVal == toInt128(7)
