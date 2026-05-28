## The typed choice-sequence IR.
##
## A `ChoiceNode` is one recorded primitive draw: the value plus the constraints
## it was drawn under. The shrinker and example database operate on sequences of
## these. Kinds and their constraint fields are added as their behaviors are
## driven out by tests, rather than all up front.

import ./int128

type
  ChoiceInt* = Int128
    ## Value domain of the integer primitive (see `int128`).

  ChoiceKind* = enum
    ckInteger

  IntConstraints* = object
    min*, max*, shrinkTowards*: ChoiceInt

  ChoiceNode* = object
    wasForced*: bool  ## value was forced (not drawn) and therefore cannot shrink
    case kind*: ChoiceKind
    of ckInteger:
      intVal*: ChoiceInt
      intC*: IntConstraints

func permits*(c: IntConstraints, v: ChoiceInt): bool =
  ## Whether `v` lies within the closed interval the integer was drawn under.
  ## This is the legality predicate the shrinker relies on: a shrunk value is
  ## only a candidate if its constraints still permit it.
  c.min <= v and v <= c.max

func integerChoice*[T: SomeInteger](value, min, max, shrinkTowards: T,
                                    forced = false): ChoiceNode =
  ## Construct an integer choice node from native integers. `shrinkTowards` is a
  ## hint and is clamped into `[min, max]`, so an out-of-range hint means "shrink
  ## toward the nearest bound."
  let lo = toInt128(min)
  let hi = toInt128(max)
  ChoiceNode(
    wasForced: forced,
    kind: ckInteger,
    intVal: toInt128(value),
    intC: IntConstraints(min: lo, max: hi,
                         shrinkTowards: clamp(toInt128(shrinkTowards), lo, hi)))
