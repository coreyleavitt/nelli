## The typed choice-sequence IR.
##
## A `ChoiceNode` is one recorded primitive draw: the value plus the constraints
## it was drawn under. The shrinker and example database operate on sequences of
## these. Kinds and their constraint fields are added as their behaviors are
## driven out by tests, rather than all up front.

import std/[math, unicode, hashes]
import ./int128

type
  ChoiceInt* = Int128
    ## Value domain of the integer primitive (see `int128`).

  ChoiceKind* = enum
    ckInteger, ckFloat, ckBoolean, ckBytes, ckString

  IntConstraints* = object
    min*, max*, shrinkTowards*: ChoiceInt

  BoolConstraints* = object
    p*: float  ## P(true); p=0 forces false, p=1 forces true

  FloatConstraints* = object
    min*, max*: float64                ## inclusive bounds
    allowNan*: bool                    ## whether NaN is a legal draw
    smallestNonzeroMagnitude*: float64 ## nonzero values with |v| below this are illegal

  BytesConstraints* = object
    minSize*, maxSize*: int  ## inclusive byte-length bounds

  IntervalSet* = object
    ## A set of allowed Unicode codepoints as inclusive ranges.
    ranges*: seq[tuple[lo, hi: int32]]

  StringConstraints* = object
    intervals*: IntervalSet  ## codepoints a character may take
    minSize*, maxSize*: int  ## inclusive bounds, counted in codepoints (not bytes)

  ChoiceNode* = object
    wasForced*: bool  ## value was forced (not drawn) and therefore cannot shrink
    case kind*: ChoiceKind
    of ckInteger:
      intVal*: ChoiceInt
      intC*: IntConstraints
    of ckFloat:
      floatVal*: float64
      floatC*: FloatConstraints
    of ckBoolean:
      boolVal*: bool
      boolC*: BoolConstraints
    of ckBytes:
      bytesVal*: seq[byte]
      bytesC*: BytesConstraints
    of ckString:
      strVal*: string
      strC*: StringConstraints

func permits*(c: IntConstraints, v: ChoiceInt): bool =
  ## Whether `v` lies within the closed interval the integer was drawn under.
  ## This is the legality predicate the shrinker relies on: a shrunk value is
  ## only a candidate if its constraints still permit it.
  c.min <= v and v <= c.max

func permits*(c: BoolConstraints, v: bool): bool =
  ## Boundary guarantee: p<=0 admits only false, p>=1 only true, otherwise both.
  ## Dependent generators rely on the p=0/p=1 endpoints being honored exactly.
  if c.p <= 0.0: v == false
  elif c.p >= 1.0: v == true
  else: true

func permits*(c: FloatConstraints, v: float64): bool =
  ## NaN is guarded first (it has no ordering); finite/inf values must lie in
  ## [min,max]; nonzero values below `smallestNonzeroMagnitude` are illegal,
  ## but ±0 always passes (its magnitude is 0, not "below smallest").
  if v != v:  # NaN
    return c.allowNan
  if v < c.min or v > c.max:
    return false
  if v != 0.0 and abs(v) < c.smallestNonzeroMagnitude:
    return false
  true

func permits*(c: BytesConstraints, v: seq[byte]): bool =
  v.len >= c.minSize and v.len <= c.maxSize

func intervals*(rs: openArray[(int32, int32)]): IntervalSet =
  ## Build an interval set from inclusive `(lo, hi)` codepoint ranges.
  for r in rs:
    result.ranges.add (lo: r[0], hi: r[1])

func contains*(s: IntervalSet, cp: int32): bool =
  for r in s.ranges:
    if cp >= r.lo and cp <= r.hi:
      return true
  false

func permits*(c: StringConstraints, v: string): bool =
  ## Length is measured in codepoints (not bytes); every codepoint must fall
  ## within the allowed intervals.
  let n = v.runeLen
  if n < c.minSize or n > c.maxSize:
    return false
  for r in v.runes:
    if int32(r) notin c.intervals:
      return false
  true

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

func floatChoice*(value, min, max: float64, allowNan: bool,
                  smallestNonzeroMagnitude: float64, forced = false): ChoiceNode =
  ## Construct a float choice node.
  ChoiceNode(
    wasForced: forced,
    kind: ckFloat,
    floatVal: value,
    floatC: FloatConstraints(min: min, max: max, allowNan: allowNan,
                             smallestNonzeroMagnitude: smallestNonzeroMagnitude))

func booleanChoice*(value: bool, p: float, forced = false): ChoiceNode =
  ChoiceNode(wasForced: forced, kind: ckBoolean, boolVal: value,
             boolC: BoolConstraints(p: p))

func bytesChoice*(value: seq[byte], minSize, maxSize: int,
                  forced = false): ChoiceNode =
  ChoiceNode(wasForced: forced, kind: ckBytes, bytesVal: value,
             bytesC: BytesConstraints(minSize: minSize, maxSize: maxSize))

func stringChoice*(value: string, intervals: IntervalSet, minSize, maxSize: int,
                   forced = false): ChoiceNode =
  ChoiceNode(wasForced: forced, kind: ckString, strVal: value,
             strC: StringConstraints(intervals: intervals, minSize: minSize,
                                     maxSize: maxSize))

func floatBitsEq(a, b: float64): bool =
  ## Bit-pattern equality: NaN equals NaN (same bits), +0.0 differs from -0.0.
  ## The engine's dedup/novelty tracking needs this, not semantic float `==`.
  cast[uint64](a) == cast[uint64](b)

func `==`*(a, b: FloatConstraints): bool =
  floatBitsEq(a.min, b.min) and floatBitsEq(a.max, b.max) and
    a.allowNan == b.allowNan and
    floatBitsEq(a.smallestNonzeroMagnitude, b.smallestNonzeroMagnitude)

func `==`*(a, b: ChoiceNode): bool =
  ## Two nodes are the same recorded draw iff same kind, forced flag, value, and
  ## constraints. Float values/constraints compare bitwise (see `floatBitsEq`);
  ## variant objects have no usable auto-generated `==`, so this is hand-written.
  if a.kind != b.kind or a.wasForced != b.wasForced:
    return false
  case a.kind
  of ckInteger: a.intVal == b.intVal and a.intC == b.intC
  of ckFloat:   floatBitsEq(a.floatVal, b.floatVal) and a.floatC == b.floatC
  of ckBoolean: a.boolVal == b.boolVal and a.boolC == b.boolC
  of ckBytes:   a.bytesVal == b.bytesVal and a.bytesC == b.bytesC
  of ckString:  a.strVal == b.strVal and a.strC == b.strC

func hash*(n: ChoiceNode): Hash =
  ## Consistent with `==`: equal nodes hash equally. Floats are hashed by bit
  ## pattern (matching `floatBitsEq`), so NaN nodes with identical bits collide
  ## and ±0 do not.
  var h: Hash = 0
  h = h !& hash(n.kind) !& hash(n.wasForced)
  case n.kind
  of ckInteger:
    h = h !& hash(n.intVal) !& hash(n.intC.min) !& hash(n.intC.max) !&
        hash(n.intC.shrinkTowards)
  of ckFloat:
    h = h !& hash(cast[uint64](n.floatVal)) !& hash(cast[uint64](n.floatC.min)) !&
        hash(cast[uint64](n.floatC.max)) !& hash(n.floatC.allowNan) !&
        hash(cast[uint64](n.floatC.smallestNonzeroMagnitude))
  of ckBoolean:
    h = h !& hash(n.boolVal) !& hash(n.boolC.p)
  of ckBytes:
    h = h !& hash(n.bytesVal) !& hash(n.bytesC.minSize) !& hash(n.bytesC.maxSize)
  of ckString:
    h = h !& hash(n.strVal) !& hash(n.strC.intervals.ranges) !&
        hash(n.strC.minSize) !& hash(n.strC.maxSize)
  !$h
