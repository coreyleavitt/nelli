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

const
  maxCodepoint* = 0x10FFFF'i32
    ## Highest Unicode scalar value. `intervals()` validates ranges against
    ## `[0, maxCodepoint]`; out-of-range bounds raise `ValueError`.
  surrogateLo* = 0xD800'i32
  surrogateHi* = 0xDFFF'i32
    ## UTF-16 surrogate block. These are *not* valid Unicode scalar values;
    ## `$Rune(0xD800)` produces ill-formed UTF-8 (CESU-8 encoding), and a
    ## string strategy yielding them would silently corrupt downstream
    ## consumers. `intervals()` rejects any range intersecting `[surrogateLo,
    ## surrogateHi]`.

func intervals*(rs: openArray[(int32, int32)]): IntervalSet =
  ## Build an interval set from inclusive `(lo, hi)` codepoint ranges. Each
  ## range must satisfy `0 <= lo <= hi <= maxCodepoint` *and* must not
  ## intersect the surrogate block `[surrogateLo, surrogateHi]`. Out-of-
  ## range, inverted, or surrogate-touching ranges raise `ValueError`.
  for r in rs:
    if r[0] > r[1]:
      raise newException(ValueError,
        "intervals: inverted range (" & $r[0] & ", " & $r[1] &
        "); lo must be <= hi")
    if r[0] < 0 or r[1] > maxCodepoint:
      raise newException(ValueError,
        "intervals: range (" & $r[0] & ", " & $r[1] &
        ") outside valid codepoint space [0, " & $maxCodepoint & "]")
    # Intersection check: ranges intersect iff `r.lo <= surrogateHi` and
    # `r.hi >= surrogateLo`.
    if r[0] <= surrogateHi and r[1] >= surrogateLo:
      raise newException(ValueError,
        "intervals: range (" & $r[0] & ", " & $r[1] &
        ") intersects the UTF-16 surrogate block [" & $surrogateLo &
        ", " & $surrogateHi & "]; surrogates are not valid Unicode " &
        "scalar values")
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

## **Per-node invariant**: every `ChoiceNode` constructor below validates
## that `value` is admissible under its `constraints`. This is the IR
## invariant the shrinker and replay paths rely on — a recorded sequence
## is only a faithful artifact if each node's value is one the strategy
## could have produced. Constructors raise `ValueError` on violation; the
## engine's `drawXxx` paths feed pre-checked data so the cost is only paid
## on hand-crafted test fixtures and corrupt-DB edge cases.

func integerChoice*[T: SomeInteger](value, min, max, shrinkTowards: T,
                                    forced = false): ChoiceNode =
  ## Construct an integer choice node from native integers. `shrinkTowards`
  ## is a hint and is clamped into `[min, max]`. `value` must be in `[min,
  ## max]` — out-of-range values raise `ValueError`.
  let lo = toInt128(min)
  let hi = toInt128(max)
  let v = toInt128(value)
  let c = IntConstraints(min: lo, max: hi,
                         shrinkTowards: clamp(toInt128(shrinkTowards), lo, hi))
  if not c.permits(v):
    raise newException(ValueError,
      "integerChoice: value " & $v & " not in [" & $lo & ", " & $hi & "]")
  ChoiceNode(wasForced: forced, kind: ckInteger, intVal: v, intC: c)

func floatChoice*(value, min, max: float64, allowNan: bool,
                  smallestNonzeroMagnitude: float64, forced = false): ChoiceNode =
  ## Construct a float choice node. `value` must satisfy `permits(c, value)` —
  ## within `[min, max]`, NaN only if `allowNan`, magnitude above
  ## `smallestNonzeroMagnitude` (or exactly 0); otherwise raises `ValueError`.
  let c = FloatConstraints(min: min, max: max, allowNan: allowNan,
                           smallestNonzeroMagnitude: smallestNonzeroMagnitude)
  if not c.permits(value):
    raise newException(ValueError,
      "floatChoice: value " & $value & " violates constraints " &
      "[" & $min & ", " & $max & "], allowNan=" & $allowNan)
  ChoiceNode(wasForced: forced, kind: ckFloat, floatVal: value, floatC: c)

func booleanChoice*(value: bool, p: float, forced = false): ChoiceNode =
  ## Boolean choice node. A forced p≤0 must have `value = false`; p≥1 must
  ## have `value = true`; otherwise raises `ValueError`. (Unforced boundary
  ## p values still admit only the forced side — that's the contract
  ## `permits` enforces.)
  let c = BoolConstraints(p: p)
  if not c.permits(value):
    raise newException(ValueError,
      "booleanChoice: value " & $value & " violates p=" & $p)
  ChoiceNode(wasForced: forced, kind: ckBoolean, boolVal: value, boolC: c)

func bytesChoice*(value: seq[byte], minSize, maxSize: int,
                  forced = false): ChoiceNode =
  ## Bytes choice node. `value.len` must be in `[minSize, maxSize]`.
  let c = BytesConstraints(minSize: minSize, maxSize: maxSize)
  if not c.permits(value):
    raise newException(ValueError,
      "bytesChoice: length " & $value.len & " not in [" &
      $minSize & ", " & $maxSize & "]")
  ChoiceNode(wasForced: forced, kind: ckBytes, bytesVal: value, bytesC: c)

func stringChoice*(value: string, intervals: IntervalSet, minSize, maxSize: int,
                   forced = false): ChoiceNode =
  ## String choice node. Codepoint length must be in `[minSize, maxSize]` and
  ## every codepoint must lie within `intervals`. Raises `ValueError` on
  ## violation.
  let c = StringConstraints(intervals: intervals, minSize: minSize,
                            maxSize: maxSize)
  if not c.permits(value):
    raise newException(ValueError,
      "stringChoice: value violates codepoint-length [" & $minSize & ", " &
      $maxSize & "] or interval-set constraints")
  ChoiceNode(wasForced: forced, kind: ckString, strVal: value, strC: c)

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

func `$`*(n: ChoiceNode): string =
  ## Compact human-readable form for repro output, e.g. `int(42)`, `bool!(true)`
  ## (the `!` marks a forced, unshrinkable draw).
  let bang = if n.wasForced: "!" else: ""
  case n.kind
  of ckInteger: "int" & bang & "(" & $n.intVal & ")"
  of ckFloat:   "float" & bang & "(" & $n.floatVal & ")"
  of ckBoolean: "bool" & bang & "(" & $n.boolVal & ")"
  of ckBytes:   "bytes" & bang & "(" & $n.bytesVal.len & ")"
  of ckString:  "string" & bang & "(\"" & n.strVal & "\")"
