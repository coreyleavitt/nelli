## Binary serialization and human-readable rendering of choice sequences.
##
## The binary form is fixed little-endian and full-fidelity: it round-trips an
## entire `seq[ChoiceNode]` (kind, forced flag, value, and constraints) exactly,
## so a stored sequence is a self-describing artifact the example database can
## persist and reload without re-running the generator.

import ./choice, ./binaryio
export binaryio  # internal-only: db.nim and tests reach for these via serialize too

# `putRawBytes` / `getRawBytes` / `putRawStr` / `getRawStr` come straight
# from `binaryio` — each call is bounds-checked at the read side, so any
# truncated input raises `DbCorrupt` rather than `IndexDefect`.

proc putIntervals(buf: var seq[byte], s: IntervalSet) =
  buf.putU64(uint64(s.ranges.len))
  for r in s.ranges:
    buf.putI32(r.lo); buf.putI32(r.hi)
proc getIntervals(data: openArray[byte], pos: var int): IntervalSet =
  # No `safeLen` here — `n` is a 64-bit count of 8-byte interval pairs, not a
  # blob byte length. The per-element reads inside the loop bounds-check
  # themselves, and a hostile `n` that exceeds the remaining buffer fires on
  # the first `getI32` call.
  let n = int(getU64(data, pos))
  for _ in 0 ..< n:
    let lo = getI32(data, pos)
    let hi = getI32(data, pos)
    result.ranges.add (lo: lo, hi: hi)

# --- node codec ---------------------------------------------------------------

proc putNode(buf: var seq[byte], n: ChoiceNode) =
  buf.add byte(ord(n.kind))
  buf.add byte(if n.wasForced: 1 else: 0)
  case n.kind
  of ckInteger:
    buf.putInt128(n.intVal)
    buf.putInt128(n.intC.min)
    buf.putInt128(n.intC.max)
    buf.putInt128(n.intC.shrinkTowards)
  of ckFloat:
    buf.putF64(n.floatVal)
    buf.putF64(n.floatC.min)
    buf.putF64(n.floatC.max)
    buf.putBool(n.floatC.allowNan)
    buf.putF64(n.floatC.smallestNonzeroMagnitude)
  of ckBoolean:
    buf.putBool(n.boolVal)
    buf.putF64(n.boolC.p)
  of ckBytes:
    buf.putRawBytes(n.bytesVal)
    buf.putI64(int64(n.bytesC.minSize))
    buf.putI64(int64(n.bytesC.maxSize))
  of ckString:
    buf.putRawStr(n.strVal)
    buf.putIntervals(n.strC.intervals)
    buf.putI64(int64(n.strC.minSize))
    buf.putI64(int64(n.strC.maxSize))

proc getNode(data: openArray[byte], pos: var int): ChoiceNode =
  # Bounds-checked reads — a truncated input on the second-node boundary
  # raises `DbCorrupt` here instead of falling through to an `IndexDefect`.
  let kindByte = getU8(data, pos)
  if int(kindByte) > ord(high(ChoiceKind)):
    raise newException(DbCorrupt, "invalid choice kind " & $kindByte)
  let kind = ChoiceKind(kindByte)
  let forced = getU8(data, pos) == 1'u8
  case kind
  of ckInteger:
    let v = getInt128(data, pos)
    let mn = getInt128(data, pos)
    let mx = getInt128(data, pos)
    let st = getInt128(data, pos)
    ChoiceNode(wasForced: forced, kind: ckInteger, intVal: v,
               intC: IntConstraints(min: mn, max: mx, shrinkTowards: st))
  of ckFloat:
    let v = getF64(data, pos)
    let mn = getF64(data, pos)
    let mx = getF64(data, pos)
    let nan = getBool(data, pos)
    let sm = getF64(data, pos)
    ChoiceNode(wasForced: forced, kind: ckFloat, floatVal: v,
               floatC: FloatConstraints(min: mn, max: mx, allowNan: nan,
                                        smallestNonzeroMagnitude: sm))
  of ckBoolean:
    let v = getBool(data, pos)
    let p = getF64(data, pos)
    ChoiceNode(wasForced: forced, kind: ckBoolean, boolVal: v,
               boolC: BoolConstraints(p: p))
  of ckBytes:
    let v = getRawBytes(data, pos)
    let mn = int(getI64(data, pos))
    let mx = int(getI64(data, pos))
    ChoiceNode(wasForced: forced, kind: ckBytes, bytesVal: v,
               bytesC: BytesConstraints(minSize: mn, maxSize: mx))
  of ckString:
    let v = getRawStr(data, pos)
    let iv = getIntervals(data, pos)
    let mn = int(getI64(data, pos))
    let mx = int(getI64(data, pos))
    ChoiceNode(wasForced: forced, kind: ckString, strVal: v,
               strC: StringConstraints(intervals: iv, minSize: mn, maxSize: mx))

# --- public API ---------------------------------------------------------------

proc toBytes*(s: seq[ChoiceNode]): seq[byte] =
  ## Serialize a choice sequence to a portable little-endian byte string.
  result.putU64(uint64(s.len))
  for n in s:
    result.putNode(n)

proc fromBytes*(data: seq[byte]): seq[ChoiceNode] =
  ## Inverse of `toBytes`: reconstruct the choice sequence exactly. Raises
  ## `DbCorrupt` on truncated, malformed, or out-of-range input — every
  ## primitive read goes through `binaryio`'s bounds-checked path. Reject
  ## counts that can't possibly fit in the remaining buffer (each node is
  ## at minimum 2 bytes — kind + forced flag).
  var pos = 0
  let nRaw = getU64(data, pos)
  let bytesLeft = uint64(data.len - pos)
  if nRaw > bytesLeft div 2'u64:
    raise newException(DbCorrupt,
      "choice-sequence count " & $nRaw &
      " exceeds what could possibly fit in the remaining " &
      $(data.len - pos) & " bytes")
  let n = int(nRaw)
  result = newSeqOfCap[ChoiceNode](n)
  for _ in 0 ..< n:
    result.add getNode(data, pos)
