## Binary serialization and human-readable rendering of choice sequences.
##
## The binary form is fixed little-endian and full-fidelity: it round-trips an
## entire `seq[ChoiceNode]` (kind, forced flag, value, and constraints) exactly,
## so a stored sequence is a self-describing artifact the example database can
## persist and reload without re-running the generator.

import ./int128, ./choice

# --- little-endian primitive writers/readers ----------------------------------

proc putU64(buf: var seq[byte], x: uint64) =
  for i in 0 ..< 8:
    buf.add byte((x shr (8 * i)) and 0xFF'u64)

proc getU64(data: openArray[byte], pos: var int): uint64 =
  for i in 0 ..< 8:
    result = result or (uint64(data[pos + i]) shl (8 * i))
  pos += 8

proc putI64(buf: var seq[byte], x: int64) = buf.putU64(cast[uint64](x))
proc getI64(data: openArray[byte], pos: var int): int64 = cast[int64](getU64(data, pos))

proc putInt128(buf: var seq[byte], x: Int128) =
  buf.putI64(x.hi); buf.putU64(x.lo)
proc getInt128(data: openArray[byte], pos: var int): Int128 =
  result.hi = getI64(data, pos)
  result.lo = getU64(data, pos)

proc putU32(buf: var seq[byte], x: uint32) =
  for i in 0 ..< 4:
    buf.add byte((x shr (8 * i)) and 0xFF'u32)
proc getU32(data: openArray[byte], pos: var int): uint32 =
  for i in 0 ..< 4:
    result = result or (uint32(data[pos + i]) shl (8 * i))
  pos += 4

proc putI32(buf: var seq[byte], x: int32) = buf.putU32(cast[uint32](x))
proc getI32(data: openArray[byte], pos: var int): int32 = cast[int32](getU32(data, pos))

proc putF64(buf: var seq[byte], x: float64) = buf.putU64(cast[uint64](x))
proc getF64(data: openArray[byte], pos: var int): float64 = cast[float64](getU64(data, pos))

proc putBool(buf: var seq[byte], b: bool) = buf.add byte(if b: 1 else: 0)
proc getBool(data: openArray[byte], pos: var int): bool =
  result = data[pos] == 1'u8
  inc pos

proc putBytes(buf: var seq[byte], b: seq[byte]) =
  buf.putU64(uint64(b.len)); buf.add b
proc getBytes(data: openArray[byte], pos: var int): seq[byte] =
  let n = int(getU64(data, pos))
  result = newSeq[byte](n)
  for i in 0 ..< n: result[i] = data[pos + i]
  pos += n

proc putStr(buf: var seq[byte], s: string) =
  buf.putU64(uint64(s.len))
  for c in s: buf.add byte(c)
proc getStr(data: openArray[byte], pos: var int): string =
  let n = int(getU64(data, pos))
  result = newString(n)
  for i in 0 ..< n: result[i] = char(data[pos + i])
  pos += n

proc putIntervals(buf: var seq[byte], s: IntervalSet) =
  buf.putU64(uint64(s.ranges.len))
  for r in s.ranges:
    buf.putI32(r.lo); buf.putI32(r.hi)
proc getIntervals(data: openArray[byte], pos: var int): IntervalSet =
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
    buf.putBytes(n.bytesVal)
    buf.putI64(int64(n.bytesC.minSize))
    buf.putI64(int64(n.bytesC.maxSize))
  of ckString:
    buf.putStr(n.strVal)
    buf.putIntervals(n.strC.intervals)
    buf.putI64(int64(n.strC.minSize))
    buf.putI64(int64(n.strC.maxSize))

proc getNode(data: openArray[byte], pos: var int): ChoiceNode =
  let kind = ChoiceKind(data[pos]); inc pos
  let forced = data[pos] == 1'u8; inc pos
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
    let v = getBytes(data, pos)
    let mn = int(getI64(data, pos))
    let mx = int(getI64(data, pos))
    ChoiceNode(wasForced: forced, kind: ckBytes, bytesVal: v,
               bytesC: BytesConstraints(minSize: mn, maxSize: mx))
  of ckString:
    let v = getStr(data, pos)
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
  ## Inverse of `toBytes`: reconstruct the choice sequence exactly.
  var pos = 0
  let n = int(getU64(data, pos))
  result = newSeqOfCap[ChoiceNode](n)
  for _ in 0 ..< n:
    result.add getNode(data, pos)
