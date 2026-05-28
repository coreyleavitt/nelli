## Binary serialization and human-readable rendering of choice sequences.
##
## The binary form is fixed little-endian and full-fidelity: it round-trips an
## entire `seq[ChoiceNode]` (kind, forced flag, value, and constraints) exactly,
## so a stored sequence is a self-describing artifact the example database can
## persist and reload without re-running the generator.

import ./int128, ./choice, ./binaryio
export binaryio  # internal-only: db.nim and tests reach for these via serialize too

proc putBytes(buf: var seq[byte], b: seq[byte]) = buf.putRawBytes b
proc getBytes(data: openArray[byte], pos: var int): seq[byte] =
  let n = int(getU64(data, pos))
  result = newSeq[byte](n)
  for i in 0 ..< n: result[i] = data[pos + i]
  pos += n

proc putStr(buf: var seq[byte], s: string) = buf.putRawStr s
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
