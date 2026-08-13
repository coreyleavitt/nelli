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
  # Each interval pair is two i32 (8 bytes); reject any count whose value
  # exceeds either `int.high` (would raise `RangeDefect` on the int cast
  # below in safe builds, escaping the engine's `except DbCorrupt` catch)
  # or what the remaining buffer can possibly hold.
  let nRaw = getU64(data, pos)
  let bytesLeft = uint64(data.len - pos)
  if nRaw > bytesLeft div 8'u64 or nRaw > uint64(high(int)):
    raise newException(DbCorrupt,
      "IntervalSet count " & $nRaw & " exceeds buffer capacity (" &
      $bytesLeft & " bytes remaining)")
  let n = int(nRaw)
  for _ in 0 ..< n:
    let lo = getI32(data, pos)
    let hi = getI32(data, pos)
    # Read-side mirror of `intervals()`'s validation, sharing the
    # predicate (`isValidIntervalRange` in choice.nim) so the legality
    # rule lives in one place. Without this, a hostile `.bin` can
    # inject inverted, out-of-Unicode-range, or surrogate-touching
    # codepoint intervals into a replay run.
    if not isValidIntervalRange(lo, hi):
      raise newException(DbCorrupt,
        "IntervalSet range (" & $lo & ", " & $hi &
        ") is invalid (inverted, out of [0, " & $maxCodepoint &
        "], or intersects the surrogate block [" & $surrogateLo &
        ", " & $surrogateHi & "])")
    result.ranges.add (lo: lo, hi: hi)

# --- node codec ---------------------------------------------------------------
#
# Per-kind put/get procs go into a `ChoiceCodec` table indexed by `ChoiceKind`.
# A `static:` exhaustiveness check fires at compile time if a new `ChoiceKind`
# is added without wiring its codec — eliminating the silent-fallthrough bug
# class that historically kills binary-format engines on enum growth.

type ChoiceCodec = object
  put: proc(buf: var seq[byte], n: ChoiceNode) {.nimcall.}
  get: proc(data: openArray[byte], pos: var int, forced: bool):
            ChoiceNode {.nimcall.}

proc putInteger(buf: var seq[byte], n: ChoiceNode) =
  buf.putInt128(n.intVal)
  buf.putInt128(n.intC.min)
  buf.putInt128(n.intC.max)
  buf.putInt128(n.intC.shrinkTowards)
proc getInteger(data: openArray[byte], pos: var int, forced: bool): ChoiceNode =
  let v  = getInt128(data, pos)
  let mn = getInt128(data, pos)
  let mx = getInt128(data, pos)
  let st = getInt128(data, pos)
  ChoiceNode(wasForced: forced, kind: ckInteger, intVal: v,
             intC: IntConstraints(min: mn, max: mx, shrinkTowards: st))

proc putFloat(buf: var seq[byte], n: ChoiceNode) =
  buf.putF64(n.floatVal)
  buf.putF64(n.floatC.min)
  buf.putF64(n.floatC.max)
  buf.putBool(n.floatC.allowNan)
  buf.putF64(n.floatC.smallestNonzeroMagnitude)
proc getFloat(data: openArray[byte], pos: var int, forced: bool): ChoiceNode =
  let v  = getF64(data, pos)
  let mn = getF64(data, pos)
  let mx = getF64(data, pos)
  let nan = getBool(data, pos)
  let sm = getF64(data, pos)
  ChoiceNode(wasForced: forced, kind: ckFloat, floatVal: v,
             floatC: FloatConstraints(min: mn, max: mx, allowNan: nan,
                                      smallestNonzeroMagnitude: sm))

proc putBoolean(buf: var seq[byte], n: ChoiceNode) =
  buf.putBool(n.boolVal)
  buf.putF64(n.boolC.p)
proc getBoolean(data: openArray[byte], pos: var int, forced: bool): ChoiceNode =
  let v = getBool(data, pos)
  let p = getF64(data, pos)
  ChoiceNode(wasForced: forced, kind: ckBoolean, boolVal: v,
             boolC: BoolConstraints(p: p))

proc putBytes(buf: var seq[byte], n: ChoiceNode) =
  buf.putRawBytes(n.bytesVal)
  buf.putI64(int64(n.bytesC.minSize))
  buf.putI64(int64(n.bytesC.maxSize))
proc getBytes(data: openArray[byte], pos: var int, forced: bool): ChoiceNode =
  let v = getRawBytes(data, pos)
  let mn = int(getI64(data, pos))
  let mx = int(getI64(data, pos))
  ChoiceNode(wasForced: forced, kind: ckBytes, bytesVal: v,
             bytesC: BytesConstraints(minSize: mn, maxSize: mx))

proc putString(buf: var seq[byte], n: ChoiceNode) =
  buf.putRawStr(n.strVal)
  buf.putIntervals(n.strC.intervals)
  buf.putI64(int64(n.strC.minSize))
  buf.putI64(int64(n.strC.maxSize))
proc getString(data: openArray[byte], pos: var int, forced: bool): ChoiceNode =
  let v = getRawStr(data, pos)
  let iv = getIntervals(data, pos)
  let mn = int(getI64(data, pos))
  let mx = int(getI64(data, pos))
  ChoiceNode(wasForced: forced, kind: ckString, strVal: v,
             strC: StringConstraints(intervals: iv, minSize: mn, maxSize: mx))

const choiceCodecs: array[ChoiceKind, ChoiceCodec] = [
  ckInteger: ChoiceCodec(put: putInteger, get: getInteger),
  ckFloat:   ChoiceCodec(put: putFloat,   get: getFloat),
  ckBoolean: ChoiceCodec(put: putBoolean, get: getBoolean),
  ckBytes:   ChoiceCodec(put: putBytes,   get: getBytes),
  ckString:  ChoiceCodec(put: putString,  get: getString),
]

static:
  # Compile-time exhaustiveness: any new `ChoiceKind` added without a
  # codec entry trips this assert. The serializer fails loud at build
  # time instead of silently falling through `case` with no branch.
  for k in ChoiceKind:
    doAssert choiceCodecs[k].put != nil, "missing codec.put for " & $k
    doAssert choiceCodecs[k].get != nil, "missing codec.get for " & $k

proc putNode(buf: var seq[byte], n: ChoiceNode) =
  buf.add byte(ord(n.kind))
  buf.add byte(if n.wasForced: 1 else: 0)
  choiceCodecs[n.kind].put(buf, n)

proc getNode(data: openArray[byte], pos: var int): ChoiceNode =
  let kindByte = getU8(data, pos)
  if int(kindByte) > ord(high(ChoiceKind)):
    raise newException(DbCorrupt, "invalid choice kind " & $kindByte)
  let kind = ChoiceKind(kindByte)
  let forced = getU8(data, pos) == 1'u8
  choiceCodecs[kind].get(data, pos, forced)

# --- public API ---------------------------------------------------------------

proc toBytes*(s: seq[ChoiceNode]): seq[byte] =
  ## Serialize a choice sequence to a portable little-endian byte string.
  result.putU64(uint64(s.len))
  for n in s:
    result.putNode(n)

const minBytesPerNode = 8
  ## Conservative lower bound on the serialized size of any `ChoiceNode`.
  ## The smallest concrete encoding (a `ckBoolean`) is ~11 bytes (kind byte
  ## + forced byte + bool byte + f64 p); 8 keeps a safety margin and bounds
  ## `fromBytes`'s pre-allocation against hostile input.

proc fromBytes*(data: seq[byte]): seq[ChoiceNode] =
  ## Inverse of `toBytes`: reconstruct the choice sequence exactly. Raises
  ## `DbCorrupt` on truncated, malformed, or out-of-range input — every
  ## primitive read goes through `binaryio`'s bounds-checked path. The count
  ## guard rejects values that exceed `bytesLeft / minBytesPerNode`, which
  ## bounds *both* the loop work *and* the `newSeqOfCap` pre-allocation
  ## against a hostile 64 MB blob trying to drive a multi-GB allocation.
  var pos = 0
  let nRaw = getU64(data, pos)
  let bytesLeft = uint64(data.len - pos)
  if nRaw > bytesLeft div uint64(minBytesPerNode):
    raise newException(DbCorrupt,
      "choice-sequence count " & $nRaw &
      " exceeds what could possibly fit in the remaining " &
      $(data.len - pos) & " bytes (min " & $minBytesPerNode & "/node)")
  let n = int(nRaw)
  result = newSeqOfCap[ChoiceNode](n)
  for _ in 0 ..< n:
    result.add getNode(data, pos)
