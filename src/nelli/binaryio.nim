## Shared little-endian primitives for binary serialization.
##
## Both `serialize.nim` (choice-sequence encoding) and `db.nim` (example DB
## file format) decode binary data through these helpers. **Every read is
## bounds-checked**: if the input ends before the expected number of bytes,
## or a length-prefix exceeds the remaining input, the primitive raises
## `DbCorrupt`. Callers can wrap a decode in `try/except DbCorrupt` to fall
## back to "empty corpus" semantics; an uncaught `DbCorrupt` becomes a
## defined, named error rather than an opaque `IndexDefect`.

import ./int128

type
  DbCorrupt* = object of CatchableError
    ## Raised by the binary decoders when input is truncated, has a bogus
    ## length field, or otherwise can't be safely decoded.

const
  maxBlobBytes* = 64 * 1024 * 1024
    ## Hard cap on any single length-prefixed blob/string. A hostile or
    ## corrupted length field can't drive an unbounded allocation.

template needBytes*(data: openArray[byte], pos: int, n: int) =
  ## Raise `DbCorrupt` if `data` doesn't have `n` more bytes at `pos`.
  if pos < 0 or n < 0 or pos + n > data.len:
    raise newException(DbCorrupt,
      "binary input truncated: need " & $n & " bytes at pos " & $pos &
      " in a " & $data.len & "-byte buffer")

proc putU64*(buf: var seq[byte], x: uint64) =
  for i in 0 ..< 8:
    buf.add byte((x shr (8 * i)) and 0xFF'u64)

proc getU64*(data: openArray[byte], pos: var int): uint64 =
  needBytes(data, pos, 8)
  for i in 0 ..< 8:
    result = result or (uint64(data[pos + i]) shl (8 * i))
  pos += 8

proc putI64*(buf: var seq[byte], x: int64) = buf.putU64(cast[uint64](x))
proc getI64*(data: openArray[byte], pos: var int): int64 =
  cast[int64](getU64(data, pos))

proc putU16*(buf: var seq[byte], x: uint16) =
  for i in 0 ..< 2:
    buf.add byte((x shr (8 * i)) and 0xFF'u16)

proc getU16*(data: openArray[byte], pos: var int): uint16 =
  needBytes(data, pos, 2)
  for i in 0 ..< 2:
    result = result or (uint16(data[pos + i]) shl (8 * i))
  pos += 2

proc putU32*(buf: var seq[byte], x: uint32) =
  for i in 0 ..< 4:
    buf.add byte((x shr (8 * i)) and 0xFF'u32)
proc getU32*(data: openArray[byte], pos: var int): uint32 =
  needBytes(data, pos, 4)
  for i in 0 ..< 4:
    result = result or (uint32(data[pos + i]) shl (8 * i))
  pos += 4

proc putI32*(buf: var seq[byte], x: int32) = buf.putU32(cast[uint32](x))
proc getI32*(data: openArray[byte], pos: var int): int32 =
  cast[int32](getU32(data, pos))

proc putF64*(buf: var seq[byte], x: float64) = buf.putU64(cast[uint64](x))
proc getF64*(data: openArray[byte], pos: var int): float64 =
  cast[float64](getU64(data, pos))

proc putInt128*(buf: var seq[byte], x: Int128) =
  buf.putI64(x.hi); buf.putU64(x.lo)
proc getInt128*(data: openArray[byte], pos: var int): Int128 =
  result.hi = getI64(data, pos)
  result.lo = getU64(data, pos)

proc putBool*(buf: var seq[byte], b: bool) =
  buf.add byte(if b: 1 else: 0)
proc getBool*(data: openArray[byte], pos: var int): bool =
  needBytes(data, pos, 1)
  result = data[pos] == 1'u8
  inc pos

proc putU8*(buf: var seq[byte], x: uint8) = buf.add x
proc getU8*(data: openArray[byte], pos: var int): uint8 =
  needBytes(data, pos, 1)
  result = data[pos]; inc pos

proc safeLen*(data: openArray[byte], pos: var int): int =
  ## Read a u64 length prefix and validate it against (a) the per-blob cap
  ## (b) the bytes remaining in `data`. Refusing the read here means the
  ## subsequent allocation/copy is always safe.
  let raw = getU64(data, pos)
  if raw > uint64(maxBlobBytes):
    raise newException(DbCorrupt, "blob length " & $raw & " exceeds cap")
  let n = int(raw)
  needBytes(data, pos, n)
  n

proc putRawBytes*(buf: var seq[byte], b: seq[byte]) =
  buf.putU64(uint64(b.len))
  buf.add b

proc getRawBytes*(data: openArray[byte], pos: var int): seq[byte] =
  let n = safeLen(data, pos)
  result = newSeq[byte](n)
  for i in 0 ..< n: result[i] = data[pos + i]
  pos += n

proc putRawStr*(buf: var seq[byte], s: string) =
  buf.putU64(uint64(s.len))
  for c in s: buf.add byte(c)

proc getRawStr*(data: openArray[byte], pos: var int): string =
  let n = safeLen(data, pos)
  result = newString(n)
  for i in 0 ..< n: result[i] = char(data[pos + i])
  pos += n
