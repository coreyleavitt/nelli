## Shared little-endian primitives for binary serialization.
##
## Both `serialize.nim` (choice-sequence encoding) and `db.nim` (example DB
## file format) need the same set of fixed little-endian primitives. They
## used to redefine the helpers in each file — any endian bug had to be
## fixed twice. This module centralizes them. Internal-only: not re-exported
## from `proptest.nim`.

import ./int128

proc putU64*(buf: var seq[byte], x: uint64) =
  for i in 0 ..< 8:
    buf.add byte((x shr (8 * i)) and 0xFF'u64)

proc getU64*(data: openArray[byte], pos: var int): uint64 =
  for i in 0 ..< 8:
    result = result or (uint64(data[pos + i]) shl (8 * i))
  pos += 8

proc putI64*(buf: var seq[byte], x: int64) = buf.putU64(cast[uint64](x))
proc getI64*(data: openArray[byte], pos: var int): int64 =
  cast[int64](getU64(data, pos))

proc putU32*(buf: var seq[byte], x: uint32) =
  for i in 0 ..< 4:
    buf.add byte((x shr (8 * i)) and 0xFF'u32)
proc getU32*(data: openArray[byte], pos: var int): uint32 =
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
  result = data[pos] == 1'u8
  inc pos

proc putRawBytes*(buf: var seq[byte], b: seq[byte]) =
  buf.putU64(uint64(b.len))
  buf.add b

proc putRawStr*(buf: var seq[byte], s: string) =
  buf.putU64(uint64(s.len))
  for c in s: buf.add byte(c)
