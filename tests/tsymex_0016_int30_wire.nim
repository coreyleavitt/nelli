## RFC-0016 INT-30 (0005 review R2-29). The wire reader a re-executed replay
## child reads its witness with (`replaywire.nim`) holds against a witness the
## host did not write, and the writer against a value too deep to write:
##
## * a seq of elements that take no bytes on the wire is backed by a byte
##   each, so its count is bounded by the bytes left and a real one at the end
##   of a witness reads back;
## * a count is not allocated ahead of the bytes that back it, so a witness of
##   a few kilobytes cannot make the reader allocate a gigabyte;
## * a chain of `ref` cells deeper than `wireDepthLimit` is refused at both
##   ends with `WireError`, never by overflowing the stack.
##
## Runs everywhere: the wire is the same encoding on every platform.
import std/unittest
import nelli/smt/replaywire
from nelli/smt/admission import cellKey, axConstruct
from ./s8cu_helpers import pinNever

type
  Empty = object
  Node = ref object
    next: Node
  Big = array[512, int64]

proc lenBytes(n: int64): string =
  result = newString(8)
  var v = n
  copyMem(addr result[0], addr v, 8)

proc chain(n: int): Node =
  for i in 0 ..< n:
    result = Node(next: result)

proc depthOf(x: Node): int =
  var p = x
  while p != nil:
    inc result
    p = p.next

suite "INT-30: zero-size elements":
  test "a seq of empty objects at the end of a witness reads back":
    var w: WireWriter
    w.wirePut(@[Empty(), Empty(), Empty()])
    var r = initWireReader(w.data)
    var got: seq[Empty]
    r.wireGet(got)
    check got.len == 3
    pinNever(cellKey(axConstruct, "replay/wire/codec"), got.len == 3,
      "a seq of three empty objects written with pad bytes reads back as three")

  test "a count of empty objects no byte backs is refused":
    var r = initWireReader(lenBytes(1_000_000_000))
    var got: seq[Empty]
    expect WireError:
      r.wireGet(got)

  test "a count of empty arrays read from the next value's bytes is refused":
    # Five elements claimed; the eight bytes after are another value's.
    var r = initWireReader(lenBytes(5) & lenBytes(0))
    var got: seq[array[0, int]]
    expect WireError:
      r.wireGet(got)

suite "INT-30: allocation follows the bytes":
  test "a count backed by too few bytes allocates no more than they hold":
    # 100000 elements of 4 KiB each claimed, 100000 bytes given.
    let data = lenBytes(100_000) & newString(100_000)
    var r = initWireReader(data)
    var got: seq[Big]
    let before = getMaxMem()
    expect WireError:
      r.wireGet(got)
    let grew = getMaxMem() - before
    checkpoint "peak heap grew by " & $grew & " bytes"
    check grew < 16 * 1024 * 1024

  test "a string count past the bytes left is refused":
    var r = initWireReader(lenBytes(1 shl 40) & "abc")
    var s: string
    expect WireError:
      r.wireGet(s)

suite "INT-30: recursion depth":
  test "a ref chain within the limit round-trips":
    let x = chain(wireDepthLimit div 4)
    var w: WireWriter
    w.wirePut(x)
    var r = initWireReader(w.data)
    var y: Node
    r.wireGet(y)
    check depthOf(y) == wireDepthLimit div 4
    pinNever(cellKey(axConstruct, "replay/wire/codec"),
      depthOf(y) == wireDepthLimit div 4,
      "a ref chain of " & $(wireDepthLimit div 4) & " cells round-trips")

  test "the writer refuses a chain past the limit":
    let x = chain(5_000)
    var w: WireWriter
    expect WireError:
      w.wirePut(x)
    # Unlinked one cell at a time: dropping the chain whole recurses as deep.
    var p = x
    while p != nil:
      let n = p.next
      p.next = nil
      p = n

  test "the reader refuses a crafted chain past the limit":
    # Cell i is new (id == cells.len), then its `next` field: cell i + 1.
    var data = ""
    for i in 0 ..< 200_000:
      data.add lenBytes(i)
    data.add lenBytes(-1)
    var r = initWireReader(data)
    var y: Node
    expect WireError:
      r.wireGet(y)
