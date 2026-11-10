## RFC-0016 PRC-07 (ref variants). Builds with `--fieldChecks:off` (its
## `.nim.cfg`). A heap-allocated case object carries the same union image as
## a value one (`tsymex_0016_fieldoff.nim`): data and indeterminate-byte mask
## cells beside its per-tag field heaps, one image per object (an alias sees
## it), kept at every constructor, `new`, field store and discriminator store.
##
## Zeroing, read from the generated C (c and cpp, pinned toolchain):
##   * `new(x)` is `nimNewObj`: every byte zero.
##   * `RV(k: ka, a: v)` naming every field of the arm is `nimNewObjUninit`:
##     the bytes no field write reaches are indeterminate; a constructor that
##     omits a field zero-fills, as a value constructor does.
## cpp: the active member is tracked (`vActive`) as for a value variant.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type
  K = enum ka, kb
  RV = ref object
    case k: K
    of ka: a: int
    of kb: b: int
  Kw = enum kwa, kwb
  RW = ref object        ## arm A: int32 (bytes 8..12); arm B: int64 (8..16)
    case k: Kw
    of kwa: x: int32
    of kwb: y: int64
  HObj = object
    case k: K
    of ka: a: int
    of kb: b: int
  RH = ref HObj

var copies = 0
proc `=copy`(d: var HObj; s: HObj) =
  inc copies
  d.k = s.k

proc sutDisc(v: int) =
  let x = RV(k: ka, a: v)
  x.k = kb
  if x.b == 3: symexTarget("hit")

proc sutAlias(v: int) =
  let x = RV(k: ka, a: v)
  let y = x
  y.k = kb
  if x.b == 3: symexTarget("hit")

proc sutCtorPad(v: int32) =
  # `y`'s high four bytes: no field of arm A, and the constructor is uninit
  let o = RW(k: kwa, x: v)
  if o.y == 7: symexTarget("hit")

proc sutNewZero(v: int32) =
  # `new` zeroes the cell; `y`'s low four bytes are then `x`'s
  var o: RW
  new(o)
  o.x = v
  if o.y == 5: symexTarget("hit")

proc sutKeepWide(v: int64) =
  # the old arm's bytes outlive its discriminator: `y`'s high half is `v`'s
  let o = RW(k: kwb, y: v)
  o.k = kwa
  o.x = 1
  o.k = kwb
  if o.y == 0x2_0000_0001'i64: symexTarget("hit")

proc sutParam(p: RV) =
  if p != nil and p.k == ka and p.b == 7: symexTarget("hit")

proc sutHooked(v: int) =
  let x = RH(k: ka, a: v)
  x.k = kb
  if x.b == 3: symexTarget("hit")

proc sutWrongWrite(v: int) =
  let x = RV(k: ka, a: v)
  x.b = 5
  if x.b == 5 and v == 3: symexTarget("hit")

proc sutWrongWriteReadOwn(v: int) =
  let x = RV(k: ka, a: v)
  x.b = 5
  if x.a == 5 and v == 3: symexTarget("hit")

proc sutOutArmWrite(v: int64) =
  # `y` is arm B's int64 (bytes 8..16): written while arm A is active, it is
  # read back through A's overlapping `x` (the low four bytes)
  let o = RW(k: kwa, x: 1)
  o.y = v
  if o.x == 5: symexTarget("hit")

proc sutOutArmWriteHigh(v: int64) =
  # the bytes above `x` are `y`'s, so a later read of `y` through the same
  # out-of-arm field sees the whole value
  let o = RW(k: kwa, x: 1)
  o.y = v
  if o.y == 0x2_0000_0005'i64: symexTarget("hit")

proc sutOutArmWriteNarrow(v: int32) =
  # arm B active, arm A's `x` (int32) written: `y` keeps its high half
  let o = RW(k: kwb, y: 0x2_0000_0001'i64)
  o.x = v
  if o.y == 0x2_0000_0007'i64: symexTarget("hit")

type
  Kc = enum kca, kcb
  RC = ref object        ## arm A: x, w (int32 each); arm B: z (int32)
    case k: Kc
    of kca: x, w: int32
    of kcb: z: int32

proc touch(o: RC) {.symexOpaque.} =
  o.x = 9

proc sutOpaqueCtor(v: int32) =
  # the constructor names every field of its arm; the opaque callee may
  # switch the arm, and `w`'s bytes are then arm B's tail, still written
  let o = RC(k: kca, x: v, w: 5)
  touch(o)
  if o.w == 5: symexTarget("hit")

proc scrub() {.noinline.} =
  var a {.volatile.}: array[8192, int]
  for i in 0 ..< a.len: a[i] = 0

template exact(fn: untyped; want: untyped) =
  let r = symexFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
  check r.status == sxSat
  check r.trusted
  check r.undefined.len == 0
  check not r.errors.named(feUnsupportedOp)
  check r.witness[0] == want

template indeterminateOrRefuted(fn: untyped) =
  scrub()
  let r = symexFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
  check not r.trusted
  check r.status in {sxSat, sxUnknown}
  check r.errors.named(feGlobalHavoc) or
        UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds

when not defined(cpp):
  suite "PRC-07 ref variants: the union image in the heap (c backend)":
    test "a branch-changing discriminator write through a ref reinterprets the bytes":
      exact(sutDisc, 3)

    test "through an alias":
      exact(sutAlias, 3)

    test "a constructor naming every arm field leaves the other arm's tail indeterminate":
      indeterminateOrRefuted(sutCtorPad)

    test "new zeroes the cell: the other arm's tail is zero":
      exact(sutNewZero, 5)

    test "a discriminator store keeps the old arm's bytes it no longer names":
      let r = symexFind(sutKeepWide, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status == sxSat
      check r.trusted
      check r.undefined.len == 0
      check (r.witness[0] shr 32) == 2

    test "an input ref's bytes are free":
      let r = symexFind(sutParam, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(feUnsupportedOp)

    test "an out-of-arm write is read back through the active arm's field":
      let r = symexFind(sutOutArmWrite, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status == sxSat
      check r.trusted
      check r.undefined.len == 0
      check not r.errors.named(feUnsupportedOp)
      check (r.witness[0] and 0xFFFF_FFFF'i64) == 5

    test "an out-of-arm write is read back whole through the same field":
      let r = symexFind(sutOutArmWriteHigh, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 0x2_0000_0005'i64

    test "an out-of-arm write keeps the bytes it does not cover":
      let r = symexFind(sutOutArmWriteNarrow, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 7

    test "a ref variant fully written by its constructor stays determinate over an opaque call":
      let r = symexFind(sutOpaqueCtor, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.undefined.len == 0
      check UbKind(ubIndeterminateRead) notin r.soundness.undefinedKinds

    test "a hooked pointee keeps the havoc model":
      let r = symexFind(sutHooked, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check not r.trusted
      check r.status != sxSat or r.errors.named(feUncheckedDiscBytes)
else:
  suite "PRC-07 ref variants: the active member in the heap (cpp backend)":
    test "a read through the member the wrong-branch write made active":
      exact(sutWrongWrite, 3)

    test "a read through the discriminator's branch after a wrong-branch write":
      let r = symexFind(sutWrongWriteReadOwn, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status != sxSat
      check symexFind(sutWrongWriteReadOwn,
                      tUndefined({UbKind(ubInactiveVariantField)}), pinSettingsConst).status == sxSat

    test "a branch-changing discriminator write leaves the old member active":
      let r = symexFind(sutDisc, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status != sxSat
      check symexFind(sutDisc,
                      tUndefined({UbKind(ubInactiveVariantField)}), pinSettingsConst).status == sxSat
