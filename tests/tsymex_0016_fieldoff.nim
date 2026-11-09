## RFC-0016 PRC-07 (variant-field half). This file builds with
## `--fieldChecks:off` (its `.nim.cfg`), on the c backend and on cpp. Nim then
## emits no `FieldDefect` check on a variant field: `v.b` is a plain union
## member access, and a write to the discriminator no longer checks that it
## stays in its branch.
##
## Native, read from the generated C of the pinned toolchain (c backend,
## `--fieldChecks:off`): `v.b` of a `ka` object is a read of the union member
## `b`, which overlaps the active `a`; a probe read the same bytes back.
##   * c backend: C11 6.5.2.3 note 95 DEFINES that read as the object
##     representation of the active member reinterpreted. The walker keeps one
##     slot per field and has no per-target byte layout of a variant, so it
##     does not model the value: the wrong-branch side is declined on its own
##     path (`fieldChecksOffLayout`, `feUnsupportedOp`), the right-branch side
##     is exact and trusted, and nothing taints the routine.
##   * cpp backend: reading a union member that is not the active one is
##     undefined in C++: that side halts as `ubInactiveVariantField` (row
##     `field/inactiveBranch`) and is an `UndefinedFinding`. A WRITE to the
##     inactive branch is defined in C++ (the member becomes active), so it
##     is no finding: it is declined on its own path like the c backend's
##     (`fieldChecksOffLayout`), the walker holding no active-member state.
##   * either: an assignment to the discriminator that changes branch leaves
##     the new branch holding the old bytes. cpp: the `dwmHavoc` model
##     (`feUncheckedDiscBytes`, replay-confirmed). c: the union image carries
##     the bytes and the new arm's fields are read from it (exact).
## No sanitizer reports an inactive union member read and gcc documents it as
## type punning, so the `field/inactiveBranch` cell has no native pin; the
## native half here is that the in-branch witnesses reproduce.
import std/[unittest, strutils, macros]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/dsl_typebridge
import nelli/smt/variant_layout
import ./s8cu_helpers

type
  K = enum ka, kb
  V = object
    case k: K
    of ka: a: int
    of kb: b: int
  RV = ref object
    case k: K
    of ka: a: int
    of kb: b: int

# The layout the walker derives for a variant, set against the layout the
# compiler gave it: `addr v.f` of a member is a plain `&v.f` with
# `fieldChecks` off, `sizeof` the struct's size. The macro computes the
# walker's side at compile time and builds the native probe for the same
# fields in the same order.
proc innerTypeSym(T: NimNode): NimNode =
  let inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst[1]
  else:
    inst

macro layoutPins(T: typedesc; v: untyped): untyped =
  let lay = variantLayout(classifyType(innerTypeSym(T)).ty)
  var nat = newCall(ident"&", newLit("size="),
                    newCall(ident"$", newCall(ident"sizeof", T)))
  for f in layoutFieldNames(lay):
    let off = newCall(ident"-",
      newTree(nnkCast, ident"int", newCall(ident"addr", newDotExpr(v, ident f))),
      newTree(nnkCast, ident"int", newCall(ident"addr", v)))
    nat = newCall(ident"&", nat, newCall(ident"&", newLit(";" & f & "@"),
                                         newCall(ident"$", off)))
  result = newTree(nnkTupleConstr, newLit(layoutDump(lay)), nat)

type
  Kw = enum kwa, kwb, kwc
  Wd = object            ## arm A: one int32; arm B: two int16
    case k: Kw
    of kwa: x: int32
    of kwb:
      wa: int16
      wb: int16
    of kwc: wc: int8
  Wp = object            ## a plain field before the case, mixed widths
    pre: int8
    case k: Kw
    of kwa: x: int64
    of kwb:
      a: int8
      b: int16
      c: int32
    of kwc: discard
  Wb = object            ## a bool discriminator, uint8 / char / bool arm
    p: int16
    case k: bool
    of true:
      u: uint8
      v: char
      w: bool
    of false: z: int32
  Wf = object            ## a float arm: sized, never reinterpreted
    case k: Kw
    of kwa: f: float64
    of kwb:
      i: int8
      j: int8
    of kwc: discard

type
  Wh = object
    case k: Kw
    of kwa: h: int16
    of kwb: w: int32
    of kwc: discard
  Wk {.packed.} = object  ## slice B 0a: no padding, every member at alignment 1
    pre: int8
    case k: Kw
    of kwa: x: int64
    of kwb:
      a: int8
      b: int32
    of kwc: discard

proc sutPackedRead(v: int64) =
  # packed: `b` is bytes 3..7 of the object, bytes 1..5 of `x` (at 2..10)
  let o = Wk(k: kwa, pre: 1, x: v)
  if o.b == 0x11223344'i32: symexTarget("hit")

const fk = cellKey(axBuild, "fieldChecks=off")
const uk = cellKey(axDefinedness, "field/inactiveBranch")
const bk = cellKey(axDefinedness, "field/inactiveBytes")

proc sutIn(v: int) =
  let x = V(k: ka, a: v)
  if x.a == 7: symexTarget("hit")

proc sutWrite(v: int) =
  var x = V(k: ka, a: v)
  x.a = 9
  if x.a == 9 and v == 3: symexTarget("hit")

proc sutDiscSame(v: int) =
  var x = V(k: ka, a: v)
  x.k = ka
  if x.a == 7: symexTarget("hit")

proc sutPick(v: int) =
  let x = if v > 0: V(k: ka, a: v) else: V(k: kb, b: v)
  if x.a == 5: symexTarget("hit")

proc sutWrongRead(v: int) =
  let x = V(k: ka, a: v)
  if x.b == x.b and v == 3: symexTarget("hit")

proc sutWrongWrite(v: int) =
  var x = V(k: ka, a: v)
  x.b = 5
  if v == 3: symexTarget("hit")

proc sutDiscChange(v: int) =
  var x = V(k: ka, a: v)
  x.k = kb
  if v == 3: symexTarget("hit")

proc sutRefIn(v: int) =
  let x = RV(k: ka, a: v)
  if x.a == 7: symexTarget("hit")

proc sutRefWrongRead(v: int) =
  let x = RV(k: ka, a: v)
  if x.b == x.b and v == 3: symexTarget("hit")

proc sutRefWrongWrite(v: int) =
  let x = RV(k: ka, a: v)
  x.b = 5
  if v == 3: symexTarget("hit")

proc sutRefDiscChange(v: int) =
  let x = RV(k: ka, a: v)
  x.k = kb
  if v == 3: symexTarget("hit")

# Slice A (c backend): a wrong-branch access whose bytes the active arm's
# integer fields cover is exact. `Wd`: arm A `x: int32` (bytes 4..8 of the
# object), arm B `wa, wb: int16` (4..6, 6..8).
proc sutWideRead(v: int32) =
  let o = Wd(k: kwa, x: v)
  if o.wb == 0x1122'i16: symexTarget("hit")

proc sutWideReadLow(v: int32) =
  let o = Wd(k: kwa, x: v)
  if o.wa == -2'i16: symexTarget("hit")

proc sutNarrowRead(v: int16) =
  # arm B holds two int16: reading the int32 `x` of arm A is the bytes of both
  let o = Wd(k: kwb, wa: v, wb: 0x0102'i16)
  if o.x == 0x01020005'i32: symexTarget("hit")

proc sutWideWrite(v: int32) =
  var o = Wd(k: kwa, x: v)
  o.wb = 0x1122'i16
  if o.x == 0x11221234'i32: symexTarget("hit")

proc sutWriteThenRead(v: int32) =
  var o = Wd(k: kwa, x: v)
  o.wb = 0x2233'i16
  if o.wb == 0x2233'i16 and (o.x and 0xFFFF) == 0x0042: symexTarget("hit")

proc sutWriteActiveThenWrong(v: int32) =
  var o = Wd(k: kwa, x: 0)
  o.x = v
  if o.wa == 0x0042'i16 and o.wb == 0x0007'i16: symexTarget("hit")

proc sutByteRead(v: int32) =
  # arm C `wc: int8` is the first byte of arm A's `x`
  let o = Wd(k: kwa, x: v)
  if o.wc == 0x44'i8: symexTarget("hit")

# Slice B (c): a branch-changing discriminator write keeps the bytes.
proc sutDiscToPair(v: int32) =
  var o = Wd(k: kwa, x: v)
  o.k = kwb
  if o.wa == 0x3344'i16 and o.wb == 0x1122'i16: symexTarget("hit")

proc sutDiscToByte(v: int32) =
  var o = Wd(k: kwa, x: v)
  o.k = kwc
  if o.wc == 0x44'i8: symexTarget("hit")

proc sutDiscThenWrite(v: int32) =
  var o = Wd(k: kwa, x: v)
  o.k = kwb
  o.wa = 0x0042'i16
  if o.x == 0x11220042'i32: symexTarget("hit")

proc sutDiscSymbolic(v: int32) =
  var o = Wd(k: kwa, x: v)
  o.k = (if v > 0: kwb else: kwc)
  if v > 0 and o.wa == 0x3344'i16: symexTarget("hit")

# Shapes the layout cannot answer stay declined, on their own path.
type
  Pd = object            ## arm B's `pb` is bytes 8..12, arm A owns only 4..8
    case k: Kw
    of kwa: x: int32
    of kwb:
      pa: int8
      pb: int32
    of kwc: discard
  Pf = object            ## a float arm is never reinterpreted
    case k: Kw
    of kwa: f: float64
    of kwb: i: int64
    of kwc: discard
  Pr = object            ## a range is not written with arbitrary bytes
    case k: Kw
    of kwa: x: int32
    of kwb: r: range[0'i32 .. 9'i32]
    of kwc: discard

proc sutDiscToRange(v: int32) =
  var o = Pr(k: kwa, x: v)
  o.k = kwb
  if o.r == 3'i32: symexTarget("hit")

proc sutPadRead(v: int32) =
  let o = Pd(k: kwa, x: v)
  if o.pb == 5: symexTarget("hit")

# Slice B: the union is one byte image. Bytes no field of the active arm
# covers are the zero of the object's initialisation (Nim zero-fills the
# whole object before it sets the fields), a float is its IEEE bits and an
# enum its raw C value.
type
  Pe = object            ## an enum arm field read from an int's byte
    case k: Kw
    of kwa: x: int8
    of kwb: e: Kw
    of kwc: discard

proc sutPadZero(v: int32) =
  # `pb` is bytes 8..12: no field of arm A owns them; zero-initialised
  let o = Pd(k: kwa, x: v)
  if o.pb == 0 and o.pa == 0x21'i8 and v == 0x4321: symexTarget("hit")

proc sutFloatFromInt(v: int64) =
  let o = Pf(k: kwb, i: v)
  if o.f == 1.0: symexTarget("hit")

proc sutEnumRead(v: int8) =
  let o = Pe(k: kwa, x: v)
  if o.e == kwb: symexTarget("hit")

proc sutWrongWriteReadOwn(v: int) =
  # c: `a` and `b` are the same bytes; cpp: `a` is no longer the active member
  var x = V(k: ka, a: v)
  x.b = 5
  if x.a == 5 and v == 3: symexTarget("hit")

proc sutWrongWriteReadSame(v: int) =
  # cpp: the write made `b` the active member, so reading it is defined
  var x = V(k: ka, a: v)
  x.b = 5
  if x.b == 5 and v == 3: symexTarget("hit")

proc sutFloatRead(v: int64) =
  let o = Pf(k: kwa, f: 1.0)
  if o.i == v: symexTarget("hit")

proc sutRangeOverwrite(v: int32) =
  # the active arm's `r` is a range: bytes written through `x` need not be
  # a value of it, so that arm's side declines
  var o = Pr(k: kwb, r: 3)
  o.x = v
  if o.r == 3: symexTarget("hit")

proc sutPartialRead(v: int16) =
  # arm A's 2 bytes against a 4-byte field of the other arm
  let o = Wh(k: kwa, h: v)
  if o.w == 7: symexTarget("hit")

proc sutCharFromInt(v: int32) =
  # `v: char` is byte 5, the second byte of `z`
  let o = Wb(k: false, p: 1, z: v)
  if o.v == 'A': symexTarget("hit")

proc sutBoolFromInt(v: int32) =
  # a bool read of bytes that need not be 0 or 1
  let o = Wb(k: false, p: 1, z: v)
  if o.w: symexTarget("hit")

proc sutIntFromBytes(v: uint8) =
  # `z` is bytes 4..8, the active arm's three fields cover 4..7 only
  let o = Wb(k: true, p: 1, u: v, v: 'A', w: true)
  if o.z == 0x14142'i32: symexTarget("hit")

proc sutUByteWrite(v: int32) =
  var o = Wb(k: false, p: 1, z: v)
  o.u = 0xAB'u8
  if (o.z and 0xFF) == 0xAB and (o.z shr 8) == (v shr 8): symexTarget("hit")

when defined(cpp):
  const wrongKind = ubInactiveVariantField
  const wrongKey = uk
else:
  const wrongKind = feUnsupportedOp
  const wrongKey = bk

suite "PRC-07: --fieldChecks:off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 309

  test "the walker's variant layout is the compiler's":
    var a = Wd(k: kwa, x: 1)
    var b = Wp(k: kwa, pre: 1, x: 2)
    var c = Wb(k: true, p: 1, u: 2)
    var d = Wf(k: kwb, i: 1, j: 2)
    let pa = layoutPins(Wd, a)
    let pb = layoutPins(Wp, b)
    let pc = layoutPins(Wb, c)
    let pd = layoutPins(Wf, d)
    checkpoint "walker " & pa[0] & " native " & pa[1]
    check pa[0] == pa[1]
    check pb[0] == pb[1]
    check pc[0] == pc[1]
    check pd[0] == pd[1]
    check pa[0] == "size=8;x@4;wa@4;wb@6;wc@4"
    # slice B 0a: a `{.packed.}` variant has no padding at any level
    var e = Wk(k: kwa, pre: 1, x: 2)
    let pe = layoutPins(Wk, e)
    checkpoint "walker " & pe[0] & " native " & pe[1]
    check pe[0] == pe[1]
    check pe[0] == "size=10;x@2;a@2;b@3"

  test "the build has the field check off and the others on":
    check coField notin buildSemantics.checks
    check coObj in buildSemantics.checks
    check coBound in buildSemantics.checks

  test "an in-branch read is exact and trusted":
    let r = pinExact(sutIn, fk, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 7
    check not r.errors.named(feCheckOption)

  test "an in-branch write is exact and trusted":
    let r = pinExact(sutWrite, fk, domain = sampled([3, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "a discriminator write inside its branch is exact":
    let r = pinExact(sutDiscSame, fk, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "no FieldDefect is reachable":
    for r in [symexFind(sutWrongRead, tRaisedExn("FieldDefect")),
              symexFind(sutWrongWrite, tRaisedExn("FieldDefect")),
              symexFind(sutDiscChange, tRaisedExn("FieldDefect")),
              symexFind(sutRefWrongRead, tRaisedExn("FieldDefect")),
              symexFind(sutRefDiscChange, tRaisedExn("FieldDefect"))]:
      checkpoint show(r.errors)
      check r.status != sxRaised
      check not r.errors.named(feCheckOption)

  test "the in-branch side of a pick is exact, the other side is its own":
    let r = symexFind(sutPick, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 5
    check not r.errors.named(feCheckOption)
    when defined(cpp):
      check r.trusted
      check r.undefined.len == 1
      check r.undefined[0].kind == UbKind(ubInactiveVariantField)
      check "outside its branch" in r.undefined[0].site
      check "tsymex_0016_fieldoff" in r.undefined[0].site
      check r.undefined[0].witness[0] <= 0
    else:
      # `a` and `b` are the same eight bytes: the other side is exact too
      check r.trusted
      check not r.errors.named(feUnsupportedOp)

  test "a read outside its branch":
    when defined(cpp):
      pinDecline(sutWrongRead, wrongKey, ubInactiveVariantField,
                 excluding = {feCheckOption})
    else:
      # the active `a` covers every byte of `b`: exact, not a decline
      let r = pinExact(sutWrongRead, fk, domain = sampled([3, 0, 1]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 3

  test "a write outside its branch is no finding on either backend":
    # C++ defines the assignment (the member becomes active), so it is not
    # `ubInactiveVariantField`; the walker holds no active-member state, so
    # the side is declined on its own path (`fieldChecksOffLayout`) on cpp.
    # On c the bytes `a` and `b` share are the active arm's: exact.
    let r = symexFind(sutWrongWrite, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 0
    check not r.errors.named(feCheckOption)
    # cpp (slice B): the walker tracks the active member, so the write is
    # exact; on c the bytes `a` and `b` share are the active arm's: exact.
    check r.status == sxSat
    check r.trusted
    check not r.errors.named(feUnsupportedOp)
    check symexFind(sutWrongWrite,
                    tUndefined({UbKind(ubInactiveVariantField)})).status != sxSat

  test "a read through the discriminator's branch after a wrong-branch write":
    # C++: `x.b = 5` made `b` the active member; `x.a` is then an inactive
    # member read, undefined where it happens. C: the same bytes.
    let r = symexFind(sutWrongWriteReadOwn, tLabel("hit"))
    checkpoint show(r.errors)
    when defined(cpp):
      check r.status != sxSat
      check symexFind(sutWrongWriteReadOwn,
                      tUndefined({UbKind(ubInactiveVariantField)})).status == sxSat
    else:
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 3

  test "a read through the member the wrong-branch write made active":
    let r = pinExact(sutWrongWriteReadSame, fk, domain = sampled([3, 0, 1]))
    check r.status == sxSat
    check r.trusted
    check r.undefined.len == 0

  test "a ref variant read outside its branch":
    when defined(cpp):
      pinDecline(sutRefWrongRead, wrongKey, ubInactiveVariantField,
                 excluding = {feCheckOption})
    else:
      # the active `a` covers every byte of `b`: exact, as a value's
      let r = pinExact(sutRefWrongRead, fk, domain = sampled([3, 0, 1]))
      check r.status == sxSat
      check r.trusted
      check r.undefined.len == 0

  test "a ref variant write outside its branch is no finding on either backend":
    # cpp: the member becomes active (defined); c: the active `a` covers every
    # byte of `b`. The ref carries the active member and the image, so both
    # are exact and trusted.
    let r = symexFind(sutRefWrongWrite, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 0
    check r.status == sxSat
    check r.trusted
    check not r.errors.named(feUnsupportedOp)
    check "fieldChecksOffLayout" notin show(r.errors)
    check symexFind(sutRefWrongWrite,
                    tUndefined({UbKind(ubInactiveVariantField)})).status != sxSat

  test "a ref variant in-branch read is exact":
    let r = pinExact(sutRefIn, fk, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "tUndefined asks for the wrong-branch input (cpp), nothing on c":
    let r = symexFind(sutPick, tUndefined({UbKind(ubInactiveVariantField)}))
    when defined(cpp):
      check r.status == sxSat
      check r.witness[0] <= 0
      check r.soundness.undefinedKinds == {UbKind(ubInactiveVariantField)}
    else:
      check r.status != sxSat

  test "a branch-changing discriminator write holds the old bytes":
    let r = symexFind(sutDiscChange, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 3
    # c: the union image carries the bytes, so the new arm is exact (slice B,
    # below); cpp holds no image and keeps the havoc model
    when defined(cpp):
      check r.errors.named(feUncheckedDiscBytes)
    else:
      check not r.errors.named(feUncheckedDiscBytes)
    check not r.errors.named(feCheckOption)

  test "a branch-changing discriminator write through a ref is exact":
    # c: the union image carries the bytes; cpp: the old member stays active
    # and the walker havocs the new arm's fields (`feUncheckedDiscBytes`)
    let r = symexFind(sutRefDiscChange, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 3
    check not r.errors.named(feUnsupportedOp)
    check "fieldChecksOffLayout" notin show(r.errors)
    check not r.errors.named(feCheckOption)
    when not defined(cpp):
      check r.trusted

when not defined(cpp):
  proc scrub() {.noinline.} =
    ## Zero the stack below the caller, where the replay's frames land, so
    ## the bytes the constructor left unwritten read zero natively and the
    ## replay confirms the witness (the same as `tsymex_0016_wa_undefined_e2e`).
    var a {.volatile.}: array[8192, int]
    for i in 0 ..< a.len: a[i] = 0

  template indeterminate(fn: untyped) =
    scrub()
    let r = symexFind(fn, tLabel("hit"))
    checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds


  template indeterminateOrRefuted(fn: untyped) =
    ## The read of a byte nothing wrote taints the path, and the witness is
    ## replayed: confirmed it is sxSat untrusted with the kind, and refuted
    ## (the model's value for the byte is not the stack's) it stays sxUnknown
    ## with the havoc decline, as a `{.noinit.}` read does. Never trusted,
    ## never an exact verdict.
    scrub()
    let r = symexFind(fn, tLabel("hit"))
    checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
    check not r.trusted
    check r.status in {sxSat, sxUnknown}
    check r.errors.named(feGlobalHavoc) or
          UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds

  suite "PRC-07 slice A: the active arm's bytes (c backend)":
    test "a wrong-branch read is the active arm's bytes, by value":
      # x: int32 at bytes 4..8, wb: int16 at 6..8 -- the high half of x
      let r = pinExact(sutWideRead, fk, domain = sampled(
        [0x11220000'i32, 0x11223344'i32, 0x1122FFFF'i32, 0, 1, -1,
         0x00001122'i32, 0x22110000'i32]))
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(feUnsupportedOp)
      let w = int32(r.witness[0])
      check (w shr 16) == 0x1122
      # the walker's witness read natively is the value it claimed
      let o = Wd(k: kwa, x: w)
      check o.wb == 0x1122'i16

    test "the low half, a signed field":
      let r = pinExact(sutWideReadLow, fk, domain = sampled(
        [0x0000FFFE'i32, -2'i32, 0x1111FFFE'i32, 0, 1, -1, 0x0000FEFF'i32]))
      check r.status == sxSat
      check r.trusted
      check (int32(r.witness[0]) and 0xFFFF) == 0xFFFE

    test "a wider field than the active arm's field is its neighbours' bytes":
      let r = pinExact(sutNarrowRead, fk, domain = sampled(
        [5'i16, 0, 1, -1, 7'i16]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 5

    test "a narrower field is one byte of the active arm's":
      let r = pinExact(sutByteRead, fk, domain = sampled(
        [0x44'i32, 0x1144'i32, 0x4400'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check (int32(r.witness[0]) and 0xFF) == 0x44

    test "a wrong-branch write is a bit-insert into the active arm's slot":
      let r = pinExact(sutWideWrite, fk, domain = sampled(
        [0x1234'i32, 0x5678'i32, 0x7FFF1234'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(feUnsupportedOp)
      check (int32(r.witness[0]) and 0xFFFF) == 0x1234

    test "a write then a read of the same field round-trips":
      let r = pinExact(sutWriteThenRead, fk, domain = sampled(
        [0x42'i32, 0x1042'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check (int32(r.witness[0]) and 0xFFFF) == 0x42

    test "a write to the active field is seen through the other arm":
      let r = pinExact(sutWriteActiveThenWrong, fk, domain = sampled(
        [0x00070042'i32, 0x42'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check int32(r.witness[0]) == 0x00070042

    test "a packed variant is declined whole by its type-pragma row, never exact-and-wrong":
      # The layout is derived (pinned above), but the walker declines every
      # `{.packed.}` type at its construction (`pragma:type/packed`: layout
      # AND passing); lifting that row is not this slice's. Until then the
      # wrong layout can never be claimed.
      let r = symexFind(sutPackedRead, tLabel("hit"))
      checkpoint show(r.errors)
      check r.status == sxUnknown
      check r.errors.named(feUnsupportedOp)
      check "pragma:type/packed" in show(r.errors)
      check not r.errors.named(feCheckOption)

    test "bytes no field of the active arm owns are indeterminate":
      # `pb` is bytes 8..12, no field of arm A owns them and the constructor
      # names every field: Nim leaves them unwritten
      indeterminateOrRefuted(sutPadRead)
      indeterminateOrRefuted(sutPadZero)

    test "a partly covered extent is the field's bytes and indeterminate bytes":
      # h: int16 at 4..6; w: int32 at 4..8, its high half unwritten
      indeterminateOrRefuted(sutPartialRead)

    test "a float arm is its IEEE bits, and int bytes read back as a float":
      let r = pinExact(sutFloatRead, fk, domain = sampled(
        [0x3FF0000000000000'i64, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 0x3FF0000000000000'i64
      let r2 = pinExact(sutFloatFromInt, fk, domain = sampled(
        [0x3FF0000000000000'i64, 0, 1, -1]))
      check r2.status == sxSat
      check r2.trusted
      check r2.witness[0] == 0x3FF0000000000000'i64

    test "an enum arm field is its raw C value":
      let r = pinExact(sutEnumRead, fk, domain = sampled([1'i8, 0, 2, -1]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 1

    test "a range field overwritten with foreign bytes stays declined":
      pinDecline(sutRangeOverwrite, bk, feUnsupportedOp, tLabel("hit"),
                 "fieldChecksOffLayout", excluding = {feCheckOption})

    test "a char is a byte of the active arm's int":
      let r = pinExact(sutCharFromInt, fk, domain = sampled(
        [0x4100'i32, 0x41'i32, 0x1241FF'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check ((int32(r.witness[0]) shr 8) and 0xFF) == 0x41

    test "an unsigned byte written over the low byte of the active int":
      let r = pinExact(sutUByteWrite, fk, domain = sampled(
        [0x1200'i32, 0x12AB'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted

    test "a bool read of arbitrary bytes stays declined":
      pinDecline(sutBoolFromInt, bk, feUnsupportedOp, tLabel("hit"),
                 "fieldChecksOffLayout", excluding = {feCheckOption})

    test "an int read past the active arm's fields takes an unwritten byte":
      # z is bytes 4..8: u, 'A', true, and the unwritten byte 7
      indeterminateOrRefuted(sutIntFromBytes)

    test "a branch-changing discriminator write keeps the bytes: the new arm reads the old":
      # Native (generated C, ORC and release alike): `o.k = kwb` is the store
      # of the tag alone, so the int16 pair reads the int32's halves.
      let r = pinExact(sutDiscToPair, fk, domain = sampled(
        [0x11223344'i32, 0x00003344'i32, 0x11220000'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check int32(r.witness[0]) == 0x11223344
      check not r.errors.named(feUncheckedDiscBytes)
      check not r.errors.named(feUnsupportedOp)
      let o = block:
        var o = Wd(k: kwa, x: int32(r.witness[0]))
        o.k = kwb
        o
      check o.wa == 0x3344'i16 and o.wb == 0x1122'i16

    test "a discriminator write to a narrower arm reads the first byte":
      let r = pinExact(sutDiscToByte, fk, domain = sampled(
        [0x44'i32, 0x1144'i32, 0x4400'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check (int32(r.witness[0]) and 0xFF) == 0x44
      check not r.errors.named(feUncheckedDiscBytes)

    test "a write into the new arm lands beside the carried bytes":
      let r = pinExact(sutDiscThenWrite, fk, domain = sampled(
        [0x11220000'i32, 0x11223344'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check (int32(r.witness[0]) shr 16) == 0x1122
      check not r.errors.named(feUncheckedDiscBytes)

    test "a symbolic discriminator write carries the bytes too":
      let r = pinExact(sutDiscSymbolic, fk, domain = sampled(
        [0x11223344'i32, 0x00003344'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(feUncheckedDiscBytes)

    test "a discriminator write to a range arm (range checks on) keeps the havoc model":
      # a range holds only its own values: foreign bytes are no value of it
      # while the walker may assume range facts, so the new arm is the havoc
      let r = symexFind(sutDiscToRange, tLabel("hit"))
      checkpoint show(r.errors)
      check r.status == sxUnknown
      check r.errors.named(feUncheckedDiscBytes)

# PRC-07 slice B, zero-fill. Native, from the generated C (debug and release,
# c and cpp alike): `var x: V`, `default(V)` and a `result` that is not
# constructed in place are `nimZeroMem` first; an object constructor that
# names every field of its arm (`V(k: ka, a: v)`) is `x.k = 0; x.a = v` with
# NO zeroing, whether bound to a `let`/`var`, assigned over an existing
# variable or to `result`; a constructor that omits a field zeroes first.
# So the bytes the written fields do not own are the zero of the
# initialisation only for the zeroed constructions, and unspecified for the
# rest: a read that depends on them is the `{.noinit.}` finding, not a value.
type
  Kx = enum kxa, kxb, kxc
  Vx = object            ## int32 / int8 / int64: the arms overlap unevenly
    case k: Kx
    of kxa: a: int32
    of kxb: b: int8
    of kxc: r: int64

proc sutCtorProbe(v: int32) =
  # the previous agent's probe: native read 0x340_7FFFFFFF, the walker said
  # 0x7FFFFFFF, because the high half of `r` is no byte the constructor wrote
  var y = Vx(k: kxa, a: v)
  y.k = kxc
  if y.r == 0x7FFFFFFF'i64 and v == 0x7FFFFFFF: symexTarget("hit")

proc sutVarZero(v: int32) =
  # `var y: Vx` is zeroed, so the high half of `r` is zero
  var y: Vx
  y.a = v
  y.k = kxc
  if y.r == 0x7FFFFFFF'i64 and v == 0x7FFFFFFF: symexTarget("hit")

proc sutDefaultZero(v: int32) =
  var y = default(Vx)
  y.a = v
  y.k = kxc
  if y.r == 0x7FFFFFFF'i64 and v == 0x7FFFFFFF: symexTarget("hit")

proc sutOmitZero(v: int32) =
  # an omitted field makes Nim zero the object first
  var y = Vx(k: kxb)
  y.k = kxc
  if y.r == 0 and v == 1: symexTarget("hit")

proc sutCtorWriteBefore(v: int32) =
  # the field written before the read is defined again: its bytes are the
  # write's, the rest of `r` the constructor's
  var y = Vx(k: kxa, a: v)
  y.k = kxc
  y.r = 0x1122334455667788'i64
  if y.r == 0x1122334455667788'i64 and v == 1: symexTarget("hit")

proc sutCtorOverVar(v: int32) =
  # `x = V(...)` over an existing variable writes the named fields in place
  var y = Vx(k: kxc, r: 0)
  y = Vx(k: kxa, a: v)
  y.k = kxc
  if y.r == 0x7FFFFFFF'i64 and v == 0x7FFFFFFF: symexTarget("hit")

proc sutCtorResult(v: int32) =
  # the read through the other arm of an object built by a callee's `result`
  proc mk(a: int32): Vx = Vx(k: kxa, a: a)
  var y = mk(v)
  y.k = kxc
  if y.r == 0x7FFFFFFF'i64 and v == 0x7FFFFFFF: symexTarget("hit")

when not defined(cpp):
  suite "PRC-07 slice B: the zero of initialisation is the zeroed constructions'":
    test "a constructor's unwritten bytes are indeterminate: the probe case":
      indeterminate(sutCtorProbe)

    test "x = V(...) over an existing variable leaves the others unspecified":
      indeterminate(sutCtorOverVar)

    test "an object a callee built with a constructor is the same":
      # The garbage is the callee's own stack bytes, which the replay's frames
      # need not hold as zero, so the replay may refute the witness. That is
      # the indeterminate-read convention, not a new behaviour: a hit through
      # a callee's `{.noinit.}` slot is likewise replayed and, refuted, stays
      # sxUnknown (`tsymex_0016_wa_undefined_e2e`, `tsymex_0016_k10aa_axis`:
      # only the scrubbed stack confirms one). Either way it is never trusted.
      scrub()
      let r = symexFind(sutCtorResult, tLabel("hit"))
      checkpoint $r.status & " " & $r.soundness & " " & show(r.errors)
      check r.status in {sxUnknown, sxSat}
      check not r.trusted
      check r.errors.named(feGlobalHavoc) or
            UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds

    test "var x: V is zeroed: the probe case is exact":
      let r = pinExact(sutVarZero, fk, domain = sampled(
        [0x7FFFFFFF'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check int32(r.witness[0]) == 0x7FFFFFFF
      check r.soundness.undefinedKinds.len == 0

    test "default(V) is zeroed too":
      let r = pinExact(sutDefaultZero, fk, domain = sampled(
        [0x7FFFFFFF'i32, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted

    test "a constructor that omits a field zeroes the object first":
      let r = pinExact(sutOmitZero, fk, domain = sampled([1'i32, 0, 2, -1]))
      check r.status == sxSat
      check r.trusted

    test "a field written after the constructor owns its own bytes":
      let r = pinExact(sutCtorWriteBefore, fk, domain = sampled([1'i32, 0, 2, -1]))
      check r.status == sxSat
      check r.trusted
