## RFC-0016 PRC-07 (slice A). The C layout of a Nim `case` object.
##
## Nim emits a variant as
##
##     struct { <fields before the case>; <disc>;
##              union { <single-field arm: the field itself>;
##                      <multi-field arm: struct { fields } _k_N>; ... }; }
##
## (read from the generated C of the pinned toolchain, c backend; a shared
## field before the case sits ahead of the discriminator, and the union is
## anonymous). The C ABI then fixes every offset: a member sits at the next
## multiple of its alignment, the union at the next multiple of the largest
## alignment among its members and spans the largest member rounded up to
## that alignment, and the struct's size is rounded to its own alignment.
##
## The walker keeps one `SymVal` slot per arm field. This module says where
## each arm field's bytes are, so a field outside the active arm can be read
## from, or written into, the bytes of the active arm's fields (C11 6.5.2.3
## note 95). It is pure: `ok` is false, with the reason, for a target whose
## layout is not derived here (the caller declines, as before).
##
## Derived for amd64 and arm64, little-endian, 64-bit pointers: there
## `alignof(T) == sizeof(T)` for every scalar below, on Linux, macOS and
## Windows (MSVC and mingw). i386 aligns an 8-byte scalar differently per
## OS, and big-endian reverses the byte order: both decline.
import std/[tables, options, strutils]
import ./types
import ./buildprofile

type
  PlaceKind* = enum
    pkInt         ## an integer or char: every bit pattern is a value
    pkRestricted  ## a `range`: readable as bytes, but arbitrary bytes may
                  ## leave its values
    pkEnum        ## an enum: its C width and raw value (slice B; an
                  ## out-of-range one is a plain value, as under
                  ## `--rangeChecks:off`)
    pkBool        ## a bool: the byte is 0 or 1
    pkOpaque      ## a float: its IEEE bits (slice B reinterprets them)

  Place* = object
    name*: string
    off*, size*: int      ## byte offset from the start of the object, and size
    kind*: PlaceKind
    ty*: IRType

  VariantLayout* = object
    ok*: bool
    why*: string          ## why not, when not `ok`
    size*, align*: int
    unionOff*: int
    plain*: seq[Place]
    arms*: OrderedTable[int, seq[Place]]   ## tag ordinal -> the arm's fields

  Piece* = object
    ## `len` bytes: from byte `fieldByte` of the arm field `field` (an index
    ## into its arm's places) to byte `targetByte` of the accessed field.
    field*, fieldByte*, targetByte*, len*: int

func alignUp(n, a: int): int = (n + a - 1) div a * a

func scalar(t: IRType): tuple[size: int, kind: PlaceKind] =
  ## The size (0: not derived) and kind of a leaf field of type `t`.
  if t == nil: return (0, pkOpaque)
  case t.kind
  of itInt:
    if t.width notin [8, 16, 32, 64]: return (0, pkOpaque)
    (t.width div 8,
     if t.enumName.len > 0: pkEnum   # an enum's ordinal range is not a `range`
     elif t.hasRange: pkRestricted
     else: pkInt)
  of itBool: (1, pkBool)
  of itFloat32: (4, pkOpaque)
  of itFloat64: (8, pkOpaque)
  else: (0, pkOpaque)

func variantLayout*(ty: IRType; cpu: Cpu; endian: Endian;
                    ptrBits: int): VariantLayout =
  func no(why: string): VariantLayout = VariantLayout(ok: false, why: why)
  if ty == nil or ty.kind != itVariant: return no("not a single-axis variant")
  if endian != enLittle: return no("a big-endian target")
  if cpu notin {cpuAmd64, cpuArm64} or ptrBits != 64:
    return no("a target whose C layout is not derived (only 64-bit amd64 " &
              "and arm64)")
  if ty.vInheritChain.len > 0 or ty.vIsAxisView:
    return no("a variant of an inheritance hierarchy")
  # RFC-0016 PRC-07 slice B (0a). `{.packed.}` is `#pragma pack(push, 1)`
  # around the whole struct (gcc also `__attribute__((__packed__))`): every
  # member of it, of the anonymous union and of each arm struct sits at
  # alignment 1 (pinned natively, `Wk` in `tsymex_0016_fieldoff`). Any other
  # layout pragma (`union`, `align`, `bitsize`, an imported struct) is a
  # layout the walker has not derived: declined, never exact-and-wrong.
  let packed = ty.vLayoutPragma == "packed"
  if ty.vLayoutPragma.len > 0 and not packed:
    return no("a `{." & ty.vLayoutPragma & ".}` object whose C layout is " &
              "not derived")
  var off = 0
  var align = 1
  proc place(at: var int; al: var int; name: string;
             t: IRType; dst: var seq[Place]; base: int): bool =
    let (sz, kind) = scalar(t)
    if sz == 0: return false
    let a = if packed: 1 else: sz
    at = alignUp(at, a)
    dst.add Place(name: name, off: base + at, size: sz, kind: kind, ty: t)
    at += sz
    al = max(al, a)
    true
  var res = VariantLayout(ok: true)
  for i, n in ty.vPlainFieldNames:
    if not place(off, align, n, ty.vPlainFieldTypes[i], res.plain, 0):
      return no("plain field `" & n & "` of a type whose size is not derived")
  let (dsz, _) = scalar(ty.vDiscTy)
  if dsz == 0: return no("a discriminator whose size is not derived")
  let dal = if packed: 1 else: dsz
  off = alignUp(off, dal) + dsz
  align = max(align, dal)
  var unionAlign, unionSize = 1
  var armRel: OrderedTable[int, seq[Place]]
  for arm in ty.vArms:
    var at = 0
    var al = 1
    var ps: seq[Place]
    for j, n in arm.fieldNames:
      if not place(at, al, n, arm.fieldTypes[j], ps, 0):
        return no("field `" & n & "` of a type whose size is not derived")
    unionAlign = max(unionAlign, al)
    unionSize = max(unionSize, alignUp(at, al))
    armRel[arm.tagOrdinal] = ps
  res.unionOff = alignUp(off, unionAlign)
  align = max(align, unionAlign)
  res.align = align
  res.size = alignUp(res.unionOff + alignUp(unionSize, unionAlign), align)
  for tag, ps in armRel:
    var abs = ps
    for p in abs.mitems: p.off += res.unionOff
    res.arms[tag] = abs
  res

func variantLayout*(ty: IRType): VariantLayout =
  ## The layout for the target this build compiles for.
  variantLayout(ty, buildSemantics.cpu, buildSemantics.endian,
                buildSemantics.ptrBits)

func layoutFieldNames*(lay: VariantLayout): seq[string] =
  ## Every arm field's name once, in declaration order.
  if not lay.ok: return
  for _, ps in lay.arms:
    for p in ps:
      if p.name notin result: result.add p.name

func layoutDump*(lay: VariantLayout): string =
  ## `size=8;x@4;a@4;b@6`: the object's size, then each arm field's offset.
  if not lay.ok: return "declined: " & lay.why
  result = "size=" & $lay.size
  for n in layoutFieldNames(lay):
    block found:
      for _, ps in lay.arms:
        for p in ps:
          if p.name == n:
            result.add ";" & n & "@" & $p.off
            break found

func accessPlace*(lay: VariantLayout; tags: openArray[int];
                  name: string): Option[Place] =
  ## The place of arm field `name` in the first of `tags` that declares it.
  if not lay.ok: return
  for t in tags:
    if lay.arms.hasKey(t):
      for p in lay.arms[t]:
        if p.name == name: return some(p)
