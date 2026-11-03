## RFC-0005 slice S8cq -- what Nim does, on each memory manager, for what the
## rule rests on. No walker: run it under `--mm:refc`, `--mm:orc`, `--mm:arc`,
## with and without `-d:release`, and `-d:danger`, on c and cpp.
##
## Item 1, the allowlist. Every type on `typeCopiedByValue` keeps its value in the
## formal across a write through another name, on every setting. Anything in the
## second test is over the line: shared, whatever the setting.
##
## Item 3. Nim evaluates a target once, and the value of `+=` and `inc` before the
## location: each shape that stays decided is here.
import std/[unittest, tables]

type
  En = enum enA, enB, enC
  Rg = range[0 .. 100]
  DI = distinct int
  O1 = object
    x: int
  O3 = object
    x, b, c: int
  Tu = tuple[x, b: int]
  OP = object
    p: ptr int
    x: int
  OD = object
    d: DI
  Bx[T] = object
    a: T
  O4 = object
    x, b, c, d: int
  Inh = object of RootObj
    x: int
  BR {.byref.} = object
    x: int
  OS = object
    s: seq[int]

var gi: int
var gb: bool
var gc: char
var ge: En
var gf: float
var gRng: Rg
var gi8: int8
var gu: uint32
var gdi: DI
var go1: O1
var go3: O3
var gtu: Tu
var gop: OP
var god: OD
var gbx: Bx[int]
var gptr: ptr int
var gpt: pointer
var gcs: cstring
var gfn: proc (): int {.nimcall.}
var gref: ref int
var cellA, cellB: int
proc one(): int = 1
proc two(): int = 2

proc fi(a: int): int = (gi = 50; a)
proc fb(a: bool): bool = (gb = true; a)
proc fc(a: char): char = (gc = 'z'; a)
proc fe(a: En): En = (ge = enC; a)
proc ff(a: float): float = (gf = 50.0; a)
proc fr(a: Rg): Rg = (gRng = 50; a)
proc fi8(a: int8): int8 = (gi8 = 50; a)
proc fu(a: uint32): uint32 = (gu = 50; a)
proc fdi(a: DI): int = (gdi = DI(50); int(a))
proc fo1(a: O1): int = (go1.x = 50; a.x)
proc fo3(a: O3): int = (go3.x = 50; a.x)
proc ftu(a: Tu): int = (gtu.x = 50; a.x)
proc fop(a: OP): int = (gop.x = 50; a.x)
proc fod(a: OD): int = (god.d = DI(50); int(a.d))
proc fbx(a: Bx[int]): int = (gbx.a = 50; a.a)
proc fptr(a: ptr int): ptr int = (gptr = addr cellB; a)
proc fpt(a: pointer): pointer = (gpt = addr cellB; a)
proc fcs(a: cstring): cstring = (gcs = "b"; a)
proc ffn(a: proc (): int {.nimcall.}): int = (gfn = two; a())
proc frefCell(a: ref int): int = (gref[] = 50; a[])

var go4: O4
var ginh: Inh
var gbr: BR
var gs: seq[int]
var gstr: string
var gset: set[0 .. 200]
var gar: array[1, int]
proc fo4(a: O4): int = (go4.x = 50; a.x)
proc finh(a: Inh): int = (ginh.x = 50; a.x)
proc fbr(a: BR): int = (gbr.x = 50; a.x)
proc fs(a: seq[int]): int = (gs[0] = 50; a[0])
proc fstr(a: string): char = (gstr[0] = 'z'; a[0])
proc fset(a: set[0 .. 200]): bool = (gset = {7}; 7 in a)
proc far(a: array[1, int]): int = (gar[0] = 50; a[0])

proc ids(a: seq[int]): seq[int] = a
proc ido(a: O4): O4 = a

var gN: int
var gR: ref int
var gRo: ref int
var gIdx: int
var gSq: seq[int]
var gSR: ref seq[int]
var gStrR: ref string
proc getR(): ref int = (inc gN; gR)
proc getSR(): ref seq[int] = (inc gN; gSR)
proc getStrR(): ref string = (inc gN; gStrR)
proc nextI(): int = (inc gN; 0)
proc bump(v: var int) = inc v
proc chgR(): int =
  new(gR)
  1
proc chgI(): int =
  gIdx = 1
  1

suite "S8cq native":
  test "the allowlist: the formal keeps its value":
    gi = 1; check fi(gi) == 1
    gb = false; check fb(gb) == false
    gc = 'a'; check fc(gc) == 'a'
    ge = enA; check fe(ge) == enA
    gf = 1.0; check ff(gf) == 1.0
    gRng = 1; check fr(gRng) == 1
    gi8 = 1; check fi8(gi8) == 1
    gu = 1; check fu(gu) == 1
    gdi = DI(1); check fdi(gdi) == 1
    go1.x = 1; check fo1(go1) == 1
    go3.x = 1; check fo3(go3) == 1
    gtu.x = 1; check ftu(gtu) == 1
    gop.x = 1; check fop(gop) == 1
    god.d = DI(1); check fod(god) == 1
    gbx.a = 1; check fbx(gbx) == 1
    gptr = addr cellA; check fptr(gptr) == addr cellA
    gpt = addr cellA; check fpt(gpt) == addr cellA
    gcs = "a"; check fcs(gcs)[0] == 'a'
    gfn = one; check ffn(gfn) == 1
    new gref; gref[] = 1; check frefCell(gref) == 50

  test "over the line: the formal is the same memory":
    go4.x = 1; check fo4(go4) == 50
    ginh.x = 1; check finh(ginh) == 50
    gbr.x = 1; check fbr(gbr) == 50
    gs = @[1]; check fs(gs) == 50
    gstr = ""; gstr.add('a'); check fstr(gstr) == 'z'
    gset = {}; check fset(gset)
    gar[0] = 1; check far(gar) == 50

  test "a call's result is its own copy":
    gs = @[1]
    let c = ids(gs)
    gs[0] = 50
    check c[0] == 1
    go4.x = 1
    let d = ido(go4)
    go4.x = 50
    check d.x == 1

  test "stays decided: the target evaluated once":
    new gR; gR[] = 1; gN = 0
    reset(getR()[])
    check gN == 1 and gR[] == 0
    new gR; gR[] = 1; gN = 0
    wasMoved(getR()[])
    check gN == 1 and gR[] == 0
    new gR; gR[] = 1; gN = 0
    bump(getR()[])
    check gN == 1 and gR[] == 2
    new gR; gR[] = 1; gN = 0
    var y = 0
    (getR()[], y) = (3, 4)
    check gN == 1 and gR[] == 3 and y == 4
    new gSR; gSR[] = @[1]; gN = 0
    getSR()[].insert(9, 0)
    check gN == 1 and gSR[] == @[9, 1]
    new gStrR; gStrR[] = "a"; gN = 0
    getStrR()[].add('c')
    check gN == 1 and gStrR[] == "ac"
    gSq = @[1, 2]; gN = 0
    bump(gSq[nextI()])
    check gN == 1 and gSq[0] == 2
    gSq = @[1, 2]; gN = 0
    gSq[nextI()] = gSq[nextI()] + 1
    check gN == 2 and gSq[0] == 2
    gSq = @[1, 2]; gN = 0
    gSq.setLen(nextI() + 1)
    check gN == 1 and gSq.len == 1

  test "stays decided: the value is evaluated before the location is taken":
    new gR; gR[] = 1; gRo = gR
    gR[] += chgR()
    check gRo[] == 1 and gR[] == 1
    new gR; gR[] = 1; gRo = gR
    inc(gR[], chgR())
    check gRo[] == 1 and gR[] == 1
    gIdx = 0; gSq = @[1, 2, 3]
    gSq[gIdx] += chgI()
    check gSq[0] == 1 and gSq[1] == 3
    gIdx = 0; gSq = @[1, 2, 3]
    inc(gSq[gIdx], chgI())
    check gSq[0] == 1 and gSq[1] == 3
