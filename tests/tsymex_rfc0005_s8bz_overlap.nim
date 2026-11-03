## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part C (item
## 6): a dereference that reaches a case object's inactive branch. Nim 2.2.10
## emits a union of one struct per branch, so the pointer reads and writes the
## active branch's bytes at that offset. The "nim" tests pin that on this
## backend, and a `confirmed` case's witness ran the real proc on it. Same-size
## scalars at one offset are modelled; anything else stays a stated decline.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.severity == sevHint
    r

template confirmed(fn: typed, lbl: string): untyped =
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

template declined(fn: typed, lbl: string): untyped =
  ## The inactive candidate's stated decline; other candidates may still hit.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feUnsupportedOp and "not the active one" in e.msg: named = true
    check named

type
  VK = enum vA, vB
  VI = object
    case k: VK
    of vA: a: int
    of vB: b: int
  VF = object
    case k: VK
    of vA: a: int64
    of vB: f: float64
  VU = object
    case k: VK
    of vA: a: int32
    of vB: u: uint32
  VS = object
    case k: VK
    of vA: a: int
    of vB: s: string
  VP = object
    case k: VK
    of vA: a32: int32
    of vB: b64: int64
  VM = object
    case k: VK
    of vA:
      x32, y32: int32
      c64: int64
    of vB:
      d64: int64
      e64: int64
  VE = object
    case k: VK
    of vA: discard
    of vB: g: int
  VK2 {.packed.} = object
    case k: VK
    of vA:
      p1: int8
      p2: int64
    of vB:
      q1: int32
      q2: int64
  HN = ref object
    case k: VK
    of vA: a: int64
    of vB: f: float64
  HF = ref object
    case k: VK
    of vA: a: int
    of vB: b: int

{.push fieldChecks: off.}
proc addrB(v: var VI): ptr int = addr v.b
proc addrF(v: var VF): ptr float64 = addr v.f
proc addrU(v: var VU): ptr uint32 = addr v.u
proc addrE64(v: var VM): ptr int64 = addr v.e64
proc addrD64(v: var VM): ptr int64 = addr v.d64
proc addrB64(v: var VP): ptr int64 = addr v.b64
proc addrQ2(v: var VK2): ptr int64 = addr v.q2
{.pop.}

suite "S8bz (6): Nim's bytes":
  test "nim: a same-size scalar at one offset is the active field":
    var v = VI(k: vA, a: 3)
    let p = addrB(v)
    check p[] == 3
    p[] = 7
    check v.a == 7
    check v.k == vA
  test "nim: a float's bytes are the integer's":
    var v = VF(k: vA, a: 0x3FF0000000000000'i64)
    let p = addrF(v)
    check p[] == 1.0
    p[] = 2.0
    check v.a == 0x4000000000000000'i64
  test "nim: a signed and an unsigned 32-bit integer":
    var v = VU(k: vA, a: -1'i32)
    let p = addrU(v)
    check p[] == 0xFFFFFFFF'u32
  test "nim: offsets past the first field, natural alignment":
    var v = VM(k: vA, x32: 1, y32: 2, c64: 99)
    check addrE64(v)[] == 99
    # A 64-bit field over two 32-bit ones: the partial overlap, not modelled.
    check addrD64(v)[] == ((2'i64 shl 32) or 1'i64)
  test "nim: under {.packed.} the fields at one natural offset do not overlap":
    var v = VK2(k: vA, p1: 0, p2: 0x0102030405060708'i64)
    check addrQ2(v)[] != 0x0102030405060708'i64
  test "nim: a wider field reads past the active one: bytes it does not hold":
    # Only that the address is the union's start: what lies past `a32` is
    # whatever the object was given, which the model does not lay out.
    var v = VP(k: vA, a32: 5)
    check cast[ptr int32](addrB64(v))[] == 5

# Each `p[] = ...; <active field> = ...` below leaves only the alias: the
# pointer's own cell would still hold what it was given.

proc p6i(v: var VI; p: ptr int) =
  if p != nil and v.k == vA:
    p[] = 1
    v.a = 3
    if p[] == 3 and v.a == 3: symexTarget("p6i")
proc p6iw(v: var VI; p: ptr int) =
  if p != nil and v.k == vA:
    v.a = 0
    p[] = 7
    if v.a == 7: symexTarget("p6iw")
proc p6idead(v: var VI; p: ptr int) =
  if p != nil and v.k == vA and v.a == 1:
    p[] = 7
    if v.a != 1 and v.a != 7: symexTarget("p6idead")
proc p6fr(v: var VF; p: ptr float64) =
  if p != nil and v.k == vA:
    p[] = 5.0
    v.a = 0x3FF0000000000000'i64
    if p[] == 1.0: symexTarget("p6fr")
proc p6fw(v: var VF; p: ptr float64) =
  if p != nil and v.k == vA:
    v.a = 0
    p[] = 1.0
    if v.a == 0x3FF0000000000000'i64: symexTarget("p6fw")
proc p6u(v: var VU; p: ptr uint32) =
  if p != nil and v.k == vA:
    p[] = 5'u32
    v.a = -1'i32
    if p[] == 0xFFFFFFFF'u32: symexTarget("p6u")
proc p6sq(xs: var seq[VI]; p: ptr int) =
  if p != nil and xs.len > 0 and xs[0].k == vA:
    p[] = 1
    xs[0].a = 3
    if p[] == 3: symexTarget("p6sq")
proc p6sqw(xs: var seq[VI]; p: ptr int) =
  if p != nil and xs.len > 0 and xs[0].k == vA:
    xs[0].a = 0
    p[] = 3
    if xs[0].a == 3: symexTarget("p6sqw")
proc p6tb(t: var Table[string, VI]; p: ptr int) =
  if p != nil and "a" in t and t["a"].k == vA:
    p[] = 1
    t["a"].a = 3
    if p[] == 3: symexTarget("p6tb")
proc p6hf(h: HF; p: ptr int) =
  if p != nil and h != nil and h.k == vA:
    h.a = 0
    p[] = 3
    if h.a == 3: symexTarget("p6hf")
proc p6s(v: var VS; p: ptr string) =
  if p != nil and v.k == vA:
    v.a = 3
    if p[] == "x": symexTarget("p6s")
proc p6p(v: var VP; p: ptr int64) =
  if p != nil and v.k == vA:
    if p[] == 3: symexTarget("p6p")
proc p6m(v: var VM; p: ptr int64) =
  if p != nil and v.k == vA:
    v.c64 = 9
    if p[] == 9: symexTarget("p6m")
proc p6k(v: var VK2; p: ptr int64) =
  if p != nil and v.k == vA:
    v.p2 = 9
    if p[] == 9: symexTarget("p6k")
proc p6hn(h: HN; p: ptr int64) =
  # The integer branch's bytes while a heap object's float is active; `a` reads
  # a NaN's bytes, which are no one value.
  if p != nil and h != nil and h.k == vB:
    h.f = 1.0
    if p[] == 0x3FF0000000000000'i64: symexTarget("p6hn")
proc p6e(v: var VE; p: ptr int) =
  if p != nil and v.k == vA:
    if p[] == 9: symexTarget("p6e")

suite "S8bz (6): an inactive branch":
  test "a same-size integer":
    confirmed(p6i, "p6i")
    confirmed(p6iw, "p6iw")
    discard clean(p6idead, "p6idead", sxUnsat)
  test "a float over an integer, and back":
    confirmed(p6fr, "p6fr")
    confirmed(p6fw, "p6fw")
    confirmed(p6u, "p6u")
  test "in a seq's element, a table's value, a heap object":
    confirmed(p6sq, "p6sq")
    confirmed(p6sqw, "p6sqw")
    confirmed(p6tb, "p6tb")
    confirmed(p6hf, "p6hf")
    confirmed(p6hn, "p6hn")
  test "any other overlap stays a stated decline":
    declined(p6s, "p6s")       # a string over an integer
    declined(p6p, "p6p")       # past the active field
    declined(p6m, "p6m")       # `d64` over two `int32`s
    declined(p6e, "p6e")       # a branch with no field
    declined(p6k, "p6k")       # the layout `{.packed.}` may change
