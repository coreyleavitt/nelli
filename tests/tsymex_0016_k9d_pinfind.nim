## RFC-0016 K9d -- `pinFind`, the generator that pins a suite's own
## `symexFind` call (W-54).
##
## `pinFind(fn, target, settings)` is `symexFind` with the same arguments and
## the same result, plus K9a's differential judgement of that result: a
## definite verdict (trusted `sxSat`, `sxUnsat`, `sxRaised`) is reproduced
## natively and written as a pin record; anything else (a decline, an untrusted
## or undefined-behaviour claim, a witness unsafe to run in-process) is
## returned as it came, with no record. The `sxUnsat` domain is generated per
## parameter from its type (`boundaryOf`): exhaustive for `bool` and for an
## ordinal of at most 256 values, the boundary sample otherwise. The cell is
## `family:generic:k9d/<file>/<fn>/<target>`, so the record says which suite
## and which call it evidences.
import std/[unittest, os, strutils, sequtils, tables, sets, algorithm, math]
import std/re
import nelli/symex
import ./s8cu_helpers
import ./k9d_hostile
import ./k9d_selective

let pinTmp = getTempDir() / ("k9d_pinfind_" & $getCurrentProcessId())
createDir(pinTmp)
# Private, as in K9a's file: the tests count this file's records.
putEnv("NELLI_PIN_DIR", pinTmp)

proc records(): seq[PinRecord] =
  for r in pinRecords(pinTmp): result.add r

proc recordsWith(part: string): seq[PinRecord] =
  records().filterIt(part in it.cell.key)

proc sutHit(x: int) =
  if x == 7: symexTarget("hit")

proc sutNever(x: int) =
  if x > 5 and x < 3: symexTarget("hit")

proc sutBool(a, b: bool) =
  if a and not a and b: symexTarget("hit")

proc sutI8(x: int8) =
  if x > 100 and x < 101: symexTarget("hit")

proc sutRange(x: range[3 .. 9]; y: int) =
  if x == 2: symexTarget("hit")

proc sutWide(x: range[0'u64 .. 5_000_000_000'u64]; y: range[1 .. 1_000_000]) =
  if x > 5_000_000_000'u64 or y > 1_000_000: symexTarget("hit")

proc sutVar(x: var int) =
  if x == 4 and x == 5: symexTarget("hit")
  x = 1

proc sutRet(x: int): int =
  if x == 9: symexTarget("hit")
  x + 1

proc sutRaise(x: int) =
  if x == 3: raise newException(ValueError, "three")

type
  Color = enum cRed, cGreen, cBlue
  Holey = enum hA = 1, hB = 5, hC = 9
  Cents = distinct int
  Tiny = distinct int8
  Flag = distinct bool

proc sutEnum(c: Color; n: int) =
  if c == cBlue and n == 2 and c == cRed: symexTarget("hit")

proc sutHoley(h: Holey) =
  if ord(h) == 5: symexTarget("hit")

proc sutDistinct(c: Cents) =
  if int(c) > 5 and int(c) < 3: symexTarget("hit")

proc sutTiny(t: Tiny) =
  if int(t) > 100 and int(t) < 101: symexTarget("hit")

# symexAssume: the walker restricts to the assumption; the native replay must
# reject a run that violates it.
proc sutAssumeUnsat(x: int) =
  symexAssume(x < 5)
  if x == 7: symexTarget("hit")

proc sutAssumeSat(x: int) =
  symexAssume(x > 5)
  if x == 7: symexTarget("hit")

proc sutAssumeAll(x: int) =
  symexAssume(x == 1000)
  if x == 7: symexTarget("hit")


proc sutAssumeSwallow(x: int) =
  try:
    symexAssume(x < 5)
  except Exception:
    discard
  if x == 7: symexTarget("hit")

# K9d-5: tuple, object and variant-object parameters (field-product domain).
type
  Pt = object
    x: int
    flag: bool
    c: Color
  Shape = object
    common: int8
    case k: Color
    of cRed: a: int
    of cGreen: b: bool
    else: c: int8
  Wide = object
    f0, f1, f2, f3, f4, f5: int
  Nested = tuple[p: Pt, n: int8]
  BoolColor = (bool, Color)
  IntBool = (int, bool)

proc sutTuple(t: (int, bool)) =
  if t[0] > 5 and t[0] < 3: symexTarget("hit")

proc sutTupleSat(t: (int, bool)) =
  if t[0] == 123_456 and t[1]: symexTarget("hit")

proc sutObject(p: Pt) =
  if p.x > 5 and p.x < 3 and p.flag: symexTarget("hit")

proc sutObjectSat(p: Pt) =
  if p.x == 4242 and p.c == cBlue: symexTarget("hit")

proc sutVariant(s: Shape) =
  if s.k == cRed and s.a > 5 and s.a < 3: symexTarget("hit")

proc sutWideObj(w: Wide) =
  if w.f0 > 5 and w.f0 < 3: symexTarget("hit")

proc sutNested(n: Nested) =
  if n.p.x > 5 and n.p.x < 3: symexTarget("hit")

type
  Flip = object
    case on: bool
    of true: x: int
    of false: y: int8

proc sutFlip(f: Flip) =
  if f.on and f.x > 5 and f.x < 3: symexTarget("hit")

proc sutSix(a, b, c, d, e, f: int) =
  if a > 5 and a < 3 and (b + c + d + e + f) == 0: symexTarget("hit")

# K9d-6: string and cstring parameters (literal-mined domain).
proc strHelper(s: string): bool =
  s == "helper-lit"

proc sutStrLit(s: string; n: int) =
  if s == "foo" and n > 5 and n < 3: symexTarget("hit")
  if s.len > 0 and s[0] == 'q' and s.len == 17: discard
  if strHelper(s): discard
  case s
  of "alpha": discard
  else: discard

proc sutStrUnsat(s: string) =
  if s.startsWith("config") and s.len > 9 and s.len < 3: symexTarget("hit")

proc sutStrSat(s: string) =
  if s.len == 4 and s[1] == '\x9C' and s[3] == 'k': symexTarget("hit")

proc sutStrTuple(t: (string, bool)) =
  if t[0] == "needle" and t[1] and not t[1]: symexTarget("hit")

type StrObj = object
  name: string
  n: int8

proc sutStrObj(o: StrObj) =
  if o.name == "obj-lit" and o.n > 5 and o.n < 3: symexTarget("hit")

proc sutStrTwo(a, b: string) =
  if a == "one" and b == "two" and a == "x": symexTarget("hit")

proc sutCstr(s: cstring) =
  if s == "cs-lit" and s == "other": symexTarget("hit")

# The bug sits at a literal's neighbour: it fires on "config" with its last
# byte removed, which only a neighbour-aware domain reaches.
proc sutNeighbour(s: string) =
  if s == "confi": symexTarget("hit")

# --- K9d-9: regex patterns ---------------------------------------------------

proc sutRxBound(s: string) =
  ## hits only on six k's: `k{2,5}` matches a prefix, the whole is outside
  if s.len == 6 and s.match(re"k{2,5}") and not s.match(re"^k{2,5}$"):
    symexTarget("hit")

proc sutRxUnsat(s: string) =
  if s.len == 2 and s.match(re"[b-d]{2}") and s[0] notin {'b' .. 'd'}:
    symexTarget("hit")

proc sutRxSat(s: string) =
  if s.len == 3 and s.match(re"x[0-9]y"): symexTarget("hit")

proc sutRxOutside(s: string) =
  if s.match(re"(.)\1") and s.len == 1: symexTarget("hit")

# K9d-7: collection parameters (seq, array, set, openArray, Table, HashSet).
type Quad = enum qA, qB, qC, qD

proc sutSeqUnsat(s: seq[int]) =
  if s.len > 5 and s.len < 3: symexTarget("hit")

proc sutSeqSat(s: seq[int]) =
  if s.len == 3 and s[0] == 4242 and s[2] == 99: symexTarget("hit")

proc sutSeqThresh(s: seq[int]) =
  if s.len == 37: symexTarget("hit")

proc sutOpen(a: openArray[int]) =
  if a.len > 5 and a.len < 3: symexTarget("hit")

proc sutArr(a: array[4, int8]) =
  if a[0] > 5 and a[0] < 3: symexTarget("hit")

proc sutSet(s: set[char]) =
  if 'a' in s and 'a' notin s: symexTarget("hit")

proc sutTable(t: Table[string, int]) =
  if t.len > 5 and t.len < 3: symexTarget("hit")

proc sutHashSet(t: HashSet[int]) =
  if t.len > 5 and t.len < 3: symexTarget("hit")

proc sutSeqTuple(t: (seq[int], bool)) =
  if t[0].len > 5 and t[0].len < 3: symexTarget("hit")

proc sutRangedTable(t: Table[string, range[0..100]]) =
  if t["a"] == 100: symexTarget("hit")

proc sutQuits(x: int) =
  if x > 5 and x < 3: symexTarget("hit")
  if x > 100: quit(3)

proc sutRangedSeq(xs: seq[range[1..100]]; i: int) =
  symexAssume(i >= 0 and i < xs.len)
  if xs[i] == 77: symexTarget("hit")

proc sutRangedArr(a: array[3, range[10..20]]) =
  if a[1] == 13: symexTarget("hit")

# ---- the float family (K9d-8) ----
type
  Meters = distinct float
  UnitF = range[0.0 .. 1.0]
  FObj = object
    w: float32
    n: int8

proc sutFloatNever(x: float) =
  if x > 2.0 and x < 1.0: symexTarget("hit")

proc sutF32Never(x: float32) =
  if x > 2.0'f32 and x < 1.0'f32: symexTarget("hit")

proc sutCdoubleNever(x: cdouble; y: cfloat) =
  if x > 2.0 and x < 1.0 and y == y: symexTarget("hit")

proc sutMetersNever(m: Meters) =
  if float(m) > 2.0 and float(m) < 1.0: symexTarget("hit")

proc sutNaN(x: float) =
  if x != x: symexTarget("hit")

proc sutNaN32(x: float32) =
  if x != x: symexTarget("hit")

proc sutNegZero(x: float) =
  if x == 0.0 and 1.0 / x < 0.0: symexTarget("hit")

proc sutNegZero32(x: float32) =
  if x == 0.0'f32 and 1.0'f32 / x < 0.0'f32: symexTarget("hit")

proc sutFloatNeighbour(x: float) =
  ## hits on exactly one value: the float64 after 0.1
  if x > 0.1 and x <= 0.10000000000000002: symexTarget("hit")

proc sutF32Neighbour(x: float32) =
  ## hits on exactly one value: the float32 after 0.1'f32
  if x > 0.1'f32 and x <= 0.10000001'f32: symexTarget("hit")

proc sutFloatLits(x: float; k: int) =
  if x > 0.75 and x < 0.25 and k == 1000: symexTarget("hit")

proc sutFloatSeq(xs: seq[float]) =
  if xs.len > 0 and xs[0] > 2.0 and xs[0] < 1.0: symexTarget("hit")

proc sutFloatArr(a: array[2, float32]) =
  if a[0] > 2.0'f32 and a[0] < 1.0'f32: symexTarget("hit")

proc sutFloatTuple(t: (float, int)) =
  if t[0] > 2.0 and t[0] < 1.0: symexTarget("hit")

proc sutFloatObj(o: FObj) =
  if o.w > 2.0'f32 and o.w < 1.0'f32: symexTarget("hit")

proc sutFloatPair(x: float; y: float32) =
  if x > 2.0 and x < 1.0 and y == y: symexTarget("hit")

proc bitsOf(x: float64): uint64 = cast[uint64](x)
proc bitsOf(x: float32): uint32 = cast[uint32](x)

proc hasBits[F](vs: seq[F]; x: F): bool =
  vs.anyIt(bitsOf(it) == bitsOf(x))

# ---- the ref family (K9d-10) ----

type
  RNode = ref object
    val: int
    next: RNode
  RHolder = object
    tag: bool
    cell: ref int

proc sutRefNil(p: ref int) =
  if p == nil: symexTarget("hit")

proc sutRefVal(p: ref int) =
  if p != nil and p[] == 7: symexTarget("hit")

proc sutAliasWrite(p, q: ref int) =
  ## hits only when `p` and `q` are one cell
  if p != nil and q != nil:
    p[] = 1
    q[] = 2
    if p[] == 2: symexTarget("hit")

proc sutAliasNever(p, q: ref int) =
  if p != nil and q != nil:
    p[] = 1
    q[] = 2
    if p == q and p[] == 1: symexTarget("hit")

proc sutTwin(p, q: ref int) =
  ## two distinct cells holding one value
  if p != nil and q != nil and p != q and p[] == q[]: symexTarget("hit")

proc sutWriteBack(p: ref int) =
  ## a write that would leak into the next run without the pool's restore
  ## (a second run on the cell would hit)
  if p != nil:
    if p[] == 424242: symexTarget("hit")
    p[] = 424242

proc sutCycle(n: RNode) =
  if n != nil and n.next == n: symexTarget("hit")

proc sutSibling(a, b: RNode) =
  if a != nil and b != nil and a != b and a.next == b: symexTarget("hit")

proc sutNodeLink(a, b: RNode) =
  if a != nil and b != nil and a.next == b and b.val == 3: symexTarget("hit")

proc sutHolderAlias(h: RHolder; p: ref int) =
  ## a field of a by-value parameter and a parameter are one cell
  if h.cell != nil and h.cell == p: symexTarget("hit")

proc sutPtrVal(p: ptr int) =
  if p != nil and p[] == 7: symexTarget("hit")

proc sutPtrShared(p, q: ptr int) =
  if p != nil and p == q: symexTarget("hit")

proc sutNodeNever(a, b: RNode) =
  if a != nil and b != nil:
    a.val = 1
    b.val = 2
    if a == b and a.val == 1: symexTarget("hit")


suite "K9d: pinFind":
  test "boundaryOf: exhaustive for bool and a small ordinal, sampled for int":
    check boundaryOf(bool).exhaustive
    check boundaryOf(bool).values == @[false, true]
    check boundaryOf(int8).exhaustive
    check boundaryOf(int8).values.len == 256
    check boundaryOf(range[3 .. 9]).values == @[3, 4, 5, 6, 7, 8, 9].mapIt(range[3 .. 9](it))
    check not boundaryOf(int).exhaustive
    check boundaryOf(int).values == boundaryInts.values
    check low(uint64) in boundaryOf(uint64).values
    check high(uint64) in boundaryOf(uint64).values

  test "a sat verdict is returned as symexFind's and pinned on its witness":
    let r = pinFind(sutHit, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 7
    let rs = recordsWith("/sutHit/")
    check rs.len == 1
    if rs.len == 1:
      check rs[0].cell.scope == faGeneric
      check rs[0].cell.key == "k9d/tsymex_0016_k9d_pinfind/sutHit/tLabel(\"hit\")"
      check rs[0].entry == "symexFind"
      check rs[0].verdict == pvExact
      check rs[0].walker == "sxSat"

  test "an unsat verdict is pinned over the generated domain":
    check pinFind(sutNever, tLabel("hit")).status == sxUnsat
    check pinFind(sutBool, tLabel("hit")).status == sxUnsat
    check pinFind(sutI8, tLabel("hit")).status == sxUnsat
    let n = recordsWith("/sutNever/")
    check n.len == 1 and not n[0].exhaustive and "[8]" in n[0].domain
    let b = recordsWith("/sutBool/")
    check b.len == 1 and b[0].exhaustive and "[4]" in b[0].domain
    let i = recordsWith("/sutI8/")
    check i.len == 1 and i[0].exhaustive and "[256]" in i[0].domain

  test "mixed parameter types, a range, a var parameter, a result":
    check pinFind(sutRange, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutRange/").len == 1
    check pinFind(sutVar, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutVar/").len == 1
    check pinFind(sutRet, tLabel("hit")).status == sxSat
    check recordsWith("/sutRet/").len == 1

  test "a raise verdict is pinned on its raising witness":
    let r = pinFind(sutRaise, tRaisedExn("ValueError"))
    check r.status == sxRaised or r.status == sxSat
    let rs = recordsWith("/sutRaise/")
    check rs.len == 1
    if rs.len == 1: check rs[0].verdict in {pvExact, pvRaised}

  test "the suite's own settings reach symexFind":
    const s = block:
      var s = defaultSymexSettings()
      s.budget.queryTimeoutMs = 0
      s
    check pinFind(sutHit, tLabel("hit"), s).status == sxSat
    check recordsWith("/sutHit/").len == 2

  test "a wide range parameter is generated and replayed at its declared type":
    ## the witness tuple holds a range as its base type, so the domain must
    ## come from the declared type or a native call would raise on conversion
    check pinFind(sutWide, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutWide/").len == 1

  test "boundaryOf an enum: every declared value, holes excluded":
    check boundaryOf(Color).exhaustive
    check boundaryOf(Color).values == @[cRed, cGreen, cBlue]
    check boundaryOf(Holey).exhaustive
    check boundaryOf(Holey).values == @[hA, hB, hC]

  test "boundaryOf a distinct type: its base type's domain, converted":
    check boundaryOf(Tiny).exhaustive
    check boundaryOf(Tiny).values.len == 256
    check boundaryOf(Flag).values.len == 2
    check not boundaryOf(Cents).exhaustive
    check boundaryOf(Cents).values.mapIt(int(it)) == boundaryInts.values

  test "enum, holey enum and distinct parameters are pinned":
    check pinFind(sutEnum, tLabel("hit")).status == sxUnsat
    check pinFind(sutHoley, tLabel("hit")).status == sxSat
    check pinFind(sutDistinct, tLabel("hit")).status == sxUnsat
    check pinFind(sutTiny, tLabel("hit")).status == sxUnsat
    let e = recordsWith("/sutEnum/")
    check e.len == 1 and not e[0].exhaustive and "[24]" in e[0].domain
    check "exhaustive[3]{cRed,cGreen,cBlue}" in e[0].domain
    check recordsWith("/sutHoley/").len == 1
    let t = recordsWith("/sutTiny/")
    check t.len == 1 and t[0].exhaustive and "[256]" in t[0].domain

  test "symexAssume: an unsat verdict that holds only under the assumption is pinned":
    check pinFind(sutAssumeUnsat, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutAssumeUnsat/").len == 1

  test "symexAssume: a sat witness satisfies the assumption and hits":
    let r = pinFind(sutAssumeSat, tLabel("hit"))
    check r.status == sxSat
    check recordsWith("/sutAssumeSat/").len == 1

  test "symexAssume: a domain every run of which is rejected fails the pin":
    ## the assumption holds only at 1000, outside the boundary sample
    check symexFind(sutAssumeAll, tLabel("hit")).status == sxUnsat
    expect PinFailure:
      discard pinFind(sutAssumeAll, tLabel("hit"))

  test "symexAssume: a SUT that catches every exception stays rejected":
    check pinFind(sutAssumeSwallow, tLabel("hit")).status == sxUnsat

  test "symexAssume: outside a pin it is unchanged (no raise, no state)":
    sutAssumeUnsat(7)
    symexAssume(false)
    let nr = nativeRun(sutAssumeUnsat(7))
    check nr.rejected
    check nr.hits.len == 0 and nr.raised.len == 0
    symexAssume(false)   # the gate is closed again after the run
    check not nativeRun(sutAssumeUnsat(1)).rejected

  test "pairwiseRows: every pair of values across two fields is in some row":
    for sizes in [@[2, 3], @[8, 8, 8, 8, 8, 8], @[3, 1, 5, 2], @[4], @[]]:
      let rows = pairwiseRows(sizes)
      check rows.len >= 1
      for i in 0 ..< sizes.len:
        for j in i + 1 ..< sizes.len:
          for a in 0 ..< sizes[i]:
            for b in 0 ..< sizes[j]:
              check rows.anyIt(it[i] == a and it[j] == b)
    check pairwiseRows(@[8, 8, 8, 8, 8, 8]).len < 1000
    check pairwiseRows(@[8, 8, 8, 8, 8, 8]) == pairwiseRows(@[8, 8, 8, 8, 8, 8])

  test "boundaryOf a tuple: the field product, exhaustive when its fields are":
    let d = boundaryOf(BoolColor)
    check d.exhaustive and d.values.len == 6
    check (true, cBlue) in d.values
    let m = boundaryOf(IntBool)
    check not m.exhaustive and m.values.len == 16

  test "boundaryOf an object: the field product, each field its own domain":
    let d = boundaryOf(Pt)
    check not d.exhaustive and d.values.len == 8 * 2 * 3
    check Pt(x: high(int), flag: true, c: cBlue) in d.values

  test "boundaryOf a variant object: each branch with its discriminator":
    let d = boundaryOf(Shape)
    check d.values.anyIt(it.k == cRed and it.a == 7)
    check d.values.anyIt(it.k == cGreen and it.b)
    check d.values.anyIt(it.k == cBlue and it.c == 127'i8)
    check d.values.anyIt(it.k == cBlue and it.common == -128'i8)
    # branch fields pair with the common field: 3 branches, 256 x ... capped
    check d.values.len > 0

  test "boundaryOf a large object is pairwise, bounded, and records its size":
    let d = boundaryOf(Wide)
    check not d.exhaustive
    check d.values.len < fieldProductFull
    check d.values.len >= 64
    for i in 0 ..< 8:
      for j in 0 ..< 8:
        let a = boundaryInts.values[i]
        let b = boundaryInts.values[j]
        check d.values.anyIt(it.f0 == a and it.f5 == b)
        check d.values.anyIt(it.f2 == a and it.f3 == b)

  test "tuple and object parameters are pinned over the field product":
    check pinFind(sutTuple, tLabel("hit")).status == sxUnsat
    check pinFind(sutObject, tLabel("hit")).status == sxUnsat
    check pinFind(sutVariant, tLabel("hit")).status == sxUnsat
    check pinFind(sutWideObj, tLabel("hit")).status == sxUnsat
    check pinFind(sutNested, tLabel("hit")).status == sxUnsat
    let t = recordsWith("/sutTuple/")
    check t.len == 1 and not t[0].exhaustive and "sampled[16]" in t[0].domain
    let o = recordsWith("/sutObject/")
    check o.len == 1 and "[48]" in o[0].domain
    check recordsWith("/sutVariant/").len == 1
    check recordsWith("/sutNested/").len == 1
    let w = recordsWith("/sutWideObj/")
    check w.len == 1 and not w[0].exhaustive

  test "a sat witness outside the pairwise set is still replayed exactly":
    let t = pinFind(sutTupleSat, tLabel("hit"))
    check t.status == sxSat
    check t.witness[0][0] == 123_456
    check not boundaryOf(IntBool).values.anyIt(it[0] == 123_456)
    let r = pinFind(sutObjectSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].x == 4242
    check recordsWith("/sutTupleSat/").len == 1
    check recordsWith("/sutObjectSat/").len == 1

  test "a parameter product beyond the cap is an all-pairs array over the parameters":
    check pinFind(sutSix, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutSix/")
    check r.len == 1 and not r[0].exhaustive
    check "sampled[" in r[0].domain and "sampled[65536]" notin r[0].domain

  test "a large exhaustive field is thinned only when the product is too large":
    check boundaryOf(Shape).values.len > 0
    let blue = boundaryOf(Shape).values.filterIt(it.k == cBlue)
    check blue.len == 81
    check blue.anyIt(it.common == low(int8) and it.c == high(int8))
    check boundaryOf(Shape).values.filterIt(it.k == cRed).len == 256 * 8

  test "a variant object whose case has no else is generated branch by branch":
    let d = boundaryOf(Flip)
    check d.values.anyIt(it.on and it.x == 7)
    check d.values.anyIt(not it.on and it.y == 127'i8)
    check d.values.len == 8 + 256
    check pinFind(sutFlip, tLabel("hit")).status == sxUnsat


  test "string literals and char literals of the SUT are harvested":
    let h = harvestLiterals(sutStrLit)
    check "foo" in h.strs and "alpha" in h.strs
    check "q" in h.strs                    # a char literal
    check "helper-lit" in h.strs           # followed into a helper
    check "hit" notin h.strs               # a symexTarget label is not data
    check 17 in h.ints and 5 in h.ints

  test "boundaryOf string: the fixed core, bounded and deterministic":
    clearStringHints()
    let d = boundaryOf(string)
    check not d.exhaustive
    check "" in d.values
    for c in ['\0', 'a', 'z', '0', '9', ' ', '-', '\x7F', '\x80', '\xFF']:
      check $c in d.values
    check "\xC3\xA9" in d.values and "\xE2\x82\xAC" in d.values
    check d.values.anyIt(it.len == 3 and it[0] == '\0')
    check d.values.len <= stringDomainCap
    check boundaryOf(string).values == d.values
    check d.values.deduplicate.len == d.values.len

  test "boundaryOf string with hints: each literal, its neighbours and its thresholds":
    setStringHints(harvestLiterals(sutStrUnsat))
    let d = boundaryOf(string)
    clearStringHints()
    check "config" in d.values
    check "confi" in d.values and "onfig" in d.values        # prefix, suffix
    check "configa" in d.values and "config\0" in d.values   # one byte appended
    check "confg" in d.values                                # one byte removed
    check "confih" in d.values                               # one byte changed
    check "CONFIG" in d.values
    check d.values.anyIt(it.len == 9) and d.values.anyIt(it.len == 10)
    check d.values.anyIt(it.len == 8)
    check d.values.len <= stringDomainCap

  test "the string domain is bounded however many literals the SUT holds":
    var strs: seq[string]
    for i in 0 ..< 200: strs.add "literal-number-" & $i
    setStringHints(StringHints(strs: strs, ints: @[3, 64, 1000]))
    let d = boundaryOf(string)
    clearStringHints()
    check d.values.len <= stringDomainCap
    check "literal-number-0" in d.values
    check "" in d.values

  test "boundaryOf cstring: the string set without an embedded NUL":
    setStringHints(StringHints(strs: @["cs-lit", "a\0b"], ints: @[]))
    let d = boundaryOf(cstring)
    clearStringHints()
    check not d.exhaustive
    check d.values.len > 100
    check d.values.allIt(it.len == ($it).len)   # no NUL cut a value short
    check "cs-lit" in d.values.mapIt($it)
    check "cs-lit".cstring in d.values

  test "a string sat witness outside the domain is still replayed exactly":
    let r = pinFind(sutStrSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 4
    check not boundaryOf(string).values.anyIt(it == r.witness[0])
    check recordsWith("/sutStrSat/").len == 1

  test "a string unsat verdict is pinned over the literal-mined domain":
    check pinFind(sutStrUnsat, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutStrUnsat/")
    check r.len == 1 and not r[0].exhaustive
    check "sampled[" in r[0].domain
    # the record is text: a NUL or a high byte in the domain shows escaped
    check r[0].domain.allIt(it in {' ' .. '~'})
    check pinFind(sutStrLit, tLabel("hit")).status == sxUnsat
    # the walker declines a cstring parameter: returned as it came, no record
    let cs = pinFind(sutCstr, tLabel("hit"))
    check cs.status == sxUnknown
    check cs.errors.named(feUnsupportedParamType)
    check recordsWith("/sutCstr/").len == 0

  test "a planted unsat claim over a literal's neighbour is refused":
    ## sutNeighbour hits on "confi", reachable only as "config" minus a byte;
    ## the harvested neighbour finds it where the fixed core cannot
    type W = tuple[s: string]
    let key = cellKey(faGeneric, "k9d6/neighbour")
    let settled = Soundness(replay: rsNotNeeded)
    let lie = SymexResult[W](status: sxUnsat, soundness: settled)
    setStringHints(StringHints(strs: @["config"], ints: @[]))
    let dom = boundaryOf(string)
    clearStringHints()
    check "confi" in dom.values
    expect PinFailure:
      discard pinExactOn(sutNeighbour, lie, key, domain = dom)
    check "confi" notin boundaryOf(string).values

  test "strings inside a tuple, an object and beside another string":
    check pinFind(sutStrTuple, tLabel("hit")).status == sxUnsat
    check pinFind(sutStrObj, tLabel("hit")).status == sxUnsat
    check pinFind(sutStrTwo, tLabel("hit")).status == sxUnsat
    let t = recordsWith("/sutStrTuple/")
    check t.len == 1 and not t[0].exhaustive
    let o = recordsWith("/sutStrObj/")
    check o.len == 1
    let w = recordsWith("/sutStrTwo/")
    check w.len == 1
    # the pair of strings stays inside the run cap, thinned not truncated
    check "sampled[" in w[0].domain and "sampled[65536]" notin w[0].domain

  test "the hints do not outlive a pinFind call":
    discard pinFind(sutStrUnsat, tLabel("hit"))
    check "config" notin boundaryOf(string).values

  test "boundaryOf seq: empty, short sequences over the core, bounded and deterministic":
    clearStringHints()
    let d = boundaryOf(seq[int])
    let core = boundaryInts.values
    check not d.exhaustive
    check d.values[0].len == 0
    for a in core:
      check @[a] in d.values
      for b in core: check @[a, b] in d.values
    check d.values.anyIt(it.len == 3 and it[0] == 0 and it[1] == -1 and it[2] == 7)
    check d.values.len <= seqDomainCap
    check boundaryOf(seq[int]).values == d.values
    check d.values.deduplicate.len == d.values.len
    check boundaryOf(seq[bool]).values.countIt(it.len == 3) == 8

  test "boundaryOf seq: lengths at the SUT's integer literals, filled with patterns":
    check 37 in harvestLiterals(sutSeqThresh).ints
    setStringHints(StringHints(strs: @[], ints: @[37]))
    let d = boundaryOf(seq[int])
    clearStringHints()
    for n in [36, 37, 38]:
      check d.values.anyIt(it.len == n and it.allIt(it == low(int)))      # all equal
      check d.values.anyIt(it.len == n and it.allIt(it == high(int)))
      check d.values.anyIt(it.len == n and it[0] == low(int) and it[^1] == high(int) and
                           it.isSorted)                                    # ascending
      check d.values.anyIt(it.len == n and it[0] == high(int) and it[^1] == low(int))
      check d.values.anyIt(it.len == n and it[0] == high(int) and
                           it[1 .. ^1].allIt(it == low(int)))              # outlier first
      check d.values.anyIt(it.len == n and it[^1] == high(int) and
                           it[0 ..< ^1].allIt(it == low(int)))             # outlier last
      check d.values.anyIt(it.len == n and it[0] == it[1] and it[0] != it[^1])  # duplicates
    check d.values.len <= seqDomainCap
    check boundaryOf(seq[int]).values.allIt(it.len != 37)    # the hints do not outlive the call

  test "boundaryOf seq is bounded however many literals the SUT holds":
    var ks: seq[int]
    for i in 1 .. 200: ks.add i
    setStringHints(StringHints(strs: @[], ints: ks))
    let d = boundaryOf(seq[byte])
    clearStringHints()
    check d.values.len <= seqDomainCap
    check @[byte(0)] in d.values and d.values[0].len == 0

  test "boundaryOf array: fixed length, all pairs over positions, plus patterns":
    let b = boundaryOf(array[3, bool])
    check b.exhaustive and b.values.len == 8
    let d = boundaryOf(array[5, int])
    let core = boundaryInts.values
    check not d.exhaustive
    check d.values.allIt(it.len == 5)
    for i in 0 ..< 5:
      for j in i + 1 ..< 5:
        for a in core:
          for c in core:
            check d.values.anyIt(it[i] == a and it[j] == c)
    for a in core: check d.values.anyIt(it.allIt(it == a))
    check d.values.anyIt(it.isSorted and it[0] != it[^1])
    check d.values.anyIt(it.reversed.isSorted and it[0] != it[^1])
    check d.values.len <= seqDomainCap
    check boundaryOf(array[3, int8]).values.len <= seqDomainCap

  test "boundaryOf set: empty, full, each singleton, each pair, each complement":
    let q = boundaryOf(set[Quad])
    check q.exhaustive and q.values.len == 16
    setStringHints(StringHints(strs: @["x"], ints: @[]))
    let d = boundaryOf(set[char])
    clearStringHints()
    check not d.exhaustive
    check d.values.anyIt(it == {})
    check d.values.anyIt(it == {'\0' .. '\255'})
    check d.values.anyIt(it == {'x'})
    check d.values.anyIt(it == {'x', '\0'})
    check d.values.anyIt(it == {'\0' .. '\255'} - {'x'})
    check d.values.len <= seqDomainCap
    check d.values.deduplicate.len == d.values.len

  test "boundaryOf Table and HashSet: empty, one to three entries over the core":
    setStringHints(StringHints(strs: @["key-lit"], ints: @[]))
    let t = boundaryOf(Table[string, int])
    clearStringHints()
    check not t.exhaustive
    check t.values[0].len == 0
    for n in 1 .. 3: check t.values.anyIt(it.len == n)
    check t.values.anyIt("key-lit" in it)
    check t.values.anyIt(it.len == 1 and it.hasKey("key-lit") and it["key-lit"] == low(int))
    check t.values.len <= seqDomainCap
    let h = boundaryOf(HashSet[int])
    check not h.exhaustive
    check h.values[0].len == 0
    for a in boundaryInts.values:
      check h.values.anyIt(it.len == 1 and a in it)
      for b in boundaryInts.values:
        if a != b: check h.values.anyIt(it.len == 2 and a in it and b in it)
    check h.values.anyIt(it.len == 3)
    check h.values.len <= seqDomainCap

  test "a seq unsat verdict is pinned over the generated domain":
    check pinFind(sutSeqUnsat, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutSeqUnsat/")
    check r.len == 1 and not r[0].exhaustive
    check "sampled[" in r[0].domain
    check pinFind(sutOpen, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutOpen/").len == 1
    check pinFind(sutSeqTuple, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutSeqTuple/").len == 1

  test "an array, a set, a table and a hash set are pinned":
    check pinFind(sutArr, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutArr/").len == 1
    check pinFind(sutSet, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutSet/").len == 1
    check pinFind(sutTable, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutTable/").len == 1
    check pinFind(sutHashSet, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutHashSet/").len == 1

  test "a seq sat witness outside the domain is still replayed exactly":
    let r = pinFind(sutSeqSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 3 and r.witness[0][0] == 4242
    check not boundaryOf(seq[int]).values.anyIt(it == r.witness[0])
    check recordsWith("/sutSeqSat/").len == 1

  test "a planted unsat claim over a harvested length is refused":
    ## sutSeqThresh hits at length 37; the SUT's own literal puts a 37-long
    ## sequence in the domain where the fixed core has none
    type W = tuple[s: seq[int]]
    let key = cellKey(faGeneric, "k9d7/threshold")
    let lie = SymexResult[W](status: sxUnsat, soundness: Soundness(replay: rsNotNeeded))
    setStringHints(harvestLiterals(sutSeqThresh))
    let dom = boundaryOf(seq[int])
    clearStringHints()
    check dom.values.anyIt(it.len == 37)
    expect PinFailure:
      discard pinExactOn(sutSeqThresh, lie, key, domain = dom)

  test "the size is recorded and bounded when collections cross":
    check pinFind(sutSeqTuple, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutSeqTuple/")
    check r.len >= 1
    let at = r[0].domain.find('[')
    let n = parseInt(r[0].domain[at + 1 ..< r[0].domain.find(']')])
    check n <= pinFindCap and n > 1

  test "a ranged element inside a collection is converted, not defaulted":
    ## the witness tuple holds `seq[range[1..100]]` as `seq[int]`; a type
    ## conversion does not turn it back, so the replay once ran the SUT on an
    ## empty collection (163rev_table_elem, 163rev_seqelem_promoted_int)
    let cs = convWitness(seq[range[1..100]], @[5, 7])
    check cs.len == 2 and cs[0] == 5 and cs[1] == 7
    expect RangeDefect:
      discard convWitness(seq[range[1..100]], @[0])
    let tb = convWitness(Table[string, range[0..100]], {"a": 100}.toTable)
    check tb.len == 1 and tb["a"] == 100
    let ca = convWitness(array[2, range[1..9]], [3, 4])
    check ca[0] == 3 and ca[1] == 4
    check convWitness(HashSet[range[1..9]], [3].toHashSet).len == 1
    expect PinFailure:
      discard convWitness(seq[string], 3)
    expect PinFailure:   # a tuple holding a ranged container: loud, not a default
      discard convWitness(tuple[s: seq[range[1..9]], n: int], (@[2], 5))
    let rt = pinFind(sutRangedTable, tLabel("hit"))
    check rt.status == sxSat
    check recordsWith("/sutRangedTable/").len == 1
    let rs = pinFind(sutRangedSeq, tLabel("hit"))
    check rs.status == sxSat
    check recordsWith("/sutRangedSeq/").len == 1
    let ra = pinFind(sutRangedArr, tLabel("hit"))
    check ra.status == sxSat
    check recordsWith("/sutRangedArr/").len == 1

  test "a suite's own overloads of add, len, items do not reach the domain":
    ## k9d_hostile declares `add(var seq[int], int)`, `len(seq[int16])` and
    ## `items(seq[int8])` and instantiates the domains under them first
    let i = hostileInt()
    check i.n == boundaryInts.values.len
    check i.st == sxUnsat
    let s = hostileSeqI16()
    check s.st == sxUnsat and s.n > 1
    check hostileSeqI8() == sxUnsat
    check recordsWith("/sutIntNever/").len == 1
    check recordsWith("/sutI16Never/").len == 1
    check recordsWith("/sutI8Never/").len == 1

  test "a seq[uint32] domain compiles beside a seq[seq[cuint]]":
    ## `system.add`'s instance for the two is shared and its C does not
    ## compile; the domain code appends with `domPut`
    check hostileSeqU32() == sxUnsat
    check recordsWith("/sutU32Never/").len == 1

  test "a SUT that calls quit is refused at compile time, not replayed":
    ## its unsat domain run would end this process at the first x > 100
    check not compiles(pinFind(sutQuits, tLabel("hit")))
    check symexFind(sutQuits, tLabel("hit")).status in {sxUnsat, sxUnknown}

  # ---- the float family (K9d-8) ----

  test "fNextUp and fNextDown step one ulp, across zero and to the infinities":
    check bitsOf(fNextUp(1.0)) == bitsOf(1.0) + 1
    check bitsOf(fNextDown(1.0)) == bitsOf(1.0) - 1
    check fNextUp(0.0) == 5e-324 and fNextDown(0.0) == -5e-324
    check fNextUp(-0.0) == 5e-324
    check bitsOf(fNextUp(-5e-324)) == bitsOf(-0.0)
    check fNextUp(fNextDown(Inf)) == Inf
    check fNextUp(Inf) == Inf and fNextDown(-Inf) == -Inf
    check fNextDown(Inf) == fNextDown(Inf)
    check fNextUp(NaN).isNaN
    check bitsOf(fNextUp(1.0'f32)) == bitsOf(1.0'f32) + 1
    check fNextUp(16777216'f32) == 16777218'f32

  test "boundaryOf float: the IEEE-754 edges, deterministic, bounded, no repeat":
    for pass in 0 .. 1:
      let d = boundaryOf(float)
      check not d.exhaustive
      check d.values.len <= seqDomainCap
      for x in [0.0, -0.0, 1.0, -1.0, 0.5, 5e-324, -5e-324,
                2.2250738585072009e-308, -2.2250738585072009e-308,
                2.2250738585072014e-308, -2.2250738585072014e-308,
                fNextDown(Inf), -fNextDown(Inf),
                Inf, -Inf, fNextUp(1.0), fNextDown(1.0),
                9007199254740992.0, fNextUp(9007199254740992.0), 9007199254740991.0,
                16777216.0, 16777217.0, 9.223372036854775807e18,
                fNextDown(9.223372036854775807e18), 2147483648.0, 2147483647.0]:
        check d.values.hasBits(x)
      check d.values.anyIt(it.isNaN)
      check d.values.countIt(it.isNaN) == 1
      var seen = initHashSet[uint64]()
      for v in d.values: check not seen.containsOrIncl(bitsOf(v))
      check d.values.mapIt(bitsOf(it)) == boundaryOf(float).values.mapIt(bitsOf(it))

  test "boundaryOf float32: every value a float32, its edges in float32 steps":
    let d = boundaryOf(float32)
    check d.values.len <= seqDomainCap
    for x in [0.0'f32, -0.0'f32, 1.0'f32, -1.0'f32, 1e-45'f32, -1e-45'f32,
              1.1754942e-38'f32, 1.17549435e-38'f32,
              fNextDown(float32(Inf)), -fNextDown(float32(Inf)),
              Inf.float32, -Inf.float32, 16777216'f32, 16777218'f32,
              16777215'f32]:
      check d.values.hasBits(x)
    check d.values.anyIt(it.isNaN)
    check d.values.hasBits(fNextUp(1.0'f32)) and d.values.hasBits(fNextDown(1.0'f32))
    var seen = initHashSet[uint32]()
    for v in d.values: check not seen.containsOrIncl(bitsOf(v))
    # the float64 domain names the float32 overflow edge (a narrowing bug)
    check boundaryOf(float).values.hasBits(float64(fNextDown(float32(Inf))))
    check boundaryOf(float).values.hasBits(fNextUp(float64(fNextDown(float32(Inf)))))

  test "float and integer literals of the SUT are harvested as numbers":
    let h = harvestLiterals(sutFloatLits)
    check 0.75 in h.nums and 0.25 in h.nums and 1000.0 in h.nums
    check harvestLiterals(sutF32Neighbour).nums.anyIt(float32(it) == 0.10000001'f32)

  test "boundaryOf float with hints: each literal, both neighbours, negated":
    setStringHints(StringHints(nums: @[0.1, 1000.0]))
    let d = boundaryOf(float)
    let d32 = boundaryOf(float32)
    clearStringHints()
    for x in [0.1, fNextUp(0.1), fNextDown(0.1), -0.1, fNextUp(-0.1),
              fNextDown(-0.1), 1000.0, fNextUp(1000.0), fNextDown(1000.0),
              -1000.0]:
      check d.values.hasBits(x)
    let t = 0.1'f32
    for x in [t, fNextUp(t), fNextDown(t), -t]:
      check d32.values.hasBits(x)
    # the float32 neighbours are float32 steps, not float64 ones rounded back
    check bitsOf(fNextUp(t)) == bitsOf(t) + 1
    check not boundaryOf(float).values.hasBits(fNextUp(0.1))

  test "the float domain is bounded however many literals the SUT holds":
    var ns: seq[float]
    for i in 0 ..< 500: ns.add float(i) * 0.37 + 0.01
    setStringHints(StringHints(nums: ns))
    let d = boundaryOf(float)
    clearStringHints()
    check d.values.len <= seqDomainCap and d.values.len > 50

  test "boundaryOf a float range, a distinct float, cfloat and cdouble":
    let r = boundaryOf(UnitF)
    check r.values.allIt(float(it) >= 0.0 and float(it) <= 1.0)
    check not r.values.anyIt(float(it).isNaN)
    check r.values.anyIt(float(it) == 1.0) and r.values.anyIt(float(it) == 5e-324)
    check r.values.anyIt(bitsOf(float(it)) == bitsOf(fNextDown(1.0)))
    let m = boundaryOf(Meters)
    check m.values.len == boundaryOf(float).values.len
    check boundaryOf(cfloat).values.len == boundaryOf(float32).values.len
    check boundaryOf(cdouble).values.len == boundaryOf(float).values.len

  test "a float unsat verdict is pinned over the generated domain":
    check pinFind(sutFloatNever, tLabel("hit")).status == sxUnsat
    check pinFind(sutF32Never, tLabel("hit")).status == sxUnsat
    check pinFind(sutCdoubleNever, tLabel("hit")).status == sxUnsat
    # (a float `range` parameter does not compile in the walker's parser,
    # `parseRangeBracket` reads its bounds as integers: its domain is
    # generated above, its pin waits on the walker)
    check pinFind(sutMetersNever, tLabel("hit")).status == sxUnsat
    for n in ["/sutFloatNever/", "/sutF32Never/", "/sutCdoubleNever/",
              "/sutMetersNever/"]:
      let r = recordsWith(n)
      check r.len == 1 and not r[0].exhaustive

  test "a NaN and a negative-zero witness replay bit-faithfully":
    let a = pinFind(sutNaN, tLabel("hit"))
    check a.status == sxSat and a.witness[0].isNaN
    let b = pinFind(sutNaN32, tLabel("hit"))
    check b.status == sxSat and b.witness[0].isNaN
    let c = pinFind(sutNegZero, tLabel("hit"))
    check c.status == sxSat and bitsOf(c.witness[0]) == bitsOf(-0.0)
    let e = pinFind(sutNegZero32, tLabel("hit"))
    check e.status == sxSat and bitsOf(e.witness[0]) == bitsOf(-0.0'f32)
    for n in ["/sutNaN/", "/sutNaN32/", "/sutNegZero/", "/sutNegZero32/"]:
      check recordsWith(n).len == 1

  test "a literal's neighbour as a sat witness is replayed exactly":
    let r = pinFind(sutFloatNeighbour, tLabel("hit"))
    check r.status == sxSat and bitsOf(r.witness[0]) == bitsOf(fNextUp(0.1))
    let s = pinFind(sutF32Neighbour, tLabel("hit"))
    check s.status == sxSat and bitsOf(s.witness[0]) == bitsOf(fNextUp(0.1'f32))
    check recordsWith("/sutFloatNeighbour/").len == 1
    check recordsWith("/sutF32Neighbour/").len == 1

  test "a planted unsat claim over a harvested float neighbour is refused":
    ## sutFloatNeighbour hits on the one float64 after 0.1: in the domain only
    ## as the harvested literal's neighbour
    let settled = Soundness(replay: rsNotNeeded)
    setStringHints(harvestLiterals(sutFloatNeighbour))
    let dom = boundaryOf(float)
    clearStringHints()
    check dom.values.hasBits(fNextUp(0.1))
    expect PinFailure:
      discard pinExactOn(sutFloatNeighbour,
        SymexResult[tuple[x: float]](status: sxUnsat, soundness: settled),
        cellKey(faGeneric, "k9d8/neighbour"), domain = dom)
    setStringHints(harvestLiterals(sutF32Neighbour))
    let dom32 = boundaryOf(float32)
    clearStringHints()
    expect PinFailure:
      discard pinExactOn(sutF32Neighbour,
        SymexResult[tuple[x: float32]](status: sxUnsat, soundness: settled),
        cellKey(faGeneric, "k9d8/neighbour32"), domain = dom32)
    # and a planted unsat over a NaN-only or a -0.0-only hit is refused
    expect PinFailure:
      discard pinExactOn(sutNaN,
        SymexResult[tuple[x: float]](status: sxUnsat, soundness: settled),
        cellKey(faGeneric, "k9d8/nan"), domain = boundaryOf(float))
    expect PinFailure:
      discard pinExactOn(sutNegZero,
        SymexResult[tuple[x: float]](status: sxUnsat, soundness: settled),
        cellKey(faGeneric, "k9d8/negzero"), domain = boundaryOf(float))

  test "floats inside a seq, an array, a tuple and an object":
    let sd = boundaryOf(seq[float])
    check sd.values.anyIt(it.len == 1 and it[0].isNaN)
    check sd.values.anyIt(it.len == 1 and bitsOf(it[0]) == bitsOf(-0.0))
    check pinFind(sutFloatSeq, tLabel("hit")).status == sxUnsat
    check pinFind(sutFloatArr, tLabel("hit")).status == sxUnsat
    check pinFind(sutFloatTuple, tLabel("hit")).status == sxUnsat
    check pinFind(sutFloatObj, tLabel("hit")).status == sxUnsat
    for n in ["/sutFloatSeq/", "/sutFloatArr/", "/sutFloatTuple/", "/sutFloatObj/"]:
      check recordsWith(n).len == 1

  test "two float parameters cross within the cap":
    check pinFind(sutFloatPair, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutFloatPair/")
    check r.len == 1
    let at = r[0].domain.find('[')
    let n = parseInt(r[0].domain[at + 1 ..< r[0].domain.find(']')])
    check n <= pinFindCap and n > 1000

  test "a suite that imports pinFind alone compiles and pins":
    ## k9d_selective imports `from ./s8cu_helpers import pinFind`; the
    ## expansion's helpers are bound where pinFind is declared
    check selectiveSat() == sxSat
    check selectiveUnsat() == sxUnsat
    check recordsWith("/selSat/").len == 1
    check recordsWith("/selUnsat/").len == 1

  test "regex literals are harvested as patterns, not as data":
    let h = harvestLiterals(sutRxBound)
    check h.pats == @["k{2,5}", "^k{2,5}$"]
    check "k{2,5}" notin h.strs
    check harvestLiterals(sutRxOutside).pats == @["(.)\\1"]

  test "regex members: each construct's members match the pattern natively":
    const pats = ["[a-z]+", "\\d{2,4}", "a|bc", "x.y", "(ab)*c", "[^0-9]?z",
                  "a+?b", "[[:punct:]]", "\\x41\\s", "colou?r", "(?:p|q)r{0,2}",
                  "[\\w-]", "\\.\\*", "(*UTF)\\x{e9}.", "(*LIMIT_MATCH=9)a{3}"]
    for p in pats:
      let r = parseRegex(p)
      check r.ok
      let mem = regexStages([p])[0]
      check mem.len > 0
      # a leading verb must stay first
      var verbs = ""
      var body = p
      while body.startsWith("(*"):
        let j = body.find(')')
        verbs.add body[0 .. j]
        body = body[j + 1 .. ^1]
      let full = re(verbs & "(?:" & body & ")\\z")
      for m in mem:
        if not m.match(full):
          checkpoint "pattern " & p & " member " & escape(m)
          check false
    let s = regexStages(["a{2,4}"])
    check "aa" in s[0] and "aaa" in s[0] and "aaaa" in s[0]
    check "a" in s[2] and "aaaaa" in s[2]           # min-1, max+1
    let alt = regexStages(["cat|dog|e"])[0]
    check "cat" in alt and "dog" in alt and "e" in alt
    let cls = regexStages(["[d-f]"])
    check "d" in cls[0] and "f" in cls[0]
    check "c" in cls[2] and "g" in cls[2]            # just outside the class
    check "" in regexStages(["a*"])[0]
    check "x\ny" in regexStages(["x.y"])[2]          # dot as a newline
    check "x\xC3\xA9y" in regexStages(["(*UTF)x.y"])[0]
    check "x\xC3\xA9y" notin regexStages(["x.y"])[0]

  test "regex boundaries: newline, CRLF, NUL and high bytes beside ^ and $":
    let b = regexStages(["^ab$"])[1]
    for v in ["ab\n", "\nab", "ab\r\n", "ab\0", "ab\xFF", "\x80ab", "", "\n"]:
      check v in b
    # PCRE's `$` matches before a final newline, `\z` does not
    check "ab\n".match(re"^ab$") and not "ab\n".match(re"^ab\z")
    let c = regexStages(["Ab"])[3]
    check "AB" in c and "ab" in c
    check regexStages(["\\d+"])[3].len == 0          # no letter, no case variant
    let e = regexStages(["abc"])[4]
    check "ac" in e and "abbc" in e and "ab\nc" in e and "abd" in e

  test "patterns outside the subset fall back to the plain string domain":
    for p in ["(.)\\1", "(?=a)b", "(?i)a", "a\\p{L}", "(?<n>a)"]:
      let r = parseRegex(p)
      check not r.ok and r.why.len > 0
      check regexValues([p]).len == 0
    let h = harvestLiterals(sutRxOutside)
    setStringHints(h)
    let d = boundaryOf(string)
    setStringHints(StringHints(strs: h.strs, ints: h.ints))
    let plain = boundaryOf(string)
    clearStringHints()
    check d.values == plain.values

  test "the regex domain is bounded and deterministic":
    var pats: seq[string]
    for i in 0 ..< 60:
      pats.add "(?:[a-" & $char(ord('b') + i mod 24) & "]{1," & $(i mod 7 + 1) &
               "}|x" & $i & "y+)\\d?$"
    let v = regexValues(pats)
    check v.len <= regexDomainCap and v.len > 200
    check v == regexValues(pats)
    check v.deduplicate.len == v.len
    check v.allIt(it.len <= 64)
    setStringHints(StringHints(pats: pats))
    let d = boundaryOf(string)
    clearStringHints()
    check d.values.len <= stringDomainCap
    check d.values.deduplicate.len == d.values.len

  test "a planted unsat claim over a quantifier's max+1 is refused":
    type W = tuple[s: string]
    let key = cellKey(faGeneric, "k9d9/rxbound")
    let settled = Soundness(replay: rsNotNeeded)
    let lie = SymexResult[W](status: sxUnsat, soundness: settled)
    check "kkkkkk" notin boundaryOf(string).values
    setStringHints(harvestLiterals(sutRxBound))
    let dom = boundaryOf(string)
    clearStringHints()
    check "kkkkkk" in dom.values
    expect PinFailure:
      discard pinExactOn(sutRxBound, lie, key, domain = dom)

  test "regex unsat and sat verdicts are pinned and record their constructs":
    check pinFind(sutRxUnsat, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutRxUnsat/")
    check r.len == 1
    check "regex[1 patterns, 0 outside]{" in r[0].domain
    check "class" in r[0].domain and "bound" in r[0].domain
    check r[0].domain.allIt(it in {' ' .. '~'})
    let s = pinFind(sutRxSat, tLabel("hit"))
    check s.status == sxSat
    check s.witness[0].match(re"x[0-9]y")
    check recordsWith("/sutRxSat/").len == 1

  # ---- the ref family (K9d-10) ----

  test "boundaryOf ref: nil first, fresh cells over the pointee's core, one pool":
    let d = boundaryOf(ref int)
    check not d.exhaustive
    check d.values[0] == nil
    check d.values.countIt(it != nil) >= 2
    # one pool per pointee type: a second call returns the same cells
    let e = boundaryOf(ref int)
    check e.values.len == d.values.len
    for i in 0 ..< d.values.len: check e.values[i] == d.values[i]
    # distinct cells holding one value (the twin)
    var twin = false
    for i in 1 ..< d.values.len:
      for j in i + 1 ..< d.values.len:
        if d.values[i][] == d.values[j][]: twin = true
    check twin
    check "nil" in describe(d) and "#" in describe(d)

  test "a nil and a fresh-cell witness replay; a ref unsat is pinned":
    let n = pinFind(sutRefNil, tLabel("hit"))
    check n.status == sxSat and n.witness[0] == nil
    let v = pinFind(sutRefVal, tLabel("hit"))
    check v.status == sxSat and v.witness[0] != nil and v.witness[0][] == 7
    check recordsWith("/sutRefNil/").len == 1
    check recordsWith("/sutRefVal/").len == 1
    check pinFind(sutAliasNever, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutAliasNever/").len == 1

  test "a planted unsat claim only an aliased input refutes is refused":
    type W = tuple[p: ref int, q: ref int]
    let lie = SymexResult[W](status: sxUnsat, soundness: Soundness(replay: rsNotNeeded))
    expect PinFailure:
      discard pinExactOn(sutAliasWrite, lie, cellKey(faGeneric, "k9d10/alias"),
                         domain = boundaryOf(ref int))
    # and one only two distinct cells of one value refute
    expect PinFailure:
      discard pinExactOn(sutTwin, lie, cellKey(faGeneric, "k9d10/twin"),
                         domain = boundaryOf(ref int))

  test "the alias witness is one cell at both positions, replayed":
    let r = pinFind(sutAliasWrite, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0] == r.witness[1]
    check recordsWith("/sutAliasWrite/").len == 1

  test "a write through a parameter does not leak into the next run":
    check pinFind(sutWriteBack, tLabel("hit")).status == sxSat
    check recordsWith("/sutWriteBack/").len == 1
    let d = boundaryOf(ref int)
    # the pin's domain runs wrote every cell; each is back to its value
    check d.values.allIt(it == nil or it[] != 424242)
    discard nativeRun(sutWriteBack(d.values[1]))
    let again = nativeRun(sutWriteBack(d.values[1]))
    check "hit" notin again.hits

  test "boundaryOf a recursive ref object: a cycle and chains, bounded":
    let d = boundaryOf(RNode)
    check d.values[0] == nil
    check d.values.len <= 16
    check d.values.anyIt(it != nil and it.next == it)
    check d.values.anyIt(it != nil and it.next != nil and it.next != it and
                         it.next.next != nil)
    type W = tuple[n: RNode]
    let lie = SymexResult[W](status: sxUnsat, soundness: Soundness(replay: rsNotNeeded))
    expect PinFailure:
      discard pinExactOn(sutCycle, lie, cellKey(faGeneric, "k9d10/cycle"),
                         domain = d)
    type W2 = tuple[a: RNode, b: RNode]
    let lie2 = SymexResult[W2](status: sxUnsat, soundness: Soundness(replay: rsNotNeeded))
    expect PinFailure:
      discard pinExactOn(sutSibling, lie2, cellKey(faGeneric, "k9d10/sibling"),
                         domain = d)

  test "a ref-object witness keeps its identity: a.next is b":
    let r = pinFind(sutNodeLink, tLabel("hit"))
    check r.status == sxSat
    check r.witness[1] != nil and r.witness[0].next == r.witness[1]
    check recordsWith("/sutNodeLink/").len == 1
    check pinFind(sutNodeNever, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutNodeNever/").len == 1

  test "a ref field of a by-value parameter shares the parameter's pool":
    let h = boundaryOf(RHolder)
    let p = boundaryOf(ref int)
    check h.values.anyIt(it.cell != nil and it.cell == p.values[1])
    proc viaHolder(h: RHolder) = sutHolderAlias(h, h.cell)
    type WH = tuple[h: RHolder]
    let lieH = SymexResult[WH](status: sxUnsat, soundness: Soundness(replay: rsNotNeeded))
    expect PinFailure:
      discard pinExactOn(viaHolder, lieH, cellKey(faGeneric, "k9d10/holder"),
                         domain = h)
    let r = pinFind(sutHolderAlias, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].cell != nil and r.witness[0].cell == r.witness[1]
    check recordsWith("/sutHolderAlias/").len == 1

  test "boundaryOf ptr: nil and the ref pool's cell addresses, shared":
    let d = boundaryOf(ptr int)
    let refs = boundaryOf(ref int)
    check d.values[0] == nil
    check d.values.len == refs.values.len
    check cast[pointer](d.values[1]) == cast[pointer](refs.values[1])
    check d.values[1][] == refs.values[1][]
    type W = tuple[p: ptr int, q: ptr int]
    let lie = SymexResult[W](status: sxUnsat, soundness: Soundness(replay: rsNotNeeded))
    expect PinFailure:
      discard pinExactOn(sutPtrShared, lie, cellKey(faGeneric, "k9d10/ptr"),
                         domain = d)
    let r = pinFind(sutPtrVal, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0][] == 7
    check recordsWith("/sutPtrVal/").len == 1
    check boundaryOf(pointer).values[0] == nil
    check boundaryOf(pointer).values.len == boundaryOf(ptr int).values.len

  test "two ref parameters cross within the bound and record sampled":
    let r = recordsWith("/sutNodeNever/")
    check r.len >= 1
    let at = r[^1].domain.find('[')
    let n = parseInt(r[^1].domain[at + 1 ..< r[^1].domain.find(']')])
    check n > 1 and n <= 2048
    check "sampled[" in r[^1].domain
