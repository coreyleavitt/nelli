## RFC-0005 (soundness channels) slice S8ba -- S8au's remainder.
##
## Pinned here (the RFC's "As landed (S8ba)" note has the design and the
## measurements):
##   (1) a declined seq read left its compiler temporary (`__sym_idx_N`)
##       unbound, and the next read of it was recorded as an unmodelled
##       global (`feGlobalReadUnmodelled`). Every declining arm that owns a
##       result now binds it; a parser temporary read unbound is a walker
##       fault, never a global; a global write next to a temporary is
##       still seen;
##   (2) a `seq` of a distinct type is modelled: the backing array holds
##       the base sort, and an element is re-boxed on every read;
##   (3) every string / seq leaf has `len <= high(int)` (Nim's `len` is a
##       non-negative `int`), so an overflow or range raise path over a
##       string-derived index decides, in both integer encodings;
##   (4) a `var` / `addr` actual whose heap cell the callee can also reach
##       through a global or a capture is passed by reference through that
##       cell (S8au declined it): S8au's five dead labels are `sxUnsat`;
##   (5) a split's axioms are built when the split is lowered, so the order
##       its terms reach the context is fixed by the program, not by the
##       first query that reaches them; S8ag's B1-1 probe is the canary.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

# ---- (1) a compiler temporary is not a global ---------------------------------

type Pair = (int, string)

proc tupSeqIdx(x: int) =
  ## `seq[(int, string)]` is not backed (a scoped decline); the element
  ## read binds the temporary `__sym_idx_N` the comparison then reads.
  var s: seq[Pair] = @[(1, "a")]
  if s[0][0] == x: symexTarget("ti")

proc tupSeqPop(x: int) =
  var s: seq[Pair] = @[(1, "a")]
  let v = s.pop()
  if v[0] == x: symexTarget("tp")

var gW: int

proc storeElem(s: seq[int]) =
  gW = s[0]

proc tempThenGlobal(x: int) =
  ## A value read into a temporary and written to a global by a callee:
  ## the global write is carried back to the caller.
  gW = 0
  storeElem(@[x, 2])
  if gW == 3 and x == 3: symexTarget("tg")
  if gW != x: symexTarget("tg_dead")

suite "S8ba (1): a compiler temporary is never read as a global":

  test "a declined element read binds its temporary":
    template one(fn: typed, lbl: string) =
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.errors.hasKind(feGlobalReadUnmodelled)
      check not r.errors.hasKind(weInternalWalkerFault)
      check "__sym_" notin show(r.errors)
    one(tupSeqIdx, "ti")
    one(tupSeqPop, "tp")

  test "a temporary is not a global name":
    check not isGlobalEnvName("__sym_idx_2")
    check isGlobalEnvName(globalEnvPrefix & "m.gW")

  test "a global written from a temporary is seen by the caller":
    discard clean(tempThenGlobal, "tg", sxSat)
    discard clean(tempThenGlobal, "tg_dead", sxUnsat)

  test "every declining arm that owns a result binds it":
    ## Source audit: inside the walker's `isIndex` and `isSeqPop` arms a
    ## tainted fork never keeps the unbound env (`p.env`): the result is
    ## bound (`declinedIndexEnv` / `declinedResultEnv`).
    const src = staticRead("../src/nelli/smt/runtime.nim")
    var arm = ""
    var bad: seq[string]
    for ln in src.splitLines:
      if ln.startsWith("  of is") and ln.endsWith(":"): arm = ln.strip
      if arm in ["of isIndex:", "of isSeqPop:"] and
         "forkPathTainted(p, p.pc, p.env," in ln:
        bad.add arm & " " & ln.strip
    checkpoint bad.join("\n")
    check bad.len == 0

# ---- (2) a seq of a distinct type --------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

proc dSeq(x: int) =
  symexAssume(x > -100 and x < 100)   # no overflow path in `+`
  var s = @[Meters(1)]
  s.add(s[0] + Meters(x))
  if s[1] == Meters(3): symexTarget("sq")
  if s[1] == Meters(3) and x != 2: symexTarget("sq_dead")

proc dSeqAssign(x: int) =
  var s = @[Meters(1), Meters(2)]
  s[1] = Meters(x)
  if s.len == 2 and s[1] < s[0]: symexTarget("sa")
  if s[1] < s[0] and x >= 1: symexTarget("sa_dead")

proc dSeqPop(x: int) =
  var s = @[Meters(x)]
  s.add Meters(7)
  let a = s.pop()
  let b = s.pop()
  if a == Meters(7) and b == Meters(4): symexTarget("sp")
  if b != Meters(x) or s.len != 0: symexTarget("sp_dead")

proc dSeqLoop(x: int) =
  symexAssume(x > -100 and x < 100)
  var s = @[Meters(x), Meters(2)]
  var t = Meters(0)
  for m in s: t = t + m
  if t == Meters(5): symexTarget("sl")
  if t == Meters(5) and x != 3: symexTarget("sl_dead")

proc addRange(x: range[0..10]) =
  ## `.add` stored an `svInt` value (a `range` param under `isOptimised`)
  ## as the constant 0: a false `sxUnsat`.
  var s: seq[int] = @[]
  s.add(x)
  if s[0] == 7: symexTarget("ar")
  if s[0] != x: symexTarget("ar_dead")

proc add32(x: int32) =
  var s: seq[int32] = @[]
  s.add(x)
  s.add(5'i32)
  if s[0] == 7 and s[1] == 5: symexTarget("a32")
  if s[0] != x: symexTarget("a32_dead")

proc addStr(x: string) =
  var s: seq[string] = @[]
  s.add(x)
  if s[0] == "ab": symexTarget("as")

proc addF(x: float) =
  var s: seq[float] = @[]
  s.add(x)
  if s[0] == 1.5: symexTarget("af")

proc dParam(s: seq[Meters]) =
  if s.len > 0 and s[0] == Meters(3): symexTarget("dp")

suite "S8ba (2): a seq of a distinct type is modelled":

  test "add and index read":
    let r = clean(dSeq, "sq", sxSat)
    if r.status == sxSat: check r.witness[0] == 2
    discard clean(dSeq, "sq_dead", sxUnsat)

  test "index assignment":
    let r = clean(dSeqAssign, "sa", sxSat)
    if r.status == sxSat: check r.witness[0] < 1
    discard clean(dSeqAssign, "sa_dead", sxUnsat)

  test "pop":
    let r = clean(dSeqPop, "sp", sxSat)
    if r.status == sxSat: check r.witness[0] == 4
    discard clean(dSeqPop, "sp_dead", sxUnsat)

  test "a loop over the seq":
    let r = clean(dSeqLoop, "sl", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard clean(dSeqLoop, "sl_dead", sxUnsat)

  test "`.add` stores every backed element kind (was int64 / bool only)":
    let r = clean(addRange, "ar", sxSat)
    if r.status == sxSat: check r.witness[0] == 7
    discard clean(addRange, "ar_dead", sxUnsat)
    discard clean(add32, "a32", sxSat)
    discard clean(add32, "a32_dead", sxUnsat)
    discard clean(addStr, "as", sxSat)
    discard clean(addF, "af", sxSat)

  test "a seq[distinct] parameter stays a scoped witness decline":
    let r = symexFind(dParam, tLabel("dp"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedWitnessType)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "nim":
    var s = @[Meters(1)]
    s.add(s[0] + Meters(2))
    check s[1] == Meters(3)

# ---- (3) len(s) <= high(int) ---------------------------------------------------

type ScanError = object of CatchableError

proc readCStrS(data: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == '\0':
      return (acc, i + 1)
    acc.add data[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sNegDivStr(data: string, start, y: int) =
  ## S8au's item-2 string variant: the target is dead, and the `start + 3`
  ## overflow raise path is dead too (`start + 2 < len(data) <= high(int)`).
  if start < 0 and y > 1 and start div y == start: symexTarget("t")
  if start < 0: return
  try:
    let (k, p) = readCStrS(data, start)
    if k.len == 2 and p == start + 3: symexTarget("hit")
  except ScanError:
    discard

proc rFindNoBound(s: string) =
  ## S8au's `rf_dead` without its `i < 100` assume: `i + 1` cannot
  ## overflow, `i < len(s)`.
  let i = s.rfind("ab")
  if i >= 0 and s.find("ab", i + 1) >= 0: symexTarget("rf_dead")

const exact = SymexSettings(integerSemantics: isExact)

suite "S8ba (3): every string / seq length is at most high(int)":

  test "nim: len is a non-negative int":
    check typeof("".len) is int
    check typeof(newSeq[int]().len) is int

  test "S8au's item-2 string variant decides":
    discard clean(sNegDivStr, "t", sxUnsat)
    discard clean(sNegDivStr, "hit", sxSat)

  test "rf_dead without its bound":
    discard clean(rFindNoBound, "rf_dead", sxUnsat)

  test "the bit-vector encoding (isExact)":
    discard clean(sNegDivStr, "t", sxUnsat, exact)
    discard clean(sNegDivStr, "hit", sxSat, exact)
    discard clean(rFindNoBound, "rf_dead", sxUnsat, exact)

  test "the fact is Nim's: len is an int":
    ## Pinned against the source: `nimLenFacts` states `high(int64)`, and
    ## only in step 1c (its terms reach the shared context there only).
    const src = staticRead("../src/nelli/smt/runtime.nim")
    check "cstring($high(int64))" in src
    check "seqRangeFacts(ctx, roots) & nimLenFacts(ctx, lens)" in src

# ---- (4) by reference through a heap cell --------------------------------------

type Box = ref object
  x: int
type Other = ref object
  y: int
type Outer = ref object
  inner: Box

var gBox: Box
var gOtherRef: Other

proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

proc readXG(v: var int, k: int): int =
  v = k
  gBox.x

proc viaXG(v: var int, k: int) = setXG(v, k)

proc setXO(v: var int, k: int) =
  v = k
  gOtherRef.y = 5

proc setPXG(p: ptr int, k: int) =
  p[] = k
  gBox.x = 5

proc rebindThenSet(v: var int, k: int) =
  gBox = Box(x: 1)
  v = k

proc sutHeapG(k: int) =
  let p = Box(x: 0)
  gBox = p
  setXG(p.x, k)
  if p.x == 5: symexTarget("hg")
  if p.x == k and k != 5: symexTarget("hg_dead")

proc sutHeapGRead(k: int) =
  let p = Box(x: 0)
  gBox = p
  if readXG(p.x, k) == 5 and k == 5: symexTarget("hgr")
  if readXG(p.x, k) != k: symexTarget("hgr_dead")

proc sutHeapGVia(k: int) =
  let p = Box(x: 0)
  gBox = p
  viaXG(p.x, k)
  if p.x == 5 and k == 1: symexTarget("hgv")
  if p.x == k and k != 5: symexTarget("hgv_dead")

proc sutHeapGAddr(k: int) =
  let p = Box(x: 0)
  gBox = p
  setPXG(addr p.x, k)
  if p.x == 5 and k == 2: symexTarget("hga")
  if p.x == k and k != 5: symexTarget("hga_dead")

proc sutHeapOther(k: int) =
  let p = Box(x: 0)
  gOtherRef = Other(y: 0)
  setXO(p.x, k)
  if p.x == k and k == 9: symexTarget("ho")
  if p.x != k: symexTarget("ho_dead")

proc sutHeapCap(k: int) =
  let p = Box(x: 0)
  let q = p
  proc setXC(v: var int) =
    v = k
    q.x = 5
  setXC(p.x)
  if p.x == 5 and k == 3: symexTarget("hc")
  if p.x == k and k != 5: symexTarget("hc_dead")

proc sutHeapDirect(k: int) =
  gBox = Box(x: 0)
  setXG(gBox.x, k)
  if gBox.x == 5 and k == 4: symexTarget("hd")
  if gBox.x == k and k != 5: symexTarget("hd_dead")

proc sutHeapRebind(k: int) =
  ## The address is taken at the call: the callee's later rebind of
  ## `gBox` does not move `v`.
  let p = Box(x: 0)
  gBox = p
  rebindThenSet(p.x, k)
  if p.x == k and gBox.x == 1 and k == 6: symexTarget("hr")
  if p.x != k or gBox.x != 1: symexTarget("hr_dead")

proc sutHeapNested(k: int) =
  let o = Outer(inner: Box(x: 0))
  gBox = o.inner
  setXG(o.inner.x, k)
  if o.inner.x == 5 and k == 8: symexTarget("hn")
  if o.inner.x == k and k != 5: symexTarget("hn_dead")

proc sutHeapTupField(k: int) =
  ## The ref is a value-object field: still one ref, read at the call.
  var t = (b: Box(x: 0), n: 1)
  gBox = t.b
  setXG(t.b.x, k)
  if t.b.x == 5 and k == 7: symexTarget("ht")
  if t.b.x == k and k != 5: symexTarget("ht_dead")

proc sutHeapArrElem(k: int) =
  ## The ref is an array element: not a shape the specialisation spells,
  ## so S8au's decline stands.
  var a = [Box(x: 0)]
  gBox = a[0]
  setXG(a[0].x, k)
  if a[0].x == k and k != 5: symexTarget("he_dead")

suite "S8ba (4): a heap cell the callee also reaches is passed by reference":

  test "nim":
    let b = Box(x: 0)
    gBox = b
    setXG(b.x, 3)
    check b.x == 5
    let b2 = Box(x: 0)
    gBox = b2
    check readXG(b2.x, 3) == 3
    let b3 = Box(x: 0)
    gBox = b3
    rebindThenSet(b3.x, 6)
    check b3.x == 6 and gBox.x == 1
    let o = Outer(inner: Box(x: 0))
    gBox = o.inner
    setXG(o.inner.x, 8)
    check o.inner.x == 5

  test "hg":
    discard clean(sutHeapG, "hg", sxSat)
    discard clean(sutHeapG, "hg_dead", sxUnsat)
  test "hgr":
    discard clean(sutHeapGRead, "hgr", sxSat)
    discard clean(sutHeapGRead, "hgr_dead", sxUnsat)
  test "hgv":
    discard clean(sutHeapGVia, "hgv", sxSat)
    discard clean(sutHeapGVia, "hgv_dead", sxUnsat)
  test "hga":
    discard clean(sutHeapGAddr, "hga", sxSat)
    discard clean(sutHeapGAddr, "hga_dead", sxUnsat)
  test "ho":
    discard clean(sutHeapOther, "ho", sxSat)
    discard clean(sutHeapOther, "ho_dead", sxUnsat)
  test "hc":
    discard clean(sutHeapCap, "hc", sxSat)
    discard clean(sutHeapCap, "hc_dead", sxUnsat)
  test "a global root":
    discard clean(sutHeapDirect, "hd", sxSat)
    discard clean(sutHeapDirect, "hd_dead", sxUnsat)
  # These two paths make more than the default eight dereferences
  # (`maxHeapDepth`, which declines them as `heDepthExhausted`); the
  # budget is raised so the verdict itself is pinned.
  const deep = SymexSettings(budget: ResourceBudget(maxHeapDepth: 32))
  test "a rebind in the callee does not move the address":
    discard clean(sutHeapRebind, "hr", sxSat, deep)
    discard clean(sutHeapRebind, "hr_dead", sxUnsat, deep)
  test "a cell behind two refs":
    discard clean(sutHeapNested, "hn", sxSat, deep)
    discard clean(sutHeapNested, "hn_dead", sxUnsat, deep)
  test "a ref held in a value field":
    discard clean(sutHeapTupField, "ht", sxSat, deep)
    discard clean(sutHeapTupField, "ht_dead", sxUnsat, deep)
  test "a shape it cannot pass still declines":
    let r = symexFind(sutHeapArrElem, tLabel("he_dead"), deep)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOp)

# ---- (5) split term order -------------------------------------------------------

proc opDataStyleSlice(data: seq[byte]) =
  ## S8ag's B1-1 probe (`tsymex_r6_b1_stringbacked`).
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  let payload = data[4 .. ^1]
  if payload.len > 3 and payload[0] == 42'u8:
    symexTarget("opdata_slice_sat")

suite "S8ba (5): split terms are built when the split is lowered":

  test "B1-1 stays under its unit ceiling":
    symexQueryStats = @[]
    let r = symexFind(opDataStyleSlice, tLabel("opdata_slice_sat"))
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    checkpoint symexQueryStatsSummary()
    check r.status == sxSat
    check units <= 1_000_000

suite "S8ba: walker version floor":

  test "symexWalkerVersion >= 200":
    check parseInt(symexWalkerVersion) >= 200
