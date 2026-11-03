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
##   (5) a split's axioms are built once, by the first query that reaches
##       it, newly reached splits in lowering order and before any chain or
##       link fact; later queries reuse them. S8ag's B1-1 probe is the
##       canary (a unit ceiling, both Z3 versions).
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8ba_remainder`, `tsymex_rfc0005_s8ba_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 76 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

# ---- (2) a seq of a distinct type --------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

type Mod10 = distinct int
proc `==`(a, b: Mod10): bool = int(a) mod 10 == int(b) mod 10
  ## A USER `==` (not borrowed): equality modulo 10. A builtin model that
  ## compares a seq's cells by their base values would contradict it.

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
