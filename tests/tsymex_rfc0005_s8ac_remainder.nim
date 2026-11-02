## RFC-0005 (soundness channels) slice S8ac -- S8aa's remainder.
##
## This slice closes:
##   (1) a callee that writes through a `var` parameter. A `var` REF
##       parameter (`proc noteR(cur: var Box, b: Box) = cur = b`) was read as
##       a dereference of the ref and faulted the walker ("sort mismatch at
##       array store value"). A `var` actual that is not a plain local (`h.n`,
##       `o.a`, `s[0]`, `p[]`, `h.cur`) was never written back: the caller
##       kept the old value (a false `sxSat` on the dead target). The
##       write-back was also dropped on a call-cache hit and on a raise, and
##       an inner `finally` did not run when an OUTER `except` caught the
##       raise (the same false `sxUnsat` in plain source);
##   (2) an unchecked signed `div` of a width-stamped Int offset by a
##       bitvector (`start div y`) reduced the whole nonlinear quotient
##       `mod 2^64`, and the query ran past 900 s (or out of
##       `seqQueryRLimit`). `-d:symexQueryStats` (this file's `.nim.cfg`)
##       now reports each query's own step count (`rlimitDelta`); the
##       recorded `rlimit` is the context's cumulative counter;
##   (3) a shift count outside `0 ..< width` took Z3's saturating
##       `bvshl`/`bvlshr`/`bvashr`, but Nim's C output masks the count with
##       `width - 1` (`5 shl 64 == 5`), so a witness could fail to replay;
##       `int8 shl int` faulted the walker (a width assertion);
##   (4) the short-circuit join declined an operand that allocates, and
##       table, set, distinct and variant state: 2^m paths.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is, c and cpp); the probe is
## quoted beside the test.
import std/[unittest, strutils, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8ac_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc walkSteps(): int =
  ## The walk's Z3 steps: the sum of each query's own count.
  for q in symexQueryStats: result += q.rlimitDelta

# ---- (1) writes through a `var` parameter ------------------------------------

type Box = ref object
  n: int
type Holder = ref object
  cur: Box
type Obj = object
  a: int
  b: int
type E = object of CatchableError

proc noteR(cur: var Box, b: Box) = cur = b
proc noteRc(cur: var Box, b: Box, x: int) =
  if x > 3: cur = b
proc readR(cur: var Box, b: Box): bool = cur == b
proc noteRn(cur: var Box, b: Box) = noteR(cur, b)
proc noteRf(cur: var Box, v: int) = cur.n = v
proc setI(c: var int, v: int) = c = v
proc setR(c: var int, v: int) =
  c = v
  return
proc setRaise(c: var int, v: int) =
  c = v
  if v > 3:
    raise newException(E, "x")
proc setAl(c: var int, h: Box, v: int) =
  c = v
  h.n = 5
proc getSet(c: var int, v: int): bool =
  c = v
  true

proc sutVarRef(a, b: Box) =
  symexAssume(a != nil and b != nil and a != b)
  var cur = a
  noteR(cur, b)
  if cur == b:
    symexTarget("vr")
  if cur == a:
    symexTarget("vr_dead")

proc sutVarRefC(a, b: Box, x: int) =
  symexAssume(a != nil and b != nil and a != b)
  var cur = a
  noteRc(cur, b, x)
  if cur == b and x < 5:
    symexTarget("vrc")
  if cur == b and x < 2:
    symexTarget("vrc_dead")

proc sutVarRefRead(a, b: Box) =
  var cur = a
  if readR(cur, b):
    symexTarget("vrr")

proc sutVarRefNest(a, b: Box) =
  symexAssume(a != nil and b != nil and a != b)
  var cur = a
  noteRn(cur, b)
  if cur == a:
    symexTarget("vrn_dead")
  if cur == b:
    symexTarget("vrn")

proc sutVarRefField(h: Holder, a, b: Box) =
  symexAssume(h != nil and a != nil and b != nil and a != b)
  h.cur = a
  noteR(h.cur, b)
  if h.cur == a:
    symexTarget("vrf_dead")
  if h.cur == b:
    symexTarget("vrf")

proc sutVarRefWriteField(a: Box, v: int) =
  symexAssume(a != nil)
  var cur = a
  noteRf(cur, v)
  if a.n == 9:
    symexTarget("vrw")

proc sutHeapField(h: Box, v: int) =
  symexAssume(h != nil)
  h.n = 1
  setI(h.n, v)
  if h.n == 1 and v != 1:
    symexTarget("hf_dead")
  if h.n == 7:
    symexTarget("hf")

proc sutValField(v: int) =
  var o = Obj(a: 1, b: 2)
  setI(o.a, v)
  if o.a == 1 and v != 1:
    symexTarget("vf_dead")

proc sutSeqElem(v: int) =
  var s = @[1, 2, 3]
  setI(s[0], v)
  if s[0] == 1 and v != 1:
    symexTarget("se_dead")

proc sutArrElem(v: int) =
  var s = [1, 2, 3]
  setI(s[0], v)
  if s[0] == 1 and v != 1:
    symexTarget("ae_dead")

proc sutDeref(p: ref int, v: int) =
  symexAssume(p != nil)
  p[] = 1
  setI(p[], v)
  if p[] == 1 and v != 1:
    symexTarget("dr_dead")

proc sutCache(v: int) =
  var a = 0
  var b = 0
  setR(a, v)
  setR(b, v)
  if b == v and v == 9:
    symexTarget("cache")

proc sutRaise(v: int) =
  var a = 0
  try:
    setRaise(a, v)
  except E:
    if a == v:
      symexTarget("raise")

proc sutRaiseField(h: Box, v: int) =
  symexAssume(h != nil)
  h.n = 0
  try:
    setRaise(h.n, v)
  except E:
    if h.n == v:
      symexTarget("rf")

proc sutExpr(h: Box, v: int) =
  symexAssume(h != nil)
  h.n = 0
  if getSet(h.n, v) and h.n == v and v == 4:
    symexTarget("ex")

proc sutFinallyOuter(v: int) =
  var u = 0
  try:
    try:
      if v > 3: raise newException(E, "x")
    finally:
      u = v
  except E:
    if u == v:
      symexTarget("fo")

proc sutAlias(h: Box, v: int) =
  symexAssume(h != nil)
  setAl(h.n, h, v)
  if h.n == 5:
    symexTarget("al")

proc sutAliasNative(h: Box, v: int) =
  ## `sutAlias`'s call, natively (RFC-0005 S8bs).
  setAl(h.n, h, v)

suite "S8ac (1): writes through a var parameter":

  template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)

  test "a var ref parameter is the caller's variable":
    ## RED: every shape `sxUnknown` (`weInternalWalkerFault`, "sort
    ## mismatch at array store value"); `vrr` `heUnresolvedRef`.
    verdict(sutVarRef, "vr", sxSat)
    verdict(sutVarRef, "vr_dead", sxUnsat)
    verdict(sutVarRefC, "vrc", sxSat)
    verdict(sutVarRefC, "vrc_dead", sxUnsat)
    verdict(sutVarRefRead, "vrr", sxSat)
    verdict(sutVarRefNest, "vrn", sxSat)
    verdict(sutVarRefNest, "vrn_dead", sxUnsat)
    verdict(sutVarRefField, "vrf", sxSat)
    verdict(sutVarRefField, "vrf_dead", sxUnsat)
    verdict(sutVarRefWriteField, "vrw", sxSat)

  test "a var actual that is a location is written back":
    ## RED: each `_dead` target `sxSat` (the caller kept the old value).
    ## Probe: `setI(h.n, 5)` leaves `h.n == 5`; the same for `o.a`, `s[0]`,
    ## an array element and `p[]`.
    verdict(sutHeapField, "hf_dead", sxUnsat)
    verdict(sutHeapField, "hf", sxSat)
    verdict(sutValField, "vf_dead", sxUnsat)
    verdict(sutSeqElem, "se_dead", sxUnsat)
    verdict(sutArrElem, "ae_dead", sxUnsat)
    verdict(sutDeref, "dr_dead", sxUnsat)

  test "the write-back survives a cache hit, a raise and an expression call":
    ## RED: `cache`, `raise` and `rf` `sxUnsat`. Probe: `sutRaise(4)`
    ## reaches the `except` with `a == 4`.
    verdict(sutCache, "cache", sxSat)
    verdict(sutRaise, "raise", sxSat)
    verdict(sutRaiseField, "rf", sxSat)
    verdict(sutExpr, "ex", sxSat)

  test "an inner finally runs when an outer except catches":
    ## RED: `sxUnsat` -- the inner `finally` was skipped when a handler of
    ## an enclosing frame matched. Probe: `sutFinallyOuter(4)` reaches the
    ## target.
    verdict(sutFinallyOuter, "fo", sxSat)

  test "a var actual that the callee may also reach goes by reference":
    ## `setAl(h.n, h, v)` writes `h.n` through both the parameter and `h`;
    ## a copy-in / copy-out write-back would pick one order, so S8ac
    ## declined it. RFC-0005 S8bs passes a heap lvalue by reference in
    ## general (S8ba's `byRefSub`): both writes land on the one cell in the
    ## callee's order, as in Nim (`h.n = 5` last, so the label is reached).
    let r = symexFind(sutAlias, tLabel("al"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOp)
    check not r.errors.hasKind(weInternalWalkerFault)
    let h = Box(n: 0)
    sutAliasNative(h, 3)
    check h.n == 5

# ---- (2) exact `start div y` ------------------------------------------------

type ScanError = object of CatchableError

proc readCStr(data: seq[byte], offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

{.push overflowChecks: off.}
proc sutDivY(data: seq[byte], start, y: int) =
  ## S8aa's probe: `start < 0 and y < 0` makes the quotient positive, or
  ## `low(int) div -1`, which traps (SIGFPE). (A negative start would
  ## raise `IndexDefect` in the scan, so it returns first.)
  if start < 0 and y < 0 and start div y < 0: symexTarget("dy_dead")
  if start < 0: return
  try:
    let (k, p) = readCStr(data, start)
    if k.len == 2 and p == start + 3: symexTarget("dy_hit")
  except ScanError:
    discard

proc sutDivP(data: seq[byte], start, y: int) =
  let (k, p) = readCStr(data, start)
  if y > 1 and p div y == 3 and k.len == 2:
    symexTarget("dp")

proc sutDivS(data: seq[byte], start, y: int) =
  let (k, p) = readCStr(data, start)
  if y > 1 and start div y == 3 and k.len == 2:
    symexTarget("ds")
{.pop.}

const exactUnchecked = SymexSettings(integerSemantics: isExact,
                                     arithChecks: {acDivByZero, acRange})

suite "S8ac (2): an exact unchecked div of an offset stays linear":

  template bounded(fn: typed, lbl: string, want: SymexStatusKind,
                   maxSteps: int) =
    block:
      symexQueryStats = @[]
      let r = symexFind(fn, tLabel(lbl), exactUnchecked)
      checkpoint lbl & " " & show(r.errors)
      checkpoint symexQueryStatsSummary()
      check r.status == want
      check not r.errors.hasKind(beSolverUndef)
      check walkSteps() <= maxSteps

  test "the dead quotient is refuted without the nonlinear wrap":
    ## RED: past 900 s (S8aa's probe). Now under 1.5M steps in all.
    bounded(sutDivY, "dy_dead", sxUnsat, 5_000_000)
    bounded(sutDivY, "dy_hit", sxSat, 5_000_000)

  test "a quotient of the scan result and of the offset are found":
    ## RED: `sxUnknown` (`beSolverUndef`, `seqQueryRLimit` exhausted: 40M
    ## and 20M steps). Now under 1M steps each.
    bounded(sutDivP, "dp", sxSat, 5_000_000)
    bounded(sutDivS, "ds", sxSat, 5_000_000)

  test "the stats report each query's own steps":
    ## `rlimit` is the context's cumulative counter: it never decreases
    ## within a walk, and the per-query deltas sum to no more than the last.
    symexQueryStats = @[]
    discard symexFind(sutDivS, tLabel("ds"), exactUnchecked)
    check symexQueryStats.len >= 2
    var prev = 0
    for q in symexQueryStats:
      check q.rlimit >= prev
      check q.rlimitDelta >= 0
      prev = q.rlimit
    check walkSteps() <= symexQueryStats[^1].rlimit

  test "measuring the steps does not change the model":
    ## RFC-0005 S8ac. The context's step counter moves about one unit per
    ## solver CREATED, and Z3's search depends on it. The measurement first
    ## read it from a solver made for that purpose, one per query: the
    ## counter under every later check shifted, and this build returned a
    ## different `dy_hit` model than a build without `-d:symexQueryStats`
    ## (`@[210, 254, 0]` for `@[140, 240, 0]` on Z3 5.1, `@[64, 254, 0]` for
    ## `@[222, 4, 0]` on 4.13.4, at walker 174). It now reads the counter
    ## from the query's own first solver. The same walk paused
    ## (`symexQueryStatsPaused`: no read, no record, as the plain build
    ## runs) and recorded must return the same model, on any Z3 and any
    ## walker.
    symexQueryStatsPaused = true
    let plain = symexFind(sutDivY, tLabel("dy_hit"), exactUnchecked)
    symexQueryStatsPaused = false
    symexQueryStats = @[]
    let measured = symexFind(sutDivY, tLabel("dy_hit"), exactUnchecked)
    check symexQueryStats.len >= 2
    check plain.status == sxSat
    check measured.status == sxSat
    if plain.status == sxSat and measured.status == sxSat:
      check measured.witness == plain.witness

# ---- (3) shift counts outside `0 ..< width` ---------------------------------

proc sutShl64(x, n: int) =
  if n == 64 and x == 5 and (x shl n) == 0:
    symexTarget("shl64_dead")
  if n >= 64 and x != 0 and (x shl n) == x:
    symexTarget("shl_mask")

proc sutShr65(x, n: int) =
  if x < 0 and n == 65 and (x shr n) == x div 2 - (if x mod 2 != 0: 1 else: 0):
    symexTarget("shr_mask")
  if x < -2 and n == 65 and (x shr n) == -1:
    symexTarget("shr_dead")

proc sutShl8(x: int8, n: int) =
  if x == 5 and n == -1 and (x shl n) == -128:
    symexTarget("shl8")

proc sutShlU(x: uint32, n: uint32) =
  if n == 33'u32 and x == 3'u32 and (x shl n) == 6'u32:
    symexTarget("shlu")

suite "S8ac (3): a shift count is masked to the operand width":

  test "x shl 64 is x, not 0":
    ## RED: `shl64_dead` `sxSat` with witness (5, 64), which does not
    ## replay (probe: `5 shl 64 == 5`); `shl_mask` `sxUnsat`.
    let d = symexFind(sutShl64, tLabel("shl64_dead"))
    checkpoint show(d.errors)
    check d.status == sxUnsat
    var x0 = 5
    var n0 = 64
    check (x0 shl n0) == 5
    let r = symexFind(sutShl64, tLabel("shl_mask"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (x, n) = r.witness
      check n >= 64 and x != 0 and (x shl n) == x

  test "a signed shr by 65 is a shr by 1":
    ## RED: `shr_mask`'s witness was (-1, 65) only (Z3's all-sign-bits);
    ## `shr_dead` `sxSat` (probe: `-4 shr 65 == -2`).
    let r = symexFind(sutShr65, tLabel("shr_mask"))
    check r.status == sxSat
    if r.status == sxSat:
      let (x, n) = r.witness
      check (x shr n) == x div 2 - (if x mod 2 != 0: 1 else: 0)
    let d = symexFind(sutShr65, tLabel("shr_dead"))
    checkpoint show(d.errors)
    check d.status == sxUnsat

  test "an int8 shifted by an int count masks by 7":
    ## RED: `weInternalWalkerFault` (`binBV: width mismatch`). Probe:
    ## `5'i8 shl -1 == -128`.
    let r = symexFind(sutShl8, tLabel("shl8"))
    checkpoint show(r.errors)
    check r.status == sxSat
    var x0 = 5'i8
    var n0 = -1
    check (x0 shl n0) == -128'i8

  test "a uint32 shl by 33 is a shl by 1":
    ## RED: `sxUnsat` (Z3's `bvshl` by 33 is 0). Probe: `3'u32 shl 33 == 6`.
    let r = symexFind(sutShlU, tLabel("shlu"))
    checkpoint show(r.errors)
    check r.status == sxSat
    var x0 = 3'u32
    var n0 = 33'u32
    check (x0 shl n0) == 6'u32

# ---- (4) the short-circuit join over allocation and container state ---------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
type K = enum kA, kB
type V = object
  case kind: K
  of kA: a: int
  of kB: b: int

proc sutAlloc(data: seq[byte], h: Holder) =
  symexAssume(data.len == 12 and h != nil)
  h.cur = Box(n: 0)
  if (data[0] == 1'u8 or (h.cur = Box(n: 1); true)) and
     (data[2] == 3'u8 or (h.cur = Box(n: 2); true)) and
     (data[4] == 5'u8 or (h.cur = Box(n: 3); true)) and
     (data[6] == 7'u8 or (h.cur = Box(n: 4); true)) and
     (data[8] == 9'u8 or (h.cur = Box(n: 5); true)) and
     (data[10] == 11'u8 or (h.cur = Box(n: 6); true)):
    if h.cur.n == 3:
      symexTarget("alloc")
    if h.cur.n == 7:
      symexTarget("alloc_dead")

proc sutAllocL(data: seq[byte]) =
  symexAssume(data.len == 12)
  var cur = Box(n: 0)
  if (data[0] == 1'u8 or (cur = Box(n: 1); true)) and
     (data[2] == 3'u8 or (cur = Box(n: 2); true)) and
     (data[4] == 5'u8 or (cur = Box(n: 3); true)) and
     (data[6] == 7'u8 or (cur = Box(n: 4); true)) and
     (data[8] == 9'u8 or (cur = Box(n: 5); true)) and
     (data[10] == 11'u8 or (cur = Box(n: 6); true)):
    if cur.n == 3:
      symexTarget("allocl")

proc sutTab(data: seq[byte], t: var Table[string, int]) =
  symexAssume(data.len == 12 and t.len == 0)
  if (data[0] == 1'u8 or (t["1"] = 1; true)) and
     (data[2] == 3'u8 or (t["2"] = 2; true)) and
     (data[4] == 5'u8 or (t["3"] = 3; true)) and
     (data[6] == 7'u8 or (t["4"] = 4; true)) and
     (data[8] == 9'u8 or (t["5"] = 5; true)) and
     (data[10] == 11'u8 or (t["6"] = 6; true)):
    if t.len == 2 and t.hasKey("3") and t.hasKey("6"):
      symexTarget("tab")
    if t.len == 1 and t.hasKey("3") and t.hasKey("6"):
      symexTarget("tab_dead")

proc sutSet(data: seq[byte], s: var HashSet[int]) =
  symexAssume(data.len == 12 and s.len == 0)
  if (data[0] == 1'u8 or (s.incl 1; true)) and
     (data[2] == 3'u8 or (s.incl 2; true)) and
     (data[4] == 5'u8 or (s.incl 3; true)) and
     (data[6] == 7'u8 or (s.incl 4; true)) and
     (data[8] == 9'u8 or (s.incl 5; true)) and
     (data[10] == 11'u8 or (s.incl 6; true)):
    if s.len == 2 and 2 in s and 5 in s:
      symexTarget("set")

proc sutDist(data: seq[byte], m0: Meters) =
  symexAssume(data.len == 12 and m0 == Meters(0))
  var m = m0
  if (data[0] == 1'u8 or (m = m + Meters(1); true)) and
     (data[2] == 3'u8 or (m = m + Meters(2); true)) and
     (data[4] == 5'u8 or (m = m + Meters(4); true)) and
     (data[6] == 7'u8 or (m = m + Meters(8); true)) and
     (data[8] == 9'u8 or (m = m + Meters(16); true)) and
     (data[10] == 11'u8 or (m = m + Meters(32); true)):
    if m == Meters(20):
      symexTarget("dist")

proc sutVar(data: seq[byte]) =
  symexAssume(data.len == 12)
  var v = V(kind: kA, a: 0)
  if (data[0] == 1'u8 or (v = V(kind: kB, b: 1); true)) and
     (data[2] == 3'u8 or (v = V(kind: kA, a: 2); true)) and
     (data[4] == 5'u8 or (v = V(kind: kB, b: 3); true)) and
     (data[6] == 7'u8 or (v = V(kind: kA, a: 4); true)) and
     (data[8] == 9'u8 or (v = V(kind: kB, b: 5); true)) and
     (data[10] == 11'u8 or (v = V(kind: kA, a: 6); true)):
    if v.kind == kB and v.b == 3:
      symexTarget("var")

const heapRoom = SymexSettings(budget: ResourceBudget(maxHeapDepth: 64))

suite "S8ac (4): the short-circuit join covers allocation and containers":

  template joined(fn: typed, lbl: string, st: static SymexSettings,
                  want: SymexStatusKind, maxCalls: int) =
    block:
      symexZ3CallCount = 0
      let r = symexFind(fn, tLabel(lbl), st)
      checkpoint lbl & " " & show(r.errors)
      checkpoint "z3 calls: " & $symexZ3CallCount
      check r.status == want
      check symexZ3CallCount <= maxCalls
      if r.status == sxSat:
        let d = r.witness[0]
        # Operand 3 (bytes 4) takes its right side; the later ones do not.
        check d[4] != 5 and d[6] == 7

  test "an operand that allocates joins (6 pairs)":
    ## RED: 87 / 441 / 75 Z3 calls.
    joined(sutAlloc, "alloc", heapRoom, sxSat, 16)
    joined(sutAlloc, "alloc_dead", heapRoom, sxUnsat, 16)
    joined(sutAllocL, "allocl", heapRoom, sxSat, 16)

  test "an operand that writes a table joins (6 pairs)":
    ## RED: 168 / 315 Z3 calls.
    joined(sutTab, "tab", SymexSettings(), sxSat, 16)
    joined(sutTab, "tab_dead", SymexSettings(), sxUnsat, 16)

  test "an operand that writes a set joins (6 pairs)":
    ## RED: 150 Z3 calls. `{2, 5}`: operands 2 and 5 take their right side.
    symexZ3CallCount = 0
    let r = symexFind(sutSet, tLabel("set"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] == 1 and d[2] != 3 and d[4] == 5 and d[6] == 7 and
            d[8] != 9 and d[10] == 11

  test "an operand that rebinds a distinct value joins (6 pairs)":
    ## RED: 229 Z3 calls. `20 == 4 + 16`: operands 3 and 5.
    symexZ3CallCount = 0
    let r = symexFind(sutDist, tLabel("dist"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 20
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] == 1 and d[2] == 3 and d[4] != 5 and d[6] == 7 and
            d[8] != 9 and d[10] == 11

  test "an operand that rebinds an object variant joins (6 pairs)":
    ## RED: 87 Z3 calls.
    joined(sutVar, "var", SymexSettings(), sxSat, 16)

  test "symexWalkerVersion >= 178":
    check parseInt(symexWalkerVersion) >= 178
