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
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8ac_remainder`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 70 s).

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

# ---- (1) writes through a `var` parameter ------------------------------------

type Box = ref object
  n: int
type Holder = ref object
  cur: Box
type Obj = object
  a: int
  b: int
{.push overflowChecks: off.}
{.pop.}

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
