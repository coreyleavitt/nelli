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
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8ac_remainder_b`. Split so that each part compiles and runs
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

# ---- (4) the short-circuit join over allocation and container state ---------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
type K = enum kA, kB
type V = object
  case kind: K
  of kA: a: int
  of kB: b: int
