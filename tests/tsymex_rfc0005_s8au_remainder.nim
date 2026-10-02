## RFC-0005 (soundness channels) slice S8au -- the S8an / S8ag remainder.
##
## Pinned here (the RFC's "As landed (S8au)" note has the design and the
## measurements):
##   (1) a local distinct value with no distinct-typed parameter: closed by
##       S8ad (`ensureDistinctSort`, walker 175); re-pinned over more shapes
##       (borrowed `+` / `==` / `<`, default-initialised, float base, a
##       returned value, an object field). A `seq` of a distinct type is a
##       scoped decline (a different mechanism, reported);
##   (2) `start < 0 and y > 1 and start div y == start` under the sequence
##       theory: closed by S8ad (`divRangeFacts`) and pinned in
##       `tsymex_rfc0005_s8ad_remainder`; re-measured for S8au, not
##       re-walked here;
##   (3) a copy-in/copy-out `var` actual (or an `addr` actual) whose heap
##       cell a global or a capture the callee reaches can also hold:
##       RED, a false `sxSat` (the callee's write through the global was
##       lost to the write-back); now a scoped `feUnsupportedOp` decline
##       naming the global;
##   (4) every `find` needle (a literal of any length, a computed one) and
##       `rfind` lower to S8ag's index split: the axioms by a randomized
##       differential against Z3's own terms with three mutants, and the
##       walker by hits that were `sxUnknown` at the base;
##   (5) the chain facts link consecutive splits only (counted);
##   (6) the `c notin t` form follows the linked Z3 version;
##   and `var ptr` formals: `f(addr x)` does not compile; a local `p = addr
##   x` passed to one was `heUnsafeCast`, and is now S8an's local pointer.
import std/[unittest, strutils, random, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template declines(fn: typed, lbl: string, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (1) local distinct values ------------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

type Secs = distinct float
proc `+`(a, b: Secs): Secs {.borrow.}
proc `<`(a, b: Secs): bool {.borrow.}

type HoldM = object
  m: Meters

proc dLine(x: int) =
  var m = Meters(0)
  m = m + Meters(1)
  if m == Meters(1) and x == 3: symexTarget("line")
  if m == Meters(2): symexTarget("line_dead")

proc dZero(x: int) =
  var m: Meters
  m = m + Meters(x)
  if m == Meters(4): symexTarget("zero")
  if m == Meters(4) and x != 4: symexTarget("zero_dead")

proc dCmp(x: int) =
  let m = Meters(x)
  if m < Meters(3) and x > 1: symexTarget("cmp")
  if m < Meters(3) and x > 5: symexTarget("cmp_dead")

proc dFloat(x: float) =
  var s = Secs(1.5)
  s = s + Secs(x)
  if Secs(2.0) < s: symexTarget("flt")

proc mkM(x: int): Meters = Meters(x) + Meters(1)

proc dRet(x: int) =
  symexAssume(x > -100 and x < 100)   # no overflow path in `mkM`
  let m = mkM(x)
  if m == Meters(5): symexTarget("ret")
  if m == Meters(5) and x != 4: symexTarget("ret_dead")

proc dField(x: int) =
  symexAssume(x > -100 and x < 100)   # no overflow path in `+`
  var o = HoldM(m: Meters(1))
  o.m = o.m + Meters(x)
  if o.m == Meters(3): symexTarget("fld")
  if o.m == Meters(3) and x != 2: symexTarget("fld_dead")

proc dSeq(x: int) =
  ## A different mechanism (reported, not fixed here): a `seq` of a
  ## distinct type is not modelled; it declines, scoped, with no fault.
  var s = @[Meters(1)]
  s.add(s[0] + Meters(x))
  if s[1] == Meters(3): symexTarget("sq")

suite "S8au (1): a local distinct value":
  test "line": (verdict(dLine, "line", sxSat); verdict(dLine, "line_dead", sxUnsat))
  test "zero": (verdict(dZero, "zero", sxSat); verdict(dZero, "zero_dead", sxUnsat))
  test "cmp": (verdict(dCmp, "cmp", sxSat); verdict(dCmp, "cmp_dead", sxUnsat))
  test "flt": verdict(dFloat, "flt", sxSat)
  test "ret": (verdict(dRet, "ret", sxSat); verdict(dRet, "ret_dead", sxUnsat))
  test "fld": (verdict(dField, "fld", sxSat); verdict(dField, "fld_dead", sxUnsat))
  test "a seq of a distinct type declines, scoped, with no walker fault":
    let r = symexFind(dSeq, tLabel("sq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(seNestedSeqUnsupported)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (3) copy-in/copy-out through a global -----------------------------------

type Box = ref object
  x: int
type Other = ref object
  y: int

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

proc sutHeapG(k: int) =
  let p = Box(x: 0)
  gBox = p
  setXG(p.x, k)
  if p.x == 5: symexTarget("hg")
  if p.x == k and k != 5: symexTarget("hg_dead")

proc sutHeapGRead(k: int) =
  let p = Box(x: 0)
  gBox = p
  if readXG(p.x, k) != k: symexTarget("hgr_dead")

proc sutHeapGVia(k: int) =
  let p = Box(x: 0)
  gBox = p
  viaXG(p.x, k)
  if p.x == k and k != 5: symexTarget("hgv_dead")

proc sutHeapGAddr(k: int) =
  let p = Box(x: 0)
  gBox = p
  setPXG(addr p.x, k)
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
  if p.x == k and k != 5: symexTarget("hc_dead")

suite "S8au (3): copy-in/copy-out through a global":
  test "hg":
    declines(sutHeapG, "hg", feUnsupportedOp, "gBox")
    declines(sutHeapG, "hg_dead", feUnsupportedOp, "gBox")
  test "hgr": declines(sutHeapGRead, "hgr_dead", feUnsupportedOp, "gBox")
  test "hgv": declines(sutHeapGVia, "hgv_dead", feUnsupportedOp, "gBox")
  test "hga": declines(sutHeapGAddr, "hga_dead", feUnsupportedOp, "gBox")
  test "ho":
    verdict(sutHeapOther, "ho", sxSat)
    verdict(sutHeapOther, "ho_dead", sxUnsat)
  test "hc": declines(sutHeapCap, "hc_dead", feUnsupportedOp, "`q`")

# ---- var ptr ------------------------------------------------------------------

proc setVP(p: var ptr int, v: int) = p[] = v
proc reVP(p: var ptr int, q: ptr int) = p = q
proc setPlain(p: ptr int, v: int) = p[] = v
proc fwdVP(p: var ptr int, v: int) = setVP(p, v)
proc toPlain(p: var ptr int, v: int) = setPlain(p, v)
proc incVP(p: var ptr int) = p[] += 1

proc sutVarPtr(v: int) =
  var x = 0
  var p = addr x
  setVP(p, v)
  if x == 7: symexTarget("vp")
  if x != v: symexTarget("vp_dead")

proc sutVarPtrFwd(v: int) =
  symexAssume(v >= 0 and v < 100)   # no overflow path in `x + 1`
  var x = 0
  var p = addr x
  fwdVP(p, v)
  toPlain(p, x + 1)
  if x == 7: symexTarget("vpf")
  if x != v + 1: symexTarget("vpf_dead")

proc sutVarPtrInc(v: int) =
  symexAssume(v >= 0 and v < 16)
  var x = v
  var p = addr x
  incVP(p)
  incVP(p)
  if x == 9: symexTarget("vpi")
  if x != v + 2: symexTarget("vpi_dead")

proc sutVarPtrRebind(v: int) =
  var x = 0
  var y = 0
  var p = addr x
  reVP(p, addr y)
  p[] = v
  if y == 3: symexTarget("vpr")

suite "S8au: var ptr":
  test "addr x cannot be passed to a var ptr formal":
    var x = 0
    check not compiles(setVP(addr x, 1))
  test "vp":
    verdict(sutVarPtr, "vp", sxSat)
    verdict(sutVarPtr, "vp_dead", sxUnsat)
  test "vpf":
    verdict(sutVarPtrFwd, "vpf", sxSat)
    verdict(sutVarPtrFwd, "vpf_dead", sxUnsat)
  test "vpi":
    verdict(sutVarPtrInc, "vpi", sxSat)
    verdict(sutVarPtrInc, "vpi_dead", sxUnsat)
  test "vpr": declines(sutVarPtrRebind, "vpr", heUnsafeCast, "addr")
  test "nim":
    var x = 0
    var p = addr x
    setVP(p, 7)
    check x == 7
    let b = Box(x: 0)
    gBox = b
    setXG(b.x, 3)
    check b.x == 5
    let b2 = Box(x: 0)
    gBox = b2
    check readXG(b2.x, 3) == 3

# ---- (4) the split for every needle, and for rfind ----------------------------
#
# S8ag split `s.find(c, i)` for a one-character literal `c` only; a longer
# literal, a computed needle and `rfind` (`seq.last_indexof`) lowered to
# Z3's own term. S8au splits them all (`indexSplitAxioms`; the RFC's S8au
# note has the equivalence): a literal of length n >= 1 with the gap
# condition `c notin x ++ c[0 ..< n - 1]` (no earlier match, overlapping
# ones included), an empty needle by its closed form (`start` when 0 <=
# start <= len(s), else -1), a computed needle by a `len(c) = 0` case split
# between the two, and `rfind` by `s = pre ++ c ++ post` with `c notin
# c[1 ..] ++ post`. Pinned by a randomized differential against Z3's own
# `str.indexof` and `seq.last_indexof` (which agree with Nim's `find` /
# `rfind`, the empty needle included: probed on Z3 5.1 and 4.13.4, and the
# oracle test below), under both `c notin t` forms; three mutants -- S8ag's
# gap, an rfind gap blind to an overlapping later match, a computed needle
# without its empty case -- fail it.

proc sidx(ctx: Z3Context; s, t: Z3String; i: Z3Int): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_index(ctx.raw, s.raw, t.raw, i.raw))

proc slast(ctx: Z3Context; s, t: Z3String): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_last_index(ctx.raw, s.raw, t.raw))

proc freshSplit(ctx: Z3Context; s, c: Z3String; start: Z3Int;
                last: bool): IndexSplit =
  IndexSplit(ix: mkIntVar(ctx, "ix"), s: s, c: c, start: start,
             pre: mkStringVar(ctx, "ix_pre"), x: mkStringVar(ctx, "ix_x"),
             post: mkStringVar(ctx, "ix_post"), last: last)

type AxiomBuilder = proc (sp: IndexSplit): seq[Z3Bool]

proc landed(sp: IndexSplit): seq[Z3Bool] =
  let ax = indexSplitAxioms(sp)
  @[ax.found, ax.notFound]

proc s8agGap(sp: IndexSplit): seq[Z3Bool] =
  ## Mutant: S8ag's one-character gap `c notin x` for every needle, blind
  ## to an earlier match that overlaps the reported one ("aba" in "ababa":
  ## 2 passes it).
  let ctx = sp.s.ctx
  if sp.last: return landed(sp)
  let found = (sp.ix >= mkInt(ctx, 0)) and
    (sp.s == concat(sp.pre, concat(sp.x, concat(sp.c, sp.post)))) and
    (len(sp.pre) == sp.start) and (sp.ix == sp.start + len(sp.x)) and
    (not contains(sp.x, sp.c)) and (len(sp.c) > mkInt(ctx, 0))
  @[(sp.ix == mkInt(ctx, -1)) or found, indexSplitAxioms(sp).notFound]

proc lastPostGap(sp: IndexSplit): seq[Z3Bool] =
  ## Mutant: rfind's gap `c notin post`, blind to a later match that
  ## overlaps the reported one ("aa" in "aaa": 0 passes it).
  let ctx = sp.s.ctx
  if not sp.last: return landed(sp)
  let found = (sp.ix >= mkInt(ctx, 0)) and
    (sp.s == concat(sp.pre, concat(sp.c, sp.post))) and
    (len(sp.pre) == sp.ix) and (not contains(sp.post, sp.c)) and
    (len(sp.c) > mkInt(ctx, 0))
  @[(sp.ix == mkInt(ctx, -1)) or found, indexSplitAxioms(sp).notFound]

proc noEmptyCase(sp: IndexSplit): seq[Z3Bool] =
  ## Mutant: a computed needle that is empty answered "not found", as a
  ## split that only knew non-empty needles would.
  let ctx = sp.s.ctx
  result = landed(sp)
  if not Z3_is_string(ctx.raw, sp.c.raw):
    result.add (len(sp.c) > mkInt(ctx, 0)) or (sp.ix == mkInt(ctx, -1))

proc differential(build: AxiomBuilder; rounds: int; seed: int64;
                  form: NotInForm): string =
  ## "" when, on `rounds` random instances -- `s` over {'a', 'b'} of length
  ## 0..5, a needle of length 0..3 over the same alphabet, given as a
  ## literal or as a variable fixed to it, `find` with a start in -1 ..
  ## len(s) + 1 or `rfind` -- the axioms under the instance are SAT and
  ## `ix` differs from Z3's `str.indexof` / `seq.last_indexof` in no model.
  ## Else the first instance that disagrees.
  var r = initRand(seed)
  notInFormOverride = some(form)
  defer: notInFormOverride = none(NotInForm)
  for round in 0 ..< rounds:
    let ctx = newContext()
    var s, c = ""
    for _ in 0 ..< r.rand(0 .. 5): s.add "ab"[r.rand(0 .. 1)]
    for _ in 0 ..< r.rand(0 .. 3): c.add "ab"[r.rand(0 .. 1)]
    let computed = r.rand(0 .. 1) == 0
    let last = r.rand(0 .. 2) == 0
    let start = if last: 0 else: r.rand(-1 .. s.len + 1)
    let sv = mkStringVar(ctx, "s")
    let cv = if computed: mkStringVar(ctx, "c") else: mkString(ctx, c)
    let iv = mkIntVar(ctx, "i")
    let sp = freshSplit(ctx, sv, cv, iv, last)
    var pins = @[sv == mkString(ctx, s), iv == mkInt(ctx, start)]
    if computed: pins.add cv == mkString(ctx, c)
    let what = (if last: "rfind" else: "find") & " s=" & s.escape &
               " c=" & c.escape & (if computed: " (computed)" else: "") &
               " start=" & $start
    let sat = newSolver(ctx)
    for a in build(sp): sat.add a
    for p in pins: sat.add p
    if sat.check() != zsSat: return what & ": axioms UNSAT"
    let differ = newSolver(ctx)
    for a in build(sp): differ.add a
    for p in pins: differ.add p
    differ.add sp.ix != (if last: slast(ctx, sv, cv) else: sidx(ctx, sv, cv, iv))
    let st = differ.check()
    if st != zsUnsat: return what & ": ix != Z3's is " & $st
  ""

type LinkBuilder = proc (a, b: IndexSplit): Z3Bool

proc landedLink(a, b: IndexSplit): Z3Bool = indexSplitLastLink(a, b)

proc strictLink(a, b: IndexSplit): Z3Bool =
  ## Mutant: the last occurrence strictly after a found one (false when
  ## the needle occurs once).
  implies(b.ix >= mkInt(a.s.ctx, 0), a.ix > b.ix)

proc linkValid(link: LinkBuilder; rounds: int; seed: int64): string =
  ## "" when, on `rounds` random instances (as `differential`'s, an `rfind`
  ## split `a` and a `find` split `b` of one haystack and needle), the two
  ## splits' axioms imply `link(a, b)`. Else the first that does not.
  var r = initRand(seed)
  for round in 0 ..< rounds:
    let ctx = newContext()
    var s, c = ""
    for _ in 0 ..< r.rand(0 .. 5): s.add "ab"[r.rand(0 .. 1)]
    for _ in 0 ..< r.rand(0 .. 3): c.add "ab"[r.rand(0 .. 1)]
    let computed = r.rand(0 .. 1) == 0
    let start = r.rand(-1 .. s.len + 1)
    let sv = mkStringVar(ctx, "s")
    let cv = if computed: mkStringVar(ctx, "c") else: mkString(ctx, c)
    let a = IndexSplit(ix: mkIntVar(ctx, "a"), s: sv, c: cv,
                       start: mkInt(ctx, 0), pre: mkStringVar(ctx, "a_pre"),
                       x: mkStringVar(ctx, "a_x"),
                       post: mkStringVar(ctx, "a_post"), last: true)
    let b = IndexSplit(ix: mkIntVar(ctx, "b"), s: sv, c: cv,
                       start: mkInt(ctx, start), pre: mkStringVar(ctx, "b_pre"),
                       x: mkStringVar(ctx, "b_x"),
                       post: mkStringVar(ctx, "b_post"))
    let solver = newSolver(ctx)
    for f in landed(a): solver.add f
    for f in landed(b): solver.add f
    solver.add sv == mkString(ctx, s)
    if computed: solver.add cv == mkString(ctx, c)
    solver.add not link(a, b)
    let st = solver.check()
    if st != zsUnsat:
      return "s=" & s.escape & " c=" & c.escape & " start=" & $start &
             ": not link is " & $st
  ""

suite "S8au (4): the split for every needle, and for rfind":

  test "the rfind-find link holds on random instances":
    check linkValid(landedLink, 200, 0x5a8) == ""

  test "the check catches a strict link":
    check linkValid(strictLink, 200, 0x5a8) != ""

  test "oracle: Nim's find / rfind agree with Z3's on the edge cases":
    ## The cases the empty needle and overlap turn on, Nim side (the Z3
    ## side is the differential's reference).
    check "abc".find("", 3) == 3 and "abc".find("", 1) == 1
    check "abc".rfind("") == 3 and "".rfind("") == 0
    check "ababa".find("aba") == 0 and "aaa".rfind("aa") == 1
    check "abcbc".rfind("bc") == 3 and "abc".rfind("abcd") == -1

  test "differential, regex form":
    check differential(landed, 250, 0x5a7, nfRegex) == ""

  test "differential, not-contains form":
    check differential(landed, 250, 0x5a7, nfNotContains) == ""

  test "the check catches S8ag's gap on a longer needle":
    check differential(s8agGap, 400, 0x5a7, nfRegex) != ""

  test "the check catches an rfind gap blind to an overlapping match":
    check differential(lastPostGap, 400, 0x5a7, nfRegex) != ""

  test "the check catches a computed needle without its empty case":
    check differential(noEmptyCase, 400, 0x5a7, nfRegex) != ""

# The walker side of (4): each of these lowered to Z3's own term at the base
# (no split). `mf_dead` and `rf_dead` were `sxUnknown` there (`mf_dead`
# 20.3M units, 350 s on Z3 5.1; `rf_dead` 20M, 163 s); every one is now
# decided through splits (`mf_dead` 0.1M units; `rf_dead` 12k with the
# rfind-find link, 10M without it), its live neighbour with a witness the
# compiled code agrees with.

proc mFind(s: string) =
  let i = s.find("\r\n")
  if i == 3:
    let j = s.find("\r\n", i + 2)
    if j == 7: symexTarget("mf")
  if i >= 0 and s[i + 1] != '\n': symexTarget("mf_dead")

proc mOverlap(s: string) =
  let i = s.find("aa")
  if i == 1 and s.len == 4: symexTarget("mo")
  if i == 2 and s[1] == 'a': symexTarget("mo_dead")

proc symFind(s, t: string) =
  symexAssume(t.len <= 2 and s.len <= 6)
  let i = s.find(t)
  if i == 2 and t.len == 2: symexTarget("sf")
  if i >= 0 and i + t.len > s.len: symexTarget("sf_dead")
  if t.len == 0 and i != 0: symexTarget("sf_dead2")

proc rFind(s: string) =
  let i = s.rfind("ab")
  if i == 2 and s.len == 6: symexTarget("rf")
  if i >= 0 and i < 100 and s.find("ab", i + 1) >= 0: symexTarget("rf_dead")

proc rFindChar(s: string) =
  let i = s.rfind(':')
  if i == 3 and s.len == 5: symexTarget("rc")
  if i >= 0 and i < s.len - 1 and s[s.len - 1] == ':': symexTarget("rc_dead")

proc rFindEmpty(s: string) =
  if s.rfind("") == 2: symexTarget("re")
  if s.rfind("") != s.len: symexTarget("re_dead")

template split(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    check indexSplitCounter > 0   # the find / rfind was split
    r

suite "S8au (4): finds and rfinds the base left to Z3 are split":

  test "two-character literal needle, chained":
    let r = split(mFind, "mf", sxSat)
    if r.status == sxSat:
      let s = r.witness[0]
      check s.find("\r\n") == 3 and s.find("\r\n", 5) == 7
    discard split(mFind, "mf_dead", sxUnsat)

  test "an overlapping needle":
    let r = split(mOverlap, "mo", sxSat)
    if r.status == sxSat: check r.witness[0].find("aa") == 1
    discard split(mOverlap, "mo_dead", sxUnsat)

  test "a computed needle, the empty one included":
    let r = split(symFind, "sf", sxSat)
    if r.status == sxSat:
      let (s, t) = r.witness
      check s.find(t) == 2 and t.len == 2
    discard split(symFind, "sf_dead", sxUnsat)
    discard split(symFind, "sf_dead2", sxUnsat)

  test "rfind of a literal, a char and the empty needle":
    let r = split(rFind, "rf", sxSat)
    if r.status == sxSat: check r.witness[0].rfind("ab") == 2
    discard split(rFind, "rf_dead", sxUnsat)
    let c = split(rFindChar, "rc", sxSat)
    if c.status == sxSat: check c.witness[0].rfind(':') == 3
    discard split(rFindChar, "rc_dead", sxUnsat)
    let e = split(rFindEmpty, "re", sxSat)
    if e.status == sxSat: check e.witness[0].len == 2
    discard split(rFindEmpty, "re_dead", sxUnsat)

# ---- (5) the chain facts: consecutive, not all pairs --------------------------
#
# S8ag asserted a chain fact (`indexSplitChain`) for every ordered pair of
# reached splits of one haystack: n (n - 1) for n splits. Each fact is
# valid on its own (implied by the two splits' axioms; S8ag (1) checks it
# on random instances), so any subset is exact, and S8au keeps the
# consecutive ones in lowering order: n - 1. Only `find` splits chain (an
# `rfind` split has no `start`), and only on one haystack.

suite "S8au (5): chain facts between consecutive splits only":

  test "four chained finds: 8 axioms and 3 chains (S8ag: 12 chains)":
    indexSplits.setLen 0
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = mkStringVar(ctx, "t")
    var ix = lowerIndexSplit(s, mkString(ctx, ":"), mkInt(ctx, 0))
    for _ in 1 .. 3:
      ix = lowerIndexSplit(s, mkString(ctx, ":"), ix + mkInt(ctx, 1))
    check indexSplitRoots(ctx, @[ix > mkInt(ctx, 0)]).len == 4 * 2 + 3
    # An rfind of the same haystack and a find of another add their two
    # axioms each and no chain.
    let r = lowerIndexSplit(s, mkString(ctx, "ab"), mkInt(ctx, 0), last = true)
    let o = lowerIndexSplit(t, mkString(ctx, ":"), mkInt(ctx, 0))
    check indexSplitRoots(ctx, @[ix > mkInt(ctx, 0), r > o]).len ==
      6 * 2 + 3
    indexSplits.setLen 0

  test "a split reached only through another's needle is reached":
    ## A computed needle may hold a split (`s.find(s[0 ..< s.find(":")])`).
    indexSplits.setLen 0
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let inner = lowerIndexSplit(s, mkString(ctx, ":"), mkInt(ctx, 0))
    let outer = lowerIndexSplit(mkStringVar(ctx, "u"),
                                substr(s, mkInt(ctx, 0), inner),
                                mkInt(ctx, 0))
    check indexSplitRoots(ctx, @[outer > mkInt(ctx, 0)]).len == 4
    indexSplits.setLen 0

# ---- (6) the `c notin t` form, per Z3 version ---------------------------------
#
# S8ag measured the one-character regex `t in (allchar & ~c)*` against
# `not str.contains(t, c)`: on Z3 5.1 the regex is far cheaper (N36 8.2M
# units against 53.5M; round-6 B1-3 needs it), on 4.13.4 `not contains`
# is cheaper for N36 (8.3M against 15.3M). S8au measured both on both
# versions (the RFC's S8au note) and takes each version's cheaper form
# (`notInFormFor`); the differential in (4) checks both forms exact.

suite "S8au (6): the c-notin-t form follows the linked Z3":

  test "5.x takes the regex, 4.x not-contains":
    check notInFormFor(5, 1) == nfRegex
    check notInFormFor(4, 13) == nfNotContains
    let v = z3Version()
    check notInForm() == notInFormFor(int(v.major), int(v.minor))

suite "S8au: walker version floor":

  test "symexWalkerVersion >= 194":
    check parseInt(symexWalkerVersion) >= 194
