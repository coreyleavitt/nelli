## RFC-0005 (soundness channels) slice S8au -- the S8an / S8ag remainder.
##
## Pinned here (the RFC's "As landed (S8au)" note has the design and the
## measurements):
##   (1) a local distinct value with no distinct-typed parameter: closed by
##       S8ad (`ensureDistinctSort`, walker 175); re-pinned over more shapes
##       (borrowed `+` / `==` / `<`, default-initialised, float base, a
##       returned value, an object field). A `seq` of a distinct type was
##       a scoped decline (a different mechanism, reported); RFC-0005 S8ba
##       models it;
##   (2) `start < 0 and y > 1 and start div y == start` under the sequence
##       theory: closed by S8ad (`divRangeFacts`) and pinned in
##       `tsymex_rfc0005_s8ad_remainder`; re-measured for S8au, not
##       re-walked here;
##   (3) a copy-in/copy-out `var` actual (or an `addr` actual) whose heap
##       cell a global or a capture the callee reaches can also hold:
##       RED, a false `sxSat` (the callee's write through the global was
##       lost to the write-back); S8au declined it (`feUnsupportedOp`),
##       and RFC-0005 S8ba passes the cell by reference, so the dead
##       labels are `sxUnsat` (`tsymex_rfc0005_s8ba_remainder` (4));
##   (4) every `find` needle (a literal of any length, a computed one) and
##       `rfind` lower to S8ag's index split: the axioms by a randomized
##       differential against Z3's own terms with three mutants, and the
##       walker by hits that were `sxUnknown` at the base;
##   (5) the chain facts link consecutive splits only (counted);
##   (6) the `c notin t` form follows the linked Z3 version;
##   and `var ptr` formals: `f(addr x)` does not compile; a local `p = addr
##   x` passed to one was `heUnsafeCast`, and is now S8an's local pointer.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8au_remainder`, `tsymex_rfc0005_s8au_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 75 s).

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

# ---- (1) local distinct values ------------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

type Secs = distinct float
proc `+`(a, b: Secs): Secs {.borrow.}
proc `<`(a, b: Secs): bool {.borrow.}

# ---- (3) copy-in/copy-out through a global -----------------------------------

type Box = ref object
  x: int
type Other = ref object
  y: int

var gBox: Box
proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

proc readXG(v: var int, k: int): int =
  v = k
  gBox.x

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
  if y != v or x != 0: symexTarget("vpr_dead")

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
  test "vpr":
    ## S8au pinned this as a decline (`heUnsafeCast`, the `addr y` actual).
    ## RFC-0005 batch 3: S8ax's address cells model `addr y` (a `ptr` cell
    ## holding `y` for the frame's lifetime), so the re-pointed `p` writes
    ## `y`, as Nim does (`tests/tsymex_rfc0005_s8ax_remainder.nim` (8)).
    verdict(sutVarPtrRebind, "vpr", sxSat)
    verdict(sutVarPtrRebind, "vpr_dead", sxUnsat)
    var x = 0
    var y = 0
    var p = addr x
    reVP(p, addr y)
    p[] = 3
    check y == 3 and x == 0
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
