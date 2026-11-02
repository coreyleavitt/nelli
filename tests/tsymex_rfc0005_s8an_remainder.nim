## RFC-0005 (soundness channels) slice S8an -- S8ac's remainder.
##
## This slice closes:
##   (1) a routine declared inside the code under test. Its declaration was
##       `feUnsupportedStmtKind` ("statement kind nnkProcDef not in
##       supported fragment"), and a read of an enclosing local or
##       parameter from its body was `feGlobalReadUnmodelled`. A nested
##       routine with no captures is an ordinary proc; one that captures is
##       a closure over the enclosing frame's variables, by reference. A
##       direct call threads each capture into the callee and back out (the
##       callee's writes reach the enclosing variable); a nested routine
##       used as a VALUE is a closure (`parseRoutineToLambda`);
##   (2) the address of a local passed as a `ptr T` argument (`setP(addr
##       x, v)`, or through `let p = addr x`) was `feUnsupportedExprKind` /
##       `heUnsafeCast`. The pointee is now a tracked heap cell for the call:
##       `x` is stored into a fresh `ptr` cell, the callee reads and writes
##       it through `p[]`, and the cell is read back into `x` on every exit.
##       Two `addr` of one location in one call share one cell (aliasing is
##       exact). A callee that can let the pointer escape declines, scoped;
##   (3) a module-level `var` written or read by a callee. The callee's
##       write was dropped (a false `sxUnsat` on the live target and a false
##       `sxSat` on the dead one, `errors` empty), and a `var` actual that
##       is the global the callee also writes was written back over the
##       callee's direct write (a false `sxSat`). Globals are now threaded
##       through every walked call, and a call whose callee reaches a `var`
##       or `addr` actual's root another way declines, scoped.
## The same audit found three silent wrong verdicts at call boundaries,
## closed here too: overloads and same-named nested routines shared one
## callee key; a `var` actual whose index (or itself) another argument
## writes was written back to the wrong location; a lambda writing a
## capture through a nested routine dropped the write.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is); the probe is quoted beside
## the test.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template declines(fn: typed, lbl: string, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (1) a routine declared inside the code under test ----------------------

proc sutNested(x: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  proc dbl(a: int): int = a * 2
  if dbl(x) == 10: symexTarget("n")
  if dbl(x) == 11: symexTarget("n_dead")

proc sutNestedFunc(x: int) =
  func half(a: int): int = a div 2
  if half(x) == 4 and x mod 2 == 1: symexTarget("nf")
  if half(x) == 4 and x > 9: symexTarget("nf_dead")

proc sutCapParam(x, k: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  symexAssume(k > -1000 and k < 1000)  # no overflow path
  proc addk(a: int): int = a + k
  if addk(x) == 10 and k == 3: symexTarget("cp")
  if addk(x) == 10 and x + k != 10: symexTarget("cp_dead")

proc sutCapLocal(x: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var k = 1
  k = x
  proc twice(): int = k * 2
  if twice() == 8: symexTarget("cl")
  if twice() == 8 and x != 4: symexTarget("cl_dead")

proc sutCapLater(x: int) =
  ## By reference: the call reads `c` as it stands at the call.
  var c = 0
  proc get(): int = c
  c = x
  if get() == 3: symexTarget("cr")
  if get() != x: symexTarget("cr_dead")

proc sutCapMut(x: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var c = 0
  proc bump() = c += x
  bump()
  bump()
  if c == 10: symexTarget("cm")
  if c == 10 and x != 5: symexTarget("cm_dead")

proc sutCapChain(x: int) =
  ## `b` reaches `c` only through `a`.
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var c = x
  proc a() = c += 1
  proc b() =
    a()
    a()
  b()
  if c == 7: symexTarget("cc")
  if c != x + 2: symexTarget("cc_dead")

proc sutCapShadow(x: int) =
  ## The callee's own `c` is not the captured `c`.
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var c = x
  proc g(): int =
    result = c
    block:
      var c = 100
      result += c
  if g() == 105: symexTarget("cs")
  if g() != x + 100: symexTarget("cs_dead")

proc sutCapRaise(x: int) =
  ## The write before the raise reaches the handler.
  var c = 0
  proc setc() =
    c = x
    if x > 3: raise newException(ValueError, "x")
  try:
    setc()
  except ValueError:
    if c == x: symexTarget("cx")
    if c != x: symexTarget("cx_dead")

proc sutCapValue(x: int) =
  ## A nested routine used as a value is a closure.
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var k = x
  proc addk(a: int): int = a + k
  let f = addk
  if f(2) == 9: symexTarget("cv")
  if f(2) != x + 2: symexTarget("cv_dead")

proc sutCapValueWrite(x: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var c = 0
  proc bump() = c += x
  let f = bump
  f()
  if c == 4: symexTarget("cvw")

proc sutCapVarAlias(x: int) =
  ## `y` and `c` are one location: `c` ends at `c + 11`, not `c + 1`.
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var c = x
  proc bumpBoth(y: var int) =
    y += 1
    c += 10
  bumpBoth(c)
  if c == 12: symexTarget("cva")

proc sutRec(x: int) =
  ## A concrete argument: each level's `k <= 1` is decided, so the walk
  ## stops where Nim's recursion does.
  proc fact(k: int): int =
    if k <= 1: 1 else: k * fact(k - 1)
  if fact(3) == x: symexTarget("r")
  if fact(3) != 6 and x == 0: symexTarget("r_dead")

proc sutRecCap(x: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  var acc = x
  proc down(k: int) =
    if k > 0:
      acc += k
      down(k - 1)
  down(2)
  if acc == 10: symexTarget("rc")
  if acc != x + 3: symexTarget("rc_dead")

proc sutRecDeep(n: int) =
  proc fact(k: int): int =
    if k <= 1: 1 else: k * fact(k - 1)
  if n >= 1 and n <= 5 and fact(n) == 24: symexTarget("rd")

proc a1(x: int): int =
  proc h(): int = x + 1
  h()
proc b1(x: int): int =
  proc h(): int = x + 100
  h()

proc sutNameClash(x: int) =
  ## Two nested `h`, one in `a1` and one in `b1`.
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  if a1(x) == 2 and b1(x) == 101: symexTarget("nc")
  if b1(x) != x + 100: symexTarget("nc_dead")

proc ov(x: int): int = x + 1
proc ov(x: string): int = x.len + 100

proc sutOverload(x: int) =
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  if ov(x) == 2 and ov("ab") == 102: symexTarget("ov")
  if ov("ab") != 102: symexTarget("ov_dead")

proc sutCapValueLater(x: int) =
  ## By reference through a closure value too: `f()` reads `c` as it
  ## stands at the call, not at `let f = getc`.
  var c = 0
  proc getc(): int = c
  let f = getc
  c = x
  if f() == 5: symexTarget("cvl")
  if f() != x: symexTarget("cvl_dead")

proc sutLambdaViaNested(x: int) =
  ## A lambda that calls a nested routine writing the enclosing `c`: the
  ## write is a by-reference capture write of the lambda.
  var c = 0
  proc setc() = c = 3
  let f = proc () = setc()
  f()
  if c == 3: symexTarget("lvn")

proc sutNestedTemplate(x: int) =
  ## A template or an iterator declared inside the code under test is a
  ## declaration with no run-time effect; its uses are what is walked.
  symexAssume(x > -1000 and x < 1000)  # no overflow path
  template twice(a: int): int = a * 2
  iterator upTo(n: int): int =
    var i = 0
    while i < n:
      yield i
      inc i
  var acc = 0
  for i in upTo(3): acc += i
  if twice(x) + acc == 13: symexTarget("nt")
  if twice(x) + acc != 2 * x + 3: symexTarget("nt_dead")

suite "S8an (1): a routine declared inside the code under test":

  test "a nested routine with no captures is an ordinary proc":
    ## RED: `feUnsupportedStmtKind` ("statement kind nnkProcDef").
    verdict(sutNested, "n", sxSat)
    verdict(sutNested, "n_dead", sxUnsat)
    verdict(sutNestedFunc, "nf", sxSat)
    verdict(sutNestedFunc, "nf_dead", sxUnsat)
    let r = symexFind(sutNested, tLabel("n"))
    if r.status == sxSat: check r.witness[0] == 5

  test "a capture reads the enclosing variable as it stands at the call":
    ## RED: `feGlobalReadUnmodelled` (the capture read as a global).
    verdict(sutCapParam, "cp", sxSat)
    verdict(sutCapParam, "cp_dead", sxUnsat)
    verdict(sutCapLocal, "cl", sxSat)
    verdict(sutCapLocal, "cl_dead", sxUnsat)
    verdict(sutCapLater, "cr", sxSat)
    verdict(sutCapLater, "cr_dead", sxUnsat)
    verdict(sutCapShadow, "cs", sxSat)
    verdict(sutCapShadow, "cs_dead", sxUnsat)
    let r = symexFind(sutCapParam, tLabel("cp"))
    if r.status == sxSat:
      let (x, k) = r.witness
      check x == 7 and k == 3

  test "a capture written by the nested routine is the enclosing variable":
    ## Probe: `sutCapMut(5)` leaves `c == 10`; `sutCapChain(5)` leaves
    ## `c == 7`; `sutCapRaise(4)` reaches the handler with `c == 4`.
    verdict(sutCapMut, "cm", sxSat)
    verdict(sutCapMut, "cm_dead", sxUnsat)
    verdict(sutCapChain, "cc", sxSat)
    verdict(sutCapChain, "cc_dead", sxUnsat)
    verdict(sutCapRaise, "cx", sxSat)
    verdict(sutCapRaise, "cx_dead", sxUnsat)
    let r = symexFind(sutCapMut, tLabel("cm"))
    if r.status == sxSat: check r.witness[0] == 5

  test "a nested routine used as a value is a closure":
    verdict(sutCapValue, "cv", sxSat)
    verdict(sutCapValue, "cv_dead", sxUnsat)
    # A closure value's write to its capture, applied in the frame that
    # built it, is written back since RFC-0005 S8as (was the scoped
    # `ceCaptureByRefUnmodelled` decline).
    verdict(sutCapValueWrite, "cvw", sxSat)

  test "a var actual that is also a capture of the callee declines, scoped":
    ## Probe: `sutCapVarAlias(1)` leaves `c == 12`; copy-in/copy-out
    ## would leave `c == 2`.
    declines(sutCapVarAlias, "cva", feUnsupportedOp, "c")

  test "a nested template or iterator declaration is not a statement":
    ## RED: `feUnsupportedStmtKind` ("statement kind nnkTemplateDef" /
    ## "nnkIteratorDef"). Probe: `sutNestedTemplate(5)` reaches `nt`.
    verdict(sutNestedTemplate, "nt", sxSat)
    verdict(sutNestedTemplate, "nt_dead", sxUnsat)

  test "routines of one spelling are distinct callees":
    ## RED: `nc` and `ov` `sxUnsat`, `nc_dead` `sxSat`, `errors` empty --
    ## both calls ran the first-registered body (a non-generic callee was
    ## keyed by its bare name). Probe: `a1(1) == 2`, `b1(1) == 101`.
    verdict(sutNameClash, "nc", sxSat)
    verdict(sutNameClash, "nc_dead", sxUnsat)
    verdict(sutOverload, "ov", sxSat)
    verdict(sutOverload, "ov_dead", sxUnsat)

  test "a lambda reaching a capture through a nested routine writes it":
    ## RED: `sxUnsat`, `errors` empty -- the lambda captured nothing, the
    ## nested routine's write to `c` landed in the closure's own env and
    ## was dropped. Probe: `sutLambdaViaNested(0)` reaches `lvn`. S8an
    ## declined it (`ceCaptureByRefUnmodelled`); RFC-0005 S8as writes the
    ## capture back to the frame that built the lambda.
    verdict(sutLambdaViaNested, "lvn", sxSat)

  test "a closure value reads its capture as it stands at the call":
    ## Probe: `sutCapValueLater(5)` reaches `cvl`.
    verdict(sutCapValueLater, "cvl", sxSat)
    verdict(sutCapValueLater, "cvl_dead", sxUnsat)

  test "recursion within the call-depth budget is walked":
    ## Recursion is bounded by `maxCallDepth` (each recursive call is one
    ## more inlined frame); within it the walk is exact. RED (with the
    ## nested routines walked): every target `beBudgetExhaustedUnmodelled`
    ## -- the `if` arm no execution takes (`fact(1)`'s `k > 1`) reached the
    ## next level and the bail; it is now dropped as infeasible there.
    verdict(sutRec, "r", sxSat)
    verdict(sutRec, "r_dead", sxUnsat)
    let r = symexFind(sutRec, tLabel("r"))
    if r.status == sxSat: check r.witness[0] == 6
    verdict(sutRecCap, "rc", sxSat)
    verdict(sutRecCap, "rc_dead", sxUnsat)

  test "recursion past the call-depth budget declines, and decides with room":
    ## On a symbolic argument every level's `k <= 1` is open, so the walk
    ## unrolled to `maxCallDepth` (3 by default) and the deepest path
    ## declined. RFC-0005 S8ax: `n <= 5` bounds the recursion, so the
    ## adaptive depth follows it past `maxCallDepth` and the default
    ## settings now decide; the unbounded shape's decline is pinned in
    ## tsymex_rfc0005_s8ax_remainder. The satisfiable `fact(4) == 24` is
    ## found with room either way.
    block:
      let r0 = symexFind(sutRecDeep, tLabel("rd"))
      checkpoint show(r0.errors)
      check r0.status == sxSat
      if r0.status == sxSat: check r0.witness[0] == 4
    let r = symexFind(sutRecDeep, tLabel("rd"),
      SymexSettings(budget: ResourceBudget(maxCallDepth: 8)))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == 4

# ---- (2) the address of a local passed as a `ptr T` --------------------------

type Pair = object
  a: int
  b: int

var gp: ptr int

proc setP(p: ptr int, v: int) = p[] = v
proc getP(p: ptr int): int = p[]
proc incP(p: ptr int) = p[] += 1
proc fwdP(p: ptr int, v: int) = setP(p, v)
proc two(p, q: ptr int, v: int) =
  p[] = v
  q[] = 3
proc same(p, q: ptr int): bool = p == q
proc setPR(p: ptr int, v: int) =
  p[] = v
  if v > 3: raise newException(ValueError, "x")
proc keepP(p: ptr int) = gp = p
proc mixP(p: ptr int, y: var int) =
  p[] = 1
  y = 2

proc sutAddr(v: int) =
  var x = 1
  setP(addr x, v)
  if x == 7: symexTarget("a")
  if x == 1 and v != 1: symexTarget("a_dead")

proc sutAddrRead(v: int) =
  var x = v
  if getP(addr x) == 7: symexTarget("ar")
  if getP(addr x) != v: symexTarget("ar_dead")

proc sutAddrInc(v: int) =
  # No overflow path. S8an kept the range narrow (`[0, 16)`): the `int`
  # heap was BV-sorted and the Int-to-BV round trip cost Z3 ~40 s per UNSAT
  # query over a wide one. RFC-0005 S8as made that heap Int-sorted.
  symexAssume(v > -1000 and v < 1000)
  var x = v
  incP(addr x)
  incP(addr x)
  if x == 9: symexTarget("ai")
  if x != v + 2: symexTarget("ai_dead")

proc sutAddrFwd(v: int) =
  var x = 0
  fwdP(addr x, v)
  if x == 6: symexTarget("af")
  if x != v: symexTarget("af_dead")

proc sutAddrAlias(v: int) =
  var x = 1
  two(addr x, addr x, v)
  if x == 3: symexTarget("aa")
  if x == v and v != 3: symexTarget("aa_dead")

proc sutAddrTwo(v: int) =
  var x = 1
  var y = 1
  two(addr x, addr y, v)
  if x == 8 and y == 3: symexTarget("at")
  if y != 3 or x != v: symexTarget("at_dead")

proc sutAddrSame(v: int) =
  var x = v
  var y = v
  if same(addr x, addr x) and not same(addr x, addr y): symexTarget("as")
  if same(addr x, addr y): symexTarget("as_dead")

proc sutAddrLet(v: int) =
  # No overflow path. S8an kept the range narrow (`[0, 16)`): the `int`
  # heap was BV-sorted and the Int-to-BV round trip cost Z3 ~40 s per UNSAT
  # query over a wide one. RFC-0005 S8as made that heap Int-sorted.
  symexAssume(v > -1000 and v < 1000)
  var x = 1
  let p = addr x
  setP(p, v)
  p[] += 1
  if x == 6: symexTarget("al")
  if x != v + 1: symexTarget("al_dead")

proc sutAddrField(v: int) =
  var o = Pair(a: 1, b: 2)
  setP(addr o.a, v)
  if o.a == 4 and o.b == 2: symexTarget("ao")
  if o.a != v or o.b != 2: symexTarget("ao_dead")

proc sutAddrRaise(v: int) =
  var x = 0
  try:
    setPR(addr x, v)
  except ValueError:
    if x == v: symexTarget("ae")
    if x != v: symexTarget("ae_dead")

proc sutAddrEscape(v: int) =
  var x = v
  keepP(addr x)
  if x == 2: symexTarget("aesc")

proc sutAddrMix(v: int) =
  var x = v
  mixP(addr x, x)
  if x == 2: symexTarget("amix")
  if x != 2: symexTarget("amix_dead")

suite "S8an (2): the address of a local passed as a ptr":

  test "the callee reads and writes the local through p[]":
    ## RED: `feUnsupportedExprKind` (`nnkAddr`).
    verdict(sutAddr, "a", sxSat)
    verdict(sutAddr, "a_dead", sxUnsat)
    verdict(sutAddrRead, "ar", sxSat)
    verdict(sutAddrRead, "ar_dead", sxUnsat)
    verdict(sutAddrInc, "ai", sxSat)
    verdict(sutAddrInc, "ai_dead", sxUnsat)
    verdict(sutAddrFwd, "af", sxSat)
    verdict(sutAddrFwd, "af_dead", sxUnsat)
    let r = symexFind(sutAddr, tLabel("a"))
    if r.status == sxSat: check r.witness[0] == 7

  test "two addr of one location are one cell":
    ## Probe: `two(addr x, addr x, 8)` leaves `x == 3`; `same(addr x,
    ## addr x)` is true and `same(addr x, addr y)` false.
    verdict(sutAddrAlias, "aa", sxSat)
    verdict(sutAddrAlias, "aa_dead", sxUnsat)
    verdict(sutAddrTwo, "at", sxSat)
    verdict(sutAddrTwo, "at_dead", sxUnsat)
    verdict(sutAddrSame, "as", sxSat)
    verdict(sutAddrSame, "as_dead", sxUnsat)

  test "a let bound to addr x is the address of x":
    ## RED: `heUnsafeCast` ("unsafe pointer materialisation (addr)").
    verdict(sutAddrLet, "al", sxSat)
    verdict(sutAddrLet, "al_dead", sxUnsat)

  test "a field's address and a raising callee":
    ## Probe: `sutAddrRaise(4)` reaches the handler with `x == 4`.
    verdict(sutAddrField, "ao", sxSat)
    verdict(sutAddrField, "ao_dead", sxUnsat)
    verdict(sutAddrRaise, "ae", sxSat)
    verdict(sutAddrRaise, "ae_dead", sxUnsat)

  test "a callee that keeps the pointer is decided":
    ## RFC-0005 S8ax: `addr x` of a routine variable is its address cell,
    ## which outlives the call, so the escape no longer declines.
    verdict(sutAddrEscape, "aesc", sxSat)
    let r = symexFind(sutAddrEscape, tLabel("aesc"))
    if r.status == sxSat: check r.witness[0] == 2

  test "an addr actual the callee also reaches as a var is one location":
    ## Probe: `mixP(addr x, x)` leaves `x == 2` (the later write). S8an
    ## declined it; RFC-0005 S8bs binds the `var` formal to the cell the
    ## `addr` actual is for the call, so both writes land on `x` in the
    ## callee's order.
    var x = 7
    mixP(addr x, x)
    check x == 2
    verdict(sutAddrMix, "amix", sxSat)
    verdict(sutAddrMix, "amix_dead", sxUnsat)

# ---- (3) a module-level var reached from a callee ----------------------------

var gCount: int
var gOther: int

proc bumpG(v: int) = gCount = v
proc readG(): int = gCount
proc addG(v: int) = gCount += v
proc viaG(v: int) = bumpG(v)
proc setAlG(c: var int, v: int) =
  c = v
  gCount = 5
proc readAlG(c: var int, v: int): int =
  c = v
  gCount
proc raiseG(v: int) =
  gCount = v
  if v > 3: raise newException(ValueError, "x")
proc touchOther(c: var int, v: int) =
  c = v
  gOther = 1
proc setPG(p: ptr int, v: int) =
  p[] = v
  gCount = 9

proc sutGlobal(v: int) =
  gCount = 0
  bumpG(v)
  if gCount == 7: symexTarget("g")
  if gCount == 0 and v != 0: symexTarget("g_dead")

proc sutGlobalRead(v: int) =
  gCount = v
  if readG() == 4: symexTarget("gr")
  if readG() != v: symexTarget("gr_dead")

proc sutGlobalNested(v: int) =
  symexAssume(v > -1000 and v < 1000)  # no overflow path
  gCount = 1
  viaG(v)
  addG(2)
  if readG() == 9: symexTarget("gn")
  if gCount != v + 2: symexTarget("gn_dead")

proc sutGlobalCache(v: int) =
  ## Two `readG()` with one argument shape: a call-cache replay of the
  ## first would ignore the write between them.
  gCount = 1
  let a = readG()
  gCount = v
  if readG() == 5 and a == 1: symexTarget("gc")

proc sutGlobalRaise(v: int) =
  gCount = 0
  try:
    raiseG(v)
  except ValueError:
    if gCount == v: symexTarget("ge")
    if gCount != v: symexTarget("ge_dead")

proc sutGlobalUnset(v: int) =
  bumpG(v)
  gOther = gCount
  if readG() == 3: symexTarget("gu")

proc sutGlobalFirstRead(v: int) =
  if readG() == v: symexTarget("gfr")

proc sutGlobalAlias(v: int) =
  gCount = 0
  setAlG(gCount, v)
  if gCount == 5: symexTarget("ga")
  if gCount == v and v != 5: symexTarget("ga_dead")

proc sutGlobalAliasRead(v: int) =
  gCount = 0
  if readAlG(gCount, v) == 7: symexTarget("gar")

proc sutGlobalNoAlias(v: int) =
  ## The callee touches a DIFFERENT global: modelled.
  gCount = 0
  touchOther(gCount, v)
  if gCount == 6 and gOther == 1: symexTarget("gna")
  if gCount != v: symexTarget("gna_dead")

proc sutGlobalLocalAlias(v: int) =
  var y = 0
  gCount = 0
  setAlG(y, v)
  if y == v and gCount == 5 and v == 9: symexTarget("gla")
  if gCount != 5: symexTarget("gla_dead")

proc sutGlobalAddr(v: int) =
  gCount = 0
  setPG(addr gCount, v)
  if gCount == 9: symexTarget("gaddr")

proc sutGlobalClosure(v: int) =
  ## A routine called through a proc value is a closure body: its write to
  ## a global is not carried back, and the call declines.
  gCount = 0
  let f = bumpG
  f(v)
  if gCount == 0: symexTarget("gcl")

proc sutGlobalLambda(v: int) =
  gCount = 0
  let f = proc () = gCount = v
  f()
  if gCount == 0: symexTarget("glam")

proc setIJ(x: var int, j: var int) =
  j = 1
  x = 7

proc sutIdxAlias(v: int) =
  ## Nim writes `s[0]` (the address taken before the call); a write-back
  ## after the call wrote `s[1]`.
  var s = @[0, 0]
  var i = 0
  setIJ(s[i], i)
  if s[0] == 7: symexTarget("ia")
  if s[1] == 7: symexTarget("ia_dead")

proc sutDupVar(v: int) =
  ## One variable passed twice by address: Nim leaves the later write
  ## (`i == 7`); two by-name write-backs left the earlier formal's.
  var i = 0
  setIJ(i, i)
  if i == 7: symexTarget("dv")
  if i == 1: symexTarget("dv_dead")

proc sutLambdaGlobalRead(v: int) =
  ## A closure reads a global as it stands at the call.
  gCount = 0
  let f = proc (): int = gCount
  gCount = v
  if f() == 5: symexTarget("lgr")
  if f() != v: symexTarget("lgr_dead")

suite "S8an (3): a module-level var reached from a callee":

  test "a callee's write to a global reaches the caller":
    ## RED: `g` `sxUnsat` and `g_dead` `sxSat`, `errors` empty (the
    ## callee's write was dropped).
    verdict(sutGlobal, "g", sxSat)
    verdict(sutGlobal, "g_dead", sxUnsat)
    let r = symexFind(sutGlobal, tLabel("g"))
    if r.status == sxSat: check r.witness[0] == 7

  test "a callee reads the global as the caller left it":
    ## RED: `feGlobalReadUnmodelled`.
    verdict(sutGlobalRead, "gr", sxSat)
    verdict(sutGlobalRead, "gr_dead", sxUnsat)
    verdict(sutGlobalNested, "gn", sxSat)
    verdict(sutGlobalNested, "gn_dead", sxUnsat)
    verdict(sutGlobalCache, "gc", sxSat)
    verdict(sutGlobalRaise, "ge", sxSat)
    verdict(sutGlobalRaise, "ge_dead", sxUnsat)
    verdict(sutGlobalNoAlias, "gna", sxSat)
    verdict(sutGlobalNoAlias, "gna_dead", sxUnsat)
    verdict(sutGlobalLocalAlias, "gla", sxSat)
    verdict(sutGlobalLocalAlias, "gla_dead", sxUnsat)

  test "a global read before any write in the walk holds its entry value":
    ## Its value at entry is whatever the program left there: since
    ## RFC-0005 S8as a fresh value of its type (`feGlobalHavoc`, a replay-
    ## gated SAT), where S8an declined (`feGlobalReadUnmodelled`).
    block:
      let r = symexFind(sutGlobalFirstRead, tLabel("gfr"))
      checkpoint show(r.errors)
      check r.status in {sxSat, sxUnknown}
      check r.errors.hasKind(feGlobalHavoc)
      check not r.errors.hasKind(feGlobalReadUnmodelled)
    verdict(sutGlobalUnset, "gu", sxSat)

  test "a var or addr actual that is a global the callee reaches declines":
    ## RED: `ga_dead` `sxSat`, `errors` empty. Probe: `setAlG(gCount, 8)`
    ## leaves `gCount == 5` (the callee's direct write is the later one).
    declines(sutGlobalAlias, "ga", feUnsupportedOp, "gCount")
    declines(sutGlobalAlias, "ga_dead", feUnsupportedOp, "gCount")
    declines(sutGlobalAliasRead, "gar", feUnsupportedOp, "gCount")
    declines(sutGlobalAddr, "gaddr", feUnsupportedOp, "gCount")

  test "a var actual whose index another argument writes declines":
    ## RED: `ia` `sxUnsat` and `ia_dead` `sxSat`; `dv` `sxUnsat` and
    ## `dv_dead` `sxSat` (`errors` empty). Probe: `setIJ(s[i], i)` leaves
    ## `s == @[7, 0]`; `setIJ(i, i)` leaves `i == 7`.
    declines(sutIdxAlias, "ia", feUnsupportedOp, "s[i]")
    declines(sutIdxAlias, "ia_dead", feUnsupportedOp, "s[i]")
    declines(sutDupVar, "dv", feUnsupportedOp, "`i`")
    declines(sutDupVar, "dv_dead", feUnsupportedOp, "`i`")

  test "a closure reads a global as it stands at the call":
    verdict(sutLambdaGlobalRead, "lgr", sxSat)
    verdict(sutLambdaGlobalRead, "lgr_dead", sxUnsat)

  test "a closure body's write to a global reaches the caller":
    ## S8an declined both (`ceCaptureByRefUnmodelled`); RFC-0005 S8as
    ## writes the global back.
    verdict(sutGlobalClosure, "gcl", sxSat)
    verdict(sutGlobalLambda, "glam", sxSat)

suite "S8an: walker version":
  test "symexWalkerVersion >= 183":
    check parseInt(symexWalkerVersion) >= 183
