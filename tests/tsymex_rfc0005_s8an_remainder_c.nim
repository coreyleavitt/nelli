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
##
## RFC-0005 S8cm: part 4 of 5 of this suite, with
## `tsymex_rfc0005_s8an_remainder`, `tsymex_rfc0005_s8an_remainder_b`,
## `tsymex_rfc0005_s8an_remainder_b2`, `tsymex_rfc0005_s8an_remainder_d`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 100 s).

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

# ---- (2) the address of a local passed as a `ptr T` --------------------------

type Pair = object
  a: int
  b: int

var gp: ptr int

proc setP(p: ptr int, v: int) = p[] = v
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
proc raiseG(v: int) =
  gCount = v
  if v > 3: raise newException(ValueError, "x")
proc touchOther(c: var int, v: int) =
  c = v
  gOther = 1
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
