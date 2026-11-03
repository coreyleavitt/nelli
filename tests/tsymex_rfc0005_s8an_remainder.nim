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
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8an_remainder_b`, `tsymex_rfc0005_s8an_remainder_c`,
## `tsymex_rfc0005_s8an_remainder_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 100 s).

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

# ---- (2) the address of a local passed as a `ptr T` --------------------------

type Pair = object
  a: int
  b: int
