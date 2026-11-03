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
## RFC-0005 S8cm: part 3 of 5 of this suite, with
## `tsymex_rfc0005_s8an_remainder`, `tsymex_rfc0005_s8an_remainder_b`,
## `tsymex_rfc0005_s8an_remainder_c`, `tsymex_rfc0005_s8an_remainder_d`. Split
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

suite "S8an (1): a routine declared inside the code under test":


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

proc setP(p: ptr int, v: int) = p[] = v
proc getP(p: ptr int): int = p[]
proc incP(p: ptr int) = p[] += 1
proc fwdP(p: ptr int, v: int) = setP(p, v)
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
