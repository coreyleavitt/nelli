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
## RFC-0005 S8cm: part 5 of 5 of this suite, with
## `tsymex_rfc0005_s8an_remainder`, `tsymex_rfc0005_s8an_remainder_b`,
## `tsymex_rfc0005_s8an_remainder_b2`, `tsymex_rfc0005_s8an_remainder_c`. Split
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

template declines(fn: typed, lbl: string, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (3) a module-level var reached from a callee ----------------------------

var gCount: int
var gOther: int

proc bumpG(v: int) = gCount = v
proc readG(): int = gCount
proc setAlG(c: var int, v: int) =
  c = v
  gCount = 5
proc readAlG(c: var int, v: int): int =
  c = v
  gCount
proc setPG(p: ptr int, v: int) =
  p[] = v
  gCount = 9

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
