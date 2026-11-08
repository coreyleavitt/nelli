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
## RFC-0005 S8cm: part 2 of 5 of this suite, with
## `tsymex_rfc0005_s8an_remainder`, `tsymex_rfc0005_s8an_remainder_b2`,
## `tsymex_rfc0005_s8an_remainder_c`, `tsymex_rfc0005_s8an_remainder_d`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 100 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8an_remainder_b")

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
    pinDecline(sutCapVarAlias, declKey, feUnsupportedOp, tLabel("cva"), "c")

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
