## Round-5, sello issue 2 (capability) — composite (tuple) returns from
## nested callees. The known retBindEq svTuple gap: `let (p, q) =
## innerTuple(x, y)` degrades classified ([feUnsupportedOp] "composite-typed
## proc return ... not yet wired", sxUnknown) since v64's catalog-#6 drain
## doctrine. This suite pins the WIRED behavior: values thread through the
## destructure with SAT witnesses and UNSAT soundness both holding. Reported
## from sello (step lemmas forced into var out-param signatures); the same
## gap underlies chapulin's t_symex shapes that avoid natural tuple returns.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

proc sumDiff(a, b: int): tuple[x, y: int] =
  symexAssume(a >= 0 and a <= 100)
  symexAssume(b >= 0 and b <= 100)
  (a + b, a - b)

proc destructureSat(x, y: int) =
  ## Non-vacuous SAT: p==10, q==2 forces x=6, y=4 through the tuple.
  symexAssume(x >= 0 and x <= 100)
  symexAssume(y >= 0 and y <= 100)
  let (p, q) = sumDiff(x, y)
  if p == 10 and q == 2:
    symexTarget("through-the-tuple")

proc destructureUnsat(x, y: int) =
  ## Soundness: x+y==10 and x-y==3 has no integer solution.
  symexAssume(x >= 0 and x <= 100)
  symexAssume(y >= 0 and y <= 100)
  let (p, q) = sumDiff(x, y)
  if p == 10 and q == 3:
    symexTarget("impossible-parity")

proc destructureClean(x, y: int) =
  ## sello's literal repro shape: bind and discard, no assert anywhere —
  ## must prove sxUnsat WITHOUT a walker fault or unsupported degrade.
  symexAssume(x >= 0 and x <= 100)
  symexAssume(y >= 0 and y <= 100)
  let (p, q) = sumDiff(x, y)
  discard p
  discard q

suite "symex round-5 sello#2 — tuple returns from nested callees":

  test "values thread through the destructure (non-vacuous SAT)":
    let r = symexFind(destructureSat, tLabel("through-the-tuple"))
    check r.status == sxSat

  test "parity contradiction through the tuple is UNSAT (soundness)":
    let r = symexFind(destructureUnsat, tLabel("impossible-parity"))
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == feUnsupportedOp)

  test "bind-and-discard shape: clean sxUnsat, no unsupported degrade":
    let r = symexFind(destructureClean, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == feUnsupportedOp)
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)
