## RFC-0005 (soundness channels) slice S8bh -- S8bf's remainder.
##
## Three soundness findings S8bf reported and did not fix:
##
## 1. A call through a proc-valued variable dropped its `var` writes: the
##    closure-call arm (`applyClosureGround`) lowered the arguments by value
##    and had no copy-out, so `let f = setBoth; f(x, y)` left `x` as it was
##    (a false `sxSat` for `x != 1`). The same held for every indirect call
##    that reaches that arm: a lambda, a generic callee's proc parameter, a
##    proc passed to a callee, and a heap actual (`f(p.x, y)`).
## 2. A `ptr` parameter never addressed a ref object's field: `q.x = 1;
##    pi[] = 2; if q.x == 2` was `sxUnsat`, but Nim reaches it with
##    `pi = addr q.x`.
## 3. Converting a ref up its inheritance chain built an ill-sorted term:
##    `Base(d) == b` was `weInternalWalkerFault`.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8bh_remainder_b`, `tsymex_rfc0005_s8bh_remainder_c`,
## `tsymex_rfc0005_s8bh_remainder_d`, `tsymex_rfc0005_s8bh_remainder_e`,
## `tsymex_rfc0005_s8bh_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 112 s).

import std/[unittest, strutils, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

# ---- 1. var writes through an indirect call ---------------------------------

type Box = ref object
  x: int
  y: int

proc setBoth(a, b: var int) =
  ## Writes `b`, then `a`: on one location, `a`'s write is the last.
  b = 2
  a = 1

proc setOne(a: var int) =
  a = 4

proc retV(a: var int): int =
  a = 9
  result = 1

proc setRaise(a: var int; k: int) =
  a = 5
  if k > 0: raise newException(ValueError, "after the write")

proc sutPV(k: int) =
  let f = setBoth
  var x = k
  var y = k
  f(x, y)
  if x != 1 or y != 2: symexTarget("pv_dead")
  if x == 1 and y == 2 and k == 3: symexTarget("pv")

proc sutPVSame(k: int) =
  ## One variable passed twice: one location, written in the callee's order.
  let f = setBoth
  var x = k
  f(x, x)
  if x != 1: symexTarget("pvs_dead")
  if x == 1 and k == 4: symexTarget("pvs")

proc sutLam(k: int) =
  if k < -1000 or k > 1000: return
  let f = proc (a: var int) = a = a + 7
  var x = k
  f(x)
  if x != k + 7: symexTarget("lam_dead")
  if x == 10: symexTarget("lam")

proc sutLamCap(k: int) =
  ## The lambda reads a capture that is not the actual.
  if k < -1000 or k > 1000: return
  let c = k * 2
  let f = proc (a: var int) = a = c + 1
  var x = k
  f(x)
  if x != 2 * k + 1: symexTarget("lc_dead")
  if x == 7: symexTarget("lc")

proc applyG[F](f: F; a, b: var int) = f(a, b)

proc sutGen(k: int) =
  ## A generic callee's proc parameter, its `var` formals forwarded.
  var x = k
  var y = k
  applyG(setBoth, x, y)
  if x != 1 or y != 2: symexTarget("gen_dead")
  if x == 1 and k == 5: symexTarget("gen")

proc applyP(f: proc (a, b: var int) {.nimcall.}; a, b: var int) = f(a, b)

proc sutHof(k: int) =
  ## A proc passed to a callee.
  var x = k
  var y = k
  applyP(setBoth, x, y)
  if x != 1 or y != 2: symexTarget("hof_dead")
  if y == 2 and k == 6: symexTarget("hof")

proc sutExpr(k: int) =
  ## A call in an expression: the write lands before the operand after it.
  let f = retV
  var x = k
  let r = f(x) + x
  if x != 9 or r != 10: symexTarget("ex_dead")
  if r == 10 and k == 2: symexTarget("ex")

proc sutCond(k: int) =
  let f = setOne
  var x = k
  if k > 3:
    f(x)
  if k > 3 and x != 4: symexTarget("cd_dead")
  if k <= 3 and x != k: symexTarget("cd2_dead")
  if x == 4 and k == 9: symexTarget("cd")

proc sutRaise(k: int) =
  ## A write before a raise is seen by the handler.
  let f = setRaise
  var x = k
  try:
    f(x, k)
  except ValueError:
    if x != 5: symexTarget("rs_dead")
    if x == 5 and k == 1: symexTarget("rs")
  if x != 5: symexTarget("rs2_dead")

proc setBothP(a, b: ptr int) =
  b[] = 2
  a[] = 1

type Ops = object
  f: proc (a, b: var int) {.nimcall.}

type Shape = ref object of RootObj
type Square = ref object of Shape

method setM(o: Shape; a: var int) {.base.} = a = 5
method setM(o: Square; a: var int) = a = 6

suite "S8bh (1): var writes through an indirect call":

  test "nim":
    var x = 3
    var y = 3
    let f = setBoth
    f(x, y)
    check x == 1 and y == 2
    f(x, x)
    check x == 1
    applyG(setBoth, x, y)
    check x == 1
    let g = retV
    x = 2
    let r = g(x) + x
    check x == 9 and r == 10
    let p = Box(x: 3)
    let q = p
    f(p.x, q.x)
    check p.x == 1
    let fp = setBothP
    fp(addr p.x, addr q.x)
    check p.x == 1
    var c = 3
    let h = proc (a: var int) =
      a = 1
      a = c + a
    h(c)
    check c == 2
    var t = (a: 1, b: 1)
    let s1 = setOne
    s1(t.a)
    check t.a == 4
    let o: Shape = Square()
    o.setM(x)
    check x == 6

  test "a proc-valued variable":
    ## RED: `sxSat` (a false one) -- the var writes were dropped.
    discard clean(sutPV, "pv_dead", sxUnsat)
    discard clean(sutPV, "pv", sxSat)

  test "one variable passed twice":
    discard clean(sutPVSame, "pvs_dead", sxUnsat)
    discard clean(sutPVSame, "pvs", sxSat)

  test "a lambda":
    discard clean(sutLam, "lam_dead", sxUnsat)
    discard clean(sutLam, "lam", sxSat)
    discard clean(sutLamCap, "lc_dead", sxUnsat)
    discard clean(sutLamCap, "lc", sxSat)

  test "a generic callee's proc parameter":
    discard clean(sutGen, "gen_dead", sxUnsat)
    discard clean(sutGen, "gen", sxSat)

  test "a proc passed to a callee":
    discard clean(sutHof, "hof_dead", sxUnsat)
    discard clean(sutHof, "hof", sxSat)

  test "a call in an expression":
    discard clean(sutExpr, "ex_dead", sxUnsat)
    discard clean(sutExpr, "ex", sxSat)

  test "a call under a branch":
    discard clean(sutCond, "cd_dead", sxUnsat)
    discard clean(sutCond, "cd2_dead", sxUnsat)
    discard clean(sutCond, "cd", sxSat)

  test "a write before a raise":
    discard clean(sutRaise, "rs_dead", sxUnsat)
    discard clean(sutRaise, "rs", sxSat)
    discard clean(sutRaise, "rs2_dead", sxUnsat)

# ---- 2. a ptr of unknown origin --------------------------------------------
#
# RFC-0005 S8bh item 2. A `ptr T` the SUT is handed (a parameter, a global,
# a field it reads) addressed only its own `ptr`-family cells: never a ref
# object's field, a global or a `var` parameter of type T, which Nim
# reaches with `addr q.x`, `addr g`, `addr v`.

type PQ = ref object
  x: int
  s: string
  b: bool

# ---- RFC-0005 batch 4: S8bh stacked on S8ax and S8be ----------------------
#
# S8be lowers a call through a proc-valued expression that is not a
# variable (`o.g(x)`, `t.g(x)`) in expression position; S8bh's
# `closureCallIR` is what writes a `var` formal back. Stacked, that arm
# goes through `closureCallIR` (it dropped the write: a false `sxSat`).
# And S8ax counts two lvalues of one array that part only at computed
# indices as two locations under a guard (`aliasConds`) the closure call
# must emit too (it emitted none: one location modelled as two).

type ROps = object
  g: proc (a: var int): int {.nimcall.}
