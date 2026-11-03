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
## RFC-0005 S8cm: part 3 of 6 of this suite, with
## `tsymex_rfc0005_s8bh_remainder`, `tsymex_rfc0005_s8bh_remainder_b`,
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

template declines(fn: typed, lbl: string, ek: SymexErrorKind,
                  needle: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == ek and needle in e.msg: named = true
    check named

# ---- 1. var writes through an indirect call ---------------------------------

type Box = ref object
  x: int
  y: int

proc setBoth(a, b: var int) =
  ## Writes `b`, then `a`: on one location, `a`'s write is the last.
  b = 2
  a = 1

proc sutCapAlias(k: int) =
  ## The actual is also the lambda's capture: one location in Nim (`a = 1`
  ## writes `c`, so `c + a` is 2); the walk keeps a copy of each.
  var c = k
  let f = proc (a: var int) =
    a = 1
    a = c + a
  f(c)
  if c != 2: symexTarget("ca_dead")

proc sutUnknown(f: proc (a, b: var int) {.nimcall.}; k: int) =
  ## A proc parameter of the code under test: no target to walk.
  var x = k
  var y = k
  f(x, y)
  if x == k: symexTarget("uk")
  if x != k: symexTarget("uk_moved")

proc sutUnknownHeap(f: proc (a: var int) {.nimcall.}; p: Box) =
  ## The unknown target may also write any heap cell.
  if p == nil: return
  p.y = 3
  var x = 0
  f(x)
  if p.y != 3: symexTarget("ukh_moved")

proc sutHeapCapture(k: int) =
  ## The lambda reaches the actual's cell through its capture: `cap.x = 5`
  ## lands on `p.x` after the formal's write (Nim: 5).
  let p = Box(x: k)
  let cap = p
  let f = proc (a: var int) =
    a = 1
    cap.x = 5
  f(p.x)
  if p.x != 5: symexTarget("hc_dead")

proc sutHeapCaptureOther(k: int) =
  ## A capture of a type that holds no ref to a `Box` cell: no decline.
  let t = (a: k, b: k)
  let p = Box(x: k)
  let f = proc (a: var int) = a = t.a + 1
  if k > 1000 or k < -1000: return
  f(p.x)
  if p.x != k + 1: symexTarget("hco_dead")
  if p.x == 4: symexTarget("hco")

var gPtr: ptr int

proc sutAddrEscape(k: int) =
  ## The body keeps the pointer: a cell for the call is not Nim's address.
  let f = proc (a: ptr int) =
    gPtr = a
    a[] = 1
  var x = k
  f(addr x)
  if x != 1: symexTarget("ae_dead")

type Ops = object
  f: proc (a, b: var int) {.nimcall.}

proc sutProcField(k: int) =
  let o = Ops(f: setBoth)
  var x = k
  var y = k
  o.f(x, y)
  if x != 1: symexTarget("pfld_dead")

type Shape = ref object of RootObj
type Square = ref object of Shape

method setM(o: Shape; a: var int) {.base.} = a = 5
method setM(o: Square; a: var int) = a = 6

proc sutMethod(k: int) =
  let o: Shape = Square()
  var x = k
  o.setM(x)
  if x != 6: symexTarget("m_dead")

suite "S8bh (1): var writes through an indirect call":
  test "an actual that is also the closure's capture declines":
    declines(sutCapAlias, "ca_dead", ceCaptureByRefUnmodelled, "`c`")

  test "an unknown target declines, and its effects are havocked":
    declines(sutUnknown, "uk", ceClosureUnknownCallee, "`f`")
    declines(sutUnknown, "uk_moved", ceClosureUnknownCallee, "`f`")
    declines(sutUnknownHeap, "ukh_moved", ceClosureUnknownCallee, "`f`")

  test "a heap actual the body reaches through a capture (RFC-0005 S8ca)":
    # S8bh declined it ("outside its formals"). RFC-0005 S8ca: the field is
    # passed by reference (`bindVarLocs`' `ref` mode), so the body's write
    # through its capture lands on the formal's location: Nim's 5.
    discard clean(sutHeapCapture, "hc_dead", sxUnsat)
    discard clean(sutHeapCaptureOther, "hco_dead", sxUnsat)
    discard clean(sutHeapCaptureOther, "hco", sxSat)

  test "an addr actual whose pointer may escape declines":
    declines(sutAddrEscape, "ae_dead", feUnsupportedOp, "escape the call")

  test "a proc field and a method call are walked (S8bn)":
    ## They declined at S8bh; S8bn (item 6) walks a call through a proc
    ## field and dispatches a method call on the run-type tag.
    discard clean(sutProcField, "pfld_dead", sxUnsat)
    discard clean(sutMethod, "m_dead", sxUnsat)

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
