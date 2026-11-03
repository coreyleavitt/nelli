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
## RFC-0005 S8cm: part 6 of 6 of this suite, with
## `tsymex_rfc0005_s8bh_remainder`, `tsymex_rfc0005_s8bh_remainder_b`,
## `tsymex_rfc0005_s8bh_remainder_c`, `tsymex_rfc0005_s8bh_remainder_d`,
## `tsymex_rfc0005_s8bh_remainder_e`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 112 s).

import std/[unittest, strutils, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import s8ct_platform   ## RFC-0005 S8ct

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

proc retV(a: var int): int =
  a = 9
  result = 1

type Ops = object
  f: proc (a, b: var int) {.nimcall.}

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

# ---- 3. a ref converted along its inheritance chain -------------------------
#
# RFC-0005 S8bh item 3. Every type of a hierarchy keyed its own `Ref_<id>`
# sort and its own field heaps, and a derived type's IR carried only the
# fields it declared itself. `Base(d)`, `let b: Base = d` and a `Base`
# parameter aliasing a `Mid` one therefore mixed two sorts (an ill-sorted
# term, `weInternalWalkerFault`), or read an inherited field from a heap the
# other static type never wrote (a false `sxUnsat`).

type
  Base3 = ref object of RootObj
    x: int
  Mid3 = ref object of Base3
    y: int
  Leaf3 = ref object of Mid3
    z: int
  Side3 = ref object of Base3
    y: string   ## a sibling's field of the same name and another type

proc sutParamDown(b: Base3) =
  ## A parameter's dynamic type is any subtype of its static one.
  try:
    let d = Mid3(b)
    if d != nil: symexTarget("pdn")
  except ObjectConversionDefect:
    symexTarget("pdn_raise")

type
  BaseObj4 = object of RootObj
    x: int
  BaseR4 = ref BaseObj4
  DerObj4 = object of BaseObj4
    y: int
  DerR4 = ref DerObj4

proc sutObjStyle(b: BaseR4; d: DerR4) =
  ## The `ref Obj` spelling of a hierarchy (its nominal ids are the
  ## objects').
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2 and BaseR4(d) == b: symexTarget("os")
  if d.x != 2 and BaseR4(d) == b: symexTarget("os_dead")
  let e = DerR4(x: 3)
  if e.y != 0: symexTarget("os_zero_dead")
  try:
    discard DerR4(BaseR4(x: 1))
    symexTarget("os_down_dead")
  except ObjectConversionDefect:
    discard

suite "S8bh (3): a ref converted along its inheritance chain":
  test "the `ref Obj` spelling of a hierarchy":
    let r = clean(sutObjStyle, "os", sxSat)
    if r.status == sxSat:
      check replayedOrNotMarshallable(replayWitness(sutObjStyle, r.witness, tLabel("os"), {}), roConfirmed)
    discard clean(sutObjStyle, "os_dead", sxUnsat)
    discard clean(sutObjStyle, "os_zero_dead", sxUnsat)
    discard clean(sutObjStyle, "os_down_dead", sxUnsat)

  test "a parameter's down-conversion may go either way":
    let r = clean(sutParamDown, "pdn_raise", sxSat)
    if r.status == sxSat:
      check replayedOrNotMarshallable(replayWitness(sutParamDown, r.witness, tLabel("pdn_raise"), {}), roConfirmed)
    discard clean(sutParamDown, "pdn", sxSat)

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

proc sutFieldExpr(k: int) =
  let o = ROps(g: retV)
  var x = k
  let r = o.g(x) + x
  if x != 9 or r != 10: symexTarget("fe_dead")
  if r == 10 and k == 2: symexTarget("fe")

proc sutTupExpr(k: int) =
  let t = (g: retV, n: 1)
  var x = k
  let r = t.g(x)
  if x != 9 or r != 1: symexTarget("te_dead")
  if r == 1 and k == 2: symexTarget("te")

proc sutIdxAlias(i, j: int) =
  if i < 0 or i > 2 or j < 0 or j > 2: return
  let f = setBoth
  var a = [0, 0, 0]
  f(a[i], a[j])
  if i == j and a[i] != 1: symexTarget("ia_dead")
  if i != j and a[i] == 1: symexTarget("ia")

suite "S8bh: stacked on S8ax and S8be (batch 4)":

  test "nim":
    let o = ROps(g: retV)
    var x = 2
    let r = o.g(x) + x
    check x == 9 and r == 10
    var a = [0, 0, 0]
    let f = setBoth
    f(a[1], a[1])
    check a[1] == 1

  test "a proc field's var write in expression position":
    discard clean(sutFieldExpr, "fe_dead", sxUnsat)
    discard clean(sutFieldExpr, "fe", sxSat)
    discard clean(sutTupExpr, "te_dead", sxUnsat)
    discard clean(sutTupExpr, "te", sxSat)

  test "var actuals one location at equal computed indices":
    # As a direct call does (`userCallStmt`): the equal-index path declines.
    declines(sutIdxAlias, "ia_dead", feUnsupportedOp, "indices are equal")
    let r = symexFind(sutIdxAlias, tLabel("ia"))
    checkpoint "ia " & $r.status & " " & show(r.errors)
    check r.status == sxSat

suite "S8bh: walker version":
  test "symexWalkerVersion >= 208":
    check parseInt(symexWalkerVersion) >= 208
