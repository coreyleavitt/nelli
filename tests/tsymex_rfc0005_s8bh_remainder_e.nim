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
## RFC-0005 S8cm: part 5 of 6 of this suite, with
## `tsymex_rfc0005_s8bh_remainder`, `tsymex_rfc0005_s8bh_remainder_b`,
## `tsymex_rfc0005_s8bh_remainder_c`, `tsymex_rfc0005_s8bh_remainder_d`,
## `tsymex_rfc0005_s8bh_remainder_f`. Split so that each part compiles and runs
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

# ---- 1. var writes through an indirect call ---------------------------------

type Box = ref object
  x: int
  y: int

proc setBoth(a, b: var int) =
  ## Writes `b`, then `a`: on one location, `a`'s write is the last.
  b = 2
  a = 1

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

proc sutCvField(k: int) =
  ## `setBoth(Base(d).x, b.x)`: one location passed twice.
  let d = Mid3(x: k, y: k)
  let b: Base3 = d
  setBoth(Base3(d).x, b.x)
  if d.x != 1: symexTarget("cvf_dead")
  if d.x == 1 and k == 3: symexTarget("cvf")

proc sutAliasParams(b: Base3; d: Mid3) =
  ## `b` and `d` may be one object (`sutAliasParams(m, m)`).
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2: symexTarget("apar")
  if d.x != 1 and d.x != 2: symexTarget("apar_dead")

proc sutAliasDisjoint(b: Base3; d: Mid3) =
  ## Control: two fresh objects never alias.
  let m = Mid3(x: 1)
  let n: Base3 = Base3(x: 5)
  n.x = 2
  if m.x != 1: symexTarget("adis_dead")

proc sutInheritedZero(k: int) =
  ## `Mid3()` zeroes the inherited `x` as well as its own `y`.
  let d = Mid3()
  if d.x != 0 or d.y != 0: symexTarget("iz_dead")
  if d.x == 0: symexTarget("iz")

proc sutUpRead(k: int) =
  let d = Mid3(x: k, y: 7)
  d.x = 3
  let b: Base3 = d
  if b.x != 3 or d.y != 7: symexTarget("ur_dead")
  b.x = 4
  if d.x == 4: symexTarget("ur")

proc sutSiblings(k: int) =
  ## `Mid3.y` and `Side3.y` are different fields.
  let s = Side3(x: k, y: "a")
  let m = Mid3(x: k, y: 3)
  if m.y != 3 or s.y != "a": symexTarget("sib_dead")
  if m.y == 3 and s.y == "a": symexTarget("sib")

proc sutDown(k: int) =
  let b: Base3 = Mid3(x: k, y: 4)
  let d = Mid3(b)
  if d.y != 4: symexTarget("dn_dead")
  if d.y == 4: symexTarget("dn")

proc sutDownLeaf(k: int) =
  ## A `Leaf3` is a `Mid3`.
  try:
    let b: Base3 = Leaf3(x: k, y: 4, z: 1)
    let d = Mid3(b)
    if d.y == 4: symexTarget("dl")
  except ObjectConversionDefect:
    symexTarget("dl_raise_dead")

proc sutDownFail(k: int) =
  ## A plain `Base3` is not a `Mid3`: ObjectConversionDefect.
  try:
    let b = Base3(x: k)
    let d = Mid3(b)
    if d.y == 0: symexTarget("dnf_dead")
  except ObjectConversionDefect:
    symexTarget("dnf_raise")

proc sutDownSide(k: int) =
  ## Nor is a sibling.
  try:
    let b: Base3 = Side3(x: k, y: "s")
    discard Mid3(b)
    symexTarget("dns_dead")
  except ObjectConversionDefect:
    symexTarget("dns_raise")

proc sutDownNil(b: Base3) =
  ## A nil converts: Nim checks a non-nil ref only.
  if b != nil: return
  try:
    let d = Mid3(b)
    if d == nil: symexTarget("dnn")
  except ObjectConversionDefect:
    symexTarget("dnn_raise_dead")

suite "S8bh (3): a ref converted along its inheritance chain":
  test "one location reached through two static types":
    ## RED: `sxRaised` (the ill-sorted index of a field heap).
    discard clean(sutCvField, "cvf_dead", sxUnsat)
    discard clean(sutCvField, "cvf", sxSat)
    discard clean(sutUpRead, "ur_dead", sxUnsat)
    discard clean(sutUpRead, "ur", sxSat)

  test "parameters of two static types may alias":
    ## RED: `sxUnsat` (a false one) -- two sorts never meet.
    let r = clean(sutAliasParams, "apar", sxSat)
    if r.status == sxSat:
      check replayedOrNotMarshallable(replayWitness(sutAliasParams, r.witness, tLabel("apar"), {}), roConfirmed)
    discard clean(sutAliasParams, "apar_dead", sxUnsat)
    discard clean(sutAliasDisjoint, "adis_dead", sxUnsat)

  test "a derived object's inherited fields are zeroed and distinct":
    discard clean(sutInheritedZero, "iz_dead", sxUnsat)
    discard clean(sutInheritedZero, "iz", sxSat)
    discard clean(sutSiblings, "sib_dead", sxUnsat)
    discard clean(sutSiblings, "sib", sxSat)

  test "a down-conversion checks the dynamic type":
    discard clean(sutDown, "dn_dead", sxUnsat)
    discard clean(sutDown, "dn", sxSat)
    discard clean(sutDownLeaf, "dl", sxSat)
    discard clean(sutDownLeaf, "dl_raise_dead", sxUnsat)
    ## RED: `sxRaised` (the walker never raised ObjectConversionDefect).
    discard clean(sutDownFail, "dnf_dead", sxUnsat)
    discard clean(sutDownFail, "dnf_raise", sxSat)
    discard clean(sutDownSide, "dns_dead", sxUnsat)
    discard clean(sutDownSide, "dns_raise", sxSat)
    discard clean(sutDownNil, "dnn", sxSat)
    discard clean(sutDownNil, "dnn_raise_dead", sxUnsat)
