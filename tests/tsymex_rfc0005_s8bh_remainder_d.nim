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
## RFC-0005 S8cm: part 4 of 6 of this suite, with
## `tsymex_rfc0005_s8bh_remainder`, `tsymex_rfc0005_s8bh_remainder_b`,
## `tsymex_rfc0005_s8bh_remainder_c`, `tsymex_rfc0005_s8bh_remainder_e`,
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

var gPI: int
var gPS: seq[int]

proc sutPField(q: PQ; pi: ptr int) =
  if q == nil or pi == nil: return
  q.x = 1
  pi[] = 2
  if q.x == 2: symexTarget("pfi")
  if q.x != 1 and q.x != 2: symexTarget("pfi_dead")

proc sutPFieldRead(q: PQ; pi: ptr int) =
  ## A read through the pointer sees the field's write.
  if q == nil or pi == nil: return
  pi[] = 5
  q.x = 7
  if pi[] == 7: symexTarget("pfr")

proc sutPString(q: PQ; ps: ptr string) =
  if q == nil or ps == nil: return
  q.s = "a"
  ps[] = "b"
  if q.s == "b": symexTarget("pfs")

proc sutPBoolDisjoint(q: PQ; pi: ptr int) =
  ## Control: an `int` pointer never addresses a `bool` field.
  if q == nil or pi == nil: return
  q.b = true
  pi[] = 0
  if not q.b: symexTarget("pfb_dead")

proc sutPFresh(pi: ptr int) =
  ## Control: the pointer predates an object the SUT allocates.
  if pi == nil: return
  let q = PQ(x: 1)
  pi[] = 2
  if q.x != 1: symexTarget("pfn_dead")

proc sutPGlobal(pi: ptr int) =
  if pi == nil: return
  gPI = 1
  pi[] = 2
  if gPI == 2: symexTarget("pg")
  if gPI != 1 and gPI != 2: symexTarget("pg_dead")

proc sutPVar(v: var int; pi: ptr int) =
  if pi == nil: return
  v = 1
  pi[] = 2
  if v == 2: symexTarget("pv2")
  if v != 1 and v != 2: symexTarget("pv2_dead")

proc sutPLocal(pi: ptr int) =
  ## Control: a local's address is never the caller's.
  if pi == nil: return
  var x = 1
  pi[] = 2
  if x != 1: symexTarget("pl_dead")

proc writeVia(pi: ptr int) =
  pi[] = 9

proc sutPCallee(q: PQ; pi: ptr int) =
  ## The write is in a callee.
  if q == nil or pi == nil: return
  q.x = 1
  writeVia(pi)
  if q.x == 9: symexTarget("pc")

proc bumpVia(v: var int; pi: ptr int) =
  v = 1
  pi[] = 2

proc sutPVarFormal(pi: ptr int) =
  ## A callee's `var` formal: a scoped decline (the walk copies it in and
  ## out, and the pointer may address its actual).
  if pi == nil: return
  var x = 0
  bumpVia(x, pi)
  if x == 1: symexTarget("pvf")

proc sutPSeqGlobal(pi: ptr int) =
  ## A global seq's element: a scoped decline.
  if pi == nil: return
  gPS = @[1]
  pi[] = 2
  if gPS[0] == 2: symexTarget("psg")

suite "S8bh (2): a ptr of unknown origin":

  test "nim":
    let q = PQ(x: 0)
    sutPField(q, addr q.x)
    check q.x == 2
    sutPGlobal(addr gPI)
    check gPI == 2
    var v = 0
    sutPVar(v, addr v)
    check v == 2

  test "a ptr parameter may address a ref object's field":
    ## RED: `sxUnsat` (a false one).
    let r = clean(sutPField, "pfi", sxSat)
    if r.status == sxSat:
      # The snapshot aims the pointer at the field (`"&<cell>.<field>"`),
      # and the typed witness hands it the field's address.
      var aimed = false
      for e in r.heapSnapshot:
        if e.name == "pi" and e.aliasRef == some("&q.x"): aimed = true
      check aimed
      check replayWitness(sutPField, r.witness, tLabel("pfi"), {}) ==
        roConfirmed
    discard clean(sutPField, "pfi_dead", sxUnsat)
    discard clean(sutPFieldRead, "pfr", sxSat)
    discard clean(sutPString, "pfs", sxSat)
    discard clean(sutPCallee, "pc", sxSat)

  test "disjoint controls":
    discard clean(sutPBoolDisjoint, "pfb_dead", sxUnsat)
    discard clean(sutPFresh, "pfn_dead", sxUnsat)
    discard clean(sutPLocal, "pl_dead", sxUnsat)

  test "a ptr parameter may address a global or a var parameter":
    ## RED: `sxUnsat` (false ones).
    discard clean(sutPGlobal, "pg", sxSat)
    discard clean(sutPGlobal, "pg_dead", sxUnsat)
    discard clean(sutPVar, "pv2", sxSat)
    discard clean(sutPVar, "pv2_dead", sxUnsat)

  test "a by-value aggregate global declines":
    ## S8bn (item 4): a seq element is a target now, but `gPS = @[1]`
    ## replaced the seq the pointer may have addressed: it may dangle.
    declines(sutPSeqGlobal, "psg", feUnsupportedOp, "may dangle")
    ## S8bn (item 3): `x` is a local whose address is never taken, so the
    ## pointer cannot address the formal's actual.
    discard clean(sutPVarFormal, "pvf", sxSat)

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

proc sutCvEq(b: Base3; d: Mid3) =
  if Base3(d) == b and d != nil: symexTarget("cv")

proc sutCvLocal(k: int) =
  let d = Mid3(x: k, y: k)
  let b: Base3 = d
  if Base3(d) == b: symexTarget("cvl")
  if Base3(d) != b: symexTarget("cvl_dead")

proc sutAliasParams(b: Base3; d: Mid3) =
  ## `b` and `d` may be one object (`sutAliasParams(m, m)`).
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2: symexTarget("apar")
  if d.x != 1 and d.x != 2: symexTarget("apar_dead")

suite "S8bh (3): a ref converted along its inheritance chain":

  test "nim":
    let m = Mid3(x: 1, y: 2)
    check Base3(m) == Base3(m)
    sutAliasParams(m, m)
    check m.x == 2
    expect ObjectConversionDefect:
      discard Mid3(Base3(x: 1))
    expect ObjectConversionDefect:
      discard Mid3(Base3(Side3()))
    check Mid3(Base3(Leaf3(y: 4))).y == 4
    check Mid3(Base3(nil)) == nil
    check Mid3().x == 0

  test "an up-conversion keeps the ref's identity":
    ## RED: `weInternalWalkerFault` (an ill-sorted term).
    let r = clean(sutCvEq, "cv", sxSat)
    if r.status == sxSat:
      check replayWitness(sutCvEq, r.witness, tLabel("cv"), {}) == roConfirmed
    discard clean(sutCvLocal, "cvl", sxSat)
    discard clean(sutCvLocal, "cvl_dead", sxUnsat)
