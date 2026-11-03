## RFC-0005 (soundness channels) slice S8at -- S8ar's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8at_remainder_b`, `tsymex_rfc0005_s8at_remainder_c`,
## `tsymex_rfc0005_s8at_remainder_d`, `tsymex_rfc0005_s8at_remainder_e`,
## `tsymex_rfc0005_s8at_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 115 s).

import std/[unittest, strutils, sequtils, tables, sets]
import nelli
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

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (2) `initTable[K, V]()` / `initHashSet[T]()` inside a SUT -------------

proc itPut(k, v: int) =
  var t = initTable[int, int]()
  t[k] = v
  if t[k] == 3 and t.len == 1: symexTarget("it_put")
  if t.len != 1: symexTarget("it_put_dead")

proc itEmpty(k: int) =
  let t = initTable[string, int]()
  if t.hasKey("a"): symexTarget("it_empty_dead")
  if t.len == 0 and k == 4: symexTarget("it_empty")

proc itSized(k: int) =
  var t = initTable[int, int](8)
  t[k] = 1
  if t.len == 1 and k == 9: symexTarget("it_sized")

proc itSymSize(n, k: int) =
  var t = initTable[int, int](n)
  t[k] = 1
  if t.len == 1 and k == 2: symexTarget("it_symsize")

proc itNeg(n: int) =
  try:
    let t = initTable[int, int](n)
    if t.len == 0: symexTarget("it_neg_ok")
  except RangeDefect:
    symexTarget("it_neg_raised")

proc itHuge(n: int) =
  if n > 2_000_000:
    let t = initTable[int, int](n)
    if t.len == 0: symexTarget("it_huge")

proc hsPut(k: int) =
  var s = initHashSet[int]()
  s.incl k
  if k in s and s.len == 1 and k == 5: symexTarget("hs_put")
  if s.len != 1: symexTarget("hs_put_dead")

proc mkOne[T](): T = T(1)

proc retOnlyGeneric(k: int) =
  let x = mkOne[int]()
  if x == 1 and k == 6: symexTarget("ret_only")
  if x != 1: symexTarget("ret_only_dead")

proc mkSeqOf[T](): seq[T] = newSeq[T]()

proc retOnlyNewSeq(k: int) =
  let s = mkSeqOf[int]()
  if s.len == 0 and k == 6: symexTarget("ret_newseq")

suite "S8at (2): initTable / initHashSet in a SUT":
  test "initTable[int, int]() then a store":
    let r = symexFind(itPut, tLabel("it_put"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(itPut(r.witness[0], r.witness[1]), "it_put")
    let d = symexFind(itPut, tLabel("it_put_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an initTable is empty":
    let r = symexFind(itEmpty, tLabel("it_empty"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(itEmpty, tLabel("it_empty_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a literal initial size":
    let r = symexFind(itSized, tLabel("it_sized"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(itSized(r.witness[0]), "it_sized")

  test "a symbolic initial size: a negative one raises RangeDefect":
    let r = symexFind(itNeg, tLabel("it_neg_raised"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] < 0
      check reproduces(itNeg(r.witness[0]), "it_neg_raised")
    let r2 = symexFind(itNeg, tLabel("it_neg_ok"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      check reproduces(itNeg(r2.witness[0]), "it_neg_ok")

  test "a symbolic initial size: a small one is modelled":
    let r = symexFind(itSymSize, tLabel("it_symsize"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(itSymSize(r.witness[0], r.witness[1]), "it_symsize")

  test "initHashSet[int]() then an incl":
    let r = symexFind(hsPut, tLabel("hs_put"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(hsPut(r.witness[0]), "hs_put")
    let d = symexFind(hsPut, tLabel("hs_put_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a generic bound only by its return type":
    let r = symexFind(retOnlyGeneric, tLabel("ret_only"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
      check reproduces(retOnlyGeneric(r.witness[0]), "ret_only")
    let d = symexFind(retOnlyGeneric, tLabel("ret_only_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "newSeq through such a generic compiles, and is modelled":
    # S8at pinned `sxSat` or `sxUnknown`: `newSeq` had no model, its stdlib
    # body walked until the call-depth budget ran out. RFC-0005 S8bc
    # (item 5) models it (`iekSeqNewZero`).
    let r = symexFind(retOnlyNewSeq, tLabel("ret_newseq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(retOnlyNewSeq(r.witness[0]), "ret_newseq")

  test "an initial size above the modelled bound declines, scoped":
    let r = symexFind(itHuge, tLabel("it_huge"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and
                         "initial size above" in it.msg)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (5) a `distinct` over a composite base ---------------------------------

type
  DSq = distinct seq[int]
  DTp = distinct (int, bool)
  DSH = ref object
    ds: DSq
    dt: DTp
    n: int

proc len(d: DSq): int {.borrow.}
