## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 7 of 8 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_b`,
## `tsymex_rfc0005_s8ar_remainder_c`, `tsymex_rfc0005_s8ar_remainder_d`,
## `tsymex_rfc0005_s8ar_remainder_g`, `tsymex_rfc0005_s8ar_remainder_e`,
## `tsymex_rfc0005_s8ar_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 120 s).
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

type
  Sub = object
    x: int
  Inner = object
    s: seq[int]
    a: int
    t: Table[string, int]
    sub: Sub
  Outer = ref object
    inner: Inner

proc dAdd(p: Outer, v: int) =
  if p == nil: return
  let n = p.inner.s.len
  p.inner.s.add v
  if p.inner.s.len != n + 1: symexTarget("d_add_len_dead")
  if p.inner.s[n] != v: symexTarget("d_add_elem_dead")
  if v == 5 and p.inner.a == 3 and n == 2: symexTarget("d_add")

proc dAsg(p: Outer, v: int) =
  if p == nil or v < -100 or v > 100: return
  p.inner.a = v
  p.inner.a += 1
  p.inner.sub.x = v * 2
  if p.inner.a != v + 1: symexTarget("d_asg_dead")
  if p.inner.sub.x != v * 2: symexTarget("d_sub_dead")
  if p.inner.a == 8: symexTarget("d_asg")

proc dIdx(p: Outer) =
  if p == nil or p.inner.s.len == 0: return
  p.inner.s[0] = 9
  if p.inner.s[0] != 9: symexTarget("d_idx_dead")
  symexTarget("d_idx")

proc dIdxRaise(p: Outer) =
  if p == nil: return
  p.inner.s[0] = 9

proc dTab(p: Outer) =
  if p == nil: return
  p.inner.t["k"] = 4
  if p.inner.t["k"] != 4: symexTarget("d_tab_dead")
  symexTarget("d_tab")

proc dAlias(p: Outer) =
  if p == nil: return
  let q = p
  let n = q.inner.s.len
  p.inner.s.insert(7, 0)
  if q.inner.s.len != n + 1 or q.inner.s[0] != 7: symexTarget("d_alias_dead")

suite "S8ar (4): a value chain rooted at a ref object's field":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(feUnsupportedStmtKind)
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "p.inner.s.add v":
    discard run(dAdd, "d_add_len_dead", sxUnsat)
    discard run(dAdd, "d_add_elem_dead", sxUnsat)
    let r = run(dAdd, "d_add", sxSat)
    if r.status == sxSat:
      check reproduces(dAdd(r.witness[0], r.witness[1]), "d_add")

  test "p.inner.a = v, p.inner.a += 1, p.inner.sub.x = v":
    discard run(dAsg, "d_asg_dead", sxUnsat)
    discard run(dAsg, "d_sub_dead", sxUnsat)
    let r = run(dAsg, "d_asg", sxSat)
    if r.status == sxSat:
      check reproduces(dAsg(r.witness[0], r.witness[1]), "d_asg")

  test "p.inner.s[0] = v forks its IndexDefect":
    discard run(dIdx, "d_idx_dead", sxUnsat)
    let r = run(dIdx, "d_idx", sxSat)
    if r.status == sxSat: check reproduces(dIdx(r.witness[0]), "d_idx")
    let ex = symexFind(dIdxRaise, tRaisedExn("IndexDefect"))
    checkpoint $ex.status & " " & show(ex.errors)
    check ex.status == sxRaised
    if ex.status == sxRaised:
      check ex.raisedWitness[0] != nil and ex.raisedWitness[0].inner.s.len == 0

  test "p.inner.t[k] = v":
    discard run(dTab, "d_tab_dead", sxUnsat)
    discard run(dTab, "d_tab", sxSat)

  test "an alias sees the write":
    discard run(dAlias, "d_alias_dead", sxUnsat)
