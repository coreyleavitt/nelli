## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 5 of 8 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_b`,
## `tsymex_rfc0005_s8ar_remainder_c`, `tsymex_rfc0005_s8ar_remainder_d`,
## `tsymex_rfc0005_s8ar_remainder_e`, `tsymex_rfc0005_s8ar_remainder_h`,
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
  TabHolder = ref object
    ti: Table[int, int]
    ts: Table[string, string]
    tf: Table[string, float]
    tb: Table[bool, int8]
  BadTab = ref object
    tq: Table[string, seq[int]]
    n: int
  OddHolder = ref object
    hs: HashSet[string]
    bad: Table[string, (int, int)]   ## RFC-0005 S8at: was `seq[int]`, now backed
    n: int

proc tIntKey(t: Table[int, int]) =
  if t.hasKey(3) and t[3] == 7 and t.len == 1: symexTarget("t_intkey")

proc tStrVal(t: Table[string, string]) =
  if "a" in t and t["a"] == "xy": symexTarget("t_strval")

proc tFloatVal(t: Table[string, float]) =
  if "a" in t and t["a"] > 1.5: symexTarget("t_floatval")

proc tLocal(v: string) =
  var t: Table[int8, string]
  t[-1] = v
  t[4] = "z"
  if t[-1] == "q" and t.len == 2: symexTarget("t_local")
  if t.len != 2: symexTarget("t_local_len_dead")
  t.del(-1)
  if -1'i8 in t: symexTarget("t_local_del_dead")
  if t.len == 1 and t[4] == "z": symexTarget("t_local_del")

proc tHeap(p: TabHolder) =
  if p == nil: return
  if 2 in p.ti and p.ti[2] == -5 and "k" in p.ts and p.ts["k"] == "v" and
     "f" in p.tf and p.tf["f"] == 0.5 and true in p.tb and p.tb[true] == -3:
    symexTarget("t_heap")

proc tHeapWrite(p: TabHolder, v: int) =
  if p == nil: return
  p.ti[v] = 1
  if p.ti[v] != 1: symexTarget("t_heap_write_dead")
  if p.ti.len == 0: symexTarget("t_heap_write_len_dead")

proc tBad(p: BadTab) =
  if p != nil and p.tq.len == 1: symexTarget("t_bad")

suite "S8ar (5, 9): every backed Table key and value type, rendered":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "an int key":
    let r = run(tIntKey, "t_intkey", sxSat)
    if r.status == sxSat: check reproduces(tIntKey(r.witness[0]), "t_intkey")

  test "a string value":
    let r = run(tStrVal, "t_strval", sxSat)
    if r.status == sxSat: check reproduces(tStrVal(r.witness[0]), "t_strval")

  test "a float value":
    let r = run(tFloatVal, "t_floatval", sxSat)
    if r.status == sxSat: check reproduces(tFloatVal(r.witness[0]), "t_floatval")

  test "a local Table[int8, string]: set, del, len":
    let r = run(tLocal, "t_local", sxSat)
    if r.status == sxSat: check reproduces(tLocal(r.witness[0]), "t_local")
    discard run(tLocal, "t_local_len_dead", sxUnsat)
    discard run(tLocal, "t_local_del_dead", sxUnsat)
    discard run(tLocal, "t_local_del", sxSat)

  test "Table fields of a ref render every backed value type":
    let r = run(tHeap, "t_heap", sxSat)
    if r.status == sxSat: check reproduces(tHeap(r.witness[0]), "t_heap")

  test "a write to an int-keyed Table field":
    discard run(tHeapWrite, "t_heap_write_dead", sxUnsat)
    discard run(tHeapWrite, "t_heap_write_len_dead", sxUnsat)

  test "a Table whose value is a container is modelled (RFC-0005 S8at)":
    # Pinned a scoped decline until RFC-0005 S8at held a container value
    # leaf-split (`tvTree`); it is now exact and renders.
    let r = run(tBad, "t_bad", sxSat)
    check r.errors.len == 0
    if r.status == sxSat: check reproduces(tBad(r.witness[0]), "t_bad")
