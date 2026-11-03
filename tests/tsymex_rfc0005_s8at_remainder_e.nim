## RFC-0005 (soundness channels) slice S8at -- S8ar's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 5 of 6 of this suite, with
## `tsymex_rfc0005_s8at_remainder`, `tsymex_rfc0005_s8at_remainder_b`,
## `tsymex_rfc0005_s8at_remainder_c`, `tsymex_rfc0005_s8at_remainder_d`,
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

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (5) a `distinct` over a composite base ---------------------------------

type
  DSq = distinct seq[int]
  DTp = distinct (int, bool)
  DSH = ref object
    ds: DSq
    dt: DTp
    n: int

proc len(d: DSq): int {.borrow.}

# ---- (7) Table float keys and container values ------------------------------

type BTab = ref object
  tq: Table[string, seq[int]]

proc tfParam(t: Table[float, int]) =
  if t.len == 1 and 1.5 in t and t[1.5] == 4: symexTarget("tf_param")

proc tfF32(t: Table[float32, int], k: float32) =
  if k < 0'f32 and k in t and t.len == 1 and t[k] == 7: symexTarget("tf_f32")

proc tfSymKey(t: Table[float, int], k: float) =
  # A symbolic NaN key is never found, whatever the table holds.
  if k != k and k in t: symexTarget("tf_symnan_dead")

proc tcVal(t: Table[string, seq[int]]) =
  if "a" in t and t["a"].len == 2 and t["a"][1] == 9: symexTarget("tc_val")

proc tcLocal(x: int) =
  var t = initTable[int, seq[int]]()
  t[1] = @[x]
  if t[1].len == 1 and t[1][0] == 5: symexTarget("tc_local")
  if t[1].len != 1: symexTarget("tc_local_dead")

proc tcHeap(p: BTab) =
  if p != nil and p.tq.len == 1 and "k" in p.tq and p.tq["k"].len == 1:
    symexTarget("tc_heap")

proc tcSet(t: Table[int, HashSet[int]]) =
  if 3 in t and t[3].len == 2 and 8 in t[3]: symexTarget("tc_set")

proc tcNested(t: Table[string, Table[string, int]]) =
  if "o" in t and "i" in t["o"] and t["o"]["i"] == 6: symexTarget("tc_nested")

proc tcStrs(t: Table[char, seq[string]]) =
  if 'c' in t and t['c'].len == 1 and t['c'][0] == "hi": symexTarget("tc_strs")

proc tcOverwrite(t: Table[string, seq[int]]) =
  var u = t
  u["a"] = @[1, 2, 3]
  if "a" in t and t["a"].len == 1 and u["a"].len == 3: symexTarget("tc_over")
  if u["a"].len != 3: symexTarget("tc_over_dead")

proc tcAdd(x: int) =
  # `t[k].add x` mutates the value in place (`[]`'s `var` overload).
  var t = initTable[string, seq[int]]()
  t["a"] = @[1]
  t["a"].add x
  if t["a"].len == 2 and t["a"][1] == 7: symexTarget("tc_add")
  if t["a"].len == 1: symexTarget("tc_add_dead")

proc tcAddParam(t: Table[string, seq[int]]) =
  var u = t
  if "a" in u:
    u["a"].add 4
    if u["a"].len == t["a"].len: symexTarget("tc_addp_dead")
    if u["a"].len == 3 and u["a"][2] == 4 and t["a"][0] == 2:
      symexTarget("tc_addp")

proc tcAddAbsent(t: Table[string, seq[int]]) =
  # An absent key raises `KeyError` before anything is added.
  var u = t
  try:
    u["z"].add 1
    if "z" notin t: symexTarget("tc_absent_dead")
  except KeyError:
    if "z" notin t: symexTarget("tc_absent")

suite "S8at (7): Table float keys and container values":
  test "a symbolic NaN key is never found":
    let d = symexFind(tfSymKey, tLabel("tf_symnan_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a float-keyed parameter":
    let r = symexFind(tfParam, tLabel("tf_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tfParam(r.witness[0]), "tf_param")

  test "a float32-keyed parameter, negative key":
    let r = symexFind(tfF32, tLabel("tf_f32"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      replays(tfF32(r.witness[0], r.witness[1]), "tf_f32")

  test "a seq-valued parameter":
    let r = symexFind(tcVal, tLabel("tc_val"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcVal(r.witness[0]), "tc_val")

  test "a seq-valued local":
    let r = symexFind(tcLocal, tLabel("tc_local"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcLocal, tLabel("tc_local_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq-valued field":
    let r = symexFind(tcHeap, tLabel("tc_heap"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcHeap(r.witness[0]), "tc_heap")

  test "a set-valued parameter":
    let r = symexFind(tcSet, tLabel("tc_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcSet(r.witness[0]), "tc_set")

  test "a table-valued parameter":
    let r = symexFind(tcNested, tLabel("tc_nested"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcNested(r.witness[0]), "tc_nested")

  test "a seq[string]-valued parameter":
    let r = symexFind(tcStrs, tLabel("tc_strs"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcStrs(r.witness[0]), "tc_strs")

  test "an overwrite leaves the copied-from table alone":
    let r = symexFind(tcOverwrite, tLabel("tc_over"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcOverwrite(r.witness[0]), "tc_over")
    let d = symexFind(tcOverwrite, tLabel("tc_over_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq value is added to in place":
    let r = symexFind(tcAdd, tLabel("tc_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcAdd, tLabel("tc_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a parameter's seq value is added to in place":
    let r = symexFind(tcAddParam, tLabel("tc_addp"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcAddParam(r.witness[0]), "tc_addp")
    let d = symexFind(tcAddParam, tLabel("tc_addp_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "adding to an absent key's value raises KeyError":
    let r = symexFind(tcAddAbsent, tLabel("tc_absent"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcAddAbsent, tLabel("tc_absent_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
