## RFC-0005 (soundness channels) slice S8bl, item 1 -- the system's
## bodiless `{.magic.}` routines with a `var` parameter. Beyond `inc`/`dec`
## (S8bc) each one reached the user-call fallback, where a magic is
## registered with an EMPTY body: the write to the `var` argument was
## dropped without a record (`swap`, `setLen` on a string, `add` to a seq
## element: a false sxSat), or the callee's parse crashed the compile
## (`wasMoved`, `move`).
import std/[unittest, strutils, tables]
import nelli
import nelli/symex
import nelli/smt/types

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

# ---- swap -------------------------------------------------------------------

proc swArr(x: int) =
  var a = [x, 2, 3]
  swap(a[0], a[2])
  if a[2] == 9: symexTarget("sw_arr")
  if a[0] == x and x != 3: symexTarget("sw_arr_dead")

proc swVars(x, y: int) =
  var a = x
  var b = y
  swap(a, b)
  if a == 4 and b == 5: symexTarget("sw_vars")
  if a == x and x != y: symexTarget("sw_vars_dead")

proc swSeq(s: seq[int]) =
  var t = s
  swap(t[0], t[1])     # an IndexDefect for `s.len < 2`
  if t[0] == 7 and s[1] != 7: symexTarget("sw_seq_dead")
  if t[1] == 3: symexTarget("sw_seq")

type SwObj = object
  a, b: string

proc swField(o: SwObj) =
  var p = o
  swap(p.a, p.b)
  if p.a == "x": symexTarget("sw_field")
  if p.a != o.b: symexTarget("sw_field_dead")

proc swTab(t: Table[string, int]) =
  var u = t
  swap(u["a"], u["b"])   # a KeyError for an absent key
  if u["a"] == 1 and t["b"] != 1: symexTarget("sw_tab_dead")

# ---- wasMoved / move / reset ------------------------------------------------

proc wmInt(x: int) =
  var a = x
  wasMoved(a)
  if a != 0: symexTarget("wm_dead")
  if x == 3: symexTarget("wm")

proc mvSeq(s: seq[int]) =
  var a = s
  let b = move(a)
  if a.len != 0: symexTarget("mv_dead")
  if b.len == 2 and b[1] == 4: symexTarget("mv")

proc mvInt(x: int) =
  var a = x
  let b = move(a)
  if a != 0 or b != x: symexTarget("mv_int_dead")

proc rsStr(s: string) =
  var a = s
  reset(a)
  if a.len != 0: symexTarget("rs_dead")
  if s == "q": symexTarget("rs")

suite "S8bl (1): swap":
  test "two array elements (was a false sxSat)":
    let d = symexFind(swArr, tLabel("sw_arr_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(swArr, tLabel("sw_arr"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(swArr(r.witness[0]), "sw_arr")

  test "two variables (was a false sxSat)":
    let d = symexFind(swVars, tLabel("sw_vars_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(swVars, tLabel("sw_vars"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(swVars(r.witness[0], r.witness[1]), "sw_vars")

  test "two seq elements, with the IndexDefect":
    let d = symexFind(swSeq, tLabel("sw_seq_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status in {sxUnsat, sxRaised}
    check not d.errors.hasKind(weInternalWalkerFault)
    let r = symexFind(swSeq, tLabel("sw_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(swSeq(r.witness[0]), "sw_seq")

  test "two object fields":
    let d = symexFind(swField, tLabel("sw_field_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(swField, tLabel("sw_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(swField(r.witness[0]), "sw_field")

  test "two Table values, with the KeyError":
    let d = symexFind(swTab, tLabel("sw_tab_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status in {sxUnsat, sxRaised}
    check not d.errors.hasKind(weInternalWalkerFault)

suite "S8bl (1): wasMoved, move, reset":
  test "wasMoved zeroes its argument (was a compile crash)":
    let d = symexFind(wmInt, tLabel("wm_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(wmInt, tLabel("wm"))
    check r.status == sxSat

  test "move returns the value and zeroes its argument (was a compile crash)":
    let d = symexFind(mvSeq, tLabel("mv_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(mvSeq, tLabel("mv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(mvSeq(r.witness[0]), "mv")
    let i = symexFind(mvInt, tLabel("mv_int_dead"))
    checkpoint $i.status & " " & show(i.errors)
    check i.status == sxUnsat

  test "reset is the type's zero (was a decline at its `when`)":
    let d = symexFind(rsStr, tLabel("rs_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(rsStr, tLabel("rs"))
    check r.status == sxSat
