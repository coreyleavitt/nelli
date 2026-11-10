## RFC-0016 K2F-1 -- the "may" analyses answer "may" for what they did not read.
##
## RFC section 8.1: a `case` over a NimNode kind has no `else`, or a declining
## one. E6's census found "may" scans whose `else: discard` read an unlisted
## kind as "no write / no rearm / no resize". The scans now list their inert
## leaves, recurse through the structural kinds, and answer "may" for any
## other kind (`mayScanLeafKinds`, `mayScanNoCodeKinds`,
## `mayScanStructuralKinds`, `dsl_parser.nim`).
##
## The REDs the audit found were in the arms beside those `else`s:
## * `mayWriteRoot` (a `for` over a container whose variable holds the
##   element's memory, S8cn) read a write only through `nnkAsgn` or
##   `nnkHiddenAddr`. A writing magic (`inc`, `+=`, `swap`) takes its `var`
##   argument with no `nnkHiddenAddr` (Nim's `FakeVarParams`), so the body
##   read as write-free and the variable kept the value read where it stood:
##   sxSat on the dead label, sxUnsat on the live one. It now reads the
##   magic (`mayWriteMagics`, widened to the whole `FakeVarParams` set).
## * `mayResizeSeq` (a pointer into a seq, S8ax) took a call through a proc
##   FIELD (`h.cb()`) as no call: a closure that replaces the seq left the
##   pointer naming freed memory, and the walk read it as the old element.
##   Natively that read is a use after free, so the pin is the decline.
## * `scanShapeReceiverMutated` (the string-backed `seq[byte]` veto) saw a
##   mutation only as `data[i] = v`, `data.add/del/insert` or a bare `var`
##   actual; `inc data[0]` and `data[0] += 1` are mutations it now reads.
##
## Walker version: 312 (from 311).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

template nativeSees(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      let h = hits(fn(n))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d

template declined(fn: typed; lbl: static string; why: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check why in show(r.errors)

# ---- mayWriteRoot: a writing magic in a `lent` loop body ---------------------
proc lInc(n: int) =
  guardN()
  var s = @[n]
  for x in s:
    inc s[0]
    if x == n + 1: symexTarget("linc_new")
    if x == n: symexTarget("linc_old")
proc lPlusEq(n: int) =
  guardN()
  var s = @[n]
  for x in s:
    s[0] += 1
    if x == n + 1: symexTarget("lpe_new")
    if x == n: symexTarget("lpe_old")
proc lSwap(n: int) =
  guardN()
  var s = @[n]
  var t = n + 1
  for x in s:
    swap(s[0], t)
    if x == n + 1: symexTarget("lsw_new")
    if x == n: symexTarget("lsw_old")
type O = object
  a: int
proc lObjInc(n: int) =
  guardN()
  var s = @[O(a: n)]
  for x in s:
    inc s[0].a
    if x.a == n + 1: symexTarget("loi_new")
    if x.a == n: symexTarget("loi_old")
proc lRead(n: int) =
  ## Precision: a body that only reads the container stays decided.
  guardN()
  var s = @[n]
  var t = 0
  for x in s:
    t += s[0]
    if x == n: symexTarget("lr_old")

# ---- mayResizeSeq / mayRearm: a call through a proc field --------------------
type
  K = enum kA, kB
  C = object
    case k: K
    of kA: a: int
    of kB: b: int
  H = object
    cb: proc() {.closure.}
proc sField(n: int) =
  guardN()
  var s = @[n]
  var h = H(cb: proc() = s = @[1, 2, 3])
  let p = addr s[0]
  h.cb()
  if p[] == n: symexTarget("sf_old")
proc rField(n: int) =
  guardN()
  var o = C(k: kA, a: n)
  var h = H(cb: proc() = o = C(k: kB, b: 7))
  let p = addr o.a
  h.cb()
  if p[] == 7: symexTarget("rf_new")

# ---- scanShapeReceiverMutated: a magic mutation of a byte-seq param ----------
proc bInfix(data: var seq[byte]) =
  if data.len > 0 and data[0] == 41'u8: data[0] += 1
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if data.len > 0 and data[0] == 41'u8:
    symexTarget("binfix_dead")
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("binfix_live")
proc bInc(data: var seq[byte]) =
  if data.len > 0 and data[0] == 41'u8: inc data[0]
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if data.len > 0 and data[0] == 41'u8:
    symexTarget("binc_dead")
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("binc_live")

suite "K2F-1: mayWriteRoot reads a writing magic":
  test "native: the variable sees the write":
    nativeSees(lInc, "linc_new", "linc_old")
    nativeSees(lPlusEq, "lpe_new", "lpe_old")
    nativeSees(lSwap, "lsw_new", "lsw_old")
    nativeSees(lObjInc, "loi_new", "loi_old")
  test "RED was sxSat on the dead label and sxUnsat on the live one; now declined":
    declined(lInc, "linc_new", "memory"); declined(lInc, "linc_old", "memory")
    declined(lPlusEq, "lpe_new", "memory"); declined(lPlusEq, "lpe_old", "memory")
    declined(lSwap, "lsw_new", "memory"); declined(lSwap, "lsw_old", "memory")
    declined(lObjInc, "loi_new", "memory"); declined(lObjInc, "loi_old", "memory")
  test "precision: a read-only body stays decided":
    check symexFind(lRead, tLabel("lr_old")).status == sxSat

suite "K2F-1: a call through a proc field may resize or rearm":
  test "RED was sxSat (a freed element read as the old one); now declined":
    declined(sField, "sf_old", "may resize")
  test "native and walk: the rearm through a field":
    for n in ns: check "rf_new" in hits(rField(n))
    check symexFind(rField, tLabel("rf_new")).status == sxUnknown

suite "K2F-1: scanShapeReceiverMutated reads a magic mutation":
  test "native":
    var d = @[41'u8, 0]
    check "binfix_live" in hits(bInfix(d))
    d = @[41'u8, 0]
    check "binc_live" in hits(bInc(d))
  test "the dead label is not sxSat, the live one is":
    let a = symexFind(bInfix, tLabel("binfix_dead"))
    checkpoint $a.status & "\n" & show(a.errors)
    check a.status != sxSat
    check symexFind(bInfix, tLabel("binfix_live")).status == sxSat
    let b = symexFind(bInc, tLabel("binc_dead"))
    checkpoint $b.status & "\n" & show(b.errors)
    check b.status != sxSat
    check symexFind(bInc, tLabel("binc_live")).status == sxSat

suite "K2F-1: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 312
