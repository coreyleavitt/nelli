## RFC-0016 K2F-3 -- the footprint and effect scanners over-approximate what
## they did not read.
##
## RFC section 8.1: a `case` over a NimNode kind has no `else`, or a declining
## one. E6's census listed the footprint, effect, read/write and name scanners
## with a transparent `else`. K2F-1's lesson held: the holes were in the arms
## beside the `else`, node shapes whose effect is not in their children.
##
## * `scanOpaqueEffects` (an opaque call's write summary, S8as) read a call
##   through a proc value (a global proc variable, a proc field, a proc
##   parameter) as a call that writes nothing: the routine it names was never
##   read, so a global it writes kept its value on the returned path. The
##   verdict was sxUnknown (the Defect fork was a candidate that replay
##   refuted), not a false sxUnsat; the label is now sxSat.
## * `scanOpaqueDefects` (an opaque call's Defects, S8be) read an object
##   down-conversion (`Kid(b)`) as a conversion that cannot raise, so
##   `except ObjectConversionDefect` around the call was unreachable: sxUnsat.
## * `claimScopedNames` (S8e) claimed a `for (k, v) in` tuple's names only up
##   to `len - 2`, as if it were a `let` tuple with a type and a value: the
##   loop's `v` kept the raw name and shared the outer `v`'s slot, so the loop
##   overwrote it. sxUnsat on a label native reaches.
##
## The import `{.all.}` row (`check_options.importedNames`/`importPathOf`) needs
## the import to be its module's first, so it is in
## `tsymex_0016_k2f3_importall`.
##
## Walker version: 313 (from 312).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize
from nelli/smt/replayproc import replayForks

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs: result.add $e.kind & "/" & $e.severity & ": " & e.msg & "\n"

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template notUnsat(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status != sxUnsat
    check "weInternalWalkerFault" notin show(r.errors)

template confirmed(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxSat

template confirmedOnFork(fn: typed; lbl: static string; holder: static string) =
  ## A hit through a proc value whose routine the replayed code does not name
  ## (`setK` is named only by the start value of `holder`). A forked child
  ## runs it: confirmed. A re-executed child (Windows) is handed the routine
  ## by its index in the table of routines the replayed code names
  ## (`replaywire.nim`, PRC-02), which `setK` is not in, so the replay
  ## declines, naming the variable. The returned path is still the
  ## candidate the decline names: never sxUnsat, and the hit is not lost.
  block:
    when replayForks:
      confirmed(fn, lbl)
    else:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
      check r.status == sxUnknown
      var named = false
      for e in r.errors:
        if e.kind == feReplayDeclined and
           "replay of a sxSat candidate (target hit)" in e.msg and
           "`" & holder & "` holds a proc value naming no routine" in e.msg:
          named = true
      check named

# ---- scanOpaqueEffects: a call through a proc value -------------------------
var gK: int
proc setK() = gK = 7
var gCb: proc() {.nimcall.} = setK
type Hk = object
  cb: proc() {.nimcall.}
var gH = Hk(cb: setK)

proc opGlobalCb(a: int) {.symexOpaque.} =
  gCb()
proc opFieldCb(a: int) {.symexOpaque.} =
  gH.cb()
proc opParamCb(cb: proc() {.nimcall.}) {.symexOpaque.} =
  cb()
proc opPassCb(a: int) {.symexOpaque.} =
  let f = gCb
  f()

proc sutGlobalCb(v: int) =
  gK = 0
  opGlobalCb(v)
  if gK == 7: symexTarget("gcb")
proc sutFieldCb(v: int) =
  gK = 0
  opFieldCb(v)
  if gK == 7: symexTarget("fcb")
proc sutParamCb(v: int) =
  gK = 0
  opParamCb(setK)
  if gK == 7: symexTarget("pcb")
proc sutPassCb(v: int) =
  gK = 0
  opPassCb(v)
  if gK == 7: symexTarget("lcb")

proc opNoCb(a: int) {.symexOpaque.} =
  discard a
proc sutNoCb(v: int) =
  ## Precision: an opaque body with no proc value keeps its empty summary.
  gK = 0
  opNoCb(v)
  if gK == 0 and v == 1: symexTarget("ncb")
  if gK != 0: symexTarget("ncb_dead")

# ---- scanOpaqueDefects: an object down-conversion --------------------------
type
  Base = ref object of RootObj
    x: int
  Kid = ref object of Base
    y: int

proc opDown(k: int) {.symexOpaque.} =
  let b = Base(x: k)
  discard Kid(b).y
proc sutDown(k: int) =
  try:
    opDown(k)
  except ObjectConversionDefect:
    symexTarget("od")

# ---- claimScopedNames: a `for` tuple's names -------------------------------
proc sutForTuple(n: int) =
  var v = n
  var t = initTable[int, int]()
  t[1] = 7
  for (k, v) in t.pairs:
    discard k
    discard v
  if v == n and n == 3: symexTarget("ft")

suite "K2F-3: scanOpaqueEffects reads a call through a proc value":
  test "native: the global is written":
    check "gcb" in hits(sutGlobalCb(1))
    check "fcb" in hits(sutFieldCb(1))
    check "pcb" in hits(sutParamCb(1))
    check "lcb" in hits(sutPassCb(1))
  test "the summary writes any variable: the hit is confirmed":
    # Before, the returned path kept `gK == 0` (the summary missed the routine
    # the value names) and only the Defect fork (`anyDefect` for a call
    # through a proc value) was a candidate, which replay refuted: sxUnknown,
    # resting on a returned path that read as unreachable.
    confirmedOnFork(sutGlobalCb, "gcb", "gCb")
    confirmedOnFork(sutFieldCb, "fcb", "gH")
    confirmed(sutParamCb, "pcb")      # the SUT names `setK`: both modes
    confirmedOnFork(sutPassCb, "lcb", "gCb")
  test "precision: no proc value, the summary stays empty":
    check "ncb" in hits(sutNoCb(1))
    check symexFind(sutNoCb, tLabel("ncb")).status == sxSat
    check symexFind(sutNoCb, tLabel("ncb_dead")).status == sxUnsat

suite "K2F-3: scanOpaqueDefects reads an object down-conversion":
  test "native: the conversion raises":
    check "od" in hits(sutDown(1))
  test "RED was sxUnsat: the handler was unreachable":
    notUnsat(sutDown, "od")
    confirmed(sutDown, "od")

suite "K2F-3: claimScopedNames claims a for tuple's names":
  test "native: the outer variable keeps its value":
    check "ft" in hits(sutForTuple(3))
  test "RED was sxUnsat: the loop's `v` overwrote the outer one":
    notUnsat(sutForTuple, "ft")
    confirmed(sutForTuple, "ft")

suite "K2F-3: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 313
