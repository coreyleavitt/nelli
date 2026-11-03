## RFC-0005 batch 10: S8cf, S8cb, S8cd, S8cl and S8cr stacked on batch 9.
## Pins for what only the stack shows, each with Nim's own run beside it.
##
##   (1) `alt_miss`: a refutation over a subject that can pass the pattern's safe
##       length is `sxUnknown`, by the limit reason. Nim reaches the label at 30
##       `a` bytes, because the first alternative stops at PCRE's match limit and
##       `contains` reads that as a miss. A larger budget does not change the
##       answer, since the reason is the library's and not the solver's.
##   (2) `procCall`, the magic S8cl declines: the value form, a method's super
##       call, and the statement form with a void routine, whose untyped actual
##       has no type for the call's arguments to read. That form stopped the
##       compile on the merged tree.
##   (3) Shapes two slices reach together: S8cl's allocating magics behind S8cd's
##       globals and `ptr` parameters, S8cb's `$` and `ensureMove` under S8cf's
##       regex and S8cl's magics. Every label agrees with the native run.
##   (4) S8cd's widened proc-value results under writes, repeat calls and copies.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_b10_integration`, `tsymex_rfc0005_b10_integration_b`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 99 s).

import std/[unittest, strutils, sets, re, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.severity == sevHint

template declines(fn: typed, lbl, why: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if why in e.msg: named = true
    check named

type Pr = object
  x, y: int
var gPr = Pr(x: 1, y: 2)
proc fieldPtr(p: ptr int) =
  if p == nil: return
  let a = gPr.y
  p[] = 9
  if gPr.y != a and gPr.y != 9: symexTarget("fp_dead")
  if gPr.y == 9 and a != 9: symexTarget("fp")

# (4) ---------------------------------------------------------------------

proc crTwoCalls(x: int) =
  if x > 1000 or x < -1000: return
  let f = proc(y: int): Table[string, int] =
    result["a"] = y
  let r1 = f(x)
  let r2 = f(x + 1)
  if r1["a"] == r2["a"]: symexTarget("cr2_dead")
  if r2["a"] == x + 1 and x == 3: symexTarget("cr2")

proc crCapture(x: int) =
  var c = 0
  let f = proc(y: int): Table[string, int] =
    inc c
    result["c"] = c
  let r = f(x)
  let s = f(x)
  if r["c"] == 1 and s["c"] == 2 and x == 1: symexTarget("crc")
  if r["c"] == s["c"]: symexTarget("crc_dead")

proc crCopy(x: int) =
  var t = initTable[string, int]()
  let f = proc(y: int): Table[string, int] = t
  let r = f(x)
  t["w"] = 1
  if r.hasKey("w"): symexTarget("cry_dead")
  if t.hasKey("w") and x == 2: symexTarget("cry")

suite "RFC-0005 batch 10: integration":
  test "a store through a ptr that may address a global's field":
    # The dead label is a proof over both worlds, aliased or not; the live one
    # stays a decline until a replay can aim the pointer at the global.
    declines(fieldPtr, "fp", "gPr.y")
    block:
      let r = symexFind(fieldPtr, tLabel("fp_dead"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnsat

  test "proc-value results: nim":
    symexCaptureBegin()
    for x in [1, 2, 3]:
      crTwoCalls(x); crCapture(x); crCopy(x)
    let hits = symexCaptureEnd()
    for l in ["cr2", "crc", "cry"]:
      checkpoint l
      check l in hits
    for l in ["cr2_dead", "crc_dead", "cry_dead"]:
      checkpoint l
      check l notin hits

  test "proc-value results: decided as nim":
    clean(crTwoCalls, "cr2", sxSat)
    clean(crTwoCalls, "cr2_dead", sxUnsat)
    clean(crCapture, "crc", sxSat)
    clean(crCapture, "crc_dead", sxUnsat)
    clean(crCopy, "cry", sxSat)
    clean(crCopy, "cry_dead", sxUnsat)
