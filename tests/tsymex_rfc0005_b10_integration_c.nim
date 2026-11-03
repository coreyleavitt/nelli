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
## whole file took 99 s). The three tests from `cross-slice shapes: nim` on
## stay together: the last reads `gPr` as the first leaves it.

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

# (3) ---------------------------------------------------------------------

var gRefU: ref int
proc globalUnsafe(k: int) =
  unsafeNew(gRefU, 8)
  gRefU[] = k
  if gRefU[] == 3: symexTarget("gun")
  if gRefU[] != k: symexTarget("gun_dead")

proc newStrPtr(p: ptr string; k: int) =
  if p == nil or k < 0 or k > 4: return
  p[] = newString(k)
  if p[].len == k and k == 2: symexTarget("nsp")
  if p[].len != k: symexTarget("nsp_dead")

proc dollarRe(k: int) =
  if ($k).contains(re"^-") and k == -3: symexTarget("dre")
  if ($k).contains(re"^-") and k >= 0: symexTarget("dre_dead")

proc emInt(k: int) =
  var a = k
  let b = ensureMove(a)
  if b == k and k == 3: symexTarget("emi")
  if b != k: symexTarget("emi_dead")

proc setChr(k: int) =
  let st = {chr(k and 255)}
  if chr(k and 255) in st and k == 3: symexTarget("sch")
  if chr(k and 255) notin st: symexTarget("sch_dead")

type Pr = object
  x, y: int
var gPr = Pr(x: 1, y: 2)
proc fieldPtr(p: ptr int) =
  if p == nil: return
  let a = gPr.y
  p[] = 9
  if gPr.y != a and gPr.y != 9: symexTarget("fp_dead")
  if gPr.y == 9 and a != 9: symexTarget("fp")

suite "RFC-0005 batch 10: integration":
  test "cross-slice shapes: nim":
    symexCaptureBegin()
    for k in [-3, 0, 1, 2, 3, 4, 5]:
      globalUnsafe(k); dollarRe(k); emInt(k); setChr(k)
      var st = ""
      newStrPtr(addr st, k)
    gPr = Pr(x: 1, y: 2)
    fieldPtr(addr gPr.y)
    let hits = symexCaptureEnd()
    for l in ["gun", "nsp", "dre", "emi", "sch", "fp"]:
      checkpoint l
      check l in hits
    for l in ["gun_dead", "nsp_dead", "dre_dead", "emi_dead", "sch_dead", "fp_dead"]:
      checkpoint l
      check l notin hits

  test "cross-slice shapes: decided as nim":
    clean(globalUnsafe, "gun", sxSat)
    clean(globalUnsafe, "gun_dead", sxUnsat)
    clean(newStrPtr, "nsp", sxSat)
    clean(newStrPtr, "nsp_dead", sxUnsat)
    clean(dollarRe, "dre", sxSat)
    clean(dollarRe, "dre_dead", sxUnsat)
    clean(emInt, "emi", sxSat)
    clean(emInt, "emi_dead", sxUnsat)
    clean(setChr, "sch", sxSat)
    clean(setChr, "sch_dead", sxUnsat)

  test "a store through a ptr that may address a global's field":
    # The dead label is a proof over both worlds, aliased or not; the live one
    # stays a decline until a replay can aim the pointer at the global.
    declines(fieldPtr, "fp", "gPr.y")
    block:
      let r = symexFind(fieldPtr, tLabel("fp_dead"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnsat
