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

# (1) ---------------------------------------------------------------------

proc altMiss(s: string) =
  if s.len > 0 and s[s.len - 1] == 'c' and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_miss")

proc altMissLen(s: string) =
  if s.len == 31 and s[30] == 'c' and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_miss_len")

proc altShort(s: string) =
  if s == "ac" and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_short")

# (2) ---------------------------------------------------------------------

proc setIt(x: var int) = x = 5
proc idf(x: int): int = x

proc pcStmt(k: int) =
  var a = k
  procCall setIt(a)
  if a == 5 and k == 3: symexTarget("pc_stmt")
  if a == k and k != 5: symexTarget("pc_stmt_dead")

proc pcValue(k: int) =
  discard procCall(idf(k))
  if k == 3: symexTarget("pc_value")

type
  Bs = ref object of RootObj
    v: int
  Dv = ref object of Bs

method m(b: Bs): int {.base.} = 1
method m(d: Dv): int = procCall(m(Bs(d))) + 1

proc pcMethod(k: int) =
  let d = Dv(v: k)
  if m(d) == 2 and k == 3: symexTarget("pc_method")
  if m(d) == 1: symexTarget("pc_method_dead")

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
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 252

  test "alt_miss: nim reaches the label past the safe length":
    symexCaptureBegin()
    altMiss('a'.repeat(30) & "c")
    altMissLen('a'.repeat(30) & "c")
    altShort("ac")
    let hits = symexCaptureEnd()
    check "alt_miss" in hits
    check "alt_miss_len" in hits
    check "alt_short" notin hits

  test "alt_miss: declines by the limit reason, never sxUnsat":
    declines(altMiss, "alt_miss", "PCRE's own limits")
    declines(altMissLen, "alt_miss_len", "PCRE's own limits")

  test "alt_short: inside the safe length the refutation stands":
    clean(altShort, "alt_short", sxUnsat)

  test "procCall: nim":
    symexCaptureBegin()
    for k in [0, 3, 5]:
      pcStmt(k); pcValue(k); pcMethod(k)
    let hits = symexCaptureEnd()
    check "pc_stmt" in hits
    check "pc_stmt_dead" notin hits
    check "pc_value" in hits
    check "pc_method" in hits
    check "pc_method_dead" notin hits

  test "procCall: every form declines, naming the magic":
    declines(pcStmt, "pc_stmt", "procCall")
    declines(pcStmt, "pc_stmt_dead", "procCall")
    declines(pcValue, "pc_value", "procCall")
    declines(pcMethod, "pc_method", "procCall")
    declines(pcMethod, "pc_method_dead", "procCall")

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
