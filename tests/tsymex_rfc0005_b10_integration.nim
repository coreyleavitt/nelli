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
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_b10_integration_b`, `tsymex_rfc0005_b10_integration_c`.
## Split so that each part compiles and runs in under 60 s on the Windows legs
## (the whole file took 99 s).

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

type Pr = object
  x, y: int
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
    # The unbounded subject: on Z3 5.1 the limit reason answers, and 4.13.4 runs out
    # of `seqQueryRLimit` first. Each is a `beSolverUndef` on an `sxUnknown`. The
    # fixed length names the limit on both.
    block:
      let r = symexFind(altMiss, tLabel("alt_miss"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      var undef = false
      for e in r.errors:
        if e.kind == beSolverUndef: undef = true
      check undef
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
