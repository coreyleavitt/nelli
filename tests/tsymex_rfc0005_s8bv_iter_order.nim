## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder, item 1 (order, a count, break, continue).
##
## `for x in s` over a builtin `set[T]` declined. It is unrolled over `T`'s
## domain in ascending order, exactly as `system.items` iterates (`T(i) in a`
## re-read at every step), up to `maxBitSetIterDomain` values. Each fixture is
## also run natively (`symexCaptureBegin`): symex's verdict agrees with the
## targets a real run hits. Split so each file stays under 60 s on Windows.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc hasMsg(errs: seq[SymexErrorInfo]; k: SymexErrorKind; sub: string): bool =
  for e in errs:
    if e.kind == k and sub in e.msg: return true
  false

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

from ./s8cu_helpers import nativeHits

proc itOrder(s: set[E4]) =
  # Ascending order: {e1, e3} accumulates 2 then 4.
  var acc = 0
  for x in s: acc = acc * 10 + ord(x) + 1
  if acc == 24: symexTarget("bv_it_order")
  if acc == 42: symexTarget("bv_it_order_rev")

proc itCount(s: set[E4]) =
  var k = 0
  for x in s: inc k
  if k != card(s): symexTarget("bv_it_count")

proc itBreak(s: set[E4]) =
  var k = 0
  for x in s:
    if x == e2: break
    inc k
  if e0 in s and e1 in s and e2 in s and k != 2: symexTarget("bv_it_break")
  if e2 in s and k == 3: symexTarget("bv_it_break_three")

proc itContinue(s: set[E4]) =
  var k = 0
  for x in s:
    if x == e1: continue
    k = k * 10 + ord(x) + 1
  if s == {e0, e1, e3} and k != 14: symexTarget("bv_it_continue")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 250

suite "S8bv (1): for x in a builtin set":
  test "ascending order":
    let r = verdict(itOrder, "bv_it_order")
    check r.status == sxSat
    check r.errors.len == 0
    check $r.witness == "({e1, e3},)"
    check verdict(itOrder, "bv_it_order_rev").status == sxUnsat
    let h = nativeHits(itOrder({e1, e3}))
    check "bv_it_order" in h and "bv_it_order_rev" notin h
  test "every member is visited once":
    check verdict(itCount, "bv_it_count").status == sxUnsat
  test "break leaves the loop":
    check verdict(itBreak, "bv_it_break").status == sxUnsat
    check verdict(itBreak, "bv_it_break_three").status == sxUnsat
    let h = nativeHits(itBreak({e0, e1, e2, e3}))
    check "bv_it_break" notin h and "bv_it_break_three" notin h
  test "continue skips to the next member":
    check verdict(itContinue, "bv_it_continue").status == sxUnsat
    check "bv_it_continue" notin nativeHits(itContinue({e0, e1, e3}))
