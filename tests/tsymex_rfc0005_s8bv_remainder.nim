## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder: the four
## precision items S8bq reported and did not fix.
##
## Item 1: `for x in s` over a builtin `set[T]` declined. It is unrolled
## over `T`'s domain in ascending order, exactly as `system.items` iterates
## (`T(i) in a` re-read at every step), up to `maxBitSetIterDomain` values.
## Each fixture is also run natively (`symexCaptureBegin`): symex's verdict
## agrees with the targets a real run hits.
import std/[unittest, strutils, sets, monotimes, times]
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
  let t0 = getMonoTime()
  let r = symexFind(sut, tLabel(label))
  echo "TIMING ", label, " ", (getMonoTime() - t0).inMilliseconds
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

template nativeHits(body: untyped): HashSet[string] =
  symexCaptureBegin()
  body
  symexCaptureEnd()

# ---- item 1: iterating a builtin set ----------------------------------------

type E4 = enum e0, e1, e2, e3

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

proc itCharFirst(s: set[char]) =
  var first = '\0'
  var seen = false
  for c in s:
    if not seen:
      first = c
      seen = true
  if 'a' in s and 'b' in s and first == 'b': symexTarget("bv_it_char_first")
  if seen and first == 'q' and card(s) == 1: symexTarget("bv_it_char_one")

proc itCharCount(s: set[char]) =
  var k = 0
  for c in s: inc k
  if k == 2: symexTarget("bv_it_char_count")

proc itInt8First(s: set[int8]) =
  var first = 0'i8
  var seen = false
  for v in s:
    if not seen:
      first = v
      seen = true
  if seen and first > 0 and -5'i8 in s: symexTarget("bv_it_int8_first")
  if seen and first == -128'i8: symexTarget("bv_it_int8_min")

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

proc itMutateSym() =
  # The container is a symbol: `items` re-reads it at every step, so an
  # element removed ahead is not visited, and one added ahead is.
  var u = {e0, e1, e2}
  var k = 0
  for x in u:
    k = k * 10 + ord(x) + 1
    if x == e0:
      u.excl e2
      u.incl e3
  if k == 124: symexTarget("bv_it_mutate_sym")

proc itMutateTemp() =
  # The container is an expression: evaluated once, into a temporary.
  var u = {e0, e1, e2}
  var k = 0
  for x in u + {}:
    k = k * 10 + ord(x) + 1
    if x == e0:
      u.excl e2
      u.incl e3
  if k == 123: symexTarget("bv_it_mutate_temp")

proc itRange(rs: set[range[0..9]]) =
  var bad = false
  for x in rs:
    if x < 0 or x > 9: bad = true
  if bad: symexTarget("bv_it_range")
  var sum = 0
  for x in rs: sum += x
  if sum == 17 and card(rs) == 2 and 9 in rs: symexTarget("bv_it_range_sum")

proc itBool(b: set[bool]) =
  var k = 0
  for x in b:
    k = k * 10 + (if x: 2 else: 1)
  if k == 12: symexTarget("bv_it_bool")
  if k == 21: symexTarget("bv_it_bool_rev")

proc itEmpty() =
  var s: set[E4]
  for x in s: symexTarget("bv_it_empty")

proc itLit(a: E4) =
  var k = 0
  for x in {e3, a}: k = k * 10 + ord(x) + 1
  if k == 14: symexTarget("bv_it_lit")
  if k == 41: symexTarget("bv_it_lit_rev")

proc itCap(s: set[int16]; k: int) =
  # A domain past `maxBitSetIterDomain` declines, scoped to its path.
  if k == 1:
    for v in s: discard v
  elif k == 2:
    symexTarget("bv_it_cap_other")
  if k == 1: symexTarget("bv_it_cap")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 226

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
  test "a set[char]":
    check verdict(itCharFirst, "bv_it_char_first").status == sxUnsat
    let r = verdict(itCharFirst, "bv_it_char_one")
    check r.status == sxSat
    check r.errors.len == 0
    check "bv_it_char_one" in nativeHits(itCharFirst({'q'}))
    check verdict(itCharCount, "bv_it_char_count").status == sxSat
  test "a signed set starts at its low bound":
    check verdict(itInt8First, "bv_it_int8_first").status == sxUnsat
    check verdict(itInt8First, "bv_it_int8_min").status == sxSat
    check "bv_it_int8_min" in nativeHits(itInt8First({-128'i8, 3}))
  test "break leaves the loop":
    check verdict(itBreak, "bv_it_break").status == sxUnsat
    check verdict(itBreak, "bv_it_break_three").status == sxUnsat
    let h = nativeHits(itBreak({e0, e1, e2, e3}))
    check "bv_it_break" notin h and "bv_it_break_three" notin h
  test "continue skips to the next member":
    check verdict(itContinue, "bv_it_continue").status == sxUnsat
    check "bv_it_continue" notin nativeHits(itContinue({e0, e1, e3}))
  test "a set variable is re-read at every step, as items does":
    check "bv_it_mutate_sym" in nativeHits(itMutateSym())
    let r = verdict(itMutateSym, "bv_it_mutate_sym")
    check r.status == sxSat
    check r.errors.len == 0
  test "a set expression is evaluated once":
    check "bv_it_mutate_temp" in nativeHits(itMutateTemp())
    let r = verdict(itMutateTemp, "bv_it_mutate_temp")
    check r.status == sxSat
    check r.errors.len == 0
  test "a range set binds values of the range":
    check verdict(itRange, "bv_it_range").status == sxUnsat
    check verdict(itRange, "bv_it_range_sum").status == sxSat
    check "bv_it_range_sum" in nativeHits(itRange({8, 9}))
  test "a bool set: false first":
    check verdict(itBool, "bv_it_bool").status == sxSat
    check verdict(itBool, "bv_it_bool_rev").status == sxUnsat
    check "bv_it_bool" in nativeHits(itBool({false, true}))
  test "the empty set runs no iteration":
    check verdict(itEmpty, "bv_it_empty").status == sxUnsat
  test "a literal with a variable element":
    check verdict(itLit, "bv_it_lit").status == sxSat
    check verdict(itLit, "bv_it_lit_rev").status == sxUnsat
    check "bv_it_lit" in nativeHits(itLit(e0))
  test "a domain past the cap declines, scoped":
    let r = verdict(itCap, "bv_it_cap")
    check r.status == sxUnknown
    check r.errors.hasMsg(feUnsupportedStmtKind, "maxBitSetIterDomain")
    check verdict(itCap, "bv_it_cap_other").status == sxSat
