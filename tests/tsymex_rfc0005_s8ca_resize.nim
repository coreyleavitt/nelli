## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 7: a
## `toOpenArray` view of negative length, and a `mitems` body that resizes
## its seq. S8bu declined both on their paths.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design), each as
## probed on the pinned toolchain:
##   (7a) `toOpenArray(s, first, last)` raises `IndexDefect` iff its length
##        is not 0 and a bound is outside `0 ..< s.len`; otherwise a length
##        below 0 is a view of that length, which no loop enters and whose
##        every index raises `IndexDefect`;
##   (7b) a `mitems` body that changes the seq's length meets Nim's
##        `assert(len(a) == L)` at the end of the iteration (an
##        `AssertionDefect`); a use of the element after the change is a
##        use of an address that may be stale, and declines.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
import std/[unittest, strutils, sets]
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
  ## A shape the walk does not model: `sxUnknown`, with the decline named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.severity == sevError and why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 3, 4, 5, 7]


proc lenOA(a: openArray[int]): int = a.len
proc forCount(a: openArray[int]): int =
  for x in a: inc result
proc rd0(a: openArray[int]): bool =
  ## True when `a[0]` raises.
  try:
    discard a[0]
  except IndexDefect:
    result = true
proc setFirst(a: var openArray[int], k: int) = a[0] = k

proc sutNegLen(k: int) =
  let s = @[1, 2, 3, 4]
  var n = -9
  var hit = false
  try:
    n = lenOA(s.toOpenArray(2, k))
  except IndexDefect:
    hit = true
  if not hit and n == -1 and k == 0: symexTarget("nv")
  if hit and k == -3: symexTarget("nv_raise")
  if (k == 0 and (hit or n != -1)) or (k == 1 and (hit or n != 0)):
    symexTarget("nv_dead")

proc sutNegIndex(k: int) =
  let s = @[1, 2, 3, 4]
  if k < 0 or k > 1: return
  let raised = rd0(s.toOpenArray(3, k))
  if raised and k == 0: symexTarget("ni")
  if not raised: symexTarget("ni_dead")

proc sutNegLoop(k: int) =
  let s = @[1, 2, 3, 4]
  if k < 0 or k > 1: return
  let c = forCount(s.toOpenArray(3, k))
  if c == 0 and k == 1: symexTarget("nl")
  if c != 0: symexTarget("nl_dead")

proc sutNegWrite(k: int) =
  var s = @[1, 2, 3, 4]
  var hit = false
  try:
    setFirst(s.toOpenArray(3, 1), k)
  except IndexDefect:
    hit = true
  let same = s.len == 4 and s[0] == 1 and s[1] == 2 and s[2] == 3 and
             s[3] == 4
  if hit and same and k == 3: symexTarget("nw")
  if not hit or not same: symexTarget("nw_dead")

proc sutMitemsAdd(k: int) =
  var s = @[1, 2, 3]
  var hit = false
  try:
    for x in mitems(s):
      if k == 3 and s.len == 3: s.add 9
  except AssertionDefect:
    hit = true
  if hit and s.len == 4 and s[3] == 9 and k == 3: symexTarget("mg")
  if hit != (k == 3) or (not hit and s.len != 3) or (hit and s.len != 4):
    symexTarget("mg_dead")

proc sutMitemsShrink(k: int) =
  var s = @[1, 2, 3]
  var hit = false
  var n = 0
  try:
    for x in mitems(s):
      inc n
      if k == 3: discard s.pop()
  except AssertionDefect:
    hit = true
  if hit and n == 1 and s.len == 2 and k == 3: symexTarget("mh")
  if hit != (k == 3) or (hit and n != 1): symexTarget("mh_dead")

proc sutMitemsUseAfter(k: int) =
  ## The element written after the body grew the seq: Nim's address may be
  ## the old storage's (freed by the growth: undefined, never run).
  var s = @[1, 2, 3]
  try:
    for x in mitems(s):
      if k == 3 and s.len == 3: s.add 9
      x = k
  except AssertionDefect:
    discard
  if s[0] == 3 and k == 3: symexTarget("mu")

suite "S8ca (7a): a toOpenArray view of negative length":

  test "nim":
    let h = nativeHits(sutNegLen, ks) + nativeHits(sutNegIndex, ks) +
            nativeHits(sutNegLoop, ks) + nativeHits(sutNegWrite, ks)
    for l in ["nv", "nv_raise", "ni", "nl", "nw"]:
      checkpoint l
      check l in h
    for l in ["nv", "ni", "nl", "nw"]:
      checkpoint l & "_dead"
      check (l & "_dead") notin h

  test "its length, its check, its index, a loop over it":
    clean(sutNegLen, "nv", sxSat)
    clean(sutNegLen, "nv_raise", sxSat)
    clean(sutNegLen, "nv_dead", sxUnsat)
    clean(sutNegIndex, "ni", sxSat)
    clean(sutNegIndex, "ni_dead", sxUnsat)
    clean(sutNegLoop, "nl", sxSat)
    clean(sutNegLoop, "nl_dead", sxUnsat)
    clean(sutNegWrite, "nw", sxSat)
    clean(sutNegWrite, "nw_dead", sxUnsat)

suite "S8ca (7b): a mitems body that resizes its seq":

  test "nim":
    # `sutMitemsUseAfter` is not run: its write may land in freed memory.
    let h = nativeHits(sutMitemsAdd, ks) + nativeHits(sutMitemsShrink, ks)
    for l in ["mg", "mh"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "Nim's assert at the end of the iteration":
    clean(sutMitemsAdd, "mg", sxSat)
    clean(sutMitemsAdd, "mg_dead", sxUnsat)
    clean(sutMitemsShrink, "mh", sxSat)
    clean(sutMitemsShrink, "mh_dead", sxUnsat)

  test "the element used after the resize declines":
    declines(sutMitemsUseAfter, "mu", "mitems element used after a resize")

suite "S8ca: walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
