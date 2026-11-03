## RFC-0005 (soundness channels) slice S8cl -- S8ca's remainder, item 4: a
## string of unknown provenance.
##
## `newString` was an opaque call, so every path through it was tainted, and a
## by-value copy of its address-taken result declined (`StrBuf`). Its result is
## fresh memory the string owns, so it can be placed: `newString` and
## `newStringOfCap` are modelled. An opaque call's result stays a decline: the
## call may return a literal's memory or memory of its own, and a by-value copy
## shares the one and not the other, so no answer is sound for both.
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
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 3, 4, 5, 7]

var gpstr: ptr string

proc rdStr(t: string): char =
  gpstr[][0] = 'z'
  t[0]

proc sutZeroed(k: int) =
  let s = newString(2)
  if s.len == 2 and s[0] == '\0' and s[1] == '\0' and k == 3: symexTarget("nz")
  if s.len != 2 or s[0] != '\0': symexTarget("nz_dead")

proc sutWrite(k: int) =
  var s = newString(2)
  s[1] = 'q'
  var c = s
  c[0] = 'w'
  if s[1] == 'q' and s[0] == '\0' and c[0] == 'w' and k == 3: symexTarget("nw")
  if s[0] == 'w': symexTarget("nw_dead")

proc sutLength(k: int) =
  ## A symbolic length: `Natural`'s check, then that many NUL bytes.
  var hit = false
  if k < 100:
    try:
      let s = newString(k)
      if s.len == 3 and s[2] == '\0': symexTarget("nl")
      if s.len != k: symexTarget("nl_dead")
    except RangeDefect:
      hit = true
  if hit and k == -3: symexTarget("nr")
  if hit and k >= 0: symexTarget("nr_dead")

proc sutHuge(k: int) =
  if k > 0 and k < 1000:
    let s = newString(k + 100_000_000)
    if s.len > 0: symexTarget("nh")

proc sutCap(k: int) =
  var s = newStringOfCap(8)
  if s.len == 0 and k == 3: symexTarget("nc")
  s.add 'x'
  if s.len != 1: symexTarget("nc_dead")

proc sutFreshView(k: int) =
  ## `newString`'s memory is its own: the copy sees the write.
  var st = newString(2)
  gpstr = addr st
  let r = rdStr(st)
  if r == 'z' and k == 3: symexTarget("bf")
  if r != 'z': symexTarget("bf_dead")

proc opaqueStr(k: int): string {.symexOpaque.} =
  if k == 3: "ab" else: "cd" & "e"

proc sutOpaqueView(k: int) =
  ## An opaque call's memory cannot be placed: declined.
  var st = opaqueStr(k)
  gpstr = addr st
  let r = rdStr(st)
  if r == 'a' and k == 3: symexTarget("bu")

proc sutUninit(k: int) =
  ## Its bytes are unspecified: never read as modelled.
  let s = newStringUninit(2)
  if s.len == 2 and k == 3: symexTarget("ui")

suite "S8cl (4): newString is fresh memory":
  test "nim":
    let h = nativeHits(sutZeroed, ks) + nativeHits(sutWrite, ks) +
            nativeHits(sutLength, ks) + nativeHits(sutCap, ks) +
            nativeHits(sutFreshView, ks) + nativeHits(sutOpaqueView, ks) +
            nativeHits(sutUninit, ks)
    for l in ["nz", "nw", "nl", "nr", "nc", "bf"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h
    check "bu" in h
    check "ui" in h

  test "its bytes and its writes":
    clean(sutZeroed, "nz", sxSat)
    clean(sutZeroed, "nz_dead", sxUnsat)
    clean(sutWrite, "nw", sxSat)
    clean(sutWrite, "nw_dead", sxUnsat)

  test "its length":
    let r = symexFind(sutLength, tLabel("nl"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    clean(sutLength, "nl_dead", sxUnsat)
    clean(sutLength, "nr", sxSat)
    clean(sutLength, "nr_dead", sxUnsat)
    declines(sutHuge, "nh", "is not modelled")

  test "newStringOfCap":
    clean(sutCap, "nc", sxSat)
    clean(sutCap, "nc_dead", sxUnsat)

  test "a by-value copy of its address-taken result":
    clean(sutFreshView, "bf", sxSat)
    clean(sutFreshView, "bf_dead", sxUnsat)

  test "what cannot be placed still declines":
    declines(sutOpaqueView, "bu", "opaqueStr")
    let u = symexFind(sutUninit, tLabel("ui"))
    checkpoint $u.status & " " & show(u.errors)
    check u.status == sxUnknown

suite "S8cl: walker version":
  test "symexWalkerVersion >= 248":
    check parseInt(symexWalkerVersion) >= 248
