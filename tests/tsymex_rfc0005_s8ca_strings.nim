## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 6:
## strings as `openArray[char]`, character writes, and a by-value string
## of an address-taken string.
##
## S11 declined every character write (`s[i] = c`): the walk's strings are
## Z3 strings, immutable values. S8bu then declined a string viewed as
## `openArray[char]` (it had been a false sxUnsat) and a by-value string
## sharing the memory of an address-taken one.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (6a) `s[i] = c` is the string with that byte replaced
##        (`iekStrSetAt`), its index checked before the value is evaluated,
##        by name, in a field and through a pointer;
##   (6b) a string viewed as `openArray[char]` is the seq of its bytes
##        (`iekStrChars`), a whole string or a `toOpenArray` slice; a `var`
##        one is written back byte for byte (`iekStrFromChars`);
##   (6c) a by-value copy of an address-taken string shares its memory:
##        of a string that owns its memory it is a `view` (an in-place
##        character write is seen); of a literal's, which Nim copies at the
##        first write, it is a plain copy; of a string whose memory the walk
##        cannot place, the call declines (`StrBuf`).
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

proc raiser(): char = raise newException(ValueError, "v")

proc sutCharWrite(k: int) =
  var s = "abc"
  var hit = false
  try:
    s[k] = 'z'
  except IndexDefect:
    hit = true
  if not hit and s == "azc" and k == 1: symexTarget("cw")
  if hit and k == 5: symexTarget("cw_raise")
  if (not hit and s[k] != 'z') or (hit and k >= 0 and k < 3):
    symexTarget("cw_dead")

proc sutCharOrder(k: int) =
  ## Nim checks the index before it evaluates the value.
  var s = "ab"
  var which = 0
  try:
    s[k] = raiser()
  except IndexDefect:
    which = 1
  except ValueError:
    which = 2
  if which == 1 and k == 5: symexTarget("co")
  if which == 2 and k == 1: symexTarget("co_value")
  if which == 2 and k == 5: symexTarget("co_dead")

type SBox = object
  s: string

proc sutFieldWrite(k: int) =
  var o = SBox(s: "ab")
  if k < 0 or k > 1: return
  o.s[k] = 'q'
  if o.s[k] == 'q' and o.s.len == 2 and k == 1: symexTarget("cf")
  if o.s[k] != 'q': symexTarget("cf_dead")

var gpstr: ptr string

proc setThrough(k: int) = gpstr[][k] = 'y'

proc sutPtrWrite(k: int) =
  var s = "abc"
  gpstr = addr s
  if k < 0 or k > 2: return
  setThrough(k)
  if s[k] == 'y' and k == 2: symexTarget("cp")
  if s[k] != 'y': symexTarget("cp_dead")

proc cntOA(a: openArray[char]): int = a.len
proc firstOA(a: openArray[char]): char = a[0]

proc sutStrOpenArray(k: int) =
  let st = "ab"
  if cntOA(st) == 2 and firstOA(st) == 'a' and k == 3: symexTarget("oa")
  if cntOA(st) != 2 or firstOA(st) != 'a': symexTarget("oa_dead")

proc sutStrSlice(k: int) =
  let st = "abcd"
  var n = -9
  var hit = false
  try:
    n = cntOA(st.toOpenArray(1, k))
  except IndexDefect:
    hit = true
  if n == 2 and k == 2 and firstOA(st.toOpenArray(1, k)) == 'b':
    symexTarget("os")
  if hit and k == 5: symexTarget("os_raise")
  if (not hit and k >= 0 and n != k) or (hit and k >= 0 and k < 4):
    symexTarget("os_dead")

proc setOA(a: var openArray[char]) = a[0] = 'z'

proc sutVarOA(k: int) =
  var s = "ab"
  setOA(s)
  if s == "zb" and k == 3: symexTarget("ov")
  if s != "zb": symexTarget("ov_dead")

proc sutVarOASlice(k: int) =
  var s = "abcd"
  setOA(s.toOpenArray(1, 2))
  if s == "azcd" and k == 3: symexTarget("ow")
  if s != "azcd": symexTarget("ow_dead")

proc rdStr(t: string): char =
  gpstr[][0] = 'z'
  t[0]

proc sutOwnedView(k: int) =
  ## The string's memory is its own (`add` copied the literal's): the copy
  ## sees the write. (`"a" & "b"` would be folded to a literal.)
  var st = "a"
  st.add 'b'
  gpstr = addr st
  let r = rdStr(st)
  if r == 'z' and k == 3: symexTarget("bo")
  if r != 'z': symexTarget("bo_dead")

proc sutLiteralView(k: int) =
  ## A literal's memory: the write copies it first, the copy does not see it.
  var st = "ab"
  gpstr = addr st
  let r = rdStr(st)
  if r == 'a' and st[0] == 'z' and k == 3: symexTarget("bl")
  if r != 'a' or st[0] != 'z': symexTarget("bl_dead")

proc sutMaybeEmptyAdd(k: int) =
  ## Appending a string, even an empty one, makes a literal's memory the
  ## string's own (Nim copies it first): the copy sees the write.
  var st = "ab"
  let e = if k == 3: "" else: "c"
  st.add e
  gpstr = addr st
  let r = rdStr(st)
  if r == 'z' and k == 3: symexTarget("be")
  if r != 'z': symexTarget("be_dead")

proc sutUnknownView(k: int) =
  ## A string of unknown provenance (`newString`, an opaque call): declined.
  ## (`$k` declined alike, after 26 s of modelling the conversion.)
  var st = newString(2)
  gpstr = addr st
  let r = rdStr(st)
  if r == 'z' and k == 3: symexTarget("bu")

suite "S8ca (6): strings":

  test "nim":
    let h = nativeHits(sutCharWrite, ks) + nativeHits(sutCharOrder, ks) +
            nativeHits(sutFieldWrite, ks) + nativeHits(sutPtrWrite, ks) +
            nativeHits(sutStrOpenArray, ks) + nativeHits(sutStrSlice, ks) +
            nativeHits(sutVarOA, ks) + nativeHits(sutVarOASlice, ks) +
            nativeHits(sutOwnedView, ks) + nativeHits(sutLiteralView, ks) +
            nativeHits(sutUnknownView, ks) + nativeHits(sutMaybeEmptyAdd, ks)
    for l in ["cw", "cw_raise", "co", "co_value", "cf", "cp", "oa", "os",
              "os_raise", "ov", "ow", "bo", "bl", "bu", "be"]:
      checkpoint l
      check l in h
    for l in ["cw", "co", "cf", "cp", "oa", "os", "ov", "ow", "bo", "bl", "be"]:
      checkpoint l & "_dead"
      check (l & "_dead") notin h

  test "a character write":
    clean(sutCharWrite, "cw", sxSat)
    clean(sutCharWrite, "cw_raise", sxSat)
    clean(sutCharWrite, "cw_dead", sxUnsat)
    clean(sutCharOrder, "co", sxSat)
    clean(sutCharOrder, "co_value", sxSat)
    clean(sutCharOrder, "co_dead", sxUnsat)
    clean(sutFieldWrite, "cf", sxSat)
    clean(sutFieldWrite, "cf_dead", sxUnsat)
    clean(sutPtrWrite, "cp", sxSat)
    clean(sutPtrWrite, "cp_dead", sxUnsat)

  test "openArray[char]":
    clean(sutStrOpenArray, "oa", sxSat)
    clean(sutStrOpenArray, "oa_dead", sxUnsat)
    clean(sutStrSlice, "os", sxSat)
    clean(sutStrSlice, "os_raise", sxSat)
    clean(sutStrSlice, "os_dead", sxUnsat)
    clean(sutVarOA, "ov", sxSat)
    clean(sutVarOA, "ov_dead", sxUnsat)
    clean(sutVarOASlice, "ow", sxSat)
    clean(sutVarOASlice, "ow_dead", sxUnsat)

  test "a by-value copy of an address-taken string":
    clean(sutOwnedView, "bo", sxSat)
    clean(sutOwnedView, "bo_dead", sxUnsat)
    clean(sutLiteralView, "bl", sxSat)
    clean(sutLiteralView, "bl_dead", sxUnsat)
    declines(sutUnknownView, "bu", "does not know whether that memory")
    clean(sutMaybeEmptyAdd, "be", sxSat)
    clean(sutMaybeEmptyAdd, "be_dead", sxUnsat)

suite "S8ca: walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
