## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 6:
## strings as `openArray[char]` and character writes. The by-value string of
## an address-taken string is `tsymex_rfc0005_s8ca_strings_byvalue` (split by
## item 9: the file was over the 60 s compile budget).
##
## S11 declined every character write (`s[i] = c`): the walk's strings are
## Z3 strings, immutable values. S8bu then declined a string viewed as
## `openArray[char]` (it had been a false sxUnsat).
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (6a) `s[i] = c` is the string with that byte replaced
##        (`iekStrSetAt`), its index checked before the value is evaluated,
##        by name, in a field and through a pointer;
##   (6b) a string viewed as `openArray[char]` is the seq of its bytes
##        (`iekStrChars`), a whole string or a `toOpenArray` slice; a `var`
##        one is written back byte for byte (`iekStrFromChars`);
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8ca_strings_b`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 65 s).

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

from ./s8cu_helpers import nativeHits

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

suite "S8ca (6): strings":

  test "nim":
    let h = nativeHits(sutCharWrite, ks) + nativeHits(sutCharOrder, ks) +
            nativeHits(sutFieldWrite, ks) + nativeHits(sutPtrWrite, ks) +
            nativeHits(sutStrOpenArray, ks) + nativeHits(sutStrSlice, ks) +
            nativeHits(sutVarOA, ks) + nativeHits(sutVarOASlice, ks)
    for l in ["cw", "cw_raise", "co", "co_value", "cf", "cp", "oa", "os",
              "os_raise", "ov", "ow"]:
      checkpoint l
      check l in h
    for l in ["cw", "co", "cf", "cp", "oa", "os", "ov", "ow"]:
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
