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
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8ca_strings`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 65 s).

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

type SBox = object
  s: string

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

suite "S8ca: walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
