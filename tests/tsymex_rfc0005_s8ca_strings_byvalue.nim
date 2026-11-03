## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 6: a
## by-value string of an address-taken string. Character writes and
## `openArray[char]` are `tsymex_rfc0005_s8ca_strings` (split by item 9: the
## file was over the 60 s compile budget).
##
## S8bu declined a by-value string sharing the memory of an address-taken
## one, a write to a character not being modelled.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
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

var gpstr: ptr string

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

proc opaqueStr(k: int): string {.symexOpaque.} =
  if k == 3: "ab" else: "cd" & "e"

proc sutUnknownView(k: int) =
  ## A string of unknown provenance (an opaque call): declined. (`newString`
  ## was this suite's source until S8cl modelled it: tsymex_rfc0005_s8cl_strings.)
  ## (`$k` declined alike, after 26 s of modelling the conversion.)
  var st = opaqueStr(k)
  gpstr = addr st
  let r = rdStr(st)
  if r == 'a' and k == 3: symexTarget("bu")

suite "S8ca (6c): a by-value copy of an address-taken string":

  test "nim":
    let h = nativeHits(sutOwnedView, ks) + nativeHits(sutLiteralView, ks) +
            nativeHits(sutUnknownView, ks) + nativeHits(sutMaybeEmptyAdd, ks)
    for l in ["bo", "bl", "bu", "be"]:
      checkpoint l
      check l in h
    for l in ["bo", "bl", "be"]:
      checkpoint l & "_dead"
      check (l & "_dead") notin h

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
