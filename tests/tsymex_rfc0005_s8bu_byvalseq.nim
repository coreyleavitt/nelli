## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 6: a
## by-value seq or string whose whole address is taken. Item 5 is
## `tsymex_rfc0005_s8bu_paths` (split by RFC-0005 S8ca, item 9: the file was
## over the 60 s compile budget).
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (6) a by-value seq formal whose actual is an address-taken seq (or a
##       seq field of one) shares its memory: it follows the cell while the
##       cell's elements are written in place (`p[][i] = v`, which was an
##       "unsupported nnkAsgn shape", or `p.s[i] = v`), and the path is
##       declined once the cell is assigned whole or resized (Nim's copy
##       then points at memory it may have freed). A string's declines: a
##       write to a character is not modelled (RFC-0005 S8ca: modelled,
##       `ss` repinned; `tsymex_rfc0005_s8ca_strings_byvalue`).
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
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
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

const ks = [-3, 0, 1, 2, 3, 5, 7]

# ---- (6) a by-value seq whose whole address is taken -----------------------

var gps: ptr seq[int]

proc rdAfter(t: seq[int], k: int): int =
  gps[][0] = k
  t[0]

proc sutSeqView(k: int) =
  var s = @[0, 0]
  gps = addr s
  let r = rdAfter(s, k)
  if r == k and k == 3: symexTarget("sv")
  if r != k: symexTarget("sv_dead")

proc rdUntouched(t: seq[int], k: int): int =
  t[0] + k

proc sutSeqUntouched(k: int) =
  if k < 0 or k > 1000: return
  var s = @[5, 0]
  gps = addr s
  let r = rdUntouched(s, k)
  if r == k + 5 and k == 3: symexTarget("su")
  if r != k + 5: symexTarget("su_dead")

proc rdInner(t: seq[int]): int = t[1]

proc rdPassOn(t: seq[int], k: int): int =
  gps[][1] = k
  rdInner(t)

proc sutSeqPassOn(k: int) =
  ## The formal passed on by value is the same memory.
  var s = @[0, 0]
  gps = addr s
  let r = rdPassOn(s, k)
  if r == k and k == 3: symexTarget("sp")
  if r != k: symexTarget("sp_dead")

type HS = object
  s: seq[int]
  n: int

var gphs: ptr HS

proc rdField(t: seq[int], k: int): int =
  gphs[].s[1] = k
  t[1] + t.len

proc sutSeqField(k: int) =
  ## A seq field of an address-taken object.
  if k < 0 or k > 1000: return
  var h = HS(s: @[0, 0], n: 1)
  gphs = addr h
  let r = rdField(h.s, k)
  if r == k + 2 and k == 3: symexTarget("sf")
  if r != k + 2: symexTarget("sf_dead")

proc rdWhole(t: seq[int], k: int): int =
  gps[] = @[k, k]
  t[0]

proc sutSeqWhole(k: int) =
  ## An assignment of the whole: Nim's copy points at freed memory.
  var s = @[0, 0]
  gps = addr s
  let r = rdWhole(s, k)
  if r == 7: symexTarget("sa")

proc rdGrow(t: seq[int], k: int): int =
  gps[] = @[k]
  t.len

proc sutSeqGrow(k: int) =
  ## A shorter seq assigned through the pointer.
  var s = @[0, 0]
  gps = addr s
  let r = rdGrow(s, k)
  if r == 2: symexTarget("sg")

var gpstr: ptr string

proc rdStr(t: string): bool =
  gpstr[][0] = 'z'
  t[0] == 'z'

proc sutStrView(k: int) =
  var st = "ab"
  st.add 'c'
  gpstr = addr st
  if rdStr(st) and k == 3: symexTarget("ss")

suite "S8bu (6): a by-value seq whose whole address is taken":

  test "nim":
    let h = nativeHits(sutSeqView, ks) + nativeHits(sutSeqUntouched, ks) +
            nativeHits(sutSeqPassOn, ks) + nativeHits(sutSeqField, ks) +
            nativeHits(sutStrView, ks)
    for l in ["sv", "su", "sp", "sf", "ss"]:
      checkpoint l
      check l in h
    for l in ["sv", "su", "sp", "sf"]:
      check (l & "_dead") notin h

  test "an element written in place is seen":
    clean(sutSeqView, "sv", sxSat)
    clean(sutSeqView, "sv_dead", sxUnsat)
    clean(sutSeqUntouched, "su", sxSat)
    clean(sutSeqUntouched, "su_dead", sxUnsat)
    clean(sutSeqPassOn, "sp", sxSat)
    clean(sutSeqPassOn, "sp_dead", sxUnsat)
    clean(sutSeqField, "sf", sxSat)
    clean(sutSeqField, "sf_dead", sxUnsat)

  test "an assignment of the whole, or a resize, declines":
    declines(sutSeqWhole, "sa", "assigned whole or resized")
    declines(sutSeqGrow, "sg", "assigned whole or resized")

  test "a string (RFC-0005 S8ca)":
    # S8bu declined it. RFC-0005 S8ca: the string owns its memory
    # (`st.add`), so the copy is a view and sees the character write.
    clean(sutStrView, "ss", sxSat)

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
