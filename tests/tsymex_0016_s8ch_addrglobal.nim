## RFC-0016 S8ch (PRC-30) -- S8cc's remainder.
##
## 1. The address of a global taken in a walked callee halted the path
##    (`heUnsafeCast`). It is the global's own cell.
## 2. `unsafeAddr` of a by-value array formal in a walked callee declined
##    (`feUnsupportedOp`). Nim passes an array by address (`ccgIntroducedPtr`;
##    a C array formal decays to a pointer), so the formal is the actual's
##    storage and a write through its address lands there.
##
## Every expectation is Nim's: each "nim" test runs the SUTs natively under a
## capture frame.

import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import s8ct_platform
from ./s8cu_helpers import nativeHits

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    if want == sxSat and r.status == sxSat:
      check replayedOrNotMarshallable(
        replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

const ks = [-1, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11]

# ---- 1. the address of a global in a walked callee -------------------------

var gi: int

proc setGi(v: int) =
  let p = addr gi
  p[] = v

proc sutAddrWrite(k: int) =
  gi = 0
  setGi(k)
  if gi == k and k == 3: symexTarget("aw")
  if gi != k: symexTarget("aw_dead")

proc readGi(): int =
  let p = addr gi
  p[]

proc sutAddrRead(k: int) =
  gi = k
  let r = readGi()
  if r == k and k == 4: symexTarget("ar")
  if r != k: symexTarget("ar_dead")

proc ptrGi(): ptr int =
  ## The address escapes the callee.
  addr gi

proc sutAddrReturned(k: int) =
  gi = 0
  let p = ptrGi()
  p[] = k
  if gi == k and k == 7: symexTarget("rp")
  if gi != k: symexTarget("rp_dead")

var gp: ptr int

proc aimGp() = gp = addr gi
proc setByName(v: int) = gi = v
proc setThrough(v: int) = gp[] = v

proc sutStoredByName(k: int) =
  ## Stored in a global pointer; another callee writes the global by name.
  gi = 0
  aimGp()
  setByName(k)
  if gp[] == k and k == 8: symexTarget("sn")
  if gp[] != k: symexTarget("sn_dead")

proc sutStoredThrough(k: int) =
  ## Another callee writes through the stored pointer; read by name.
  gi = 0
  aimGp()
  setThrough(k)
  if gi == k and k == 9: symexTarget("sp")
  if gi != k: symexTarget("sp_dead")

proc sutSameAddr(k: int) =
  ## The caller's `addr gi` and the callee's are one pointer.
  gi = k
  let q = addr gi
  let p = ptrGi()
  if p == q and p[] == k and k == 10: symexTarget("eq")
  if p != q: symexTarget("eq_dead")

# ---- 2. `unsafeAddr` of a by-value array formal -----------------------------

var gBig: array[8, int]

proc wrByVal(x: array[8, int]; v: int): int =
  ## The write lands in the caller's storage, and the formal reads it.
  let p = unsafeAddr x
  p[][1] = v
  x[1]

proc sutByValGlobal(k: int) =
  gBig[1] = 2
  let r = wrByVal(gBig, k)
  if gBig[1] == k and r == k and k == 5: symexTarget("bv")
  if gBig[1] != k or r != k: symexTarget("bv_dead")

proc sutByValLocal(k: int) =
  var a: array[8, int]
  a[1] = 2
  let r = wrByVal(a, k)
  if a[1] == k and r == k and k == 6: symexTarget("bl")
  if a[1] != k or r != k: symexTarget("bl_dead")

template declines(fn: typed, lbl: string) =
  ## Item 2 is not modelled yet: the verdict is untrusted, with the kind.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and e.severity == sevError: named = true
    check named

suite "S8ch: native":
  test "nim":
    let h = nativeHits(sutAddrWrite, ks) + nativeHits(sutAddrRead, ks) +
            nativeHits(sutByValGlobal, ks) + nativeHits(sutByValLocal, ks) +
            nativeHits(sutAddrReturned, ks) + nativeHits(sutStoredByName, ks) +
            nativeHits(sutStoredThrough, ks) + nativeHits(sutSameAddr, ks)
    for l in ["aw", "ar", "bv", "bl", "rp", "sn", "sp", "eq"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

suite "S8ch: the address of a global in a walked callee":
  test "a write through it":
    clean(sutAddrWrite, "aw", sxSat)
    clean(sutAddrWrite, "aw_dead", sxUnsat)
  test "a read through it":
    clean(sutAddrRead, "ar", sxSat)
    clean(sutAddrRead, "ar_dead", sxUnsat)

  test "returned to the caller":
    ## Open (handoff): the caller's pointer is the call's fresh result, so
    ## `p[] = k` writes the cell and, through S8bh's target selector, `gi` by
    ## name; the frame sees both written in one statement and declines.
    declines(sutAddrReturned, "rp")
    declines(sutAddrReturned, "rp_dead")
  test "stored in a global pointer, the global written by name":
    clean(sutStoredByName, "sn", sxSat)
    clean(sutStoredByName, "sn_dead", sxUnsat)
  test "stored in a global pointer, written through it":
    clean(sutStoredThrough, "sp", sxSat)
    clean(sutStoredThrough, "sp_dead", sxUnsat)
  test "one pointer in every frame":
    clean(sutSameAddr, "eq", sxSat)
    clean(sutSameAddr, "eq_dead", sxUnsat)

suite "S8ch: unsafeAddr of a by-value array formal":
  ## Item 2 is S8ch's open remainder (the handoff has the native reading:
  ## an array formal is the actual's storage, a write through its address
  ## lands there, and one into constant data faults). These pin today's
  ## honest decline; the exact model flips them to `clean`.
  test "the actual is a global":
    declines(sutByValGlobal, "bv")
    declines(sutByValGlobal, "bv_dead")
  test "the actual is a local":
    declines(sutByValLocal, "bl")
    declines(sutByValLocal, "bl_dead")

suite "S8ch: walker version":
  test "symexWalkerVersion >= 376":
    check parseInt(symexWalkerVersion) >= 376
