## RFC-0016 S8ch (PRC-30) -- S8cc's remainder.
##
## 1. The address of a global taken in a walked callee halted the path
##    (`heUnsafeCast`). It is the global's own cell.
## 2. `unsafeAddr` of a by-value array formal in a walked callee declined
##    (`feUnsupportedOp`). Nim passes an array by address (`ccgIntroducedPtr`;
##    a C array formal decays to a pointer), so the formal is the actual's
##    storage and a write through its address lands there: in a `var`, in a
##    part of one (`h.a`, `m[j]`), or in a temporary.
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
  gBig = default(array[8, int])   # every element the copy-in reads is known
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

proc sutByValTemp(k: int) =
  ## A temporary actual: the callee writes the temporary, the caller sees
  ## nothing.
  var t = 3
  let r = wrByVal([t, 2, 3, 4, 5, 6, 7, 8], k)
  if r == k and t == 3 and k == 4: symexTarget("bt")
  if r != k or t != 3: symexTarget("bt_dead")

type Holder = object
  a: array[8, int]

proc sutByValField(k: int) =
  ## A field actual: natively the callee writes the field, which is the
  ## formal's storage (the field's address is passed).
  var h: Holder
  h.a[1] = 2
  let r = wrByVal(h.a, k)
  if h.a[1] == k and r == k and k == 3: symexTarget("bf")
  if h.a[1] != k or r != k: symexTarget("bf_dead")

proc sutByValElem(k: int) =
  ## An element of an array of arrays: that element is the storage, and its
  ## neighbour is left alone.
  var m: array[2, array[8, int]]
  m[1][1] = 2
  let r = wrByVal(m[1], k)
  if m[1][1] == k and m[0][1] == 0 and r == k and k == 7: symexTarget("be")
  if m[1][1] != k or m[0][1] != 0 or r != k: symexTarget("be_dead")

var gH: Holder

proc sutByValGlobalField(k: int) =
  ## A field of a module-level `var`: the field's location.
  gH = default(Holder)
  gH.a[1] = 2
  let r = wrByVal(gH.a, k)
  if gH.a[1] == k and r == k and k == 9: symexTarget("bg")
  if gH.a[1] != k or r != k: symexTarget("bg_dead")

proc wrReadG(x: array[8, int]; v: int): int =
  ## Reads the global the actual is a part of, after the write.
  let p = unsafeAddr x
  p[][1] = v
  gH.a[1]

proc sutByValGlobalReach(k: int) =
  ## The callee reaches the actual's variable by name too: natively one
  ## location, so it reads what it wrote.
  gH = default(Holder)
  let r = wrReadG(gH.a, k)
  if r == k and k == 10: symexTarget("gr")
  if r != k: symexTarget("gr_dead")

proc wrAndRead(x: array[8, int]; h: Holder): int =
  ## `h` is larger than three words: Nim passes it by address too, so the
  ## write through `x` is seen through `h` when both are one variable.
  let p = unsafeAddr x
  p[][1] = 5
  h.a[1]

proc sutByValFieldAlias(k: int) =
  var h: Holder
  h.a[1] = k
  let r = wrAndRead(h.a, h)
  if r == 5 and k == 8: symexTarget("ba")
  if r != 5: symexTarget("ba_dead")

let gLet = [1, 2, 3, 4, 5, 6, 7, 8]
  ## Nim emits it as `NIM_CONST` data: a write through the formal's address
  ## faults (SIGSEGV; `scratchpad/cgen/arr.nim` in the handoff). No native
  ## run here: it would kill the test binary.

proc sutByValConst(k: int) =
  let r = wrByVal(gLet, k)
  if r == k and k == 11: symexTarget("bc")

template declines(fn: typed, lbl: string, why: string) =
  ## The verdict is untrusted, with the kind and the reason.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and e.severity == sevError and
         why in e.msg: named = true
    check named

suite "S8ch: native":
  test "nim":
    let h = nativeHits(sutAddrWrite, ks) + nativeHits(sutAddrRead, ks) +
            nativeHits(sutByValGlobal, ks) + nativeHits(sutByValLocal, ks) +
            nativeHits(sutAddrReturned, ks) + nativeHits(sutStoredByName, ks) +
            nativeHits(sutStoredThrough, ks) + nativeHits(sutSameAddr, ks) +
            nativeHits(sutByValTemp, ks) + nativeHits(sutByValField, ks) +
            nativeHits(sutByValElem, ks) + nativeHits(sutByValFieldAlias, ks) +
            nativeHits(sutByValGlobalField, ks) +
            nativeHits(sutByValGlobalReach, ks)
    for l in ["aw", "ar", "bv", "bl", "rp", "sn", "sp", "eq", "bt", "bf",
              "be", "ba", "bg", "gr"]:
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
    ## The caller's pointer is the call's fresh result, equal to the cell
    ## only in the path condition. Through S8bh's target selector it may
    ## address `gi`, whose storage is its cell: the write lands there, and
    ## the frame sees one location written.
    clean(sutAddrReturned, "rp", sxSat)
    clean(sutAddrReturned, "rp_dead", sxUnsat)
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
  ## An array formal is a C array parameter: the actual's storage, at any
  ## size. A write through its address lands in a `var` actual, in a
  ## temporary the caller never reads, and faults in constant data.
  test "the actual is a global":
    clean(sutByValGlobal, "bv", sxSat)
    clean(sutByValGlobal, "bv_dead", sxUnsat)
  test "the actual is a local":
    clean(sutByValLocal, "bl", sxSat)
    clean(sutByValLocal, "bl_dead", sxUnsat)
  test "the actual is a temporary":
    clean(sutByValTemp, "bt", sxSat)
    clean(sutByValTemp, "bt_dead", sxUnsat)
  test "the actual is a field":
    ## The field's own location, written back after the call.
    clean(sutByValField, "bf", sxSat)
    clean(sutByValField, "bf_dead", sxUnsat)
  test "the actual is an element of an array":
    clean(sutByValElem, "be", sxSat)
    clean(sutByValElem, "be_dead", sxUnsat)
  test "the actual is a field of a global":
    clean(sutByValGlobalField, "bg", sxSat)
    clean(sutByValGlobalField, "bg_dead", sxUnsat)
  test "the callee also reaches the actual's global":
    ## Natively one location (`gr` is reached, "nim" above); the walk copies
    ## the argument in and out, so the direct read declines.
    declines(sutByValGlobalReach, "gr", "both through")
    declines(sutByValGlobalReach, "gr_dead", "both through")
  test "the actual's variable is also another actual":
    declines(sutByValFieldAlias, "ba", "also")
  test "the actual is constant data":
    declines(sutByValConst, "bc", "SIGSEGV")

suite "S8ch: walker version":
  test "symexWalkerVersion >= 376":
    check parseInt(symexWalkerVersion) >= 376
