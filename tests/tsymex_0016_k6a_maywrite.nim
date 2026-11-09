## RFC-0016 K6a (W-08, row W-08) -- `mayWrite`, the one "may this write memory" oracle
## behind the S8cn `lent` / `let` decline (`mayWriteRoot`'s pointer branch).
##
## A write-shape corpus. Each SUT iterates a global seq (`for x in gs`, the
## element's own memory) while the body writes that memory through `gpq`, a
## pointer to the seq, in one shape. `mayWrite` is an allowlist of
## node kinds proved read-only: a shape it does not know, an opaque callee, a
## cycle and a proc value all read as "may write", and the loop declines
## (`sxUnknown`, "written through a pointer or a ref"). A shape proved
## read-only stays decided. Each pin names which side of that line the
## verdict is on. Native runs confirm the aliasing (`x` sees the write) for
## the may-write shapes and the unchanged element for the read-only ones.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template nativeSees(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      let h = hits(fn(n))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d

template mayWriteDeclines(fn: typed; lbl: static string) =
  ## The verdict that follows from `mayWrite == true`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check "written through a pointer or a ref" in show(r.errors)

template readOnlyDecides(fn: typed; live, dead: static string) =
  ## The verdict that follows from `mayWrite == false`.
  block:
    let a = symexFind(fn, tLabel(live))
    checkpoint live & " " & $a.status & "\n" & show(a.errors)
    check a.status == sxSat
    let b = symexFind(fn, tLabel(dead))
    checkpoint dead & " " & $b.status & "\n" & show(b.errors)
    check b.status == sxUnsat

var gs: seq[int]
var gpq: ptr seq[int]
var gother: int

# ---- callees ---------------------------------------------------------------
proc bump() = inc(gpq[][0])                       # walked, writes
proc bumpDeep() = bump()
proc pongW(k: int)
proc pingW(k: int) =                           # recursive pair, writes
  if k > 0: pongW(k - 1) else: inc(gpq[][0])
proc pongW(k: int) = pingW(k)
proc pongP(k: int): int
proc pingP(k: int): int =                      # recursive pair, pure
  if k > 0: pongP(k - 1) else: 0
proc pongP(k: int): int = pingP(k)
proc pureAdd(a, b: int): int = a + b           # walked, pure
proc peek(): int = gother                        # walked, reads another global
proc pureDeep(a: int): int = pureAdd(pureAdd(a, 1), 2)
proc cMemset(s: pointer; c: cint; n: csize_t): pointer
  {.importc: "memset", header: "<string.h>", discardable.}   # opaque

# ---- the corpus: one write shape per SUT -------------------------------------
template shape(name: untyped; lNew, lOld: static string; newV: untyped;
               body: untyped) {.dirty.} =
  proc name(n: int) =
    if n > 1000 or n < -1000 or n == 99 or n == 0: return
    gs = @[n]
    gpq = addr gs
    var t = 99
    for x in gs:
      body
      if x == newV: symexTarget(lNew)
      if x == n: symexTarget(lOld)

shape(wDeref, "wDeref_new", "wDeref_old", 99): gpq[][0] = 99
shape(wInc, "wInc_new", "wInc_old", n + 1): inc(gpq[][0])
shape(wSwap, "wSwap_new", "wSwap_old", 99): swap(gpq[][0], t)
shape(wCopyMem, "wCopyMem_new", "wCopyMem_old", 99): copyMem(addr gpq[][0], addr t, 8)
shape(wZeroMem, "wZeroMem_new", "wZeroMem_old", 0): zeroMem(addr gpq[][0], 8)
shape(wCast, "wCast_new", "wCast_old", n + 1): inc(cast[ptr int](cast[pointer](addr gpq[][0]))[])
shape(wEmit, "wEmit_new", "wEmit_old", 99): {.emit: "`gs`.p->data[0] = 99;".}
shape(wWalked, "wWalked_new", "wWalked_old", n + 1): bump()
shape(wWalkedDeep, "wWalkedDeep_new", "wWalkedDeep_old", n + 1): bumpDeep()
shape(wRecPair, "wRecPair_new", "wRecPair_old", n + 1): pingW(2)
shape(wOpaque, "wOpaque_new", "wOpaque_old", 0): cMemset(addr gpq[][0], 0, 8)
shape(wProcValue, "wProcValue_new", "wProcValue_old", n + 1):
  var pf: proc () = bump
  pf()
# a cycle with no write in it: a cycle defaults to may-write
shape(wRecPure, "wRecPure_new", "wRecPure_old", 99): discard pingP(2)
# read-only: no pointer is set (the walker declines `addr` outright)
template roShape(name: untyped; lNew, lOld: static string;
                 body: untyped) {.dirty.} =
  proc name(n: int) =
    if n > 1000 or n < -1000 or n == 99 or n == 0: return
    gs = @[n]
    for x in gs:
      body
      if x == 99: symexTarget(lNew)
      if x == n: symexTarget(lOld)

roShape(rPure, "rPure_new", "rPure_old"): discard pureAdd(x, 1)
roShape(rPureDeep, "rPureDeep_new", "rPureDeep_old"): discard pureDeep(x)
roShape(rLocal, "rLocal_new", "rLocal_old"):
  var acc = 0
  acc += x
  if acc < 0: acc = -acc
roShape(rPeek, "rPeek_new", "rPeek_old"): discard peek()
roShape(rReadDeref, "rReadDeref_new", "rReadDeref_old"):
  discard gother

suite "K6a: version floor":
  test "K6a changed the decline set: walker 293 or later":
    check parseInt(symexWalkerVersion) >= 299

suite "K6a: the write-shape corpus (mayWrite == true declines)":
  test "native: the element's memory sees the write":
    nativeSees(wDeref, "wDeref_new", "wDeref_old")
    nativeSees(wInc, "wInc_new", "wInc_old")
    nativeSees(wSwap, "wSwap_new", "wSwap_old")
    nativeSees(wCopyMem, "wCopyMem_new", "wCopyMem_old")
    nativeSees(wZeroMem, "wZeroMem_new", "wZeroMem_old")
    nativeSees(wCast, "wCast_new", "wCast_old")
    nativeSees(wEmit, "wEmit_new", "wEmit_old")
    nativeSees(wWalked, "wWalked_new", "wWalked_old")
    nativeSees(wWalkedDeep, "wWalkedDeep_new", "wWalkedDeep_old")
    nativeSees(wRecPair, "wRecPair_new", "wRecPair_old")
    nativeSees(wOpaque, "wOpaque_new", "wOpaque_old")
    nativeSees(wProcValue, "wProcValue_new", "wProcValue_old")
  test "a direct store through the pointer":
    mayWriteDeclines(wDeref, "wDeref_new")
  test "a stdlib `var`-formal routine fed a dereference":
    mayWriteDeclines(wInc, "wInc_new")
    mayWriteDeclines(wSwap, "wSwap_new")
  test "a stdlib routine given a pointer":
    mayWriteDeclines(wCopyMem, "wCopyMem_new")
    mayWriteDeclines(wZeroMem, "wZeroMem_new")
  test "a cast, an emit":
    mayWriteDeclines(wCast, "wCast_new")
    mayWriteDeclines(wEmit, "wEmit_new")
  test "a walked callee recurses":
    mayWriteDeclines(wWalked, "wWalked_new")
    mayWriteDeclines(wWalkedDeep, "wWalkedDeep_new")
  test "a recursive pair that writes":
    mayWriteDeclines(wRecPair, "wRecPair_new")
  test "an opaque callee may write anything":
    mayWriteDeclines(wOpaque, "wOpaque_new")
  test "a proc value may write anything":
    # declined by the by-name scan before the pointer branch is reached
    let r = symexFind(wProcValue, tLabel("wProcValue_new"))
    check r.status == sxUnknown
    check "may write it" in show(r.errors)
  test "a cycle defaults to may-write (conservative: nothing in it writes)":
    nativeSees(wRecPure, "wRecPure_old", "wRecPure_new")
    mayWriteDeclines(wRecPure, "wRecPure_old")

suite "K6a: the write-shape corpus (mayWrite == false decides)":
  test "native: the element is unchanged":
    nativeSees(rPure, "rPure_old", "rPure_new")
    nativeSees(rPureDeep, "rPureDeep_old", "rPureDeep_new")
    nativeSees(rLocal, "rLocal_old", "rLocal_new")
    nativeSees(rPeek, "rPeek_old", "rPeek_new")
    nativeSees(rReadDeref, "rReadDeref_old", "rReadDeref_new")
  test "a walked pure callee, a nest of them":
    readOnlyDecides(rPure, "rPure_old", "rPure_new")
    readOnlyDecides(rPureDeep, "rPureDeep_old", "rPureDeep_new")
  test "local scalar work":
    readOnlyDecides(rLocal, "rLocal_old", "rLocal_new")
  test "a read of the container, direct or in a walked callee":
    readOnlyDecides(rPeek, "rPeek_old", "rPeek_new")
    readOnlyDecides(rReadDeref, "rReadDeref_old", "rReadDeref_new")
