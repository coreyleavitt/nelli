import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity == sevError: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(" | ") & "]"
template nh(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()
template pr(fn: typed; lbl: static string; native: untyped) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    echo lbl, " => ", r.status, " native=", (lbl in native), " witness=", (if r.status == sxSat: $r.witness else: ""), " ", show(r.errors).replace("\n"," ")[^min(240, show(r.errors).len)..^1]
template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return


proc sItems(n: int) =
  if n > 1000 or n < -1000 or n == 5: return
  var s = @[n]
  var r = 0
  for x in s:
    s[0] = 5
    r = x
  if r == n: symexTarget("it_copy")
  if r == 5: symexTarget("it_shared")
proc wr5(s: var seq[int]) = s[0] = 5
proc sItemsCall(n: int) =
  if n > 1000 or n < -1000 or n == 5: return
  var s = @[n]
  var r = 0
  for x in s:
    wr5(s)
    r = x
  if r == n: symexTarget("ic_copy")
  if r == 5: symexTarget("ic_shared")
proc sValues(t0: Table[string,int]) =
  if t0.len != 1 or "a" notin t0: return
  let n = t0["a"]
  if n > 1000 or n < -1000 or n == 5: return
  var t = t0
  var r = 0
  for x in t.values:
    t["a"] = 5
    r = x
  if r == n: symexTarget("tv_copy")
  if r == 5: symexTarget("tv_shared")
var gseq: seq[int]
proc pv2(s: seq[int]): int =
  let c = s
  gseq[0] = 5
  c[0]
proc sGlCur(n: int) =
  if n > 1000 or n < -1000 or n == 5: return
  gseq = @[n]
  let r = pv2(gseq)
  if r == n: symexTarget("gc_copy")
  if r == 5: symexTarget("gc_shared")
let t5 = {"a": 4}.toTable
pr(sItems, "it_copy", nh(sItems(4)))
pr(sItems, "it_shared", nh(sItems(4)))
pr(sItemsCall, "ic_copy", nh(sItemsCall(4)))
pr(sItemsCall, "ic_shared", nh(sItemsCall(4)))
pr(sValues, "tv_copy", nh(sValues(t5)))
pr(sValues, "tv_shared", nh(sValues(t5)))
pr(sGlCur, "gc_copy", nh(sGlCur(4)))
pr(sGlCur, "gc_shared", nh(sGlCur(4)))
var c1, s1, c2, s2, c3, s3, c4, s4 = 0
for n in -5 .. 40:
  if n == 5: continue
  if "it_copy" in nh(sItems(n)): inc c1
  if "it_shared" in nh(sItems(n)): inc s1
  if "ic_copy" in nh(sItemsCall(n)): inc c2
  if "ic_shared" in nh(sItemsCall(n)): inc s2
  if "tv_copy" in nh(sValues({"a": n}.toTable)): inc c3
  if "tv_shared" in nh(sValues({"a": n}.toTable)): inc s3
  if "gc_copy" in nh(sGlCur(n)): inc c4
  if "gc_shared" in nh(sGlCur(n)): inc s4
echo "NATIVE n=-5..40 it copy=", c1, " shared=", s1, "; ic copy=", c2, " shared=", s2, "; tv copy=", c3, " shared=", s3, "; gc copy=", c4, " shared=", s4
