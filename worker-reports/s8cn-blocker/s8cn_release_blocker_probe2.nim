import std/[tables, strutils, sets]
import nelli
import nelli/symex
var gs: seq[int]
var gt: Table[string, int]
proc gWrite(a: seq[int]): int =
  gs[0] = 50
  a[0]
proc gtWrite(a: Table[string, int]): int =
  gt["a"] = 50
  a["a"]
proc rab(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]
proc dSeq(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let r = gWrite(gs)
  if r == 50: symexTarget("ds_shared")
  if r == x: symexTarget("ds_copy")
proc dTab(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000 or x == 50: return
  gt = t0
  let r = gtWrite(gt)
  if r == 50: symexTarget("dt_shared")
  if r == x: symexTarget("dt_copy")
proc dVar(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  let r = rab(t["a"], t, "a")
  if r == x + 1: symexTarget("dv_shared")
  if r == x: symexTarget("dv_copy")
template nat(call: untyped): untyped =
  block:
    symexCaptureBegin()
    call
    symexCaptureEnd()
template v(fn: typed; l: static string) =
  block:
    let r = symexFind(fn, tLabel(l))
    var m: seq[string]
    for e in r.errors: m.add $e.kind
    echo l, " ", r.status, " ", m.join(",")
echo "native ", nat(dSeq(@[5])), " ", nat(dTab({"a": 5}.toTable)), " ", nat(dVar({"a": 5}.toTable))
v(dSeq, "ds_shared"); v(dSeq, "ds_copy")
v(dTab, "dt_shared"); v(dTab, "dt_copy")
v(dVar, "dv_shared"); v(dVar, "dv_copy")
