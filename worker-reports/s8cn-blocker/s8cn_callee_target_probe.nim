import std/[tables, strutils]
import nelli
import nelli/symex
proc two(a, b: var int) =
  a = 99
  if b == 99: symexTarget("tw_shared")
  else: symexTarget("tw_copy")
proc wbTwo(n: int) =
  if n == 99 or n > 1000 or n < -1000: return
  var s = @[n]
  two(s[0], s[0])
type Box = ref object
  x: int
var gBox: Box
proc viaBox(a: var int) =
  a = 99
  if gBox.x == 99: symexTarget("vb_shared")
  else: symexTarget("vb_copy")
proc wbBox(n: int) =
  if n == 99 or n > 1000 or n < -1000: return
  gBox = Box(x: n)
  let p = gBox
  viaBox(p.x)
var gs2: seq[int]
proc oaw(a: var openArray[int]) =
  gs2[0] = 99
  if a[0] == 99: symexTarget("oa_shared")
  else: symexTarget("oa_copy")
proc wbOa(n: int) =
  if n == 99 or n > 1000 or n < -1000: return
  gs2 = @[n]
  oaw(gs2)
template nat(call: untyped): untyped =
  block:
    symexCaptureBegin()
    call
    symexCaptureEnd()
template q(fn: typed; l: static string) =
  block:
    let r = symexFind(fn, tLabel(l))
    var m: seq[string]
    for e in r.errors: m.add $e.kind
    echo l, " ", r.status, " ", m.join(",")
echo "native ", nat(wbTwo(5)), " ", nat(wbBox(5)), " ", nat(wbOa(5))
q(wbTwo, "tw_shared"); q(wbTwo, "tw_copy")
q(wbBox, "vb_shared"); q(wbBox, "vb_copy")
q(wbOa, "oa_shared"); q(wbOa, "oa_copy")
