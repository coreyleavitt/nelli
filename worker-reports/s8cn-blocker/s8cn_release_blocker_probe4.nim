# A target in a closure body whose call declines. The value at the target is the write
# through the alias, so cg_old, cl_old and cv_old are unreachable under the shared-slot reading.
import std/[strutils, tables]
import nelli
import nelli/symex
var gs: seq[int]
proc gwBody(a: seq[int]) =
  gs[0] = 99
  if a[0] == 99: symexTarget("cg_new")
  else: symexTarget("cg_old")
proc cGlobal(n: int) =
  if n < 0 or n > 5: return
  gs = @[n]
  var f = gwBody
  f(gs)
proc cLambda(n: int) =
  if n < 0 or n > 5: return
  var s = @[n]
  let f = proc (a: seq[int]) =
    s[0] = 99
    if a[0] == 99: symexTarget("cl_new")
    else: symexTarget("cl_old")
  f(s)
proc tvBody(v: var int; t: Table[string, int]) =
  v = 99
  if t["a"] == 99: symexTarget("cv_new")
  else: symexTarget("cv_old")
proc cVarCall(t0: Table[string, int]) =
  if "a" notin t0 or t0["a"] != 7: return
  var t = t0
  var f = tvBody
  f(t["a"], t)
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
echo "native cg ", nat(cGlobal(1))
echo "native cl ", nat(cLambda(1))
echo "native cv ", nat(cVarCall({"a": 7}.toTable))
q(cGlobal, "cg_new"); q(cGlobal, "cg_old")
q(cLambda, "cl_new"); q(cLambda, "cl_old")
q(cVarCall, "cv_new"); q(cVarCall, "cv_old")
