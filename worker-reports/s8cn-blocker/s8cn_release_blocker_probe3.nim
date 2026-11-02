# A target in a closure body, with the caller's branch excluding it. Native: never reached.
import std/strutils
import nelli
import nelli/symex
proc nc(a: int) =
  if a == 77: symexTarget("nc_never")
proc cPc(n: int) =
  var f = nc
  if n != 77: f(n)
proc cPc2(n: int) =
  var f = nc
  if n > 100: f(n)
proc cLam(n: int) =
  let f = proc (a: int) =
    if a == 77: symexTarget("nc_never")
  if n != 77: f(n)
proc dPc(n: int) =
  if n != 77: nc(n)
template nat(call: untyped): untyped =
  block:
    symexCaptureBegin()
    call
    symexCaptureEnd()
template q(fn: typed; l: static string; name: string) =
  block:
    let r = symexFind(fn, tLabel(l))
    var m: seq[string]
    for e in r.errors: m.add $e.kind
    echo name, " ", r.status, " ", m.join(",")
var hit = false
for n in [-1, 0, 76, 77, 78, 101, 177]:
  for h in [nat(cPc(n)), nat(cPc2(n)), nat(cLam(n)), nat(dPc(n))]:
    if "nc_never" in h: hit = true
echo "native hit=", hit
q(cPc, "nc_never", "var_proc_value"); q(cPc2, "nc_never", "var_proc_value_gt"); q(cLam, "nc_never", "lambda"); q(dPc, "nc_never", "direct")
