## S8cp's module-level check-pragma probe, run on the channel tip.
import std/[strutils, sets]
import nelli
import nelli/symex

type K = enum kA, kB, kC, kD
type P = object
  case k: K
  of kA, kB: x: int
  of kC: y: int
  else: discard

{.push fieldChecks: off.}
proc off1(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("a")
{.pop.}

{.push overflowChecks: off.}
proc off2(v: int) =
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("b")
{.pop.}

proc inner3(v: int) =
  {.push fieldChecks: off.}
  var o = P(k: kA, x: v)
  o.y = v
  {.pop.}
  symexTarget("c")

template nh(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      echo "NATIVE raised ", getCurrentExceptionMsg()
    symexCaptureEnd()

echo "NATIVE a=", "a" in nh(off1(4))
echo "NATIVE b=", "b" in nh(off2(high(int)))
echo "NATIVE c=", "c" in nh(inner3(4))

template v(fn: typed; lbl: static string; tgt: untyped) =
  block:
    let r = symexFind(fn, tgt)
    var parts: seq[string]
    for e in r.errors:
      if e.severity == sevError: parts.add $e.kind
    echo "WALK ", lbl, " ", r.status, " [", parts.join(","), "]"

v(off1, "a_label", tLabel("a"))
v(off1, "a_fielddefect", tFieldDefect())
v(off2, "b_label", tLabel("b"))
v(inner3, "c_label", tLabel("c"))
