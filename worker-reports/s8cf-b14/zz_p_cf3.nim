## S8cf check for release-sort row B14, from sort-probes/p_cf3.nim.
import std/[re, strutils, sets]
import nelli
import nelli/symex

proc altMiss(s: string) =
  if s.len > 0 and s[s.len - 1] == 'c' and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_miss")
proc altMissB(s: string) =
  if s.len == 31 and s[30] == 'c' and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_miss_b")
proc altShort(s: string) =
  if s == "ac" and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_short")

template nh(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

for s in ['a'.repeat(30) & "c", "ac", "c"]:
  echo "NATIVE len=", s.len, " alt_miss=", "alt_miss" in nh(altMiss(s)),
    " alt_miss_b=", "alt_miss_b" in nh(altMissB(s)),
    " alt_short=", "alt_short" in nh(altShort(s))

template v(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    var parts: seq[string]
    for e in r.errors:
      if e.severity == sevError: parts.add $e.kind
    echo "WALK ", lbl, " ", r.status, " [", parts.join(","), "]",
      (if r.status == sxSat: " witness=" & $r.witness else: "")

v(altMiss, "alt_miss")
v(altMissB, "alt_miss_b")
v(altShort, "alt_short")
