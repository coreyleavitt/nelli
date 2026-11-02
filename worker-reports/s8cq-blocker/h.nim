import std/[strutils, algorithm, sets]
import nelli/symex
export symex
var natHits*: HashSet[string]
template nat*(call: untyped) =
  block:
    symexCaptureBegin()
    try:
      call
    except CatchableError: discard
    for h in symexCaptureEnd(): natHits.incl h
proc natDump*() =
  var l: seq[string]
  for x in natHits: l.add x
  l.sort
  echo "NATIVE ", l.join(" ")
template v*(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    var errs: seq[string]
    for e in r.errors: errs.add $e.kind
    echo "V ", lbl, " ", (if lbl in natHits: "HIT" else: "no "), " ", r.status, " ", errs.join(",")
template vv*(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    var errs: seq[string]
    for e in r.errors: errs.add $e.kind
    let hit = lbl in natHits
    let bad = (hit and r.status == sxUnsat) or (not hit and r.status == sxSat)
    echo (if bad: "FALSE " else: "ok    "), lbl, " ", (if hit: "HIT" else: "no "), " ", r.status, " ", errs.join(",")
