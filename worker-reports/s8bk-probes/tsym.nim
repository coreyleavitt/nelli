import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

type Box = ref object
  x: int
var gP: Box
var gSeen: int
var gi: int
var gA: array[3, Box]

proc moveP(): int =
  gP = Box(x: 100)
  0
proc incI(): int =
  inc gi
  0
proc touch(v: var int; k: int) = v = v + 5 + k
proc touchG(v: var int; k: int) =
  v = v + 5 + k
  gSeen = gP.x
proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k
proc touchPG(v: ptr int; k: int) =
  v[] = v[] + 5 + k
  gSeen = gP.x

proc sCopy(k: int) =
  gP = Box(x: k)
  let old = gP
  touch(gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 1: symexTarget("nim")
  if gP.x == k + 5: symexTarget("stale")
  if old.x == k + 5: symexTarget("old")

proc sByRef(k: int) =
  gP = Box(x: k)
  let old = gP
  touchG(gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 1: symexTarget("nim")
  if gP.x == k + 5: symexTarget("stale")
  if old.x == k + 5: symexTarget("old")

proc sAddr(k: int) =
  gP = Box(x: k)
  let old = gP
  touchP(addr gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 1: symexTarget("nim")
  if gP.x == k + 5: symexTarget("stale")
  if old.x == k + 5: symexTarget("old")

proc sAddrG(k: int) =
  gP = Box(x: k)
  let old = gP
  touchPG(addr gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 1: symexTarget("nim")
  if gP.x == k + 5: symexTarget("stale")
  if old.x == k + 5: symexTarget("old")

proc sIdx(k: int) =
  var a = [k, 20, 30]
  gi = 0
  touch(a[gi], incI())
  if a[1] == 25 and a[0] == k and k == 1: symexTarget("nim")
  if a[1] == k + 5 and k != 20: symexTarget("stale")
  if a[0] == k + 5: symexTarget("old")

proc sElem(k: int) =
  gA = [Box(x: k), Box(x: 20), Box(x: 30)]
  gP = gA[0]
  gi = 0
  touchG(gA[gi].x, incI())
  if gA[1].x == 25 and gA[0].x == k and k == 1: symexTarget("nim")
  if gA[0].x == k + 5: symexTarget("old")

template one(f: typed; nm, l: static string) =
  block:
    let r = symexFind(f, tLabel(l))
    echo nm, " ", l, " ", r.status, " ", show(r.errors)
template three(f: typed; nm: static string) =
  one(f, nm, "nim"); one(f, nm, "stale"); one(f, nm, "old")
three(sCopy, "copy")
three(sByRef, "byref")
three(sAddr, "addr")
three(sAddrG, "addrG")
three(sIdx, "idx")
three(sElem, "elem")
