# Which shapes hit the walker's KeyError on 6cbfe8f: a callee writing a global element.
import std/strutils
import nelli
import nelli/symex
var gs: seq[int]
proc wNoArg() = gs[0] = 99
proc sNoArg(n: int) =
  if n < 0 or n > 5: return
  gs = @[n]
  wNoArg()
  if gs[0] == 99: symexTarget("na_new")
  else: symexTarget("na_old")
proc wByVal(a: seq[int]) =
  gs[0] = 99
proc sByVal(n: int) =
  if n < 0 or n > 5: return
  gs = @[n]
  wByVal(gs)
  if gs[0] == 99: symexTarget("bv_new")
  else: symexTarget("bv_old")
proc wOtherArg(a: int) = gs[0] = a
proc sOtherArg(n: int) =
  if n < 0 or n > 5: return
  gs = @[n]
  wOtherArg(99)
  if gs[0] == 99: symexTarget("oa_new")
  else: symexTarget("oa_old")
proc wVarArg(a: var seq[int]) = gs[0] = 99
proc sVarArg(n: int) =
  if n < 0 or n > 5: return
  gs = @[n]
  wVarArg(gs)
  if gs[0] == 99: symexTarget("va_new")
  else: symexTarget("va_old")
template q(fn: typed; l: static string) =
  block:
    let r = symexFind(fn, tLabel(l))
    var m: seq[string]
    for e in r.errors: m.add $e.kind
    echo l, " ", r.status, " ", m.join(",")
q(sNoArg, "na_new"); q(sNoArg, "na_old")
q(sByVal, "bv_new"); q(sByVal, "bv_old")
q(sOtherArg, "oa_new"); q(sOtherArg, "oa_old")
q(sVarArg, "va_new"); q(sVarArg, "va_old")
