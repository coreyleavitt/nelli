## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 5: a
## seq argument of a proc value or a closure.
##
## A proc value's application is an uninterpreted function of its
## arguments (ADR-0009 D4) alongside the body's descent; its domain is the
## flattened sorts of the arguments (`paramSorts`, `sortOfTuple`). A seq,
## a table or a set has no single sort, and the call declined
## (`seUnsupportedCompoundSortLeaf`), a `var openArray` through a proc value
## among them.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (5) a seq, table or set contributes the sort of each of its leaves (its
##       data arrays and its length), as a nested tuple does.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.severity == sevHint

template declines(fn: typed, lbl, why: string): untyped =
  ## A shape the walk does not model: `sxUnknown`, with the decline named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.severity == sevError and why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 3, 4, 5, 7]

proc sumFirst(s: seq[int], k: int): int = s[0] + s.len + k

proc sutSeqArg(k: int) =
  if k < -100 or k > 100: return
  let f = sumFirst
  let r = f(@[k, 1], k)
  if r == 2 * k + 2 and k == 3: symexTarget("pq")
  if r != 2 * k + 2: symexTarget("pq_dead")

proc addTo(s: var seq[int], k: int) = s.add k

proc sutVarSeqArg(k: int) =
  var s = @[1]
  let f = addTo
  f(s, k)
  if s.len == 2 and s[1] == k and k == 3: symexTarget("ps")
  if s.len != 2 or s[1] != k: symexTarget("ps_dead")

proc setFirst(a: var openArray[int], k: int) =
  a[0] = k

proc sutVarOpenArray(k: int) =
  var a = [0, 0, 0]
  let f = setFirst
  f(a, k)
  if a[0] == k and k == 3: symexTarget("pw")
  if a[0] != k: symexTarget("pw_dead")

proc sutClosureSeq(k: int) =
  if k < -100 or k > 100: return
  var base = 2
  let g = proc (s: seq[int]): int = s.len + base
  base = k
  let r = g(@[1, 2, 3])
  if r == k + 3 and k == 3: symexTarget("pc")
  if r != k + 3: symexTarget("pc_dead")

suite "S8ca (5): a seq argument of a proc value or a closure":

  test "nim":
    let h = nativeHits(sutSeqArg, ks) + nativeHits(sutVarSeqArg, ks) +
            nativeHits(sutVarOpenArray, ks) + nativeHits(sutClosureSeq, ks)
    for l in ["pq", "ps", "pw", "pc"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a proc value":
    clean(sutSeqArg, "pq", sxSat)
    clean(sutSeqArg, "pq_dead", sxUnsat)
    clean(sutVarSeqArg, "ps", sxSat)
    clean(sutVarSeqArg, "ps_dead", sxUnsat)
    clean(sutVarOpenArray, "pw", sxSat)
    clean(sutVarOpenArray, "pw_dead", sxUnsat)

  test "a closure":
    clean(sutClosureSeq, "pc", sxSat)
    clean(sutClosureSeq, "pc_dead", sxUnsat)

suite "S8ca: walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
