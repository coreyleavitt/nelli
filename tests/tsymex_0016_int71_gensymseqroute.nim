## RFC-0016 INT-71 (red, registered nowhere): a `seq` local declared by a
## template inside the walked routine, in a module that imports `z3`,
## declines every read with `feGlobalRouteUnproved`.
##
## Found by INT-62: its six type x memory-op rows, defined in the test
## module (which imports `z3` for the fact tests), declined; moved to a
## module of their own (`tests/int62_rows.nim`) they are exact. The
## route scan opens `routeAnyValue` there: it reaches the `z3` library's
## module-level state (`currentZ3Ctx`, softlink's function pointers) and
## its owning types' `=destroy` hooks, one of which holds a `while` loop
## and "cannot be summarised", so a read of ANY variable ('a', 't',
## 'acc', ...) declines. The same body written inline (no template), or
## the template over a `string` instead of a `seq`, is exact.
##
## Closes when `gensymSeq` below is exact; then register this file in
## `nelli.nimble` and name it as the row's pin.
import std/unittest
import z3
import nelli
import nelli/symex
import ./s8cu_helpers

template seqRow(acc) =
  var x {.gensym.}: seq[int] = @[t, u]
  acc = acc + x[0]

proc gensymSeq(a, b: int8) =
  let t {.used.} = int(a)
  let u {.used.} = int(b)
  var acc = 0
  seqRow(acc)
  if acc == 2: symexTarget("hit")

proc inlineSeq(a, b: int8) =
  let t {.used.} = int(a)
  let u {.used.} = int(b)
  var acc = 0
  var x: seq[int] = @[t, u]
  acc = acc + x[0]
  if acc == 2: symexTarget("hit")

template strRow(acc) =
  let s {.gensym.} = "ab"
  acc = acc + s.len + t

proc gensymStr(a, b: int8) =
  let t {.used.} = int(a)
  var acc = 0
  strRow(acc)
  if acc == 5: symexTarget("hit")

suite "INT-71: a template's seq local beside an imported z3":
  template exact(fn: untyped) =
    let r = symexFind(fn, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " &
      ($r.errors)[0 ..< min(400, ($r.errors).len)]
    check r.status == sxSat
    check r.trusted

  test "control: the same body inline is exact":
    exact(inlineSeq)
  test "control: a template's string local is exact":
    exact(gensymStr)
  test "RED: a template's seq local is exact":
    exact(gensymSeq)
