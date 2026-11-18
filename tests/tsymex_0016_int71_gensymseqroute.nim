## RFC-0016 INT-71: a `seq` local declared by a template inside the walked
## routine, in a module that imports `z3`, declined every read with
## `feGlobalRouteUnproved`.
##
## Found by INT-62: its six type x memory-op rows, defined in the test
## module (which imports `z3` for the fact tests), declined; moved to a
## module of their own (`tests/int62_rows.nim`) they were exact.
##
## Cause: the route scan (S8cs `routeScan`) read the type slot of the
## template's `var x {.gensym.}: seq[int]` as code. A template body is
## bound where the template is defined, so its `seq[int]` stays in the
## expanded routine as `[](seq, int)` over the open choice of every `[]` in
## scope there; the scan took each of those 29 routines (`z3`'s `[]`
## overloads among them) as a callee, walked into `z3`, and read its
## types' `=destroy` hooks, one of which holds a `while` loop and cannot be
## summarised, so a read of any variable declined (`routeAnyValue`). The
## same body inline writes `seq[int]` as a bracket over the type symbol,
## and a template's `let s = "ab"` has no type slot. A type slot runs
## nothing: the declared name's symbol carries the resolved type, and the
## scan routes that.
##
##   (1) the template's `seq` local, the same body inline, and a template's
##       `string` local are exact (K9 records);
##   (2) the route proof still sees a hook through the name: a template's
##       local of a type whose `=destroy` writes a global the walk reads
##       declines `feGlobalRouteUnproved`;
##   (3) the version floor.
import std/[unittest, strutils, sequtils]
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

suite "INT-71 (1): a template's seq local beside an imported z3 is exact":
  template exact(fn: untyped; key: CellKey) =
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    let r = pinExact(fn, key, tLabel("hit"), all)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " &
      ($r.errors)[0 ..< min(400, ($r.errors).len)]
    check r.status == sxSat
    check r.trusted

  test "control: the same body inline":
    exact(inlineSeq, cellKey(axTypeOp, "letCursor/seq"))
  test "control: a template's string local":
    exact(gensymStr, cellKey(axTypeOp, "letCursor/string"))
  test "a template's seq local":
    exact(gensymSeq, cellKey(axTypeOp, "letCursor/seq"))

# ---- (2) a hook the declared name's type has is still read --------------------

var int71Dropped = 0

type Int71Tracked = object
  v: int

proc `=destroy`(x: Int71Tracked) =
  int71Dropped = int71Dropped + 1

template trackedRow(acc) =
  var y {.gensym.}: Int71Tracked = Int71Tracked(v: t)
  acc = acc + y.v

proc gensymTracked(a: int8) =
  let t {.used.} = int(a)
  var acc = 0
  trackedRow(acc)
  if int71Dropped == 7: symexTarget("hit")
  if acc == 3: symexTarget("hit")

suite "INT-71 (2): the route proof still reads the declared type's hook":
  test "a template's local whose =destroy writes a read global declines":
    let r = symexFind(gensymTracked, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " &
      ($r.errors)[0 ..< min(400, ($r.errors).len)]
    check not r.trusted
    var routed = false
    for e in r.errors:
      if e.kind == feGlobalRouteUnproved and "int71Dropped" in e.msg:
        routed = true
    check routed

# ---- (3) the version floor ---------------------------------------------------

suite "INT-71 (3)":
  test "symexWalkerVersion >= 425":
    check parseInt(symexWalkerVersion) >= 425
