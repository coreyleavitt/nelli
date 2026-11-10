## RFC-0016 W3-z P16 -- a local `ptr int` / `ptr char` / `ptr float`: nil-ness.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/canonicalize
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("p16_pins_" & $getCurrentProcessId()))

proc a1(c: int) =
  var x = 5
  let p = addr x
  p[] = c
  if x == 7: symexTarget("hit")
proc a2(c: bool) =
  let p: ptr int = nil
  if p.isNil and c: symexTarget("hit")
proc a3(c: bool) =
  let p: ptr int = nil
  if p == nil and c: symexTarget("hit")
proc a4(c: bool) =
  let p = cast[ptr int](0)
  if p.isNil and c: symexTarget("hit")
proc a5(p: ptr int) =
  if p == nil: symexTarget("hit")
proc a4c(c: bool) =
  let p = cast[ptr char](0)
  if p == nil and c: symexTarget("hit")
proc a4d(c: bool) =
  let p = cast[ptr float](0)
  if p != nil and c: symexTarget("hit")
proc a6(c: bool) =
  var x = 5
  let p = addr x
  if p != nil and c: symexTarget("hit")
proc a7(c: bool) =
  var x = 5
  let p = addr x
  if p.isNil and c: symexTarget("hit")
proc a8(c: bool) =
  let p = (ptr int)(nil)
  if p.isNil and c: symexTarget("hit")
proc a9(c: bool) =
  let p = (ptr char)(nil)
  if p != nil and c: symexTarget("hit")
proc a10(c: bool) =
  let p = (ptr float)(nil)
  if p == nil and c: symexTarget("hit")

suite "P16":
  test "addr write": discard pinExact(a1, cellKey(axTypeClass, "ptr"), domain = sampled([6, 7, 8]))
  test "nil isNil": discard pinExact(a2, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "nil ==": discard pinExact(a3, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "cast 0": discard pinExact(a4, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "cast 0 char": discard pinExact(a4c, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "cast 0 float !=": discard pinExact(a4d, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "addr !=": discard pinExact(a6, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "addr isNil": discard pinExact(a7, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "conv int": discard pinExact(a8, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "conv char !=": discard pinExact(a9, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "conv float": discard pinExact(a10, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))

proc b1(c: bool) =
  var p: ptr int
  if p.isNil and c: symexTarget("hit")
proc b2(c: bool) =
  var x = 5
  var p: ptr int = nil
  if c: p = addr x
  if p.isNil: symexTarget("hit")
proc b3(c: bool) =
  var x = 'a'
  let p = addr x
  p[] = 'b'
  if x == 'b' and not p.isNil and c: symexTarget("hit")
proc b4(c: bool) =
  var x = 1.5
  var p: ptr float
  if c: p = addr x
  if p == nil: symexTarget("hit")
proc mkp(x: ptr int, c: bool): ptr int = (if c: x else: nil)
proc b5(c: bool) =
  var x = 5
  let p = mkp(addr x, c)
  if p.isNil: symexTarget("hit")
proc b6(c: bool) =
  let p = cast[ptr int](nil)
  if p.isNil and c: symexTarget("hit")
type HP = object
  p: ptr int
proc b7(c: bool) =
  var x = 5
  var h = HP(p: nil)
  if c: h.p = addr x
  if h.p.isNil: symexTarget("hit")
proc b8(c: bool) =
  var x = 5
  var h: HP
  if c: h.p = addr x
  if h.p.isNil: symexTarget("hit")
proc b9(c: bool) =
  var x = 5
  var y = 6
  let p = addr x
  let q = addr y
  if p == q and c: symexTarget("hit")
proc b10(c: bool) =
  var x = 5
  let p = addr x
  let q = p
  if p == q and c: symexTarget("hit")

suite "P16 more":
  test "default": discard pinExact(b1, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "cond addr": discard pinExact(b2, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "char": discard pinExact(b3, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "float": discard pinExact(b4, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "callee": discard pinExact(b5, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "cast nil": discard pinExact(b6, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "field nil": discard pinExact(b7, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "field default": discard pinExact(b8, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "distinct addr eq": discard pinExact(b9, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "alias eq": discard pinExact(b10, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))

proc pp(p: ptr int) =
  if p == nil: symexTarget("hit")
proc pp2(p: ptr int) =
  if p.isNil: symexTarget("hit")
proc pp3(p: ptr int) =
  if p != nil: symexTarget("hit")
proc pp4(p: ptr char) =
  if p.isNil: symexTarget("hit")
proc pp5(p: ptr float) =
  if p != nil: symexTarget("hit")
proc pq(p: ptr int) =
  if p == nil and p != nil: symexTarget("hit")
suite "P16 param":
  test "param probes":
    check symexFind(pp, tLabel("hit")).status == sxSat
    check symexFind(pp2, tLabel("hit")).status == sxSat
    check symexFind(pp3, tLabel("hit")).status == sxSat
    check symexFind(pp4, tLabel("hit")).status == sxSat
    check symexFind(pp5, tLabel("hit")).status == sxSat
  test "a nil-guarded param is unsat on the nil side":
    check symexFind(pq, tLabel("hit")).status == sxUnsat
  test "walker version floor":
    check symexWalkerVersion.parseInt >= 319

proc nz(k: int) =
  let p = cast[ptr int](8)
  if p.isNil: symexTarget("hit")
suite "P16 nonzero cast":
  test "a nonzero address stays declined (no address model)":
    let r = symexFind(nz, tLabel("hit"))
    check r.status == sxUnknown
