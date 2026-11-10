## RFC-0016 W3-z P14 -- (a) `RefO(nil)`: a `Conv` of a nil literal builds the
## TARGET type's nil value (the literal's own type is `nil`, so the type of
## the conversion, not of its operand, picks the representation). (b) `block:`
## used as an expression (`nnkBlockExpr`) lowers like `nnkStmtListExpr` inside
## its own scope. Each is pinned exactly against native.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/canonicalize
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("p14_pins_" & $getCurrentProcessId()))

type
  RefO = ref object
    v: int
  Ob = object
    v: int
  PI = ptr Ob   ## a ptr to a scalar is no modelled local (it declines, sound)

proc c1(c: bool) =
  let r = RefO(nil)
  if r.isNil and c: symexTarget("hit")
proc c1b(c: bool) =
  let r = (if c: RefO(nil) else: RefO(v: 1))
  if r.isNil: symexTarget("hit")
proc c2(c: bool) =
  let p = PI(nil)
  if p.isNil and c: symexTarget("hit")
proc c2b(c: bool) =
  let p = PI(nil)
  if not p.isNil and c: symexTarget("hit")

proc e1(a: int) =
  let x = (block: (var t = a; t += 1; t))
  if x == 5: symexTarget("hit")
proc e2(a: int) =
  var t = 100
  let x = (block: (var t = a; t += 1; t))
  if x == 5 and t == 100: symexTarget("hit")
proc e3(a: int) =
  let x = block foo:
    var t = a
    if t > 3: t = 3
    t * 2
  if x == 6: symexTarget("hit")
proc e4(a: int) =
  var n = 0
  block foo:
    if a > 3:
      n = 1
      break foo
    n = 2
  let x = (block: (n += 10; n))
  if x == 11: symexTarget("hit")

suite "RFC-0016 W3-z P14: Conv of nil, and block expressions":
  test "RefO(nil) agrees with native":
    discard pinExact(c1, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
  test "RefO(nil) in an if-expression agrees with native":
    discard pinExact(c1b, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
  test "a ptr conversion of nil agrees with native":
    discard pinExact(c2, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "a ptr conversion of nil, negated test, agrees with native":
    discard pinExact(c2b, cellKey(axTypeClass, "ptr"), domain = sampled([true, false]))
  test "a block expression agrees with native":
    discard pinExact(e1, cellKey(axConstruct, "blockExpr/tail"), domain = sampled([3, 4, 5]))
    discard pinExact(e2, cellKey(axConstruct, "blockExpr/scoped"), domain = sampled([3, 4, 5]))
    discard pinExact(e3, cellKey(axConstruct, "blockExpr/labelled"), domain = sampled([1, 2, 3, 4, 9]))
    discard pinExact(e4, cellKey(axConstruct, "blockExpr/afterBreak"), domain = sampled([1, 4, 9]))
