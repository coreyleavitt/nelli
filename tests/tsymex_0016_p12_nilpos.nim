## RFC-0016 W3-z P12 -- audit of `isNil` on a NimNode. In the macro API a
## `nnkNilLit` node taken out of a tree answers `isNil` true, like an absent
## reference, so a site that means "absent" and meets a `nil` literal is wrong
## (P6b: `armYieldsValue`). The audit found every other site's receiver is a
## symbol, a type, an implementation, a lvalue root or a tree scanner whose
## nil-literal outcome equals its absent outcome; this file pins that a
## `nil` literal in each expression position agrees with native.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/canonicalize
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("p12_pins_" & $getCurrentProcessId()))

type
  RefO = ref object
    v: int
  N = ref object
    next: N
    v: int
var gr: RefO

proc takeNil(r: RefO): bool = r == nil

proc dp(r: RefO = nil): bool = r == nil
proc mk(c: bool): RefO = (if c: RefO(v: 1) else: nil)
proc mk2(c: bool): RefO =
  if c: return nil
  RefO(v: 1)
proc mk3(c: bool): RefO =
  result = RefO(v: 1)
  if c: result = nil
proc clr(r: var RefO) = r = nil

proc a1(c: bool) =
  if takeNil(nil) and c: symexTarget("hit")

proc a1c(c: bool) =
  if not takeNil(nil) and c: symexTarget("hit")
proc a2(c: bool) =
  if mk(c) == nil: symexTarget("hit")
proc a3(c: bool) =
  if mk2(c) == nil: symexTarget("hit")
proc a3b(c: bool) =
  if mk3(c) == nil: symexTarget("hit")
proc a4(c: bool) =
  let n = N(v: 1, next: nil)
  if n.next == nil and c: symexTarget("hit")
proc a4b(c: bool) =
  let n = N(v: 1, next: (if c: N(v: 2) else: nil))
  if n.next == nil: symexTarget("hit")
proc a5(c: bool) =
  if dp() and c: symexTarget("hit")
proc a6(c: bool) =
  var r = RefO(v: 1)
  if c: r = nil
  if r == nil: symexTarget("hit")
proc a7(c: bool) =
  let t: (bool, RefO) = (c, nil)
  if t[0] and t[1] == nil: symexTarget("hit")

proc a9(c: bool) =
  var r = RefO(v: 1)
  if c: clr(r)
  if r == nil: symexTarget("hit")

proc a11(c: bool) =
  var r: RefO = nil
  if c: r = RefO(v: 1)
  if r == nil: symexTarget("hit")
proc a12(c: bool) =
  gr = nil
  if c and gr == nil: symexTarget("hit")
proc a13(c: bool) =
  let r = (if c: nil else: RefO(v: 1))
  if r == nil: symexTarget("hit")
proc a14(k: int) =
  let r = (case k
           of 1: RefO(v: 1)
           of 2: nil
           else: RefO(v: 2))
  if r == nil: symexTarget("hit")
proc a15(c: bool) =
  var r = RefO(v: 1)
  r = (if c: nil else: r)
  if r == nil: symexTarget("hit")
proc a16(c: bool) =
  let n = N(v: 1)
  n.next = (if c: nil else: N(v: 2))
  if n.next == nil: symexTarget("hit")



proc b2(c: bool) =
  let s = @[RefO(v: 1), nil]
  if c and s[1] == nil: symexTarget("hit")
proc b3(c: bool) =
  var s = @[RefO(v: 1), RefO(v: 2)]
  s[0] = nil
  if c and s[0] == nil: symexTarget("hit")
proc b4(c: bool) =
  let s = [RefO(v: 1), nil]
  if c and s[1] == nil: symexTarget("hit")
proc b5(c: bool) =
  var s: seq[RefO]
  s.add nil
  if c and s[0] == nil: symexTarget("hit")

suite "RFC-0016 W3-z P12: a nil literal in an expression position":
  test "the nil literal agrees with native in every position":
    discard pinExact(a1, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a1c, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a2, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a3, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a3b, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a4, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a4b, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a5, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a6, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a7, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a9, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a11, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a12, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a13, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a14, cellKey(axTypeClass, "ref"), domain = sampled([0, 1, 2, 3]))
    discard pinExact(a15, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(a16, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(b2, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(b3, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(b4, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(b5, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
