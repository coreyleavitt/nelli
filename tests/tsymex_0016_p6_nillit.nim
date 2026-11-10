## RFC-0016 W3-z P6 -- `nil` assigned to a cstring/pointer/proc/ref slot beside
## a non-nil arm. The nil literal reached `coerceIntLit` with a composite
## prototype and faulted the walker; it must be modelled or declined.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/canonicalize
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("p6_pins_" & $getCurrentProcessId()))

type RefO = ref object
  v: int

var gc: cstring
var gp: pointer
var gr: RefO
var gf: proc (a: int): int {.nimcall.}
proc idp(a: int): int = a

proc pcsGlobal(c: bool) =
  gc = (if c: cstring"abc" else: nil)
  if gc != nil: symexTarget("hit")
proc pcsLocal(c: bool) =
  var g: cstring
  g = (if c: cstring"abc" else: nil)
  if g != nil: symexTarget("hit")
proc pcsCase(k: int) =
  var g: cstring
  g = (case k
       of 1: cstring"abc"
       else: nil)
  if g != nil: symexTarget("hit")
proc pptr(c: bool) =
  var q: pointer
  var x = 1
  q = (if c: addr x else: nil)
  if q != nil: symexTarget("hit")
proc pptrG(c: bool) =
  var x = 1
  gp = (if c: addr x else: nil)
  if gp != nil: symexTarget("hit")
proc pref(c: bool) =
  var r: RefO
  r = (if c: RefO(v: 1) else: nil)
  if r != nil: symexTarget("hit")
proc prefG(c: bool) =
  gr = (if c: RefO(v: 1) else: nil)
  if gr != nil: symexTarget("hit")
proc pproc(c: bool) =
  var f: proc (a: int): int {.nimcall.}
  f = (if c: idp else: nil)
  if f != nil: symexTarget("hit")
proc pprocG(c: bool) =
  gf = (if c: idp else: nil)
  if gf != nil: symexTarget("hit")

suite "RFC-0016 W3-z P6: nil in a composite slot":
  test "cstring and pointer nil arms decline by name (were a walker fault)":
    check parseInt(symexWalkerVersion) >= 316
    pinDecline(pcsGlobal, cellKey(axTypeClass, "cstring"), feUnsupportedExprKind)
    pinDecline(pcsLocal, cellKey(axTypeClass, "cstring"), feUnsupportedExprKind)
    pinDecline(pptr, cellKey(axTypeClass, "pointer"), feUnsupportedExprKind)
    pinDecline(pptrG, cellKey(axTypeClass, "pointer"), feUnsupportedExprKind)

  test "the case-expression form no longer faults in coerceIntLit":
    # A different fault remains here (P6b): the case-expression temp is read
    # unbound after the declined nil arm. It is recorded, not pinned.
    let r = symexFind(pcsCase, tLabel("hit"), pinSettingsConst)
    check r.status == sxUnknown
    for e in r.errors:
      check "coerceIntLit" notin e.msg

  test "a ref nil arm is modelled and agrees with native":
    discard pinExact(pref, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))
    discard pinExact(prefG, cellKey(axTypeClass, "ref"), domain = sampled([true, false]))

  test "a proc nil arm declines by name":
    pinDecline(pproc, cellKey(axTypeClass, "proc"), ceUnsupportedHof)
    pinDecline(pprocG, cellKey(axTypeClass, "proc"), ceUnsupportedHof)
