## RFC-0005 S8cu -- a push the source text does not show.
##
## A macro that builds the pragma (from a string or from nodes), and a pushing
## template or macro from another module, push where they are called, and the scan
## cannot expand them. Their `{.pop.}` is in the text, though, and matches no push
## the scan read: every call statement before it then reads as possibly pushing
## every check off, up to that pop. Each row ran unchecked natively and was a
## false `sxRaised`; the macro-built and imported pushes still decline.
##
## An `import` under a push in a module the walk never enters (`m1` imports
## `m2` under a push of three checks off) was found by the import graph and
## declined. RFC-0016 int6 (walker 477, `replayCompileOrder`) replays Nim's
## compile order: `system` first, then this file's imports depth first, the
## first import of a module compiling it. Nothing before `m1` imports `m2`, and
## no module-level call precedes the import, so `m2` is first compiled under
## `m1`'s push: its routines are walked with those checks off and decide
## exactly, judged natively (their wrong-branch write and out-of-range
## conversion reach the label); the down-conversion of a base instance is
## undefined unchecked and halts as `ubInvalidObjConversion`.
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets, macros, strutils]
## nelli comes first: `buildprofile`'s `buildSemantics` constant is compiled
## where it is first imported, so importing it through a fixture's push of
## check options would record those checks as off (RFC-0016 W1-d2, import
## order; see `buildprofile.nim`).
import nelli
import nelli/symex
import nelli/smt/check_options
import ./s8cu_helpers
import ./s8cu_fix_hidden_m1
import ./s8cu_fix_hidden_m2
import ./s8cu_fix_hidden_tpl

const declKey = cellKey(faGeneric, "s8cu_hidden")

type K = enum kA, kB
type P = object
  case k: K
  of kA: x: int
  of kB: y: int
type Par = ref object of RootObj
  a: int
type Ch = ref object of Par
  b: int

macro pushOffStr(): untyped =
  parseStmt("{.push " & "fieldChecks: off, rangeChecks: off, objChecks: off.}")
macro pushOffAst(): untyped =
  result = newNimNode(nnkPragma)
  result.add ident"push"
  for o in ["fieldChecks", "rangeChecks", "objChecks"]:
    result.add newColonExpr(ident(o), ident"off")

pushOffStr()
proc strField(v: int) =
  var q = P(k: kA, x: v)
  q.y = v
  symexTarget("hit")
proc strRange(v: int) =
  if v == 300:
    let w = int8(v)
    if w == 44'i8: symexTarget("hit")
proc strObj(v: int) =
  let p = Par(a: v)
  let c = Ch(p)
  if c.a == v: symexTarget("hit")
{.pop.}

pushOffAst()
proc astField(v: int) =
  var q = P(k: kA, x: v)
  q.y = v
  symexTarget("hit")
{.pop.}

pushOffTpl()
proc tplField(v: int) =
  var q = P(k: kA, x: v)
  q.y = v
  symexTarget("hit")
proc tplRange(v: int) =
  if v == 300:
    let w = int8(v)
    if w == 44'i8: symexTarget("hit")
{.pop.}

pushOffMacro()
proc macObj(v: int) =
  let p = Par(a: v)
  let c = Ch(p)
  if c.a == v: symexTarget("hit")
{.pop.}

# Controls, after every pop: checked.
proc ctlField(v: int) =
  var q = P(k: kA, x: v)
  q.y = v
  symexTarget("hit")
proc ctlRange(v: int) =
  if v == 300:
    let w = int8(v)
    if w == 44'i8: symexTarget("hit")
proc ctlObj(v: int) =
  let p = Par(a: v)
  let c = Ch(p)
  if c.a == v: symexTarget("hit")

const self = currentSourcePath()
proc devAt(text: string; line: int): set[CheckOption] {.compileTime.} =
  deviation(stateAt(scanModuleText(self, text), self, line, 0))
const callThenPop = "foo()\nproc a() = discard\n{.pop.}\nproc b() = discard\n"
const callA = devAt(callThenPop, 2)
const callB = devAt(callThenPop, 4)
const bareHiddenPop =
  scanModuleText(self, "proc a() = discard\n{.pop.}\n").unknownReason

template walkedOff(fn: untyped) =
  ## A trusted `sxSat`, its witness replayed natively (`pinExact`).
  block:
    let r = pinExact(fn, declKey)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted

suite "S8cu: a push the text does not show":

  test "a macro building the pragma from a string":
    check native(strField(4)) == "hit"
    pinDecline(strField, declKey, feCheckOption)
    check native(strRange(300)) == "hit"
    pinDecline(strRange, declKey, feCheckOption)
    check native(strObj(4)) == "hit"
    pinDecline(strObj, declKey, feCheckOption)

  test "a macro building it from nodes":
    check native(astField(4)) == "hit"
    pinDecline(astField, declKey, feCheckOption)

  test "a pushing template or macro from another module":
    check native(tplField(4)) == "hit"
    pinDecline(tplField, declKey, feCheckOption)
    check native(tplRange(300)) == "hit"
    pinDecline(tplRange, declKey, feCheckOption)
    check native(macObj(4)) == "hit"
    pinDecline(macObj, declKey, feCheckOption)

  test "an import under a push in a module the walk never enters: walked off":
    # RFC-0016 int6 (walker 477): the compile-order replay finds `m2` first
    # compiled under `m1`'s push, so it is walked with the three checks off
    # instead of declining with `feCheckOption`. Native agrees: each reaches
    # the label, and the walker's witness is replayed natively.
    check native(impField(4)) == "hit"
    walkedOff(impField)
    check native(impRange(300)) == "hit"
    walkedOff(impRange)
    # The down-conversion of an `LPar` to an `LCh` with `objChecks` off is no
    # `ObjectConversionDefect` but type confusion, undefined in C: the walk
    # halts there as `ubInvalidObjConversion` (as `tsymex_0016_objoff`),
    # never a false `sxRaised`. Native reads the base field and reaches the
    # label.
    check native(impObj(4)) == "hit"
    pinDecline(impObj, declKey, ubInvalidObjConversion,
               excluding = {feCheckOption})

  test "after the pop the checks are back (control)":
    check native(ctlField(4)) == "FieldDefect"
    decides(ctlField, sxRaised)
    check native(ctlRange(300)) == "RangeDefect"
    decides(ctlRange, sxRaised)
    check native(ctlObj(4)) == "ObjectConversionDefect"
    decides(ctlObj, sxRaised)

  test "the scan: a call before an unmatched pop reads as pushing off":
    check callA == {coField, coOverflow, coRange, coBound, coObj}
    check callB == {}

  test "the scan: an unmatched pop with no call before it is unknown":
    check "pops a push the scan cannot see" in bareHiddenPop
