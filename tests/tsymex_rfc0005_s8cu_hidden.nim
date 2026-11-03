## RFC-0005 S8cu -- a push the source text does not show.
##
## A macro that builds the pragma (from a string or from nodes), and a pushing
## template or macro from another module, push where they are called, and the scan
## cannot expand them. Their `{.pop.}` is in the text, though, and matches no push
## the scan read: every call statement before it then reads as possibly pushing
## every check off, up to that pop. An `import` under a push in a module the walk
## never enters is found by the import graph from the routine's module and the
## project file. Each row ran unchecked natively and was a false `sxRaised`.
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets, macros, strutils]
import ./s8cu_fix_hidden_m1
import ./s8cu_fix_hidden_m2
import ./s8cu_fix_hidden_tpl
import nelli
import nelli/symex
import nelli/smt/check_options
import ./s8cu_helpers

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

suite "S8cu: a push the text does not show":

  test "a macro building the pragma from a string":
    check native(strField(4)) == "hit"
    declines(strField, feCheckOption)
    check native(strRange(300)) == "hit"
    declines(strRange, feCheckOption)
    check native(strObj(4)) == "hit"
    declines(strObj, feCheckOption)

  test "a macro building it from nodes":
    check native(astField(4)) == "hit"
    declines(astField, feCheckOption)

  test "a pushing template or macro from another module":
    check native(tplField(4)) == "hit"
    declines(tplField, feCheckOption)
    check native(tplRange(300)) == "hit"
    declines(tplRange, feCheckOption)
    check native(macObj(4)) == "hit"
    declines(macObj, feCheckOption)

  test "an import under a push in a module the walk never enters":
    check native(impField(4)) == "hit"
    declines(impField, feCheckOption)
    check native(impRange(300)) == "hit"
    declines(impRange, feCheckOption)
    check native(impObj(4)) == "hit"
    declines(impObj, feCheckOption)

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
