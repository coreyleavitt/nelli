## RFC-0016 ADM-IR (section 8.1, "Admission is a proof the IR demands").
##
## `Admit`'s fields are private, so only `admission.nim` can make one. The rule
## is that an IR constructor of a keyed-axis node takes the axis's `Admit`, so a
## parser arm that skips the table does not type-check. This file is that
## rule's test, one block per axis whose node has a constructor:
##
##   * type x memory-op (`typeop:fieldDefault/<kind>`): `mkZeroValue`.
##
## The compile-time half is `compiles(...)`: the call without a proof must not
## compile and the call with one must. The census half counts raw
## `IRExpr(kind: iekZeroValue` constructions outside `types.nim` (the IR
## module), allowlist zero. The behavioural half runs the real parser entry
## (`symexFind`): a declined row still declines, and an admitted one still
## decides as before.
import std/[unittest, strutils, os, tables, math, options]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/types
import nelli/smt/typeaxes
import nelli/smt/definedness
import nelli/smt/magic_rows
import nelli/smt/stdlib_rows
import nelli/smt/pragmaaxes
import nelli/smt/canonicalize

suite "ADM-IR: the type x memory-op axis (mkZeroValue)":
  let tbl = tTable(tString(), tInt(64, true))
  test "no proof, no node":
    check not compiles(mkZeroValue(tbl))
  test "a wrong-axis proof is not a proof":
    check not compiles(mkZeroValue(admitTypeClass(ntyInt, tcClassify), tbl))
  test "with the fieldDefault proof it builds":
    check compiles(mkZeroValue(admitTypeOp(itTable, moFieldDefault, toZeroValue), tbl))
    let a = admitTypeOp(itTable, moFieldDefault, toZeroValue)
    check a.admitted
    let e = mkZeroValue(a, tbl)
    check e.kind == iekZeroValue
    check e.zvTy == tbl
  test "a declined proof does not reach the constructor":
    let a = admitTypeOp(itUninterp, moFieldDefault, toZeroValue)
    check not a.admitted
    expect AssertionDefect:
      discard mkZeroValue(a, tTable(tString(), tInt(64, true)))
  test "a proof of another operation does not reach the constructor":
    let a = admitTypeOp(itTable, moLetCursor)
    expect AssertionDefect:
      discard mkZeroValue(a, tbl)

proc rawCount(): int =
  ## Raw constructions of the zero-value node outside the IR module.
  let dir = currentSourcePath().parentDir() / ".." / "src" / "nelli"
  let tok = "IRExpr(kind: " & "iekZeroValue"
  for f in walkDirRec(dir):
    if not f.endsWith(".nim") or f.endsWith("smt" / "types.nim"): continue
    for line in readFile(f).splitLines:
      let i = line.find('#')
      if tok in (if i >= 0: line[0 ..< i] else: line): inc result

suite "ADM-IR: no raw construction outside the IR module":
  test "iekZeroValue is built only by mkZeroValue":
    check rawCount() == 0

type Tab = Table[int, int]
proc zeroTable(k: int) =
  var t: Tab
  if t.len == 0: symexTarget("hit")
proc zeroTableNonEmpty(k: int) =
  var t: Tab
  if t.len > 0: symexTarget("hit")
proc zeroSeq(k: int) =
  var s: seq[int]
  if s.len == 0: symexTarget("hit")

suite "ADM-IR: verdicts through the real parser are unchanged":
  test "an admitted zero-value row still decides":
    let a = symexFind(zeroTable, tLabel("hit"))
    check a.status == sxSat
    let b = symexFind(zeroTableNonEmpty, tLabel("hit"))
    check b.status == sxUnsat
    check symexFind(zeroSeq, tLabel("hit")).status == sxSat

proc zeroCstring(k: int) =
  var f: cstring
  if k == 1: symexTarget("hit")

suite "ADM-IR: a declined fieldDefault row still declines through the parser":
  test "an uninterp zero is not built; the walk reports the decline":
    check not admitTypeOp(itUninterp, moFieldDefault, toZeroValue).admitted
    let r = symexFind(zeroCstring, tLabel("hit"))
    check r.status == sxUnknown
    var seen = false
    for e in r.errors:
      if e.kind == feUnsupportedParamType and "no zero value" in e.msg:
        seen = true
    check seen

# ---------------------------------------------------------------------------
# definedness and the magic defect scan: mkOpaqueCall
# ---------------------------------------------------------------------------

suite "ADM-IR: the walker version":
  test "the float parse-time decline is at the 303 floor":
    check parseInt(symexWalkerVersion) >= 303

suite "ADM-IR: the opaque-call scan (mkOpaqueCall)":
  test "no scan, no node; raw sets are not a scan":
    check not compiles(mkOpaqueCall("f", "", @[], tBool()))
    check not compiles(mkOpaqueCall("f", "", @[], tBool(), {UbKind(ubSignedOverflow)}))
    check not compiles(mkOpaqueCall("f", "", @[], tBool(), @["IndexDefect"]))
  test "a wrong-axis proof is not a scan":
    check not compiles(mkOpaqueCall("f", "", @[], tBool(),
                                    admitMagic("AddI", msDefOverflow)))
    var scan: OpaqueScan
    check not compiles(scan.noteUndefined(admitMagic("AddI", msDefOverflow), dpChecked))
    check not compiles(scan.noteMagicDefect(
      admitDefined(aoCall, ocOpaqueBody, dsOpaque), "OverflowDefect"))
  test "admitted rows fill the scan and the node reads it":
    var scan: OpaqueScan
    scan.noteUndefined(admitDefined(aoCall, ocOpaqueBody, dsOpaque), dpChecked)
    scan.noteMagicDefect(admitMagic("AddI", msDefOverflow), "OverflowDefect")
    scan.noteDefect("IndexDefect")
    let st = mkOpaqueCall("f", "", @[], tBool(), scan)
    check st.opaqueUndefined == {UbKind(ubTailUnverified)}
    check st.opaqueDefects == @["OverflowDefect", "IndexDefect"]
    check mkOpaqueCall("f", "", @[], tBool(), unscanned).opaqueDefects.len == 0
  test "a declined proof asserts":
    var scan: OpaqueScan
    expect AssertionDefect:
      scan.noteUndefined(admitDefined(aoMod, ocPointer, dsArith), dpChecked)
    expect AssertionDefect:
      scan.noteMagicDefect(admitMagic("Spawn", msDefOverflow), "OverflowDefect")

proc cAbs(x: cint): cint {.importc: "abs", header: "<stdlib.h>".}
proc sutTailForeign(x: int32) =
  if x == 5: symexTarget("hit")
  discard cAbs(cint(x))

proc gAdd(a: int) {.symexOpaque.} =
  discard a + 1
proc sutAdd(v: int) =
  symexAssume(v == high(int))
  gAdd(v)

suite "ADM-IR: the scan's verdicts through the real parser are unchanged":
  test "a foreign body after the label is untrusted, carrying ubTailUnverified":
    let r = symexFind(sutTailForeign, tLabel("hit"))
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubTailUnverified) in r.soundness.undefinedKinds
  test "the magic defect scan still forks OverflowDefect":
    check symexFind(sutAdd, tRaisedExn("OverflowDefect")).status == sxRaised

# ---------------------------------------------------------------------------
# stdlib body, float calls: mkMathCall
# ---------------------------------------------------------------------------

suite "ADM-IR: the stdlib-body axis, float calls (mkMathCall)":
  test "no proof, no node; a wrong-axis proof is not a proof":
    check not compiles(mkMathCall("sqrt", @[mkIntLit(1)]))
    check not compiles(mkMathCall(admitMagic("AddI", msArm), "sqrt", @[mkIntLit(1)]))
    check not compiles(mkMathCall(admitPragma(ppRoutine, "inline", psRoutineDecl),
                                  "sqrt", @[mkIntLit(1)]))
  test "an admitted row builds":
    let e = mkMathCall(admitFloatCall("sqrt", 1), "sqrt", @[mkIntLit(1)])
    check e.kind == iekMathCall
    check e.mathOp == "sqrt"
    for op in ["abs", "min", "max", "isInf", "isFinite", "isNormal",
               "toFloat32", "toFloat64"]:
      check admitFloatCall(op, 1).admitted
  test "a declined or absent row, or another op's row, asserts":
    check not admitFloatCall("sin", 1).admitted
    check not admitFloatCall("nextafter", 2).admitted
    check not admitFloatCall("noSuchMath", 1).admitted
    check admitFloatCall("noSuchMath", 1).decline[0] == some(feUnsupportedOpAborted)
    expect AssertionDefect:
      discard mkMathCall(admitFloatCall("sin", 1), "sin", @[mkIntLit(1)])
    expect AssertionDefect:
      discard mkMathCall(admitFloatCall("sqrt", 1), "floor", @[mkIntLit(1)])

proc fSin(a: float) =
  if sin(a) == 0.0: symexTarget("hit")
proc fAbs(a: float) =
  if abs(a) == 2.5 and a == -2.5: symexTarget("hit")
proc fMin(a, b: float) =
  if min(a, b) == 1.0 and a == 1.0 and b == 2.0: symexTarget("hit")

proc declinedWith(r: SymexResult; cell: string): bool =
  for e in r.errors:
    if e.kind == feUnsupportedOpAborted and cell in e.msg: return true

suite "ADM-IR: a declined float row still declines through the parser":
  test "sin is a declined row, naming its cell":
    let r = symexFind(fSin, tLabel("hit"))
    check r.status == sxUnknown
    check r.declinedWith("stdlib:math.sin")
  test "modelled names still decide":
    check symexFind(fAbs, tLabel("hit")).status == sxSat
    check symexFind(fMin, tLabel("hit")).status == sxSat

# ---------------------------------------------------------------------------
# pragma / stdlib arithmetic stamp: mkArithBlock
# ---------------------------------------------------------------------------

suite "ADM-IR: the arithmetic stamp (mkArithBlock)":
  test "no proof, no node; a wrong-axis proof is not a proof":
    check not compiles(mkArithBlock(asBuild, @[mkBreak()]))
    check not compiles(mkArithBlock(arithFromPragma(
      admitStdlibBody("math.floorDiv", ssBodyWalk)), @[mkBreak()]))
    check not compiles(mkArithBlock(arithFromStdlib(
      admitPragma(ppRoutine, "overflowChecks", psRoutineDecl)), @[mkBreak()]))
    check not compiles(arithFromStdlib(admitMagic("AddI", msArm)))
  test "each axis's proof stamps its scope":
    let chk = arithFromPragma(admitPragma(ppRoutine, "overflowChecks", psRoutineDecl))
    check mkArithBlock(chk, @[mkBreak()]).blkArith == asChecked
    let unc = arithFromStdlib(admitStdlibBody("math.floorDiv", ssBodyWalk))
    check mkArithBlock(unc, @[mkBreak()]).blkArith == asUnchecked
    check replayArith(asBuild).arithScope == asBuild
  test "a declined or beside-the-point proof asserts":
    expect AssertionDefect:
      discard arithFromPragma(admitPragma(ppLocal, "cursor", psLocalDecl))
    expect AssertionDefect:   # admitted, but not the overflowChecks row
      discard arithFromPragma(admitPragma(ppRoutine, "inline", psRoutineDecl))
    expect AssertionDefect:   # declined row
      discard arithFromStdlib(admitStdlibBody("math.divmod", ssBodyWalk))
    expect AssertionDefect:   # lowered by name (PRC-09), not walked by body
      discard arithFromStdlib(admitStdlibBody("math.ceilDiv", ssBodyWalk))
    expect AssertionDefect:   # admitted, but its body trips no overflow check
      discard arithFromStdlib(admitStdlibBody("math.sgn", ssBodyWalk))

proc sNextPow2Min(a: int) =
  if nextPowerOfTwo(a) == 1 and a == low(int): symexTarget("hit")
proc sUserDecMin(a: int) =
  if a - 1 == 0 and a == low(int): symexTarget("hit")

suite "ADM-IR: the stdlib stamp's verdicts through the parser are unchanged":
  test "user `x - 1` raises; the stdlib body (asUnchecked) is undefined, not a raise":
    check symexFind(sUserDecMin, tLabel("hit")).status == sxRaised
    check symexFind(sNextPow2Min, tLabel("hit")).status != sxRaised

# ---------------------------------------------------------------------------
# magic: lowerMagic and the arm census; PCRE is enforced at its runtime consumer
# ---------------------------------------------------------------------------

suite "ADM-IR: the magic axis (lowerMagic)":
  test "an admitted proof runs the arm; a declined one does not":
    var ran = false
    lowerMagic(admitMagic("AddI", msArm)):
      ran = true
    check ran
    expect AssertionDefect:
      lowerMagic(admitMagic("Spawn", msArm)):
        ran = false
    check ran
    lowerMagic(admitStdlibBody("system.+%", ssInfix)):
      ran = false
    check not ran
  test "another axis's proof is not a magic's":
    check not compiles(lowerMagic(admitTypeClass(ntyInt, tcClassify), 0))
    check not compiles(lowerMagic(admitPragma(ppRoutine, "inline", psRoutineDecl), 0))

suite "ADM-IR: expression-form magic reads (whenMagic)":
  test "a name with no row does not compile; a row's name does":
    check not compiles(magicIs("x", "NoSuchMagic"))
    check compiles(magicIs("x", "IsNil"))
    check not compiles(whenMagic("x", "NoSuchMagic", (let z = 1)))
  test "the body runs for its magic, under the row's proof":
    var ran = 0
    whenMagic("IsNil", "IsNil"): inc ran
    whenMagic("Move", "IsNil"): inc ran
    check ran == 1
    whenMagicIn("IntToStr", @["BoolToStr", "IntToStr"]): inc ran
    whenMagicIn("Move", @["BoolToStr", "IntToStr"]): inc ran
    check ran == 2
  test "a magic the table declines does not run its body":
    var ran = false
    expect AssertionDefect:
      whenMagic("ProcCall", "ProcCall"): ran = true
    check not ran
  test "declinedMagic runs only under a declined proof":
    var ran = false
    declinedMagic(admitMagic("ProcCall", msProcRegister)): ran = true
    check ran
    expect AssertionDefect:
      declinedMagic(admitMagic("IsNil", msArm)): ran = false
    check ran
  test "the to-string magics have rows, admitted where the walker models them":
    for k in ["IntToStr", "Int64ToStr", "BoolToStr", "EnumToStr"]:
      check admitMagic(k, msArm).admitted

proc magicInc(a: int) =
  var x = a
  inc x
  if x == 5 and a == 4: symexTarget("hit")
proc magicUnsigned(a: int) =
  if (a +% 1) == 4: symexTarget("hit")

suite "ADM-IR: dispatched magics still decide":
  test "inc and an unsigned operator":
    check symexFind(magicInc, tLabel("hit")).status == sxSat
    check symexFind(magicUnsigned, tLabel("hit")).status == sxSat

proc srcLines(file: string): seq[string] =
  let f = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt" / file
  for line in readFile(f).splitLines:
    let i = line.find('#')
    result.add (if i >= 0: line[0 ..< i] else: line)

proc countIn(file, tok: string): int =
  for l in srcLines(file):
    if tok in l: inc result

proc countOutside(tok: string; skip: openArray[string]): int =
  let dir = currentSourcePath().parentDir() / ".." / "src" / "nelli"
  for f in walkDirRec(dir):
    if not f.endsWith(".nim") or f.extractFilename in skip: continue
    for line in readFile(f).splitLines:
      let i = line.find('#')
      if tok in (if i >= 0: line[0 ..< i] else: line): inc result

proc magicArmsOutsideDispatch(): int =
  ## `of "<magic>"` arms of dsl_parser.nim that sit outside a `dispatchMagic`.
  var inside = false
  var ind = 0
  for l in srcLines("dsl_parser.nim"):
    let t = l.strip
    if t.len == 0: continue
    let cur = l.len - l.strip(trailing = false).len
    if inside and cur <= ind: inside = false
    if not inside and "dispatchMagic(" in l:
      inside = true
      ind = cur
      continue
    if not inside and t.startsWith("of \""):
      for k in magicAxis.keys:
        if ("\"" & k & "\"") in t: inc result

proc magicReadsOutsideDispatch(): int =
  ## Expression-form reads of a magic's name in dsl_parser.nim outside a
  ## `dispatchMagic`: `<magic> == "K"`, `!=`, or `<magic> in [..."K"...]`,
  ## where `<magic>` is `routineMagic(..)`, `callMagic(..)`, `magic` or `m`.
  ## Each is a node built, or a decision taken, on a magic's name without
  ## the table (`whenMagic` / `magicIs` read it).
  var inside = false
  var ind = 0
  for l in srcLines("dsl_parser.nim"):
    let t = l.strip
    if t.len == 0: continue
    let cur = l.len - l.strip(trailing = false).len
    if inside and cur <= ind: inside = false
    if not inside and "dispatchMagic(" in l:
      inside = true
      ind = cur
      continue
    if inside: continue
    proc isMagicRef(tok: string): bool =
      tok in ["m", "magic"] or tok.startsWith("routineMagic(") or
        tok.startsWith("callMagic(")
    for op in [" == \"", " != \""]:
      let i = l.find(op)
      if i < 0: continue
      let lhs = l[0 ..< i].strip.splitWhitespace
      if lhs.len == 0 or not isMagicRef(lhs[^1]): continue
      let k = l[i + op.len ..< l.len].split('"')[0]
      if magicAxis.hasRow(k): inc result
    for ref0 in ["routineMagic(", "callMagic("]:
      let j = l.find(ref0)
      if j >= 0 and " in [" in l[j ..< l.len]:
        inc result
    if " in [" in l and (t.startsWith("magic in") or t.startsWith("m in")):
      inc result

suite "ADM-IR: censuses (allowlist zero unless named)":
  test "no raw scan, math, or arithmetic-stamp construction outside the IR module":
    check countOutside("opaqueDefects:", ["types.nim"]) == 0
    check countOutside(" opaqueUndefined:", ["types.nim"]) == 0
    check countOutside("IRExpr(kind: iekMathCall", ["types.nim"]) == 0
    check countOutside("blkArith:", ["types.nim"]) == 0
    check countOutside(".blkArith =", ["types.nim"]) == 0
  test "the emit's replays are the only rebuilds":
    check countIn("dsl_parser.nim", "bindSym\"replayScan\"") == 1
    check countIn("dsl_parser.nim", "bindSym\"replayArith\"") == 1
    check countOutside("replayScan(", ["definedness.nim", "dsl_parser.nim"]) == 0
    check countOutside("replayArith(", ["types.nim", "dsl_parser.nim"]) == 0
  test "an arm that never ran the scan names `unscanned`: three, allowlisted":
    check countIn("dsl_parser.nim", "unscanned") == 3
    check countOutside("unscanned", ["definedness.nim", "dsl_parser.nim", "types.nim"]) == 0
  test "every dispatched site goes through the macro; no magic arm sits outside it":
    check countIn("dsl_parser.nim", "dispatchMagic(") == card(magicDispatchSites)
    check magicArmsOutsideDispatch() == 0
  test "no expression-form magic read sits outside the table (allowlist zero)":
    check magicReadsOutsideDispatch() == 0
