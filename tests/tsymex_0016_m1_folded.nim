## RFC-0016 W3-z (M1): the `mFolded` magic rows, plus `Nimvm` (a declined row), each pinned
## through `symexFind`. The compiler folds each of these before the walker
## reads a call, so the pin shows the folded value flows into the verdict: a
## SUT compares it with its native value and the walker agrees with a native
## run over the domain.
import std/[unittest, typetraits]
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type M1Obj = object
  x: int64
  y: int64

proc sSizeOf(a: int) =
  if sizeof(int64) == 8 and a == 3: symexTarget("hit")
proc sAlignOf(a: int) =
  if alignof(int64) == 8 and a == 3: symexTarget("hit")
proc sOffsetOf(a: int) =
  const o = offsetof(M1Obj, y)
  if o == 8 and a == 3: symexTarget("hit")
proc sIs(a: int) =
  if (a is int) and not (a is string) and a == 3: symexTarget("hit")
proc sTypeOf(a: int) =
  let b: typeof(a) = 3
  if b == a: symexTarget("hit")
proc sTypeTrait(a: int) =
  if name(int) == "int" and a == 3: symexTarget("hit")
proc sDefined(a: int) =
  if defined(nelliM1NoSuchSymbol) == false and a == 3: symexTarget("hit")
proc sDeclared(a: int) =
  if declared(a) and not declared(m1NoSuchName) and a == 3:
    symexTarget("hit")
proc sDeclaredInScope(a: int) =
  if declaredInScope(a) and a == 3: symexTarget("hit")
proc sCompiles(a: int) =
  if compiles(a + 1) and not compiles(a + "x") and a == 3:
    symexTarget("hit")
proc sAstToStr(a: int) =
  if astToStr(a) == "a" and a == 3: symexTarget("hit")
proc sCompileOption(a: int) =
  if compileOption("stackTrace") == compileOption("stackTrace") and a == 3:
    symexTarget("hit")
proc sCompileOptionArg(a: int) =
  if compileOption("mm", "orc") == defined(gcOrc) and a == 3:
    symexTarget("hit")
proc sSlurp(a: int) =
  const src = slurp("tsymex_0016_m1_folded.nim")
  if src.len > 0 and a == 3: symexTarget("hit")
proc sStaticExec(a: int) =
  const out1 = staticExec("echo m1")
  if out1 == "m1" and a == 3: symexTarget("hit")
proc sRunnableExamples(a: int) =
  runnableExamples:
    discard 1
  if a == 3: symexTarget("hit")
proc sInstantiationInfo(a: int) =
  const line = instantiationInfo().line
  if line > 0 and a == 3: symexTarget("hit")
proc sCpuEndian(a: int) =
  if (cpuEndian == littleEndian) == defined(littleEndian) and a == 3:
    symexTarget("hit")
proc sHostCPU(a: int) =
  if (hostCPU == "amd64") == defined(amd64) and a == 3: symexTarget("hit")
proc sHostOS(a: int) =
  if (hostOS == "linux") == defined(linux) and a == 3: symexTarget("hit")
proc sAppType(a: int) =
  if appType == "console" and a == 3: symexTarget("hit")
proc sCompileDate(a: int) =
  if CompileDate[0] == '2' and CompileDate.len == 10 and a == 3: symexTarget("hit")
proc sCompileTime(a: int) =
  if CompileTime.len == 8 and a == 3: symexTarget("hit")
proc sNimvm(a: int) =
  var rt = 0
  when nimvm:
    rt = 1
  else:
    rt = 2
  if rt == 2 and a == 3: symexTarget("hit")

type M1Finalized = ref object
  v: int
proc m1Fin(x: M1Finalized) {.nimcall.} = discard
proc sNewFinalizer(k: int) =
  var b: M1Finalized
  new(b, m1Fin)
  b.v = k
  if b.v == 3: symexTarget("hit")

const m1Dom = sampled([-3, 0, 2, 3, 4, 9])

template foldedCell(sut: untyped; cell: static string) =
  test cell:
    let r = pinExact(sut, cellKey(axMagic, cell), domain = m1Dom)
    check r.status in {sxSat, sxUnsat}

suite "M1: the folded magic rows, through symexFind":
  foldedCell(sSizeOf, "SizeOf")
  foldedCell(sAlignOf, "AlignOf")
  foldedCell(sOffsetOf, "OffsetOf")
  foldedCell(sIs, "Is")
  foldedCell(sTypeOf, "TypeOf")
  foldedCell(sTypeTrait, "TypeTrait")
  foldedCell(sDefined, "Defined")
  foldedCell(sDeclared, "Declared")
  foldedCell(sDeclaredInScope, "DeclaredInScope")
  foldedCell(sCompiles, "Compiles")
  foldedCell(sAstToStr, "AstToStr")
  foldedCell(sCompileOption, "CompileOption")
  foldedCell(sCompileOptionArg, "CompileOptionArg")
  foldedCell(sSlurp, "Slurp")
  foldedCell(sStaticExec, "StaticExec")
  foldedCell(sRunnableExamples, "RunnableExamples")
  foldedCell(sInstantiationInfo, "InstantiationInfo")
  foldedCell(sCpuEndian, "CpuEndian")
  foldedCell(sHostCPU, "HostCPU")
  foldedCell(sHostOS, "HostOS")
  foldedCell(sAppType, "AppType")
  foldedCell(sCompileDate, "CompileDate")
  foldedCell(sCompileTime, "CompileTime")

suite "M1: the declined row of the compile-time group":
  test "Nimvm":
    pinDecline(sNimvm, cellKey(axMagic, "Nimvm"), feUnsupportedStmtKind)
  test "NewFinalize":
    pinDecline(sNewFinalizer, cellKey(axMagic, "NewFinalize"), feUnsupportedOp)
