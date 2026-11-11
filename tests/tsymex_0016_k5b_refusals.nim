## RFC-0016 K5b (section 8.3, Refusals). Every build configuration the profile
## cannot stand behind is refused by NAME, never answered with a verdict, and
## each is a cell of the build axis (`buildCells`).
##
## A configuration this CI host cannot build (32-bit, big-endian, arm64, macOS,
## `-d:nelliFwrapv` under vcc) is tested through the decision function over a
## SYNTHETIC build description (`pinAdmission`); the platform is not faked. The
## ones a child compile can reach are also built for real (`pinRefused`).
## The hazards that stay as they are (STY-01, STY-08, AUD-01, `sizeof`) are
## `never` cells, each with the native fact that holds on this host
## (`pinNever`).
import std/[unittest, strutils, options, os, osproc, tempfiles]
import nelli
import nelli/symex
import nelli/smt/buildprofile
import ./s8cu_helpers

const
  srcDir = currentSourcePath().parentDir.parentDir / "src"
  symexProbe = "import nelli\nimport nelli/symex\n" &
    "proc sut(v: int) =\n  if v == 3: symexTarget(\"h\")\n" &
    "let r = symexFind(sut, tLabel(\"h\"))\necho r.status\n"

var base = buildSemantics
base.os = osLinux; base.backend = beC; base.mm = mmOrc; base.exceptions = exGoto
base.cpu = cpuAmd64; base.ptrBits = 64; base.endian = enLittle
base.caseObjects = cmStrict; base.fwrapv = false
let gcc = BuildProvenance(ccFamily: ccGcc, nimVersion: "2.2.10")

var gLit = 5
proc sLitGlobal(x: int) =
  if gLit == 6 and x == 1: symexTarget("hit")

proc cell(k: static string): CellKey = cellKey(axBuild, k)

suite "K5b: the build axis has a cell for every refusal":
  test "the refusal, hazard and cfg cells are in the table":
    var have: seq[string]
    for k in buildCells.keys: have.add k
    for want in ["mm=refc", "ptrBits=32", "endian=big", "cpu=arm64",
                 "os=macosx", "fwrapv/vcc", "exceptions/setjmp/windows", "nim/unpatched", "z3/unverified", "pcre/unverified",
                 "profile/unprojectable", "finally/returnOnRaise", "z3/deepUnsat",
                 "setting/isLoose", "semantics/globalLiteralEntry", "sizeof/host", "mm=arc", "mm=atomicArc",
                 "useMalloc", "exceptions/setjmp", "release", "fwrapv"]:
      check want in have

suite "K5b: refusals through the decision function (synthetic builds)":
  test "a pinned profile is admitted (the synthetic base)":
    check admitBuild(base, gcc).isNone

  test "32-bit int":
    var b = base
    b.ptrBits = 32; b.cpu = cpuI386
    pinAdmission(cell"ptrBits=32", admitBuild(b, gcc), bfPtrBits, "32-bit")

  test "big-endian":
    var b = base
    b.endian = enBig
    pinAdmission(cell"endian=big", admitBuild(b, gcc), bfEndian, "big-endian")

  test "arm64, and arm":
    var b = base
    b.cpu = cpuArm64
    pinAdmission(cell"cpu=arm64", admitBuild(b, gcc), bfCpu, "arm64")
    b.cpu = cpuArm
    check admitBuild(b, gcc).get.field == bfCpu

  test "macOS":
    var b = base
    b.os = osMacosx
    pinAdmission(cell"os=macosx", admitBuild(b, gcc), bfOs, "macOS")

  test "-d:nelliFwrapv under vcc":
    var b = base
    b.os = osWindows; b.fwrapv = true
    pinAdmission(cell"fwrapv/vcc",
                 admitBuild(b, BuildProvenance(ccFamily: ccVcc)), bfFwrapv, "vcc")
    # The same build under mingw is a row.
    check rowOf(b, unreadHost, BuildProvenance(ccFamily: ccGcc)) == some(brMingw)

  test "--exceptions:setjmp on Windows (INT-12)":
    var b = base
    b.os = osWindows; b.exceptions = exSetjmp
    for p in [gcc, BuildProvenance(ccFamily: ccVcc, nimVersion: "2.2.10")]:
      pinAdmission(cell"exceptions/setjmp/windows", admitBuild(b, p),
                   bfExceptions, "INT-12")
      check rowOf(b, unreadHost, p).isNone
    # The same build on Linux, and goto exceptions on Windows, are rows.
    check rowOf(base, unreadHost, gcc) == some(brLinuxC)
    b.exceptions = exGoto
    check admitBuild(b, gcc).isNone
    b.os = osLinux; b.exceptions = exSetjmp
    check admitBuild(b, gcc).isNone

  test "an unpatched Nim":
    var p = gcc
    p.stockNim = true
    pinAdmission(cell"nim/unpatched", admitBuild(base, p), bfNim, "unpatched Nim")
    check rowOf(base, unreadHost, p).isNone
    check rowOf(base, unreadHost, gcc).isSome

  test "an unverified Z3 is the host half's refusal":
    var h = unreadHost
    h.z3 = z3Other
    h.z3Full = "4.8.12.0"
    pinAdmission(cell"z3/unverified", admitHost(h, base, gcc), bfZ3, "4.8.12")
    for v in [z3v4_13_4, z3v5_1]:
      h.z3 = v
      check admitHost(h, base, gcc).isNone

  test "no row covers the profile":
    var b = base
    b.mm = mmMarkAndSweep
    pinAdmission(cell"profile/unprojectable", admitBuild(b, gcc), bfRow, "no verified build row")
    b = base
    b.exceptions = exQuirky
    check admitBuild(b, gcc).get.field == bfRow
    b = base
    b.caseObjects = cmOld
    check admitBuild(b, gcc).get.field == bfRow
    check admitBuild(base, BuildProvenance(ccFamily: ccOther)).get.field == bfRow

suite "K5b: this toolchain is the patched one":
  test "the probes saw both backports":
    check not buildProvenance.stockNim
    check "backport-25858" in buildProvenance.patchset
    check "backport-26093" in buildProvenance.patchset
    check admitBuild().isNone

suite "K5b: refusals by a real child build":
  test "a 32-bit target is refused at the import":
    pinRefused(cell"ptrBits=32", symexProbe,
      ["--cpu:i386", "--path:" & srcDir], "[field: ptrBits]")

suite "K5b: the hazards that stay (never cells)":
  proc raiseThroughFinally(): int =
    try:
      raise newException(ValueError, "r")
    finally:
      return 7

  test "STY-01: return in finally on a raised path differs by backend":
    var res = -1
    var raised = false
    try: res = raiseThroughFinally()
    except ValueError: raised = true
    when defined(cpp):
      pinNever(cell"finally/returnOnRaise", res == 7 and not raised,
               "cpp: the return wins, no re-raise")
    else:
      pinNever(cell"finally/returnOnRaise", res == -1 and raised,
               "c: the exception propagates past the finally's return")

  test "STY-08: the Z3 version is a fact of the host, not of the SUT":
    let h = readHost("4.13.4.0")
    pinNever(cell"z3/deepUnsat", h.z3 == z3v4_13_4 and
             z3VersionOf("5.1.0.0") == z3v5_1 and
             buildSegment(buildSemantics, h) !=
               buildSegment(buildSemantics, readHost("5.1.0.0")),
             "the two verified Z3 builds are two cache keys")

  test "AUD-01: isLoose stays opt-in (ADR-0001)":
    pinNever(cell"setting/isLoose", true,
             "opt-in unsound, banner on main (ADR-0001); no build axis moves it")

  test "AUD-09: a literal-initialised var global is not read at its initialiser":
    # Natively `gLit` is 5 on entry, so the target is unreachable; the walker
    # does not claim that: it answers sxUnknown, never a trusted verdict.
    let r = symexFind(sLitGlobal, tLabel("hit"), pinSettingsConst)
    pinNever(cell"semantics/globalLiteralEntry",
             gLit == 5 and r.status == sxUnknown and not r.trusted,
             "native entry value " & $gLit & "; walker verdict " & $r.status)

  test "W-52: sizeof is the host's":
    pinNever(cell"sizeof/host",
             sizeof(int) * 8 == buildSemantics.ptrBits and sizeof(int) == 8,
             "sizeof(int) = " & $sizeof(int) & " on a refused-unless-64-bit axis")

suite "K5b: the stock-Nim corpus slice":
  # `NELLI_STOCK_NIM` names an unmodified Nim 2.2.10. No CI leg has one (the
  # three Windows legs and the Linux image use the patched toolchain), so the
  # slice is a run the person with a stock Nim makes: the profile test file
  # under it, and a symexFind SUT refused by name.
  test "an unmodified Nim reads as stock and is refused":
    let stockNim = getEnv("NELLI_STOCK_NIM")
    if stockNim.len == 0:
      skipCell(cell"nim/unpatched",
               "NELLI_STOCK_NIM is not set: no unmodified Nim 2.2.10 here")
    else:
      let here = currentSourcePath().parentDir
      let (o1, rc1) = execCmdEx(quoteShell(stockNim) & " c -r --hints:off " &
        "--nimcache:" & (getTempDir() / "k5b_stock_nc") & " --path:" & srcDir &
        " " & quoteShell(here / "tsymex_0016_k5b_stock.nim"))
      checkpoint o1
      check rc1 == 0
      check "stock Nim: refused by name" in o1
      let dir = createTempDir("k5b_stock_", "")
      writeFile(dir / "probe.nim", symexProbe)
      let (o2, rc2) = execCmdEx(quoteShell(stockNim) & " c --hints:off " &
        "--nimcache:" & (dir / "nc") & " --path:" & srcDir & " " &
        quoteShell(dir / "probe.nim"))
      removeDir(dir)
      checkpoint o2
      check rc2 != 0
      check "[field: nim]" in o2
