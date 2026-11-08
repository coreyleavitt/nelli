## RFC-0016 K5a (section 8.3). The build profile's types, `rowOf` and the
## compile-time and host halves of the refusals.
import std/[unittest, strutils, options]
import nelli/smt/buildprofile

func host(z3: Z3Version): HostSemantics =
  HostSemantics(pcre: peInterp, z3: z3)

suite "K5a: BuildSemantics, HostSemantics, BuildProvenance":
  test "this build's profile":
    check buildSemantics.ptrBits == 64
    check buildSemantics.endian == enLittle
    check buildSemantics.cpu == cpuAmd64
    check buildSemantics.opt == optUnknown   # not readable: never guessed
    check buildSemantics.caseObjects == cmStrict
    when defined(linux): check buildSemantics.os == osLinux
    when defined(windows): check buildSemantics.os == osWindows
    check buildSemantics.fwrapv == defined(nelliFwrapv)
    check buildProvenance.nimVersion == NimVersion
    check (cfFwrapv in buildProvenance.assumedAbsent) == not defined(nelliFwrapv)
    check cfFastMath in buildProvenance.assumedAbsent

  test "z3VersionOf":
    check z3VersionOf("4.13.4.0") == z3v4_13_4
    check z3VersionOf("5.1.0.0") == z3v5_1
    check z3VersionOf("5.1.2") == z3v5_1
    check z3VersionOf("4.12.2.0") == z3Other
    check z3VersionOf("4.13.3.0") == z3Other
    check z3VersionOf("") == z3Other

suite "K5a: rowOf":
  var lin = buildSemantics
  lin.os = osLinux; lin.backend = beC; lin.mm = mmOrc
  lin.exceptions = exGoto; lin.cpu = cpuAmd64; lin.ptrBits = 64
  lin.endian = enLittle; lin.caseObjects = cmStrict; lin.fwrapv = false
  let gcc = BuildProvenance(ccFamily: ccGcc)

  test "the six pinned rows":
    check rowOf(lin, host(z3v5_1), gcc) == some(brLinuxC)
    check rowOf(lin, host(z3v4_13_4), gcc) == some(brZ3v4_13_4)
    var cpp = lin
    cpp.backend = beCpp; cpp.exceptions = exCpp
    check rowOf(cpp, host(z3v5_1), gcc) == some(brLinuxCpp)
    var win = lin
    win.os = osWindows
    check rowOf(win, host(z3v4_13_4), gcc) == some(brMingw)
    check rowOf(win, host(z3v4_13_4), BuildProvenance(ccFamily: ccVcc)) ==
      some(brMsvc)

  test "an unread host asks the compile-time question":
    check rowOf(lin, host(z3Unread), gcc).isSome
    check rowOf(lin, host(z3Other), gcc).isNone

  test "fields that no row covers":
    for m in [mmRefc, mmMarkAndSweep, mmBoehm, mmGo, mmNone, mmOther]:
      var b = lin
      b.mm = m
      check rowOf(b, host(z3v5_1), gcc).isNone
    for m in [mmOrc, mmArc, mmAtomicArc]:
      var b = lin
      b.mm = m
      check rowOf(b, host(z3v5_1), gcc).isSome
    var q = lin
    q.exceptions = exQuirky
    check rowOf(q, host(z3v5_1), gcc).isNone
    var o = lin
    o.caseObjects = cmOld
    check rowOf(o, host(z3v5_1), gcc).isNone
    check rowOf(lin, host(z3v5_1), BuildProvenance(ccFamily: ccOther)).isNone

  test "neutral fields do not move the row":
    var b = lin
    b.checks = {}
    b.panics = true; b.danger = true; b.release = true
    b.threads = true; b.stackTrace = true; b.lineTrace = true
    b.fwrapv = true
    check rowOf(b, host(z3v5_1), gcc) == some(brLinuxC)

suite "K5a: admitBuild refuses by name":
  var ok = buildSemantics
  ok.os = osLinux; ok.backend = beC; ok.mm = mmOrc; ok.exceptions = exGoto
  ok.cpu = cpuAmd64; ok.ptrBits = 64; ok.endian = enLittle
  ok.caseObjects = cmStrict; ok.fwrapv = false
  let gcc = BuildProvenance(ccFamily: ccGcc)

  proc refusedField(b: BuildSemantics; p = gcc): BuildField =
    let r = admitBuild(b, p)
    check r.isSome
    r.get.field

  test "a pinned profile is admitted":
    check admitBuild(ok, gcc).isNone

  test "32-bit int":
    var b = ok
    b.ptrBits = 32
    check refusedField(b) == bfPtrBits

  test "big-endian":
    var b = ok
    b.endian = enBig
    check refusedField(b) == bfEndian

  test "-d:nelliFwrapv under vcc":
    var b = ok
    b.os = osWindows; b.fwrapv = true
    check refusedField(b, BuildProvenance(ccFamily: ccVcc)) == bfFwrapv
    check "vcc" in admitBuild(b, BuildProvenance(ccFamily: ccVcc)).get.reason

  test "arm64 and macOS":
    var b = ok
    b.cpu = cpuArm64
    check refusedField(b) == bfCpu
    var m = ok
    m.os = osMacosx
    check refusedField(m) == bfOs

  test "a profile rowOf cannot project":
    var b = ok
    b.mm = mmBoehm
    check refusedField(b) == bfRow
    var q = ok
    q.exceptions = exQuirky
    check refusedField(q) == bfRow
    check refusedField(ok, BuildProvenance(ccFamily: ccOther)) == bfRow

  test "refc keeps its Wave-1 refusal":
    var b = ok
    b.mm = mmRefc
    check refusedField(b) == bfMm

  test "the host half refuses an unverified Z3":
    check admitHost(host(z3v5_1), ok, gcc).isNone
    check admitHost(host(z3v4_13_4), ok, gcc).isNone
    let r = admitHost(host(z3Other), ok, gcc)
    check r.isSome
    check r.get.field == bfZ3
    # Linux cpp is pinned on 5.1 only
    var cpp = ok
    cpp.backend = beCpp
    check admitHost(host(z3v4_13_4), cpp, gcc).get.field == bfRow

  test "this build is admitted":
    check admitBuild().isNone
