## RFC-0016 ADM-1 (§8.1). The admission interface through its two first
## consumers: the magic axis (`magicAxis`, read by
## `ensureProcRegistered`) and the build axis (`pcreLibs`, read by the
## regex model). No verdict changes: the rows say what the old tables said.
import std/[unittest, options, strutils]
import nelli/smt/types
import nelli/smt/admission
import nelli/smt/magic_rows
import nelli/smt/pcre_engine

suite "ADM-1 magic axis":
  test "a modelled magic is admitted at its arm":
    let a = admitMagic("Swap", msVarStmt)
    check a.admitted
    check a.payload == mmModelled
    check render(a.cell) == "magic:Swap"

  test "a modelled magic declines at ensureProcRegistered, as before":
    let a = admitMagic("Swap", msProcRegister)
    check not a.admitted
    let (kind, why) = a.decline
    check kind == some(feUnsupportedOp)
    check "magic:Swap" in why

  test "a declined magic is admitted nowhere and keeps its note":
    for site in MagicSite:
      let a = admitMagic("Destroy", site)
      check not a.admitted
      let (kind, why) = a.decline
      check kind == some(feUnsupportedOp)
      check "magic:Destroy" in why

  test "a magic with no row is feUnadmitted":
    let a = admitMagic("NoSuchMagic", msProcRegister)
    check not a.admitted
    let (kind, why) = a.decline
    check kind == some(feUnadmitted)
    check classOf(feUnadmitted) == dcOmitted  ## K7b (was dcNoAnswer)
    check "magic:NoSuchMagic" in why

suite "ADM-1 build axis (PCRE)":
  test "the three verified builds are admitted with their engine":
    check admitPcreLib("8.45 2021-06-15", false).payload == peInterp
    check admitPcreLib("8.37 2015-04-28", true).payload == peJit837
    check admitPcreLib("8.37 2015-04-28", false).payload == peInterp
    check admitPcreLib("8.45 2021-06-15", false).admitted

  test "an unverified build declines in the axis's own vocabulary":
    let a = admitPcreLib("8.44 2020-02-12", false)
    check not a.admitted
    let (kind, why) = a.decline
    check kind.isNone
    check "build:" in why
    check not admitPcreLib("8.45 2021-06-15", true).admitted

  test "the cell keys render":
    check render(admitPcreLib("8.45 2021-06-15", false).cell) ==
      "build:8.45 2021-06-15|interp"
    check render(admitPcreLib("8.37 2015-04-28", true).cell) ==
      "build:8.37 2015-04-28|jit"
    check render(admitMagic("Inc", msArm).cell) == "magic:Inc"
