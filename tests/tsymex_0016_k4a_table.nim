## RFC-0016 K4a-table (section 8.1): the magic axis's rows, keyed by name, and
## the lib-wide guard. STY-05 (`nextafter`) is its `never` cell.
##
## Every `{.magic: "X".}` in the toolchain's `lib/` has a row in `magicAxis`,
## so a toolchain that adds a magic fails here until it is classified (the
## S8bl guard, `tsymex_rfc0005_s8bl_magicscan`, covers only the `var`
## parameter magics and stays as the narrower check). The axis absorbs
## `varParamMagics` (deleted in K4a-dispatch, which dispatches the sites; see
## `tsymex_0016_k4a_dispatch`).
import std/[unittest, os, strutils, compilesettings, sets, options, tables]
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/magic_rows
import nelli/smt/dsl_parser

const nimLib = querySetting(libPath)

proc libMagics(): HashSet[string] =
  ## Every magic name declared under `lib/`: `magic: "Name"` or `magic:"Name"`.
  for f in walkDirRec(nimLib):
    if not f.endsWith(".nim"): continue
    let text = readFile(f)
    for pat in ["magic: \"", "magic:\""]:
      var at = 0
      while true:
        let i = text.find(pat, at)
        if i < 0: break
        let s = i + pat.len
        let e = text.find('"', s)
        if e < 0: break
        let name = text[s ..< e]
        # A match in a `#` comment line is prose (macros.nim's `"Foo"`).
        let ls = text.rfind('\n', 0, i) + 1
        let inComment = text[ls ..< i].strip.startsWith("#")
        if not inComment and name.len > 0 and
           name.allCharsInSet({'A'..'Z', 'a'..'z', '0'..'9', '_'}):
          result.incl name
        at = e

suite "RFC-0016 K4a-table: the magic axis":
  test "every magic declared in lib/ has a row (the lib-wide guard)":
    let found = libMagics()
    checkpoint "magics found: " & $found.len
    # Not vacuous: the scan sees the arithmetic and the var-parameter magics.
    check found.len >= 150
    for m in ["AddI", "DivU", "Swap", "Inc", "NewSeq", "LePtr", "Spawn"]:
      checkpoint m
      check m in found
    var rows: HashSet[string]
    for k in keys(magicAxis): rows.incl k
    var missing: seq[string]
    for m in found:
      if m notin rows: missing.add m
    checkpoint "magics with no row in magicAxis: " & $missing
    check missing.len == 0

  test "the axis is keyed by name on the magic scope":
    check render(magicAxis.cellOf("DivU")) == "magic:DivU"
    check admitMagic("DivU", msArm).cell == cellKey(axMagic, "DivU")

  test "a modelled magic is admitted at its arm":
    for m in ["AddI", "DivU", "Swap", "LtF64"]:
      checkpoint m
      check admitMagic(m, msArm).admitted

  test "a declined magic names its cell and a kind":
    for m in ["XorSet", "LePtr", "DeepCopy", "Destroy", "NewFinalize"]:
      checkpoint m
      let a = admitMagic(m, msArm)
      check not a.admitted
      let (kind, reason) = a.decline
      check kind == some(feUnsupportedOp)
      check ("magic:" & m) in reason

  test "a compile-time-only magic is a never cell":
    var seen = 0
    for c in magicAxis.cells:
      if render(c.cell) in ["magic:Spawn", "magic:Is", "magic:Implies"]:
        inc seen
    check seen == 3
    check not admitMagic("Spawn", msArm).admitted
    for c in magicAxis.cells:
      if render(c.cell) == "magic:Spawn":
        check c.intent == iNever

  test "an absent name is a feUnadmitted decline":
    let a = admitMagic("NoSuchMagic", msArm)
    check not a.admitted
    check a.decline[0] == some(feUnadmitted)

  test "STY-05: nextafter is a never cell":
    let a = admitMagic("nextafter", msArm)
    check not a.admitted
    check a.decline[0] == some(feUnsupportedOp)
    check "magic:nextafter" in a.decline[1]
    var found = false
    for c in magicAxis.cells:
      if render(c.cell) == "magic:nextafter":
        found = true
        check not c.admitted
        check c.intent == iNever
    check found
