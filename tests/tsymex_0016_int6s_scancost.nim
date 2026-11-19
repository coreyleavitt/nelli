## RFC-0016 int6-s: the check-option scan's cost in the compile-time VM.
##
## int6-w (2b795fe7) made the scan count each visited text's lines and collect
## its routine definitions on every visit. `scanModuleText` reads a module once
## per world (each combination of its undecided `when` conditions, read twice
## where a pop matched no push), and a world visits every file the module
## includes, so `system.nim`'s scan visited its 64 files 1,462 times: 13.5 MB of
## text counted a byte at a time, 15,821,232 VM iterations for that one scan
## against the compiler's default `--maxLoopIterationsVM` of 10,000,000. Every
## program whose walk registers a `system.nim` routine (an `items` over a seq)
## failed to compile (`tsymex_0016_k9cg_unbacked_p`).
##
## The bound, in `tsymex_0016_int6s_scancost.nim.cfg`, is this file's whole
## VM budget: 4,000,000 iterations per evaluation. Measured on the pinned
## toolchain (2.2.10), the smallest budget under which each scan compiles:
##
##   module           before int6-w   int6-w      int6-s
##   system.nim       1,941,908       15,821,232  1,941,908
##   core/macros       95,603          1,270,524     95,603
##   pure/strutils     41,815          1,026,385     41,815
##   collections/tables 47,538           416,036     47,538
##
## 4,000,000 is twice the largest (`system.nim`, 652,085 bytes in 64 files:
## about three iterations per byte of distinct text) and a quarter of the
## regression. A count or a collection per visit again puts `system.nim` past
## it; a scan of each file once per world, at its module level, does not.
import std/[unittest, os, compilesettings, strutils]
import nelli/smt/check_scan

proc dExists(p: string): bool = fileExists(p)
proc dRead(p: string): string = staticRead(p)
proc dAnchor(p: string): string = p

const lib = querySetting(libPath)
const env = SourceEnv(exists: dExists, read: dRead, anchor: dAnchor,
                      searchPaths: querySettingSeq(searchPaths), libDir: lib)

const
  systemScan = scanModule(lib / "system.nim", env)
  macrosScan = scanModule(lib / "core" / "macros.nim", env)
  strutilsScan = scanModule(lib / "pure" / "strutils.nim", env)
  tablesScan = scanModule(lib / "pure" / "collections" / "tables.nim", env)
  # The lazy half: a routine placed against the text, once per parsed text.
  systemLen = staticRead(lib / "system.nim").count('\n')
  systemPast = textDisagrees(systemScan, lib / "system.nim", "nope",
                             systemLen + 10)
  systemIn = textDisagrees(systemScan, lib / "system.nim", "nope", 1)

suite "int6-s: the check scan stays inside the VM's iteration budget":
  test "each stdlib scan reads its whole world":
    check systemScan.unknownReason == ""
    check macrosScan.unknownReason == ""
    check strutilsScan.unknownReason == ""
    check tablesScan.unknownReason == ""

  test "the text's shape is still read where a routine is placed":
    check systemIn == ""
    checkpoint systemPast
    check "lines, and the compiler placed `nope`" in systemPast
