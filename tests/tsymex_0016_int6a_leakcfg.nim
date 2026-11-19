## RFC-0016 int6-a, leaked scopes, a fallback: `--import:` in this file's
## `.nim.cfg`. The module it names is imported into every module the program
## compiles, ahead of the program's own imports, and the scan does not read
## it. Natively `s0016_int6a_leaked` is still first compiled under the push,
## and `leakConv(300)` keeps 300; the compile order is not replayed under a
## configured import: the coarse reading stands, and the routine declines.

import std/unittest
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/check_options

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6a_leakcfg")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-a leaked scopes: a configured import keeps the coarse reading":
  test "the leaked routine declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
  test "what reads as a configured import":
    check namesImportSwitch("--import:\"x\"")
    check namesImportSwitch("--include:x.nim")
    check namesImportSwitch("import = \"x\"")
    check namesImportSwitch("switch(\"import\", \"x\")")
    check not namesImportSwitch("cincludes: \"/usr/local/include\"")
    check not namesImportSwitch("include \"nimble.paths\"")
    check not namesImportSwitch("import std/os")
    check not namesImportSwitch("{.importc: \"f\".}")
    check not namesImportSwitch("# --import:x")
