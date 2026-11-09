## RFC-0016 K5b (W-51, per-build pins): the PCRE library this build runs on is
## a cell of the build axis (`pcreLibs`), and the walker reads a regex only on
## a verified one. A regex SUT is pinned against the loaded library's own cell
## (the Linux image's 8.45 interpreter, the Windows legs' 8.37 JIT); an
## unverified library (`overridePcreLib`) declines every regex call by name
## (`psUnverifiedLib`) and is the `pcre/unverified` cell.
import std/[unittest, strutils, re]
import nelli
import nelli/symex
import nelli/smt/pcre_engine
import ./s8cu_helpers

proc findSut(s: string) =
  if s.len == 2 and s.find(re"b") == 1:
    symexTarget("hit")

proc matchSut(s: string) =
  if s.len == 1 and s.match(re"(?:a|b)c?"):
    symexTarget("hit")

proc hostCell(): CellKey =
  ## `pcreLibs`' key for the library std/re loaded: `version|engine`.
  CellKey(scope: axBuild,
          key: pcreVersion() & "|" & (if pcreRunsJit(): "jit" else: "interp"))

suite "K5b: per-build regex pins":
  test "the loaded library is a verified cell":
    check pcreLibVerified()
    var found = false
    for k in pcreLibs.keys:
      if k == hostCell().key: found = true
    check found

  test "find on the loaded library":
    let r = pinExact(findSut, hostCell(), domain = sampled(["ab", "bb", "a"]))
    check r.status == sxSat
    check r.trusted

  test "match on the loaded library":
    let r = pinExact(matchSut, hostCell(), domain = sampled(["a", "bc", "x"]))
    check r.status == sxSat
    check r.trusted

  test "an unverified library declines every regex call by name":
    overridePcreLib("8.44 2020-02-12", pcreRunsJit())
    defer: clearPcreLibOverride()
    pinDecline(findSut, cellKey(axBuild, "pcre/unverified"),
               seUnsupportedRegex, needle = "psUnverifiedLib")
