## RFC-0005 S8bt (item 1, SOUNDNESS) -- the walker reads a regex only when
## std/re's libpcre is a build the model has been verified against
## (`pcre_engine.verifiedLibs`: the version string `pcre_version()` reports
## and the engine std/re runs unanchored calls on). Any other library --
## another version, an engine not verified for that version, or one the
## walker cannot ask -- declines every regex call with a named reason
## (`pcre_engine.unverifiedLibReason`): ⊤, as for a pattern whose validity
## the reader does not decide. Before S8bt such a library was recorded in
## the cache key but read with PCRE 8.45's model.
##
## The detected library is overridden for the test
## (`pcre_engine.overridePcreLib`); the real one must itself be verified.
import std/[unittest, strutils, re, times]
import pcre
import nelli/symex
import nelli/smt/types
import nelli/smt/pcre_syntax
import nelli/smt/pcre_engine

proc jitEngine(): bool =
  var v: cint
  discard pcre.config(pcre.CONFIG_JIT, addr v)
  v == 1

template verdict(sut: untyped; label: string): SymexResult =
  let t0 = epochTime()
  let r = symexFind(sut, tLabel(label))
  echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t0,
                                                     ffDecimal, 1), " s"
  r

proc findTarget(s: string) =
  if s.len == 2 and s.find(re"b") == 1:
    symexTarget("bt_lib_find")

proc matchTarget(s: string) =
  if s.len == 1 and s.match(re"(?:a|b)c?"):
    symexTarget("bt_lib_match")

proc replaceTarget(s: string) =
  if s == "ab" and s.replace(re"a", "x") == "xb":
    symexTarget("bt_lib_replace")

proc rejectedTarget(s: string) =
  # PCRE 8.45 rejects `a{2,1}`; whether another library does is not known.
  try:
    if s.len == 1 and s.contains(re"a{2,1}"):
      symexTarget("bt_lib_rejected_hit")
  except RegexError:
    symexTarget("bt_lib_rejected")

let realVersion = $pcre.version()

suite "S8bt: the verified libpcre builds":

  test "the library std/re loads here is a verified one":
    check pcreVersion() == realVersion
    check pcreRunsJit() == jitEngine()
    checkpoint "libpcre " & realVersion & (if jitEngine(): " (JIT)" else: "")
    check pcreLibVerified()
    check unverifiedLibReason() == ""

  test "the allowlist":
    # 8.45 (the Linux test image's) and 8.37 (the Windows legs', JIT).
    check isVerifiedLib("8.45 2021-06-15", false)
    check isVerifiedLib("8.37 2015-04-28", true)
    check isVerifiedLib("8.37 2015-04-28", false)
    # Another version, a different build date, or no answer: not verified.
    check not isVerifiedLib("8.44 2020-02-12", false)
    check not isVerifiedLib("8.45 2021-06-16", false)
    check not isVerifiedLib("", false)
    check not isVerifiedLib("", true)

suite "S8bt: an unverified libpcre declines every regex call":

  test "parseSpec: psUnknown with the named reason":
    overridePcreLib("8.44 2020-02-12", false)
    defer: clearPcreLibOverride()
    check not pcreLibVerified()
    check pcreEngineName() == "pcre-interp-8.44"
    for p in ["a", "a{2,1}", "(*UTF)\\x{100}", "x{0}(?i)a"]:
      let pr = parseSpec(RegexSpec(entry: "find", flag: "re", pattern: p))
      check pr.status == psUnknown
      check pr.reason == unverifiedLibReason()
      check "8.44 2020-02-12" in pr.reason
    # The reader itself (the compile-time parser's) is unchanged.
    check parsePcre("a").status == psOk

  test "a library the walker cannot ask":
    overridePcreLib("", true)
    defer: clearPcreLibOverride()
    check not pcreLibVerified()
    check parseSpec(RegexSpec(entry: "find", flag: "re",
                              pattern: "a")).status == psUnknown

  test "the walker: verdicts become sxUnknown":
    # With the real (verified) library these are decided.
    check verdict(findTarget, "bt_lib_find").status == sxSat
    check verdict(matchTarget, "bt_lib_match").status == sxSat
    check verdict(replaceTarget, "bt_lib_replace").status == sxSat
    check verdict(rejectedTarget, "bt_lib_rejected").status in {sxSat, sxRaised}
    overridePcreLib("8.44 2020-02-12", jitEngine())
    defer: clearPcreLibOverride()
    let rf = verdict(findTarget, "bt_lib_find")
    check rf.status == sxUnknown
    var named = false
    for e in rf.errors:
      if "psUnverifiedLib" in e.msg: named = true
    check named
    check verdict(matchTarget, "bt_lib_match").status == sxUnknown
    check verdict(replaceTarget, "bt_lib_replace").status == sxUnknown
    check verdict(rejectedTarget, "bt_lib_rejected").status == sxUnknown

suite "S8bt: walker version":

  test "the walker version is at least 224":
    check parseInt(symexWalkerVersion) >= 224
