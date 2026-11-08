## RFC-0005 code review, round 1, R1-08 -- the cache key carries the build
## flags that change what the native `fn` does.
##
## A cached `rsConfirmed` `:sat` or `:raised` is a fact about the native `fn`,
## which a replay ran. A debug build's confirmed `IndexDefect` cannot happen in
## a `-d:danger` build, where `fn` does not check, yet nothing in the key varied
## with `-d:danger`, `--assertions:off` or a check switch: one database shared
## by the two builds served the debug build's raise to the danger one as
## trusted. The key now ends in `|bs=` (`buildSegment`, RFC-0016 K5a): the checks this
## build compiles in, `danger`, `release` and the memory model, and the rest of
## the build profile.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/buildprofile

const allOn = {coAssert, coBound, coField, coObj, coOverflow, coRange}

proc key(b: BuildSemantics): string =
  symexCacheKey(SymexProgram(body: IRStmt(kind: isBlock)), tIndexError(),
                defaultSymexSettings(), z3Version = "z", nimVersion = "n",
                walkerVersion = "w", renderingVersion = "r",
                replayMode = "fork",
                buildSeg = buildSegment(b, readHost("z")))

proc base(): BuildSemantics =
  ## An explicit base, so no variation equals this build's own value.
  result = buildSemantics
  result.checks = allOn
  result.danger = false
  result.release = false
  result.mm = mmOrc
  result.backend = beC
  result.exceptions = exQuirky
  result.threads = false
  result.stackTrace = false
  result.lineTrace = false
  result.fwrapv = false

# R2 SM3: backend, exceptions, threads and stack traces are keyed
suite "R2 SM3: backend, exceptions, threads and stack traces are keyed":

  test "each is a different key":
    let k0 = key(base())
    var b = base(); b.backend = beCpp
    check key(b) != k0
    b = base(); b.exceptions = exGoto
    let goto = key(b)
    check goto != k0
    b = base(); b.exceptions = exSetjmp
    check key(b) != k0
    check key(b) != goto
    b = base(); b.threads = true
    check key(b) != k0
    b = base(); b.stackTrace = true
    check key(b) != k0
    b = base(); b.lineTrace = true
    check key(b) != k0

  test "the default is this build's":
    let seg = buildSegment(buildSemantics, readHost("z"))
    check ("backend=cpp" in seg) == defined(cpp)
    check ("threads=1" in seg) == compileOption("threads")
    check ("stackTrace=1" in seg) == compileOption("stackTrace")
    check ("exceptions=goto" in seg) == compileOption("exceptions", "goto")

suite "R1-08: the key varies with the build's checks and flags":

  test "each check, turned off, is a different key":
    let k0 = key(base())
    for c in allOn:
      var b = base()
      b.checks.excl c
      checkpoint $c
      check key(b) != k0

  test "the float checks, turned on, are a different key":
    let k0 = key(base())
    var b = base(); b.checks.incl coNan
    check key(b) != k0
    b = base(); b.checks.incl coInf
    check key(b) != k0

  test "danger, release and the memory model are each a different key":
    let k0 = key(base())
    var d = base(); d.checks = {}; d.danger = true; d.release = true
    check key(d) != k0
    var r = base(); r.release = true
    check key(r) != k0
    var m = base(); m.mm = mmRefc
    check key(m) != k0
    var none = base(); none.checks = {}
    check key(none) != key(d)

  test "the default is this build's":
    let seg = buildSegment(buildSemantics, readHost("z"))
    check ("boundChecks" in seg) == compileOption("boundChecks")
    check ("assertions" in seg) == compileOption("assertions")
    check ("overflowChecks" in seg) == compileOption("overflowChecks")
    check ("danger=1" in seg) == defined(danger)
    check ("mm=orc" in seg) == compileOption("mm", "orc")
    check symexCacheKey(SymexProgram(body: IRStmt(kind: isBlock)),
                        tIndexError(), defaultSymexSettings(), "z", "n", "w",
                        "r", replayMode = "fork") == key(buildSemantics)
