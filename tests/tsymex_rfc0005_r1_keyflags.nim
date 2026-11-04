## RFC-0005 code review, round 1, R1-08 -- the cache key carries the build
## flags that change what the native `fn` does.
##
## A cached `rsConfirmed` `:sat` or `:raised` is a fact about the native `fn`,
## which a replay ran. A debug build's confirmed `IndexDefect` cannot happen in
## a `-d:danger` build, where `fn` does not check, yet nothing in the key varied
## with `-d:danger`, `--assertions:off` or a check switch: one database shared
## by the two builds served the debug build's raise to the danger one as
## trusted. The key now ends in `|bf=` (`buildFlagsSegment`): the checks this
## build compiles in, `danger`, `release` and the memory model.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc key(bf: string): string =
  symexCacheKey(SymexProgram(body: IRStmt(kind: isBlock)), tIndexError(),
                defaultSymexSettings(), z3Version = "z", nimVersion = "n",
                walkerVersion = "w", renderingVersion = "r",
                replayMode = "fork", buildFlags = bf)

const allOn = @["assertions", "boundChecks", "fieldChecks", "objChecks",
                "overflowChecks", "rangeChecks"]

# R2 SM3: the arguments after the memory model, named so the old positional
# calls above keep their meaning.
suite "R2 SM3: backend, exceptions, threads and stack traces are keyed":

  test "each is a different key":
    # An explicit base, so no argument equals this build's own default.
    proc seg(be = "c"; ex = "quirky"; thr = false; st = false; lt = false): string =
      key(buildFlagsSegment(allOn, false, false, "orc", be, ex, thr, st, lt))
    let base = seg()
    check seg(be = "cpp") != base
    check seg(ex = "goto") != base
    check seg(ex = "setjmp") != base
    check seg(ex = "goto") != seg(ex = "setjmp")
    check seg(thr = true) != base
    check seg(st = true) != base
    check seg(lt = true) != base

  test "the default is this build's":
    let seg = buildFlagsSegment()
    check ("+be=cpp" in seg) == defined(cpp)
    check ("+thr" in seg) == compileOption("threads")
    check ("+st" in seg) == compileOption("stackTrace")
    check ("+ex=goto" in seg) == compileOption("exceptions", "goto")

suite "R1-08: the key varies with the build's checks and flags":

  test "each check, turned off, is a different key":
    let base = key(buildFlagsSegment(allOn, false, false, "orc"))
    for c in allOn:
      var less = allOn
      less.delete(less.find(c))
      checkpoint c
      check key(buildFlagsSegment(less, false, false, "orc")) != base

  test "the float checks, turned on, are a different key":
    let base = key(buildFlagsSegment(allOn, false, false, "orc"))
    check key(buildFlagsSegment(allOn & "nanChecks", false, false, "orc")) != base
    check key(buildFlagsSegment(allOn & "infChecks", false, false, "orc")) != base

  test "danger, release and the memory model are each a different key":
    let base = key(buildFlagsSegment(allOn, false, false, "orc"))
    let danger = key(buildFlagsSegment(@[], true, true, "orc"))
    check danger != base
    check key(buildFlagsSegment(allOn, false, true, "orc")) != base
    check key(buildFlagsSegment(allOn, false, false, "refc")) != base
    check key(buildFlagsSegment(@[], false, false, "orc")) != danger

  test "the default is this build's":
    let seg = buildFlagsSegment()
    check ("boundChecks" in seg) == compileOption("boundChecks")
    check ("assertions" in seg) == compileOption("assertions")
    check ("overflowChecks" in seg) == compileOption("overflowChecks")
    check ("+danger" in seg) == defined(danger)
    check ("+mm=orc" in seg) == compileOption("mm", "orc")
    check symexCacheKey(SymexProgram(body: IRStmt(kind: isBlock)),
                        tIndexError(), defaultSymexSettings(), "z", "n", "w",
                        "r", replayMode = "fork") == key(seg)

