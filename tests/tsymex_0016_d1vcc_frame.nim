## RFC-0016 D1 (stack): an entry macro's IR is built in a frame of its own.
##
## `symexFind` and its siblings used to build the IR constructor inline, so a
## module top level with many calls put every expansion's temporaries into one
## C function, `NimMainModule`. An MSVC debug build gives each temporary its
## own slot: `tsymex_0016_k4a_dispatch` (91 sites, one file then) overran the
## 1 MB reserve of a Windows main thread (0xC00000FD).
##
## The probe `s0016_d1vcc_probe` is that shape: 16 `symexFind` sites at the top
## level over a 24-routine SUT. It is built in a child and
##   * structurally: `NimMainModule` calls an `irBuild` proc per site and holds
##     no `RoutineArithFacts` / `stampFor` of its own;
##   * behaviourally: it is run with a main stack of `probeStackKb` and must not
##     die of it.
##
## The stack bound, from the requirement (the 1 MB Windows reserve):
##   * MSVC debug frames run about 5.3x gcc's: k4a's `NimMainModule` is 193 KB
##     at gcc -O0 and just under 1 MB at MSVC.
##   * so a site may cost 1024 KB / 91 sites / 5.3 = 2.1 KB of gcc frame, and
##     16 sites 34 KB;
##   * the runtime itself needs a base: measured, the probe runs at 128 KB and
##     dies at 96 KB;
##   * 128 + 34 = 162, rounded down to 160.
## Measured at the fix: frame 9.6 KB (needs ~138 KB), against 58.7 KB inline
## (needs ~187 KB), so the bound sits between the two with 20 KB either side.
import std/[unittest, os, osproc, strutils]
import ./probe_build   # the child build alone: the engine is the probe's, not this suite's

# The C++ backend's frames are larger: measured at the fix, the builder build
# runs down to about 160 KB and dies below it, the inline one needs 256 KB; the
# bound sits between them (c: 138 vs 187, see above).
const probeStackKb = hostStackBoundKb(defined(cpp), 160, 192, 16, 1024)
  ## c 160 / cpp 192 at gcc. On MSVC the same model is re-derived (see
  ## `stackBoundKb`): 128 + 16 * 1024 / 91 = 308, rounded down to 304 (c), 336
  ## (cpp). Builder needs about 128 + 9.6 * 5.3 = 179 there, the inline shape
  ## about 128 + 58.7 * 5.3 = 439, so 304 keeps over 120 KB either side.

proc mainModuleBody(c: string): string =
  ## The text of the C function `NimMainModule`: to the next declaration at
  ## column 0 (its own body has nested braces at column 0, so the first
  ## closing one is not its end).
  let at = c.find("NimMainModule)(void) {")
  doAssert at >= 0, "the probe's C has no NimMainModule"
  var stop = -1
  for marker in ["\nN_LIB_PRIVATE", "\nN_CDECL", "\nN_NIMCALL", "\nstatic ",
                 "\nextern "]:
    let m = c.find(marker, at + 1)
    if m >= 0 and (stop < 0 or m < stop): stop = m
  c[at ..< (if stop < 0: c.len else: stop)]

suite "RFC-0016 D1: the IR is built outside the caller's frame":
  test "a top level of symexFind sites builds each IR in its own proc":
    let pb = prepareProbe("d1vcc", "tests" / "s0016_d1vcc_probe.nim",
                          hostStackLinkFlags(probeStackKb))
    defer: removeDir(pb.dir)
    let (cout, crc) = execCmdEx(pb.cmd)
    if crc != 0: checkpoint cout
    require crc == 0
    var main = ""
    # The probe's own module, whatever the child named it (`probe_src.nim` when
    # it was copied into the temp dir, as on Windows): the one that defines
    # `NimMainModule`.
    for f in walkFiles(pb.dir / "cache" / "*"):
      if f.endsWith(".nim.c") or f.endsWith(".nim.cpp"):
        let c = readFile(f)
        if "NimMainModule)(void) {" in c: main = mainModuleBody(c)
    require main.len > 0
    # Structural: one builder call per site, and no IR facts built inline.
    let builders = main.count("irBuild__")
    let inlineFacts = "RoutineArithFacts" in main or "stampFor" in main
    check builders == 16
    check not inlineFacts

    # Behavioural: the child runs on a reduced main stack and does not die of
    # it (a stack overflow is a signal exit on POSIX, 0xC00000FD on Windows;
    # both are rc >= 128). The bound is `ulimit -s` on POSIX and the link-time
    # reserve elsewhere, see `stackLinkFlags` (it is in the probe's build above).
    let (o, rc) = runBoundedStack(pb.exe, probeStackKb)
    checkpoint o[0 ..< min(o.len, 400)]
    check rc < 128

  test "the bound is built faithfully for every OS and compiler":
    check stackBoundKb(false, false, false, 160, 192, 16, 1024) == 160
    check stackBoundKb(false, false, true, 160, 192, 16, 1024) == 192
    check stackBoundKb(true, false, false, 160, 192, 16, 1024) == 160
    check stackBoundKb(true, true, false, 160, 192, 16, 1024) == 304
    check stackBoundKb(true, true, true, 160, 192, 16, 1024) == 336
    check stackLinkFlags(false, false, 160).len == 0
    check stackLinkFlags(true, false, 160) == @["--passL:-Wl,--stack,163840"]
    check stackLinkFlags(true, true, 304) == @["--passL:/F311296"]
    check stackRunCommand(true, "C:\\t\\probe.exe", 160) ==
      (exe: "C:\\t\\probe.exe", args: newSeq[string]())
    let p = stackRunCommand(false, "/t/probe", 160)
    check p.exe == "sh"
    check p.args == @["-c", "ulimit -s 160 && exec \"$0\"", "/t/probe"]
