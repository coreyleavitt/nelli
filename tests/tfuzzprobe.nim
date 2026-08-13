## Phase 3 (docs/fuzz/FUZZ_PLAN.md): CoverageProbe — read a finished run's map.
## `inProcessProbe` snapshots the {.cover.} bitmap (resetsPerRun); `sancovFileProbe`
## parses a child's dumped sancov file (D5: raise on garbage, absent → empty, D7).
## The sancov fixtures are generated LIVE from the Phase-1b runtime (no checked-in blob).

import std/[unittest, os, osproc]
import nelli
import fuzzsupport

const covRuntime = staticRead("../src/nelli/nelli_cov.c")
const branchTarget = """
int main(int argc, char** argv){
  if (argc > 1 && argv[1][0] == 'x') return 3;
  return 0;
}
"""

proc classify(n: int): string {.cover.} =
  if n < 0: "neg"
  elif n == 0: "zero"
  else: "pos"

suite "fuzz: CoverageProbe (Phase 3)":
  test "inProcessProbe snapshots the {.cover.} bitmap (resetsPerRun)":
    let probe = inProcessProbe()
    check probe.resetsPerRun
    setCoverageMode(cmRecording)
    resetCoverage()
    discard classify(-1)
    discard classify(7)
    let cov = probe.read()
    setCoverageMode(cmOff)
    check cov.counters.len == 8192             # the full bitmap
    var hit = 0
    for b in cov.counters:
      if b > 0'u8: inc hit
    check hit > 0                              # the branches recorded edges
    var f = newCoverageFrontier()
    check f.admit(cov).interesting            # and it feeds the frontier

  test "parseCoverageMap raises on malformed input":
    expect ValueError: discard parseCoverageMap("not a coverage map at all")
    expect ValueError: discard parseCoverageMap("PCOV\1\0\0\0")           # too short
    # right magic + version, but a length that doesn't match the body
    expect ValueError:
      discard parseCoverageMap("PCOV\1\0\0\0\0\0\0\0\xff\xff\xff\xff")

  test "sancovFileProbe: absent → empty; garbage → raises; live dump parses":
    let absentPath = getTempDir() / "ptprobe_absent.cov"
    removeFile(absentPath)
    check sancovFileProbe(absentPath).read().counters.len == 0   # absent ≠ stale

    let garbagePath = getTempDir() / "ptprobe_garbage.cov"
    writeFile(garbagePath, "PCOVnnnnnnnnnnnnnnnnnnnn")           # valid magic, bad rest
    expect ValueError: discard sancovFileProbe(garbagePath).read()
    removeFile(garbagePath)

    for backend in [cbGcc, cbClang]:
      if not available(backend): continue
      let bin = buildInstrumented(backend, @[branchTarget], covRuntime)
      let covFile = getTempDir() / ("ptprobe_live_" & $backend & ".cov")
      removeFile(covFile)
      putEnv("NELLI_COV_FILE", covFile)
      discard execCmdEx(quoteShell(bin) & " x")
      let probe = sancovFileProbe(covFile)
      check (not probe.resetsPerRun)
      check probe.read().counters.len > 0     # a valid, non-empty live map
      removeDir(bin.parentDir)
      removeFile(covFile)
