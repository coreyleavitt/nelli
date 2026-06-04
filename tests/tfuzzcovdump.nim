## Phase 1b (docs/fuzz/FUZZ_PLAN.md): the real coverage dump runtime
## (src/proptest/proptest_cov.c). Build a TWO-TU instrumented target linked with
## the runtime, run it with $PROPTEST_COV_FILE set, and check the dumped map:
##   - valid wire format (magic / version / len / checksum, D5)
##   - input-sensitive (a branch in TU1 changes the map → multi-TU coverage works)
##   - deterministic (same input → same map)
##   - D7 adversarial: _exit() before dump → NO file (absent, never stale);
##                     SIGSEGV → the signal handler still dumps a VALID map.

import std/[unittest, os, osproc]
import fuzzsupport

const covRuntime = staticRead("../src/proptest/proptest_cov.c")

const tu0main = """
extern int helper(int);
int main(int argc, char** argv){
  int c = (argc > 1) ? argv[1][0] : 0;
  return helper(c);
}
"""
const tu1helper = """
int helper(int c){
  if (c == 'x') return 3;   /* a branch in a SECOND TU — exercises multi-TU coverage */
  return 0;
}
"""

proc le32(s: string; off: int): uint32 =
  uint32(s[off].byte) or (uint32(s[off+1].byte) shl 8) or
  (uint32(s[off+2].byte) shl 16) or (uint32(s[off+3].byte) shl 24)

proc parseCov(raw: string): tuple[ok: bool; version, length: uint32; counters: string] =
  if raw.len < 20 or raw[0..3] != "PCOV": return
  let version = le32(raw, 4)
  let length = le32(raw, 12)
  if raw.len != 16 + int(length) + 4: return
  let counters = raw[16 ..< 16 + int(length)]
  var calc: uint32 = 0
  for ch in counters: calc += uint32(ch.byte)
  if calc != le32(raw, 16 + int(length)): return       # checksum mismatch → torn/poisoned
  (true, version, length, counters)

proc covSig(c: string): uint32 =
  ## A compact FNV-1a signature of the counter bytes, so equality checks don't dump
  ## 64 KB bitmaps into the test log on failure.
  result = 2166136261'u32
  for ch in c: result = (result xor uint32(ch.byte)) * 16777619'u32

var covCounter = 0
proc runCov(bin: string; args: openArray[string]): tuple[exists: bool; raw: string] =
  inc covCounter
  let covFile = getTempDir() / ("ptcov_out_" & $covCounter & ".cov")
  removeFile(covFile)
  putEnv("PROPTEST_COV_FILE", covFile)
  var cmd = quoteShell(bin)
  for a in args: cmd.add " " & quoteShell(a)
  discard execCmdEx(cmd)
  if fileExists(covFile): (true, readFile(covFile)) else: (false, "")

suite "fuzz: coverage dump runtime (Phase 1b)":
  for backend in [cbGcc, cbClang]:
    test "dump is valid, input-sensitive, deterministic — " & $backend:
      if not available(backend): skip()
      else:
        let bin = buildInstrumented(backend, @[tu0main, tu1helper], covRuntime)
        let a = runCov(bin, [])              # default: no branch
        let b = runCov(bin, ["x"])           # takes the TU1 branch
        let a2 = runCov(bin, [])             # repeat of `a`
        check a.exists and b.exists and a2.exists
        let pa = parseCov(a.raw)
        let pb = parseCov(b.raw)
        let pa2 = parseCov(a2.raw)
        check pa.ok and pb.ok and pa2.ok
        check pa.version == 1'u32 and pa.length > 0'u32
        check covSig(pb.counters) != covSig(pa.counters)   # different input → different coverage
        check covSig(pa2.counters) == covSig(pa.counters)  # same input → same coverage (determinism)
        removeDir(bin.parentDir)

  test "_exit() before dump leaves NO file (absent, not stale) — gcc":
    if not available(cbGcc): skip()
    else:
      const exitMain = "#include <unistd.h>\nint main(void){ _exit(0); }\n"
      let bin = buildInstrumented(cbGcc, @[exitMain], covRuntime)
      check not runCov(bin, []).exists       # _exit bypasses atexit → no dump
      removeDir(bin.parentDir)

  test "SIGSEGV target dumps a VALID map via the signal handler — gcc":
    if not available(cbGcc): skip()
    else:
      const segMain = "int main(void){ volatile int* p = 0; return *p; }\n"
      let bin = buildInstrumented(cbGcc, @[segMain], covRuntime)
      let r = runCov(bin, [])
      check r.exists                         # the signal handler dumped
      check parseCov(r.raw).ok               # and it is a valid map, not garbage
      removeDir(bin.parentDir)
