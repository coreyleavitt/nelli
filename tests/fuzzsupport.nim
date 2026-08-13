## Shared test support for the coverage-fuzzing build (Phase 1a/1b). Builds an
## instrumented external C target under either backend; the sancov runtime is a
## SEPARATE object compiled WITHOUT the flag (see src/nelli/nelli_cov.c and
## docs/fuzz/FUZZ_PLAN.md D1). Not a test itself — imported by t*fuzz* tests.
import std/[os, osproc, strutils, sequtils]

type CovBackend* = enum cbGcc, cbClang

proc compilerOf*(b: CovBackend): string =
  case b
  of cbGcc: findExe("gcc")
  of cbClang: findExe("clang")

proc sancovFlag*(b: CovBackend): string =
  case b
  of cbGcc: "-fsanitize-coverage=trace-pc"
  of cbClang: "-fsanitize-coverage=inline-8bit-counters"

proc runtimeDefine*(b: CovBackend): string =
  case b
  of cbGcc: "-DNELLI_COV_GCC"
  of cbClang: ""

proc noopRuntime*(b: CovBackend): string =
  ## A do-nothing runtime that only resolves the callbacks (Phase 1a).
  case b
  of cbGcc:   "void __sanitizer_cov_trace_pc(void){}\n"
  of cbClang: "void __sanitizer_cov_8bit_counters_init(unsigned char* s, unsigned char* e){}\n"

proc flagSupported*(b: CovBackend): bool =
  let cc = compilerOf(b)
  if cc.len == 0: return false
  let tmp = getTempDir() / ("ptcov_probe_" & $b & ".c")
  writeFile(tmp, "int main(void){return 0;}\n")
  let obj = tmp & ".o"
  let (_, code) = execCmdEx(cc & " " & sancovFlag(b) & " -c " & quoteShell(tmp) & " -o " & quoteShell(obj))
  removeFile(tmp); removeFile(obj)
  code == 0

proc available*(b: CovBackend): bool =
  compilerOf(b).len > 0 and flagSupported(b)

var ptBuildCtr = 0
proc buildInstrumented*(b: CovBackend; tus: seq[string]; runtimeSrc: string): string =
  ## Compile each translation unit in `tus` instrumented, the runtime WITHOUT the
  ## sancov flag (with the backend's define), link, and return the binary path.
  ## Each call gets a unique build dir, so a caller can hold several distinct
  ## binaries at once (differential testing builds two children side by side).
  let cc = compilerOf(b)
  inc ptBuildCtr
  let dir = getTempDir() / ("ptcov_build_" & $b & "_" & $ptBuildCtr)
  removeDir(dir); createDir(dir)
  # -fno-pie/-no-pie: the gcc trace-pc backend hashes absolute return addresses, so
  # the target's code must load at a FIXED address (else ASLR breaks determinism).
  # Harmless for clang's section-index counters. (The general alternative — disabling
  # ASLR per-run in externalTarget — is the Phase-5 story; here we pin it at build.)
  var objs: seq[string]
  for i, src in tus:
    let cpath = dir / ("tu" & $i & ".c")
    let opath = dir / ("tu" & $i & ".o")
    writeFile(cpath, src)
    let (o, c) = execCmdEx(cc & " " & sancovFlag(b) & " -fno-pie -c " & quoteShell(cpath) & " -o " & quoteShell(opath))
    doAssert c == 0, "instrumented compile (tu" & $i & ") failed:\n" & o
    objs.add opath
  let rtC = dir / "rt.c"
  let rtO = dir / "rt.o"
  writeFile(rtC, runtimeSrc)
  let (ro, rc) = execCmdEx(cc & " " & runtimeDefine(b) & " -fno-pie -c " & quoteShell(rtC) & " -o " & quoteShell(rtO))
  doAssert rc == 0, "runtime compile failed:\n" & ro
  let bin = dir / "target"
  let (lo, lc) = execCmdEx(cc & " -no-pie " & (objs & @[rtO]).map(quoteShell).join(" ") & " -o " & quoteShell(bin))
  doAssert lc == 0, "link failed:\n" & lo
  bin
