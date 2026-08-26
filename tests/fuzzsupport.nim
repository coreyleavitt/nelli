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
  ## RFC-fuzzer-nextgen E4b/E4c: `buildInstrumented` below always compiles
  ## `nelli_shm.c` (`sys/mman.h`) and the runtime's signal handler
  ## (`unistd.h`, `SIGBUS`) — both POSIX-only. A Windows host's mingw
  ## gcc/clang PASSES the compiler+flag probe (`flagSupported`) but then
  ## fails deep inside the real build on code the probe never touches, so
  ## the platform truth has to be asserted here, not inferred from the
  ## probe — this is the ONE PLACE every caller's `available()`/skip-guard
  ## relies on. Widen this when E4b (Windows shm transport) lands; E4c
  ## un-gates the external tier onto Windows generally.
  when not defined(posix):
    false
  else:
    compilerOf(b).len > 0 and flagSupported(b)

const nelliShmSrc = staticRead("../src/nelli/nelli_shm.c")
  ## RFC-fuzzer-nextgen E2b: `nelli_cov.c` now `extern`s its shm primitives
  ## from a separate `nelli_shm.c` (deliberately dependency-free — no
  ## constructor, no signal handlers — see that file's header for why). A
  ## real external-target build always links both, so `buildInstrumented`
  ## compiles+links it alongside the caller's `nelli_cov.c` source
  ## unconditionally; a caller that never sets `$NELLI_COV_SHM`/calls
  ## `pt_shm_init` never exercises it, and it costs nothing (dead code,
  ## unreferenced statics) when unused.

var ptBuildCtr = 0
proc buildInstrumentedRaw(cc, tag, sancovFlagStr, defineStr: string;
                          tus: seq[string]; runtimeSrc: string): string =
  ## The shared build body: compile each `tus` entry with `sancovFlagStr`,
  ## the runtime WITHOUT it (with `defineStr`), link both against
  ## `nelli_shm.c`, and return the binary path. `buildInstrumented` (the
  ## `CovBackend`-keyed entry point below) and `buildInstrumentedTraceCmp`
  ## (RFC-fuzzer-nextgen G4 C3 — a clang-only flag variant that doesn't fit
  ## the two-value `CovBackend` enum, since gcc has no `trace-cmp` analog)
  ## both delegate here rather than duplicating the compile/link recipe.
  ## Each call gets a unique build dir, so a caller can hold several
  ## distinct binaries at once (differential testing builds two children
  ## side by side).
  inc ptBuildCtr
  let dir = getTempDir() / ("ptcov_build_" & tag & "_" & $ptBuildCtr)
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
    let (o, c) = execCmdEx(cc & " " & sancovFlagStr & " -fno-pie -c " & quoteShell(cpath) & " -o " & quoteShell(opath))
    doAssert c == 0, "instrumented compile (tu" & $i & ") failed:\n" & o
    objs.add opath
  let rtC = dir / "rt.c"
  let rtO = dir / "rt.o"
  writeFile(rtC, runtimeSrc)
  let (ro, rc) = execCmdEx(cc & " " & defineStr & " -fno-pie -c " & quoteShell(rtC) & " -o " & quoteShell(rtO))
  doAssert rc == 0, "runtime compile failed:\n" & ro
  let shmC = dir / "shm.c"
  let shmO = dir / "shm.o"
  writeFile(shmC, nelliShmSrc)
  let (so, sc) = execCmdEx(cc & " -fno-pie -c " & quoteShell(shmC) & " -o " & quoteShell(shmO))
  doAssert sc == 0, "shm runtime compile failed:\n" & so
  let bin = dir / "target"
  let (lo, lc) = execCmdEx(cc & " -no-pie " & (objs & @[rtO, shmO]).map(quoteShell).join(" ") & " -o " & quoteShell(bin))
  doAssert lc == 0, "link failed:\n" & lo
  bin

proc buildInstrumented*(b: CovBackend; tus: seq[string]; runtimeSrc: string): string =
  ## Compile each translation unit in `tus` instrumented, the runtime WITHOUT the
  ## sancov flag (with the backend's define), link, and return the binary path.
  buildInstrumentedRaw(compilerOf(b), $b, sancovFlag(b), runtimeDefine(b), tus, runtimeSrc)

const traceCmpFlag* = "-fsanitize-coverage=inline-8bit-counters,trace-cmp"
  ## RFC-fuzzer-nextgen G4 C3: clang-only — `trace-cmp` has no gcc analog
  ## (gcc's `-fsanitize-coverage=trace-pc` sancov subset never implemented
  ## the `__sanitizer_cov_trace_cmp*`/`_const_cmp*` callbacks), so this is a
  ## flag VARIANT on `cbClang`, not a third `CovBackend` value.

proc traceCmpSupported*(): bool =
  ## Whether this host's clang accepts `traceCmpFlag` — probed the same way
  ## `flagSupported` probes the two `CovBackend` flags, so an environment
  ## without clang (or an old clang predating `trace-cmp`) skips rather
  ## than fails. Same E4b/E4c posix rule as `available` above: the real
  ## build behind this flag is POSIX-only, so this is forced false off
  ## POSIX rather than trusting the flag probe.
  when not defined(posix):
    false
  else:
    let cc = compilerOf(cbClang)
    if cc.len == 0: return false
    let tmp = getTempDir() / "ptcov_probe_tracecmp.c"
    writeFile(tmp, "int main(void){return 0;}\n")
    let obj = tmp & ".o"
    let (_, code) = execCmdEx(cc & " " & traceCmpFlag & " -c " & quoteShell(tmp) & " -o " & quoteShell(obj))
    removeFile(tmp); removeFile(obj)
    code == 0

proc buildInstrumentedTraceCmp*(tus: seq[string]; runtimeSrc: string): string =
  ## `buildInstrumented(cbClang, ...)`'s G4 C3 sibling: same recipe, with
  ## `,trace-cmp` added to the sancov flag so the target's comparison
  ## operators ALSO call `__sanitizer_cov_trace_cmp*`/`_const_cmp*`
  ## (`nelli_cov.c`'s new hooks pick those up and log operand pairs to the
  ## cmp log's shm channel — see that file's G4 C3 comment).
  buildInstrumentedRaw(compilerOf(cbClang), "tracecmp", traceCmpFlag, runtimeDefine(cbClang), tus, runtimeSrc)
