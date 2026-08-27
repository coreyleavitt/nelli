## Shared test support for the coverage-fuzzing build (Phase 1a/1b). Builds an
## instrumented external C target under either backend; the sancov runtime is a
## SEPARATE object compiled WITHOUT the flag (see src/nelli/nelli_cov.c and
## docs/fuzz/FUZZ_PLAN.md D1). Not a test itself — imported by t*fuzz* tests.
import std/[os, osproc, strutils, sequtils, macros]

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
  ## `nelli_shm.c` and the runtime's crash-detection hook (POSIX signals /
  ## Windows `SetUnhandledExceptionFilter`) — both of which USED to be
  ## POSIX-only (`sys/mman.h`, `unistd.h`+`SIGBUS`), which is why this used
  ## to hardcode `false` off `defined(posix)` regardless of what the flag
  ## probe below said: a Windows host's mingw gcc/clang PASSED
  ## `flagSupported` but then failed deep inside the real build on code the
  ## probe never touched.
  ##
  ## E4b gave `nelli_shm.c` a `_WIN32` arm (`CreateFileMapping`/
  ## `MapViewOfFile`); E4c gave `nelli_cov.c` (this file's own `rt.c`, per
  ## `buildInstrumentedRaw`) one too (`SetUnhandledExceptionFilter` in place
  ## of the POSIX signal handlers, portable `_open`/`_write`/`_close` file
  ## I/O in place of `<unistd.h>`) — the real build this probe stands in for
  ## no longer has ANY POSIX-only code path, so the platform hardcode is
  ## gone: this is back to the plain probe-don't-assume discipline
  ## `flagSupported` already embodies (compiler present, flag accepted) —
  ## trusted on EVERY platform now, including the WINDOWS CI runner (which
  ## carries both gcc and clang, per the fuzzer-windows leg's own toolchain).
  compilerOf(b).len > 0 and flagSupported(b)

const embedChunkSize* = 8000
  ## MSVC's cl.exe caps a single C string literal at 16380 bytes
  ## (`error C2026: string too big, trailing characters truncated`). Nim's
  ## C backend emits a `staticRead`/`const string` result as ONE C string
  ## literal, so any embedded source file anywhere near that size blows the
  ## cap under `--cc:vcc` — GCC/mingw has no such limit, which is exactly
  ## why every prior (GCC-only) CI leg missed this. `nelli_cov.c` (26100
  ## bytes) and `nelli_shm.c` (29451 bytes) both exceed it.
  ##
  ## Nim's C-emission escaping EXPANDS bytes (a non-printable/`"`/`\` source
  ## byte becomes a multi-character escape sequence in the emitted C
  ## literal), so the byte budget here is NOT 1:1 with source bytes. Using a
  ## conservative worst case (every escaped byte costs 4 emitted
  ## characters), an 8000-byte chunk of the two real files above emits at
  ## most ~8680 characters — comfortably under 16380 with ~45% headroom to
  ## spare. 8000 is chosen to keep that headroom generous rather than
  ## shaving it close to the cap; `embedCSource` below asserts this bound
  ## holds for every chunk it actually produces, so a future oversized
  ## source file (or a careless change to this constant) fails the BUILD,
  ## not silently at MSVC link/compile time in CI.

proc embedWorstCaseEscapedLen*(chunk: string): int =
  ## Conservative (over-)estimate of how many characters `chunk` could
  ## occupy once Nim emits it as a C string literal: printable, non-special
  ## ASCII costs 1 emitted char; `"`/`\` cost 2 (`\"`/`\\`); everything else
  ## (control bytes, high bytes) is bounded at 4 (covers `\ooo`-style octal
  ## and `\xHH`-style hex escapes, whichever Nim's cgen actually uses) —
  ## real output is never larger than this, so a chunk passing this check
  ## can never trip MSVC's C2026 regardless of the exact escaping scheme.
  for c in chunk:
    let b = ord(c)
    if b == ord('"') or b == ord('\\'): result += 2
    elif b >= 0x20 and b <= 0x7E: result += 1
    else: result += 4

macro embedCSource*(path: static string): untyped =
  ## Compile-time chunked replacement for `const x = staticRead(path)`.
  ## Reads `path` (resolved relative to THIS file, tests/ — same base every
  ## existing call site already used) at macro-expansion time and emits a
  ## `&`-chain of sub-`embedChunkSize` string literals instead of one
  ## literal spanning the whole file, so no single emitted C literal can
  ## ever reach MSVC's 16380-byte cap.
  ##
  ## Callers MUST bind the result with `let`, not `const`: a `const`
  ## initializer is fully constant-folded by Nim, which collapses this
  ## whole `&`-chain back into ONE string value before codegen — reproducing
  ## exactly the oversized single literal this macro exists to avoid. `let`
  ## keeps the chain as a runtime concatenation (each chunk its own small
  ## literal, joined by `&` calls at load time), which is fine for every
  ## known call site — all of them consume the result at runtime (compiling
  ## test C sources, writing them to disk), never at compile time.
  let content = staticRead(path)
  var chunks: seq[string]
  var i = 0
  while i < content.len:
    let e = min(i + embedChunkSize, content.len)
    chunks.add content[i ..< e]
    i = e
  if chunks.len == 0:
    chunks.add ""
  for c in chunks:
    doAssert c.len <= embedChunkSize,
      "embedCSource: chunk exceeds embedChunkSize (" & $embedChunkSize &
      ") for " & path & " — chunking logic is broken"
    doAssert embedWorstCaseEscapedLen(c) < 16380,
      "embedCSource: chunk of " & path & " could emit a C literal at or " &
      "over MSVC's 16380-byte C2026 cap even in the worst escaping case " &
      "(" & $embedWorstCaseEscapedLen(c) & " estimated chars) — shrink embedChunkSize"
  result = newLit(chunks[0])
  for j in 1 ..< chunks.len:
    result = infix(result, "&", newLit(chunks[j]))

let nelliShmSrc = embedCSource("../src/nelli/nelli_shm.c")
  ## RFC-fuzzer-nextgen E2b: `nelli_cov.c` now `extern`s its shm primitives
  ## from a separate `nelli_shm.c` (deliberately dependency-free — no
  ## constructor, no signal handlers — see that file's header for why). A
  ## real external-target build always links both, so `buildInstrumented`
  ## compiles+links it alongside the caller's `nelli_cov.c` source
  ## unconditionally; a caller that never sets `$NELLI_COV_SHM`/calls
  ## `pt_shm_init` never exercises it, and it costs nothing (dead code,
  ## unreferenced statics) when unused. `let`, not `const` — see
  ## `embedCSource`'s doc comment for why it must stay a runtime value.

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
  ## than fails. RFC-fuzzer-nextgen E4c: the real build behind this flag
  ## (`buildInstrumentedTraceCmp`, which links the SAME `nelli_cov.c`/
  ## `nelli_shm.c` pair `available` above now trusts on every platform) is
  ## no longer POSIX-only either — see that proc's doc comment for what
  ## changed. Widened the same way: plain flag-probe result, no platform
  ## hardcode.
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
