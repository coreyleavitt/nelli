## Regression guard for `fuzzsupport.embedCSource` (MSVC `error C2026: string
## too big, trailing characters truncated`). MSVC's cl.exe caps a single C
## string literal at 16380 bytes; Nim's C backend emits a `staticRead`/`const
## string` result as ONE literal, so embedding `src/nelli/nelli_cov.c`
## (26100 bytes) or `src/nelli/nelli_shm.c` (29451 bytes) as a plain `const`
## blew that cap under `--cc:vcc` (5 `tfuzz*` suites failed CI run
## 33026020686) even though GCC/mingw — which has no such limit — never
## noticed. `embedCSource` fixes this by chunking at macro-expansion time and
## joining sub-`embedChunkSize` literals with runtime `&`, bound via `let`
## (never `const`, which would re-fold the chunks into one oversized
## literal again).
##
## `embedCSource` itself asserts its own bound (`embedWorstCaseEscapedLen`)
## at EVERY call site's compile time, so a careless bump to `embedChunkSize`
## already fails the build everywhere it's used. This file adds two things
## that those per-site asserts don't cover on their own:
##   1. a content-independent worst case (every byte forced through the
##      most expensive escape) — proves the bound holds even for a future
##      embedded file with different (less printable-ASCII-heavy) content;
##   2. a byte-for-byte round trip against the real oversized files, proving
##      the chunk/join scheme reproduces the source exactly, not just
##      "some string of the right rough shape".
##
## Deliberately does NOT `staticRead`/embed either big file directly for the
## round-trip comparison (that would reintroduce the exact C2026 literal
## this test exists to guard against) — it reads them at RUNTIME instead via
## `readFile`, relative to this file's own compile-time location.

import std/[unittest, os]
import fuzzsupport

proc srcSibling(relPath: string): string =
  ## Resolve `relPath` (e.g. "../src/nelli/nelli_cov.c") the same way
  ## `staticRead`/`embedCSource` resolve their path argument: relative to
  ## THIS file's own directory, not the process's current working
  ## directory (which the MSVC CI runner sets to the repo root, not tests/).
  parentDir(currentSourcePath()) / relPath

suite "fuzzsupport: embedCSource (chunked embed, MSVC C2026 guard)":
  test "every real chunk of nelli_cov.c/nelli_shm.c stays under MSVC's 16380-byte cap":
    # Mirrors embedCSource's own internal per-call doAssert, but against the
    # files as they exist ON DISK right now, read at RUNTIME (not
    # re-embedded) — a standalone check that doesn't depend on the macro's
    # internal assert having fired during THIS compile (e.g. if a future
    # refactor moved that assert or changed how errors surface).
    for relPath in ["../src/nelli/nelli_cov.c", "../src/nelli/nelli_shm.c"]:
      let content = readFile(srcSibling(relPath))
      var i = 0
      while i < content.len:
        let e = min(i + embedChunkSize, content.len)
        let chunk = content[i ..< e]
        check embedWorstCaseEscapedLen(chunk) < 16380
        i = e

  test "embedCSource(nelli_cov.c) reproduces the file byte-for-byte and actually chunks it":
    let embedded = embedCSource("../src/nelli/nelli_cov.c")
    let onDisk = readFile(srcSibling("../src/nelli/nelli_cov.c"))
    check embedded == onDisk
    # Sanity: this file is well over embedChunkSize, so a correct macro MUST
    # have split it into more than one literal — a passing round-trip with
    # only one chunk would mean the chunking loop silently never ran.
    check onDisk.len > embedChunkSize

  test "embedCSource(nelli_shm.c) reproduces the file byte-for-byte and actually chunks it":
    let embedded = embedCSource("../src/nelli/nelli_shm.c")
    let onDisk = readFile(srcSibling("../src/nelli/nelli_shm.c"))
    check embedded == onDisk
    check onDisk.len > embedChunkSize
