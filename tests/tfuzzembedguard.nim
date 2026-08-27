## Regression guard for `fuzzsupport.embedCSource` (MSVC `error C2026: string
## too big, trailing characters truncated`).
##
## THREE NUMBERS MATTER, and they are different metrics — do not conflate
## them:
##   - 16380: MSVC's cl.exe cap on a single C string literal's SOURCE TOKEN
##     length (counted AFTER escaping — a non-printable/`"`/`\` byte can
##     expand to several emitted characters, so this is not 1:1 with
##     content bytes).
##   - 4095: the C99+ minimum guaranteed translation limit on a string
##     literal's LOGICAL content length (the decoded byte count), which is
##     exactly what GCC's `-Woverlength-strings` warns about. This one IS
##     1:1 with content bytes.
##   - 4000 (`fuzzsupport.embedChunkSize`): the chosen chunk size, kept a
##     bit under 4095. Since 4 * 4095 = 16380 exactly, staying under GCC's
##     4095 content-length limit is a PROOF that the emitted token can never
##     exceed MSVC's 16380 even in the worst-case escape blowup — not a
##     proxy or a guess.
##
## HISTORY (why this file's shape changed): the first fix chunked to 8000
## bytes and joined chunks with Nim's `&` operator. That still failed under
## MSVC (CI run 33027469865, which also broke THIS file — two of its own
## `embedCSource` calls emitted over-long literals): Nim's semantic
## analysis constant-folds a `&`-chain of string LITERALS back into a
## single literal before codegen, regardless of `let` vs `const` —
## foldability is a property of the expression (all-literal `&`), not the
## binding. `embedCSource` now avoids the fold entirely: it emits a `const`
## ARRAY of chunk literals (array construction is not a `&`-fold candidate,
## so each element survives to codegen as its own small literal) and joins
## it with an ordinary runtime `add` loop. See `embedChunkSize`'s doc
## comment in fuzzsupport.nim for the full mechanism.
##
## Nim-level string reasoning (both the old `&`-fold bug and any future
## variant of it) is exactly what escaped detection here before — the
## previous version of this file asserted a hand-rolled escape-length
## estimate against each chunk, which stayed green even while the actual
## compiled C was broken, because the estimate never modeled compiler-level
## constant folding. THE ACTUAL REGRESSION-PROOF LIVES OUTSIDE THIS FILE,
## in the real C toolchain: whenever `embedCSource` or `embedChunkSize`
## changes, compile an affected suite to C ONLY, then compile the
## generated `.c` files DIRECTLY with GCC's overlength-string check turned
## into a hard error, and confirm it stays green:
##
##   podman run --rm -v "$PWD:/work" -w /work localhost/nelli-dev:latest \
##     bash -c 'nim c --compileOnly --hints:off --threads:on \
##       --nimcache:/tmp/owl tests/tfuzzcovdump.nim'
##   podman run --rm -v "$PWD:/work" -v /tmp/owl:/tmp/owl -w /tmp/owl \
##     localhost/nelli-dev:latest \
##     bash -c 'gcc -c -std=c99 -Woverlength-strings -Werror=overlength-strings \
##       -fno-strict-aliasing -pthread -I/opt/nim/2.2.10-patched/lib -I/work \
##       "@mfuzzsupport.nim.c" -o /tmp/discard.o && \
##       gcc -c -std=c99 -Woverlength-strings -Werror=overlength-strings \
##       -fno-strict-aliasing -pthread -I/opt/nim/2.2.10-patched/lib -I/work \
##       "@mtfuzzcovdump.nim.c" -o /tmp/discard.o'
##
## DO NOT just add `--passC:-Woverlength-strings --passC:-Werror=overlength-strings`
## to a normal `nim c -r` invocation and call it proof — this project's
## `nim.cfg`/the compiler's own gcc profile unconditionally appends `-w`
## ("inhibit ALL warning messages") to every C compile, and empirically
## `-w` silently wins over a later explicit `-Werror=overlength-strings` on
## the SAME command line (confirmed by hand: it suppresses the error
## outright, exit 0, no diagnostic — a false negative that would have let
## this exact regression back in). Compiling the generated `.c` file
## directly, outside Nim's own C-invocation step, is the only way to get a
## trustworthy answer.
##
## GCC's 4095 threshold is STRICTER than what MSVC needs (see the 4x-factor
## proof above), so a green compile under `-Werror=overlength-strings` (via
## the direct-gcc method, not `--passC`) is a genuine local proof of
## MSVC-safety, not a proxy. Verified both directions by hand while fixing
## this: the direct-gcc check FAILS (`string length '29451'/'26100' is
## greater than the length '4095'...`) against the old, broken `&`-chain
## macro, and PASSES against the current array/join one, whose longest
## emitted literal across every touched file was 4366 characters —
## comfortably under 16380 and consistent with the 4000-byte chunk size.
##
## What THIS file still usefully guards, without a real toolchain:
##   1. `embedCSource` reproduces the real files byte-for-byte (the
##      chunk/join scheme is content-correct, not just "some string of
##      about the right size").
##   2. every chunk `embedCSource` would actually build from the files ON
##      DISK today stays under both size metrics above, as an early/cheap
##      (but NOT sufficient on its own, per the HISTORY note) tripwire.
##
## Deliberately does NOT `staticRead`/embed either big file a second time
## for the round-trip comparison (that would add its own oversized
## literal) — reads them at RUNTIME instead via `readFile`, relative to
## this file's own compile-time location.

import std/[unittest, os]
import fuzzsupport

proc srcSibling(relPath: string): string =
  ## Resolve `relPath` (e.g. "../src/nelli/nelli_cov.c") the same way
  ## `staticRead`/`embedCSource` resolve their path argument: relative to
  ## THIS file's own directory, not the process's current working
  ## directory (which the MSVC CI runner sets to the repo root, not tests/).
  parentDir(currentSourcePath()) / relPath

suite "fuzzsupport: embedCSource (chunked embed, MSVC C2026 guard)":
  test "embedCSource(nelli_cov.c) reproduces the file byte-for-byte and actually chunks it":
    let embedded = embedCSource("../src/nelli/nelli_cov.c")
    let onDisk = readFile(srcSibling("../src/nelli/nelli_cov.c"))
    check embedded == onDisk
    # Sanity: this file is well over embedChunkSize, so a correct macro MUST
    # have split it into more than one array element — a passing round-trip
    # with only one chunk would mean the chunking loop silently never ran.
    check onDisk.len > embedChunkSize

  test "embedCSource(nelli_shm.c) reproduces the file byte-for-byte and actually chunks it":
    let embedded = embedCSource("../src/nelli/nelli_shm.c")
    let onDisk = readFile(srcSibling("../src/nelli/nelli_shm.c"))
    check embedded == onDisk
    check onDisk.len > embedChunkSize

  test "every chunk embedCSource would build from the files on disk stays under both size metrics (cheap tripwire, not a substitute for the GCC flag-compile above)":
    for relPath in ["../src/nelli/nelli_cov.c", "../src/nelli/nelli_shm.c"]:
      let content = readFile(srcSibling(relPath))
      var i = 0
      while i < content.len:
        let e = min(i + embedChunkSize, content.len)
        let chunk = content[i ..< e]
        check chunk.len <= 4095                       # GCC/ISO content-length limit
        check embedWorstCaseEscapedLen(chunk) < 16380  # MSVC token-length cap
        i = e
