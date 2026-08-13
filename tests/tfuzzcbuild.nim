## Phase 1a (docs/fuzz/FUZZ_PLAN.md): prove nelli's test harness can build +
## run an instrumented EXTERNAL C target. Net-new machinery — nelli had no
## C-compilation and no subprocess use in its tests before this. The build helpers
## live in fuzzsupport.nim; this just exercises the dual backend at the smallest
## scope. A backend whose compiler or sancov flag is absent is skipped, never failed.

import std/[unittest, os, osproc]
import fuzzsupport

const branchTarget = """
int main(int argc, char** argv) {
  if (argc > 1 && argv[1][0] == 'x') return 3;   /* a branch coverage will differ on */
  return 0;
}
"""

suite "fuzz: instrumented-C build + run scaffold (Phase 1a)":
  test "at least one coverage backend is available":
    # gcc is always present in the stock nimlang image, so the scaffold can
    # actually exercise something (not every backend skipped).
    check (available(cbGcc) or available(cbClang))

  for backend in [cbGcc, cbClang]:
    test "build & run an instrumented C target — " & $backend:
      if not available(backend):
        skip()
      else:
        let bin = buildInstrumented(backend, @[branchTarget], noopRuntime(backend))
        let (_, code0) = execCmdEx(quoteShell(bin))
        check code0 == 0                       # default path
        let (_, code3) = execCmdEx(quoteShell(bin) & " x")
        check code3 == 3                       # the branch was taken
        removeDir(bin.parentDir)
