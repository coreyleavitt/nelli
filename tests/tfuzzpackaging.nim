## Phase 7 (docs/fuzz/FUZZ_PLAN.md): packaging. The normative usage guide (docs/fuzz/USAGE.md)
## promises a public surface — `bytes()`, the delivery/oracle built-ins, persistence keying, and
## the corpus-interop helpers. This test pins that surface so the guide can't drift from the API.

import std/[unittest, os, options]
import nelli

suite "fuzz: packaging surface (Phase 7)":
  test "bytes() honors its length bounds":
    var s = defaultSettings()
    let r = forAll(bytes(2, 6), (proc(x: seq[byte]) = ensure x.len >= 2 and x.len <= 6), s)
    check r.outcome == otPassed

  test "the documented public API resolves and composes":
    # input delivery + oracle built-ins (D13/D14)
    let d = argvFileDelivery(".nim")
    let o = sanitizerOracle[seq[byte]]()
    discard d; discard o
    # persistence key (6b)
    check fuzzCorpusKey("camp", "v1") == "camp#v1"
    # corpus interop round-trip (6d)
    let dir = getTempDir() / "ptpkg_corpus"
    removeDir(dir)
    exportCorpusDir(dir, @[@[1'u8, 2, 3]])
    check importCorpusDir(dir).len == 1
    removeDir(dir)
    # replayInput recovers a value from choice-IR (backs exportCrashes)
    check replayInput(just(@[9'u8]), @[]).isSome

  test "the vendored runtime ships with the package":
    check fileExists("src/nelli/nelli_cov.c")
