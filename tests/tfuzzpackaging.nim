## Phase 7 (docs/fuzz/FUZZ_PLAN.md): packaging. The normative usage guide (docs/fuzz/USAGE.md)
## promises a public surface — `bytes()`, the delivery/oracle built-ins, persistence keying, and
## the corpus-interop helpers. This test pins that surface so the guide can't drift from the API.

import std/[unittest, os, options, strutils]
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
    check fileExists("src/nelli/nelli_shm.c")   # RFC-fuzzer-nextgen E2b: the shm transport

suite "docs/fuzz/INTERFACE.md is checked, not merely asserted (RFC-z3-optional S4)":
  ## INTERFACE.md calls itself normative and says "changes here are spec
  ## changes -- escalate, don't drift". Until this suite, nothing in the tree
  ## referenced it, and it had drifted exactly as that predicts: it still
  ## documented `GuidanceConfig.stallRounds`, a field RFC-z3-optional removed.
  ##
  ## These are compile-level pins on the signatures that file freezes. They
  ## are deliberately shallow -- `compiles(...)` over each documented shape,
  ## not behavior, which the topic suites own. The point is that a signature
  ## change now has to touch this file, which puts INTERFACE.md in the
  ## author's line of sight.

  test "the Z3-free config surface matches INTERFACE.md's Configuration section":
    # GuidanceConfig carries I2S ONLY. The two concolic knobs moved to
    # ConcolicAssist; documenting them here again would be the drift.
    check compiles(GuidanceConfig(enableI2S: true))
    check not compiles(GuidanceConfig(stallRounds: 1))
    check not compiles(GuidanceConfig(concolicMaxBranchAttempts: 8))

    let a = ConcolicAssist(bridge: nil, stallRounds: 1, maxBranchAttempts: 8)
    check a.stallRounds == 1
    check a.maxBranchAttempts == 8
    check a.bridge == nil

  test "the documented loop entry point takes `assist`, and `fuzzWith` still doesn't":
    var frontier = newCoverageFrontier()
    let target = inProcessTarget(proc(x: int) = discard x)
    check compiles(fuzz(just(0), target, frontier, FuzzSettings()))
    check compiles(fuzz(just(0), target, frontier, FuzzSettings(),
                        assist = ConcolicAssist()))
    # The old spelling is gone, not merely discouraged -- an upgrader gets a
    # compile error naming the parameter, which is the whole point of moving
    # it rather than deprecating it.
    check not compiles(fuzz(just(0), target, frontier, FuzzSettings(),
                            concolicBridge = ConcolicBridgeEntry(nil)))

  test "the raw orchestrator seam keeps BOTH knobs, as INTERFACE.md documents":
    # Deliberate asymmetry with the entry point above: at this layer
    # "bridge configured, stallRounds 0 => inert" is the contract, not a bug.
    var frontier = newCoverageFrontier()
    let target = inProcessTarget(proc(x: int) = discard x)
    check compiles(newOrchestrator(just(0), target, frontier,
                                   policy = orchestratorPolicy(stallRounds = 1,
                                                               concolicMaxBranchAttempts = 4),
                                   concolicBridge = ConcolicBridgeEntry(nil)))
    let p = orchestratorPolicy()
    check p.stallRounds == 0
    check p.concolicMaxBranchAttempts == 8

  test "ConcolicAssistError is a public, catchable type":
    check ConcolicAssistError is CatchableError
    var caught = false
    try:
      raise newException(ConcolicAssistError, "x")
    except ConcolicAssistError:
      caught = true
    check caught

suite "the package version has one meaning across all three of its sites (RFC-z3-optional S5)":
  ## `nelliVersion` sat at "0.1.0" through five releases and `milpa.kdl` at
  ## "0.4.0", while `nelli.nimble` alone was kept current -- because the only
  ## test touching any of them asserted `nelliVersion.len > 0`, which is true
  ## of every wrong answer. Three sources of truth with no agreement check is
  ## drift waiting to happen, and it happened.
  ##
  ## Reads the manifests repo-relative, the same way this suite already
  ## checks the vendored C runtime ships, so it runs identically on the
  ## Windows legs.

  test "nelli.nimble, milpa.kdl and nelliVersion all agree":
    proc firstMatch(path, prefix: string): string =
      for line in lines(path):
        let t = line.strip()
        if t.startsWith(prefix):
          # `version       = "0.7.0"` / `version "0.7.0"` -- take what is quoted
          let a = t.find('"')
          let b = t.rfind('"')
          if a >= 0 and b > a:
            return t[a+1 ..< b]
      ""

    let nimbleVersion = firstMatch("nelli.nimble", "version")
    let milpaVersion = firstMatch("milpa.kdl", "version")
    check nimbleVersion.len > 0
    check milpaVersion.len > 0
    check nimbleVersion == nelliVersion
    check milpaVersion == nelliVersion
