## F7 (docs/rfc/0001-chapulin-hardening.md ~line 638): surface `captureIR`'s
## dropped-seed count in `FuzzReport`.
##
## `fuzz`'s two preloaded-seed loops (`FuzzSettings.initialIRCorpus`, and any
## corpus resumed from the `ExampleDatabase` via `loadCorpus`) each replay a
## seed's choice sequence through the strategy via `captureIR`. Per the
## "2N+1" draw-order protocol documented on `lists` (`strategy.nim`), replay
## consumes one `ChoiceNode` per primitive draw the strategy performs —
## including forced boundary booleans — and raises `Overrun` (`captureIR`
## returns `ok: false`) when the sequence runs out early or a node's `kind`
## doesn't match what the current draw expects. Before F7, such a seed was
## silently dropped; `FuzzReport.droppedSeeds` now counts it.
##
## These suites use a closed edge-space target (`x mod n` -> hot slot `x mod
## n`), mirroring `tfuzzseedcov`, and are driven by stub `Target`s — pure, no
## subprocess.

import std/unittest
import nelli
import nelli/choice

proc modCoverage(n: int): Target[int] =
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](n)
    c[((x mod n) + n) mod n] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc goodSeed(i: int): seq[ChoiceNode] =
  ## A well-formed seed for `integers(0, 1000)`: exactly the one `ckInteger`
  ## node that strategy's `run` closure draws.
  @[integerChoice(i, 0, 1000, 0)]

proc kindMismatchSeed(): seq[ChoiceNode] =
  ## `integers(0, 1000)` draws a `ckInteger` first; a `ckBoolean` node in
  ## that slot triggers `takeReplay`'s "choice kind mismatch during replay"
  ## -> `Overrun` -> `captureIR` returns `ok: false`.
  @[booleanChoice(true, 0.5)]

proc emptySeed(): seq[ChoiceNode] =
  ## `integers(0, 1000)` needs one draw; an empty sequence triggers
  ## `takeReplay`'s "choice sequence exhausted" -> `Overrun`.
  @[]

suite "F7: FuzzReport.droppedSeeds — captureIR-dropped preloaded seeds":
  test "initialIRCorpus: misaligned seeds are dropped and counted; good seeds still populate the corpus":
    const n = 4
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add goodSeed(i)
    seeds.add kindMismatchSeed()
    seeds.add emptySeed()
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds))
    check r.droppedSeeds == 2
    for i in 0 ..< n:
      check goodSeed(i) in r.corpus.irEntries

  test "all-valid seeds: droppedSeeds == 0":
    const n = 5
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add goodSeed(i)
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds))
    check r.droppedSeeds == 0

  test "no preloaded seeds: droppedSeeds == 0 (the generated fallback seed doesn't count)":
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(8), fr,
                 FuzzSettings(maxIterations: 10, seed: 1))
    check r.droppedSeeds == 0
    check r.corpus.irEntries.len >= 1

  test "DB-resumed seeds (loadCorpus) are also captureIR-checked and counted":
    const n = 3
    let db = inMemoryDatabase()
    let testId = fuzzCorpusKey("camp", "bin1")
    for i in 0 ..< n: db.saveCorpus(testId, goodSeed(i))
    db.saveCorpus(testId, kindMismatchSeed())
    var fr = newCoverageFrontier("bin1")
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, database: db,
                              persistKey: "camp"))
    check r.droppedSeeds == 1
    for i in 0 ..< n:
      check goodSeed(i) in r.corpus.irEntries

  test "both initialIRCorpus and DB-resumed drops accumulate into one count":
    const n = 2
    let db = inMemoryDatabase()
    let testId = fuzzCorpusKey("camp2", "bin2")
    db.saveCorpus(testId, goodSeed(0))
    db.saveCorpus(testId, emptySeed())
    var seeds = @[goodSeed(1), kindMismatchSeed()]
    var fr = newCoverageFrontier("bin2")
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, database: db,
                              persistKey: "camp2", initialIRCorpus: seeds))
    check r.droppedSeeds == 2

  test "determinism: identical preloaded seeds + identical settings => identical droppedSeeds":
    const n = 3
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add goodSeed(i)
    seeds.add kindMismatchSeed()
    var fr1 = newCoverageFrontier()
    var fr2 = newCoverageFrontier()
    let s = FuzzSettings(maxIterations: 25, seed: 7, initialIRCorpus: seeds)
    let a = fuzz(integers(0, 1000), modCoverage(n), fr1, s)
    let b = fuzz(integers(0, 1000), modCoverage(n), fr2, s)
    check a.droppedSeeds == b.droppedSeeds
    check a.droppedSeeds == 1
