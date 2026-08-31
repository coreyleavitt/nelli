## F2 (docs/rfc/0001-chapulin-hardening.md ~line 632): up-front coverage-replay pass
## over preloaded seeds. Before F2, a seed added to the working corpus from
## either `FuzzSettings.initialIRCorpus` or the DB's `loadCorpus(testId)`
## (F1's dedicated, never-pruned corpus section) got a zero-value `Coverage`
## in `corpusCov[i]` — real coverage was only ever recorded once (if ever) the
## seed was picked as a mutation *parent* and its *mutant* got run. The seed's
## own coverage was never captured. `minimalCovering` (6c, `fuzz.nim:341`)
## builds its "edges that still need covering" set purely from `corpusCov`, so
## an un-run seed's real edges were invisible to it — `minimizeCorpus` could
## silently drop (or fail to credit) a preloaded/external corpus's seeds,
## which is the opposite of lossless.
##
## F2 fixes this with an up-front pass, right after the initial corpus is
## assembled from seeds (and before the mutation loop starts), that replays
## each seed through the same replay -> generate -> `target.run` path the loop
## already uses per iteration, and folds the result into both `corpusCov[i]`
## and the `CoverageFrontier`. Pure — stub Targets, no subprocess.
##
## These suites use a closed edge-space target (`x mod n` -> hot slot `x mod
## n`) so a single post-seed mutation iteration can never discover an edge
## outside the seeds' own coverage — that makes the minimized-corpus size a
## fully deterministic assertion, not a probabilistic one.

import std/unittest
import nelli
import nelli/choice

proc modCoverage(n: int): Target[int] =
  ## One hot slot per `x mod n` — a closed edge-space, so post-seed mutation
  ## can only ever rediscover an edge some seed already covers, never a new
  ## one. That's what makes "did minimization retain every seed" deterministic.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](n)
    c[((x mod n) + n) mod n] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc seedFor(i: int): seq[ChoiceNode] =
  @[integerChoice(i, 0, 1000, 0)]

suite "F2: up-front coverage-replay of preloaded seeds — lossless minimization":
  test "initialIRCorpus seeds each covering a distinct edge all survive minimizeCorpus":
    const n = 5
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add seedFor(i)
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds,
                              minimizeCorpus: true))
    # Pre-F2, every seed's corpusCov was empty, so minimalCovering's covering
    # set was built from nothing (or, if the one post-seed mutation happened
    # to land new coverage, from that single mutant alone) — the N real seeds
    # would be dropped from the minimized corpus despite each covering a real,
    # otherwise-uncovered edge. F2 makes this lossless: all N survive.
    check r.corpus.irEntries.len == n
    for i in 0 ..< n:
      check seedFor(i) in r.corpus.irEntries

  test "a redundant seed (covers only an already-covered edge) is dropped by minimizeCorpus":
    const n = 3
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add seedFor(i)
    seeds.add seedFor(0)          # redundant: same edge as seed 0
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds,
                              minimizeCorpus: true))
    check r.corpus.irEntries.len == n   # the duplicate contributes no new edge

  test "without minimizeCorpus, preloaded seeds are kept as-is (no dedup)":
    const n = 3
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add seedFor(i)
    seeds.add seedFor(0)
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds))
    check r.corpus.irEntries.len >= n + 1   # all 4 seeds retained, growth possible on top

  test "seed coverage is admitted into the frontier up front: coverageHits reflects it immediately":
    const n = 4
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add seedFor(i)
    var fr = newCoverageFrontier()
    # maxIterations: 1 forces exactly one mutation; the closed edge-space means
    # it can only ever land on an edge the seeds already registered, so
    # coverageHits is pinned at n regardless of what that one mutation does —
    # UNLESS seeds were never admitted to the frontier (the pre-F2 bug), in
    # which case the frontier could start at 0 and only reach n via mutation
    # coincidence, which isn't guaranteed within one iteration.
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds))
    check r.coverageHits == n

  test "DB-resumed seeds (loadCorpus) also get up-front coverage on lossless minimization":
    const n = 4
    let db = inMemoryDatabase()
    let testId = fuzzCorpusKey("camp", "bin1")
    for i in 0 ..< n: db.saveCorpus(testId, seedFor(i))
    var fr = newCoverageFrontier("bin1")
    let r = fuzz(integers(0, 1000), modCoverage(n), fr,
                 FuzzSettings(maxIterations: 1, seed: 1, database: db,
                              persistKey: "camp", minimizeCorpus: true))
    check r.corpus.irEntries.len == n
    for i in 0 ..< n:
      check seedFor(i) in r.corpus.irEntries

  test "no preloaded seeds: behavior is unchanged (single random seed, no up-front replay)":
    # Sanity guard against a regression where F2's pass reaches into the
    # fallback single-random-seed path too. With no initialIRCorpus/DB corpus,
    # the loop still starts from exactly one generated seed and runs on.
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), modCoverage(8), fr,
                 FuzzSettings(maxIterations: 100, seed: 1))
    check r.corpus.irEntries.len >= 1
    check r.iterations == 100

  test "determinism: identical preloaded seeds + identical seed => identical report":
    const n = 5
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< n: seeds.add seedFor(i)
    var fr1 = newCoverageFrontier()
    var fr2 = newCoverageFrontier()
    let s = FuzzSettings(maxIterations: 50, seed: 42, initialIRCorpus: seeds,
                         minimizeCorpus: true)
    let a = fuzz(integers(0, 1000), modCoverage(n), fr1, s)
    let b = fuzz(integers(0, 1000), modCoverage(n), fr2, s)
    check a.iterations == b.iterations
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries == b.corpus.irEntries
