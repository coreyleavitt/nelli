## RFC-fuzzer-nextgen S1: Entropic (information-gain) power schedule + Phase
## 6c corpus minimization. S1 SUBSUMES Phase 6c's opt-in `powerSchedule`
## flag (docs/RFC-fuzzer-nextgen.md Track S/S1): Entropic energy-weighted
## parent selection (`entropicEnergy`, coverage.nim) is now the DEFAULT —
## previously uniform selection was the default and the coarse `+1.0`-
## lineage scheme was opt-in via `powerSchedule`. `uniformSchedule: true` is
## the new opt-out: it reproduces the pre-S1 DEFAULT trajectory byte-for-
## byte (parent selection, mutation, and RNG consumption are all identical
## to the old uniform path — `FrontierStats` bookkeeping still updates, but
## purely as side bookkeeping nothing in the loop reads under this flag),
## kept both for callers/tests that need the old behavior and as Track S's
## ablation-harness uniform baseline (RFC §Evaluation). `minimizeCorpus` is
## untouched by S1 and stays opt-in. Pure — stub Targets, no subprocess.

import std/unittest
import nelli

proc monotoneCoverage(): Target[int] =
  ## Bigger inputs light strictly more edges (x → min(x,64) hot slots), so one
  ## large input subsumes all smaller ones — ideal to expose both features.
  Target[int](run: proc(x: int): Observation[int] =
    let k = max(0, min(x, 64))
    var c = newSeq[byte](64)
    for i in 0 ..< k: c[i] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

const N = 400

suite "fuzz: Entropic power schedule + minimization (RFC-fuzzer-nextgen S1)":
  test "Entropic scheduling (the default) is deterministic in the seed":
    var f1 = newCoverageFrontier()
    var f2 = newCoverageFrontier()
    let a = fuzz(integers(0, 100000), monotoneCoverage(), f1,
                 FuzzSettings(maxIterations: N, seed: 7))
    let b = fuzz(integers(0, 100000), monotoneCoverage(), f2,
                 FuzzSettings(maxIterations: N, seed: 7))
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len

  test "uniformSchedule fallback is deterministic in the seed":
    var f1 = newCoverageFrontier()
    var f2 = newCoverageFrontier()
    let a = fuzz(integers(0, 100000), monotoneCoverage(), f1,
                 FuzzSettings(maxIterations: N, seed: 7, scheduling: SchedulingConfig(uniformSchedule: true)))
    let b = fuzz(integers(0, 100000), monotoneCoverage(), f2,
                 FuzzSettings(maxIterations: N, seed: 7, scheduling: SchedulingConfig(uniformSchedule: true)))
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len

  test "Entropic (default) finds at least as much coverage as the uniform fallback":
    var fe = newCoverageFrontier()
    var fu = newCoverageFrontier()
    let e = fuzz(integers(0, 100000), monotoneCoverage(), fe,
                 FuzzSettings(maxIterations: N, seed: 3))
    let u = fuzz(integers(0, 100000), monotoneCoverage(), fu,
                 FuzzSettings(maxIterations: N, seed: 3, scheduling: SchedulingConfig(uniformSchedule: true)))
    check e.coverageHits > 0
    check e.coverageHits >= u.coverageHits

  test "Entropic scheduling folds FrontierStats via the loop's own admits (no separate bookkeeping)":
    # The loop never recomputes rarity inline — it reads `frontier.stats`,
    # which `admit` (coverage.nim) maintains. A live campaign's frontier
    # should show a fully-populated stats object after a run.
    var f = newCoverageFrontier()
    discard fuzz(integers(0, 100000), monotoneCoverage(), f,
                 FuzzSettings(maxIterations: N, seed: 11))
    check f.stats.totalAdmitted > 0
    check f.stats.hitCount(0) > 0        # slot 0 is hit by every nonzero input

  test "minimization shrinks the corpus while preserving frontier coverage":
    # RFC-fuzzer-nextgen S4: `ffull` needs `uniformCorpus: true` here — this
    # test isolates minimizeCorpus's OWN one-shot end-of-run cover against a
    # corpus that otherwise only ever GROWS. Left at S4's own default,
    # periodic in-campaign culling would (correctly, by its own RFC-S4
    # contract) ALSO collapse this strictly-nested-coverage fixture down to
    # one entry on its own, making the two converge and this comparison
    # meaningless — an unrelated new axis, not a reason to loosen the check
    # (same scoping precedent S3 used on tfuzzbias's boundary test).
    var fmin = newCoverageFrontier()
    var ffull = newCoverageFrontier()
    let m = fuzz(integers(0, 100000), monotoneCoverage(), fmin,
                 FuzzSettings(maxIterations: N, seed: 5, minimizeCorpus: true))
    let f = fuzz(integers(0, 100000), monotoneCoverage(), ffull,
                 FuzzSettings(maxIterations: N, seed: 5, scheduling: SchedulingConfig(uniformCorpus: true)))
    check m.coverageHits == f.coverageHits                 # frontier untouched
    check m.corpus.irEntries.len < f.corpus.irEntries.len  # but the corpus is smaller
    check m.corpus.irEntries.len >= 1
