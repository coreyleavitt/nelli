## Phase 6c (docs/fuzz/FUZZ_PLAN.md): power schedule + corpus minimization. Both opt-in, so
## the default loop (and tfuzzir) is untouched. Power scheduling biases parent selection toward
## coverage-growing lineages; minimization reduces the reported corpus to a minimal covering
## subset without losing frontier coverage. Pure — stub Targets, no subprocess.

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

suite "fuzz: power schedule + minimization (Phase 6c)":
  test "power scheduling is deterministic in the seed":
    var f1 = newCoverageFrontier()
    var f2 = newCoverageFrontier()
    let a = fuzz(integers(0, 100000), monotoneCoverage(), f1,
                 FuzzSettings(maxIterations: N, seed: 7, powerSchedule: true))
    let b = fuzz(integers(0, 100000), monotoneCoverage(), f2,
                 FuzzSettings(maxIterations: N, seed: 7, powerSchedule: true))
    check a.coverageHits == b.coverageHits
    check a.corpus.irEntries.len == b.corpus.irEntries.len

  test "power scheduling finds at least as much coverage as uniform":
    var fp = newCoverageFrontier()
    var fu = newCoverageFrontier()
    let p = fuzz(integers(0, 100000), monotoneCoverage(), fp,
                 FuzzSettings(maxIterations: N, seed: 3, powerSchedule: true))
    let u = fuzz(integers(0, 100000), monotoneCoverage(), fu,
                 FuzzSettings(maxIterations: N, seed: 3))
    check p.coverageHits > 0
    check p.coverageHits >= u.coverageHits

  test "minimization shrinks the corpus while preserving frontier coverage":
    var fmin = newCoverageFrontier()
    var ffull = newCoverageFrontier()
    let m = fuzz(integers(0, 100000), monotoneCoverage(), fmin,
                 FuzzSettings(maxIterations: N, seed: 5, minimizeCorpus: true))
    let f = fuzz(integers(0, 100000), monotoneCoverage(), ffull,
                 FuzzSettings(maxIterations: N, seed: 5))
    check m.coverageHits == f.coverageHits                 # frontier untouched
    check m.corpus.irEntries.len < f.corpus.irEntries.len  # but the corpus is smaller
    check m.corpus.irEntries.len >= 1
