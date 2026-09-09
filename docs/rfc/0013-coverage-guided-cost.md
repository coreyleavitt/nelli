# RFC — coverage-guided `forAll` pays O(edges) per example

- **Status:** seed — composed 2026-09-09 from a downstream regression report
  with a bisected first-bad commit. The mechanism is identified and the fix
  has a real design choice in it; nothing is designed yet.
- Category: core
- Size: S
- Value: high
- **Depends on:** none.

## §0 — Thesis

`forAll` with `Settings.coverageGuided = true` snapshots, scores and folds the
entire coverage bitmap **on every property call**. It used to compute a scalar
delta. Nobody measured the difference.

Per call, today (`engine.nim`, the `coverageGuided` wrapper):

```nim
let cov = snapshotCoverage()            # newSeq[uint8](edgeCount) + full copy
let value = score(covFrontier, cov)     # full pass over every edge
discard admit(covFrontier, cov)         # second full pass
```

Three O(edges) passes and one O(edges) heap allocation per example, where the
retired code read a counter and subtracted. For a binary with a large counter
array and a few hundred examples per property, that is the dominant cost of
the run.

This is not a defect of the change that introduced it — it is a cost nobody
priced. Which is why it wants a design pass rather than a revert; see §2.

## §1 — Evidence

**Origin.** `1b804311` (2026-08-26), *"feat(fuzzer): U1 C2 — route forAll
coverageGuided onto CoverageFrontier"*, RFC-0003 fuzzer-nextgen Track U. It
retired an ad hoc `currentCoverage()`-before/after scalar delta and routed the
`forAll` path onto the same bucketed `CoverageFrontier` model `fuzz.nim` uses.

Its commit message argues carefully that the new computation is *numerically
equivalent* to the old one for every existing scenario, and proves it by
keeping the `tcovguided` suite green unmodified. That argument is sound and
still holds. It is also entirely a **correctness** argument — the message says
nothing about cost, and no benchmark gated the change. The suite could not have
caught this: it asserts values, and the values did not move.

**Report.** From the downstream consumer `sello`, whose property suites set
`coverageGuided = true` as a standing convention (its RFC-002 slice 3 item 3),
so every property job pays this cost:

| job | duration |
|---|---|
| `property-linux-amd64-gcc` | 15.62 min |
| `property-linux-amd64-clang` | 15.38 min |
| `property-linux-arm64-gcc` | 17.25 min |
| `coverage-ratchet` (full unit + property + coverage instrumentation) | 31.12 min |

against a previously documented ceiling of ~9.5 min for the same jobs. The
same shape reproduced on clean GitHub-hosted runners, which rules out local
host contention. A single small property file was observed taking minutes of
CPU where prior sessions' own comments describe it running in seconds.

**Separately**, `sello` bisected a `coverageGuided` per-example
`CoverageFrontier`-snapshot regression to `1b804311`, and confirmed by
source diff that nelli 0.8.0 does not fix it.

**Be precise about what is and is not established.** The bisect to `1b804311`
is theirs and is specific. The 9.5 → 15–17 min CI shift is measured, and is
consistent with this mechanism, but was *not* proven to be wholly attributable
to it — their own note attributes it to "somewhere in nelli 0.6.0/0.7.0's
engine" and flags the profiling as not done. Treat the mechanism as identified
and the magnitude as unquantified. §4 is how to close that gap.

**Blast radius is bounded.** `coverageGuided` defaults to `false` and RFC-0010
did not change that, so only callers who opt in pay this. That makes it less
urgent than the numbers alone suggest — and it also means the cost has been
invisible to anyone who does not use the feature, which is why it survived
from August to a downstream's CI bill.

## §2 — Why this is not a revert

The change that introduced the cost was made for a good reason, stated plainly
in its own message: `forAll`'s coverage model duplicated `CoverageFrontier`'s
admission model (FUZZ_PLAN D10), and `Report.coverageHits` was being computed
from a second, independent raw bitmap read. One source of truth replaced two.

Reverting to the scalar delta reintroduces exactly that duplication, and with
it the drift risk between two models of the same quantity. This repo has spent
an RFC on what happens when one fact lives in two places.

So the design question is the interesting one:

> Can `forAll` keep the single bucketed model while not paying O(edges) — and
> an allocation — on every example?

That is what this RFC is for. A revert is the fallback if the answer turns out
to be no, not the proposal.

## §3 — Candidate directions

Unranked; none has been prototyped or measured.

1. **Fuse `score` + `admit` into one pass.** They walk the same array back to
   back, and the sequencing is load-bearing (`score` must peek before `admit`
   folds, or a re-proposed candidate reads 0 — see the U1 note in
   `engine.nim`). A single pass returning both the peeked value and the
   admission would preserve that ordering by construction and halve the walk.
   Cheapest of these, and strictly an improvement regardless of what else is
   done.
2. **Stop allocating per call.** `snapshotCoverage()` builds a fresh
   `seq[uint8]` sized to the whole counter array on every example. A reusable
   buffer threaded through the wrapper removes the allocation and its GC
   pressure without touching the model at all. Also unconditionally good.
3. **Only snapshot when a consumer is live.** The Pareto-visible value exists
   for the targeted phase. If no `target()` is in play and nothing will read
   the coverage objective this run, the per-call snapshot is pure overhead and
   `Report.coverageHits` could come from a single post-run read. This is the
   one with real design content — it changes *when* the model runs, and needs
   care that `coverageHits` stays authoritative and that the targeted phase's
   re-scoring still sees repeatable values.
4. **Cheap pre-filter before the full pass.** The in-process `{.cover.}` bitmap
   is binary and first-hit-only, so most calls after the first few admit
   nothing. A dirty-bit or a cheap summary that short-circuits the full walk on
   the common "nothing new" path may capture most of the win. Speculative:
   depends on whether the bitmap can be cheaply summarised.

(1) and (2) look like clear wins with no semantic content and could land
independently of the design question. (3) is where the actual decision is.

## §4 — What has to be measured before deciding

The magnitude is currently inferred, and this RFC should not proceed on an
inferred number.

- **A/B the feature directly**, in-tree. The isolating measurement is the same
  properties run twice, once with `coverageGuided = true` and once `false`,
  differing in nothing else. That shape exists in the wild already — the
  reporting downstream has a property file carrying exactly that pair for
  unrelated reasons — but nelli should own its own benchmark rather than
  measure against a consumer's suite.
- **Separate fixed from scaling cost.** Profile one small property file at
  several example counts to establish whether the overhead is per-`forAll` or
  per-example. The mechanism predicts per-example and linear in edge count;
  confirm rather than assume.
- **Establish the edge-count dependence.** The cost is O(edges), so a large
  instrumented binary should hurt far more than a small one. If that does not
  reproduce, the mechanism identified here is not the whole story and the
  attribution in §1 is wrong.
- **Bisect the residual.** If the fix recovers only part of the 9.5 → 15–17
  min gap, the remainder is a second regression somewhere in 0.6.0/0.7.0 and
  wants its own entry rather than being folded into this one.

## §5 — Related

- **RFC-0003 (fuzzer-nextgen), Track U** — where the change originated. It is
  `implemented` and closed; this is recorded as a new RFC rather than reopening
  it, per `docs/rfc/README.md`.
- **RFC-0012 (complexity-properties)** — unrelated despite the name. That RFC
  is about testing *user code's* cost. This one is about nelli's own.
- No RFC currently owns nelli's runtime performance as a subject. If a second
  perf item lands, consider whether these want to merge into a standing
  performance RFC rather than accumulating as separate seeds.
