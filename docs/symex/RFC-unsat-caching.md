# RFC — UNSAT / UNKNOWN result caching

> Closes [Phase 12 deferral #9](PHASE12_PLAN.md): UNSAT and UNKNOWN
> findings are re-derived on every call. On a SUT with N
> UNSAT-prone targets, cold-cache cost is `queryRLimit ×
> per-target-step` *every run*, not just the first.
>
> **Revision history**:
> - **v1**: cached SAT-only carry-over; assumed `queryTimeoutMs`
>   bounded Z3 (it doesn't); 12 cycles.
> - **v2**: first architect round (4 frames) surfaced 28
>   findings including 5 CRITICAL. Major changes: wire Z3's
>   `rlimit` + rename `queryTimeoutMs → queryRLimit`;
>   `verdictCacheMaxEntries = 1` named const; cycle 1
>   tautological RED merged into cycle 2; cycle 9 out-of-fragment
>   SUT replaced with loop-unwind UNKNOWN; cycle 7 wrong-verdict
>   pre-seed; migration regression + acceptUnknownAsCovered
>   integration cycles added.
> - **v3 (current)**: second architect round (4 frames) surfaced
>   2 CRITICAL + 7 HIGH + 6 MEDIUM. Major changes:
>   (1) cycle 1 touch list enumerated to 6 exact sites,
>   canonicalize tag prefix renamed `";to="` → `";rl="`, default
>   value claim corrected to 0 (unbounded; rlimit opt-in);
>   (2) cycle 2 collateral RED list corrected (3 tests, 2 files,
>   correct line numbers 238 + 257); sharp test reframed around
>   a new `symexCacheKeyForFn` macro helper;
>   (3) cycle 3 absorbs `db.save` DbError wrapping (routes to
>   `Report.dbErrors` per the documented DB contract) — fixes
>   a pre-existing cross-layer inconsistency;
>   (4) `SymexFinding.fromCache: bool` added — closes Phase 12
>   future-work #6 cheaply since constructor sites are already
>   being touched;
>   (5) cycle 9 (acceptUnknownAsCovered guard) renumbered to
>   cycle 6 as defense-in-depth before the Layer 1 wire changes;
>   (6) `symexZ3CallCount` always-on (no compile-time gate;
>   no convention exists, cost negligible);
>   (7) per-`trySolve` budget semantics documented;
>   (8) `nim-z3` rlimit guarantee for default solver claimed
>   in cycle 11 docs; corruption self-heal, sink stale state,
>   settings mutation gotcha, UNSAT-vs-UNKNOWN disclaimer
>   tiering all added.

## Why

Phase 10's content-addressed cache solved SAT: a SAT witness is
stored under `SHA1(canonical_IR ‖ target ‖ settings ‖ z3v ‖ nimv
‖ walkerv ‖ renderv)`. Any input that could change the witness
rotates the key.

That content-addressing applies to UNSAT and UNKNOWN — but
`saveSymexWitnessImpl` short-circuits:

```nim
proc saveSymexWitnessImpl*(db, prog, target, settings, finding, ...) =
  if finding.status != sfSat: return        # ← drops on the floor
  ...
```

Consequence: `symexFindAllWitnesses` re-runs Z3 against every
UNSAT-proven target on every call. This RFC fixes it.

## Z3 bound is wrong today — fix it first

**The v2 audit surfaced**: `runtime.nim:trySolve` calls
`s.check()` with no params; `settings.queryTimeoutMs`
participates in the cache key but is never applied to the
solver. Today's `sxUnknown` arises only from walker-internal
decisions (`maxLoopUnwind`, `maxCallDepth`, opaque calls,
`isUnsupported` nodes, Z3 theory-incompleteness `zsUnknown`),
never from a time bound.

For UNKNOWN caching to be *deterministic*, the bound must be
deterministic. Wall-clock timeouts aren't — CPU contention,
thermal throttling, scheduler load. Z3 exposes `rlimit`: a
logical step count that produces identical outcomes across
machines for a fixed Z3 build. **v3 wires it.**

**Field rename:**

| Before | After |
|---|---|
| `SymexSettings.queryTimeoutMs: uint` (units: ms, semantics: wall-clock, never wired) | `SymexSettings.queryRLimit: uint` (units: Z3 logical steps, semantics: deterministic resource bound, wired to `Z3_solver_set_params`) |
| Canonicalize tag prefix `";to="` (legacy "timeout") | `";rl="` (current "rlimit") |
| Default `queryTimeoutMs: 0` (silent no-op) | Default `queryRLimit: 0` (Z3's documented "unbounded" — opt-in semantics) |

**Default value commitment.** `queryRLimit: 0` means *unbounded
solver* — Z3's documented default. Callers wanting a deterministic
UNKNOWN must explicitly set `queryRLimit` to a positive value.
This preserves existing behavior (`defaultSymexSettings()`
remains unbounded) and matches the audit-confirmed observation
that today's `queryTimeoutMs` field is a no-op for all default
callers. The two existing literal sites that set
`queryTimeoutMs: 5000` (`tsymex_phase7_assertcovered.nim:59`,
`examples/symex_loops.nim:60`) carry the value forward as
`queryRLimit: 5000` — still meaningful, just under the new
semantics. The Cycle 8 UNKNOWN test deliberately uses the
walker-decided UNKNOWN path (loop-unwind exhaustion) so it works
regardless of any `queryRLimit` configuration.

**Per-`trySolve` budget.** `runSymex` invokes `trySolve` per
target/path; each call creates a fresh Z3 solver and gets a
fresh `queryRLimit` budget. `queryRLimit` is therefore a per-
**solver-invocation** budget, not a total-per-`runSymex` cap. A
SUT with M target labels could spend `M × queryRLimit` steps
total. This is correct for deterministic caching (each `trySolve`
invocation is independently reproducible) but is a sharp edge
documented in cycle 11.

**`random_seed = 0'u` set explicitly** in `trySolve` so
determinism doesn't rely on Z3's undocumented internal default.
This overrides any global params (`setGlobalParam`) the caller's
process may have set elsewhere — a deliberate strength: the
cache lives or dies by the determinism guarantee.

**Wiring sketch** in `runtime.nim:trySolve`:

```nim
proc trySolve(...) =
  let s = newSolver(ctx)
  let p = newParams(ctx)
  p.set("rlimit", settings.queryRLimit)
  p.set("random_seed", 0'u)
  s.setParams(p)
  for c in path.pc:
    s.add(c)
  let r = s.check()
  inc symexZ3CallCount        # always-on; see cycle 1
```

**rlimit semantics caveat for Z3.** The default `newSolver(ctx)`
constructs Z3's portfolio solver. For BV + linear-integer
formulas (what this codebase produces), the portfolio honors
`rlimit` cleanly — when exhausted it returns `Z3_L_UNDEF`
(`zsUnknown`). This is sound in practice. nim-z3 doesn't
document this; cycle 11 docs add the explicit guarantee with
a note that non-linear and quantifier tactics may treat
`rlimit` as best-effort (out of scope for this codebase's
walker output).

## Semantic claims, audited

**UNSAT.** Permanently cacheable. UNSAT is a logical property
of the explored fragment — two sub-cases:
- *Z3-reported UNSAT*: `s.check()` returned `zsUnsat`. Sound
  "no input exists" within the explored path conditions.
- *Walker-decided UNSAT*: walker finished traversal without
  finding SAT AND without setting `sawUnknown`. Bounded by
  `maxLoopUnwind`/`maxCallDepth` (in the key). Promise: "no
  input within the configured exploration bounds."

**UNKNOWN.** Cacheable under `queryRLimit`. Same SUT + target +
settings + Z3 build → same walker traversal → same Z3 queries →
same rlimit-bound outcomes. Reproducible across machines.
Escape hatches: bump `queryRLimit` (rotates key) or Z3 version
(also rotates).

**`acceptUnknownAsCovered`** is provably excluded from the
cache key (existing canonicalize contract). Cycle 6
(integration guard, moved from old position 9) confirms
verdict cache returns identical findings regardless of toggle.

**`Settings.derandomize`** does not interact with `runSymex`
(symex consumes `SymexSettings`, not engine `Settings`).
Verdict cache is vacuously composable with `derandomize=true`.
Cycle 11 docs state this explicitly.

## What this does NOT cover

UNSAT verdicts are stable under all of the items below (logical
property of the IR). UNKNOWN verdicts depend on Z3's rlimit step
counting being deterministic across configurations; cycle 11
docs disclaim the marginal cases.

- `symexFind` and `assertCoveredBy` don't use the cache today
  and still won't. Extending them is a separate RFC.
- **Z3 env vars** (`Z3_NUM_THREADS`, `OMP_NUM_THREADS`):
  UNSAT-stable; UNKNOWN-cached deterministically only when
  parallel solving is disabled (defaults).
- **Nim build flags** (`-d:release` vs `-d:debug`): UNSAT-stable;
  UNKNOWN-stable (symbolic semantics don't change between
  compilation modes).
- **OS / Z3 build heuristics**: UNSAT-stable; UNKNOWN-stable for
  fixed Z3 build (which is in the key via `z3FullVersion()`);
  cross-platform Z3 binaries from different distros could in
  theory differ for UNKNOWN.
- **Multi-process concurrent writes** to the same directory-
  backed DB: safe by design. The tmp+rename protocol is atomic
  per file; concurrent saves of the same verdict key write
  identical sentinel blobs (last-writer-wins is a no-op).
- **Verdict freshness mechanisms** (TTL, periodic re-validation):
  unnecessary under content-addressing.
- **`multiplexedDatabase` shared-corpus verdicts**: undefined
  precedence on divergence. **Verdict keys MUST NOT appear in
  shared/secondary corpora.** Documented as a configuration
  invariant.
- **`maxFrontierSize`**: declared, in the cache key, but
  never enforced in `runtime.nim`. Forward-compatible; cycle
  1 does not address this (out of scope; separate frontier
  enforcement work).

## Design

### Cache schema: per-verdict key suffix

Three sibling keys per content-addressed namespace:

```
"sx:" & H & ":sat"    → seq[ChoiceNode]  (the witness)
"sx:" & H & ":unsat"  → @[]              (sentinel — verdict-only)
"sx:" & H & ":unk"    → @[]              (sentinel — verdict-only)
```

`H` is the existing content-addressed SHA-1. Suffix lives *after*
the hash so a future grep/dump groups all verdicts for a given
SUT/target.

**Sentinel encoding — open question CLOSED.** `@[]` round-trips
distinct from missing in both backends (v1-audit-confirmed,
restated):
- inMemory: `saveImpl(@[])` → `applySave` stores `c.primary =
  @[@[]]`; `loadPrimaryImpl` returns `@[@[]]` (len 1, value
  empty). Missing key returns `@[]` (len 0).
- Directory: `toBytes(@[])` writes an 8-byte length-prefix blob
  (non-empty file); `parseContents` round-trips it to `@[]`.

`db.loadPrimary(verdictKey).len == 1 AND result[0] == @[]` ↔
verdict cache hit. `.len == 0` ↔ miss.

**`verdictCacheMaxEntries = 1` is mandatory.** Without it, the
default `maxEntries = 16` allows accumulation: a verdict slot
holding `@[@[]]` could become `@[someEntry, @[]]` under a stray
non-sentinel write, and `result[0] == @[]` would silently fail.
Named const in `canonicalize.nim`:

```nim
const verdictCacheMaxEntries* = 1
```

Used at every `saveSymexVerdictImpl` call site.

**Corruption recovery (self-healing).** If a verdict file has
`@[[a, b, c]]` (non-empty seq, structural corruption from manual
edit or stray write), `loadSymexVerdictImpl` treats it as a miss
(`result[0] != @[]`), falls through to the next suffix, and on
total miss runs Z3 fresh. The correct verdict overwrites the
corrupted slot on next save. No crash, no false hit.

**Tie-break order:** if both `:unsat` and `:unk` are present for
the same `H`, **UNSAT wins** (stronger verdict). `loadSymexVerdictImpl`
checks `:unsat` first, returns `some(sfUnsat)` on hit; only on
miss falls through to `:unk`. This is a *load-order* rule,
independent of save order — cycle 3 RED tests both save orders
(save UNSAT-then-UNKNOWN AND save UNKNOWN-then-UNSAT) to prove
load order alone determines the outcome.

### New API surface

Two new pure runtime primitives in `nelli/symex.nim`:

```nim
proc saveSymexVerdictImpl*(db: ExampleDatabase, prog: SymexProgram,
                           target: SymexTarget, settings: SymexSettings,
                           status: SymexFindingStatus,
                           errors: var seq[string])
  ## Persist a non-SAT verdict under the content-addressed key
  ## suffixed with `:unsat` or `:unk` and
  ## `maxEntries = verdictCacheMaxEntries`. No-op for sfSat (use
  ## saveSymexWitnessImpl) and sfNotApplicable (verdict is local
  ## context, not a Z3 outcome).
  ##
  ## `errors` accumulates any `DbError`/`OSError` raised by the
  ## underlying `db.save` — caller routes into `Report.dbErrors`.
  ## Save is best-effort: cache failures NEVER abort the analysis.

proc loadSymexVerdictImpl*(db: ExampleDatabase, prog: SymexProgram,
                           target: SymexTarget, settings: SymexSettings,
                           errors: var seq[string]
                          ): Option[SymexFindingStatus]
  ## Cache lookup for non-SAT verdicts. Tries `:unsat` then `:unk`.
  ## Returns `some(sfUnsat)` / `some(sfUnknown)` on hit, `none` on
  ## miss. Never exposes raw `seq[seq[ChoiceNode]]` to callers —
  ## invariant: the sentinel must not leak into any code path that
  ## might pass it to `db.removeMany`.
  ##
  ## `errors` accumulates any `DbError` from the load path; load
  ## failures degrade to "miss" so analysis continues.
```

**`saveSymexWitnessImpl` migrated** to the same error-routing
contract: a new `errors: var seq[string]` parameter, save-failure
appends instead of raising. Macro callers append to a local
errors-seq then flow it into `state.acc.dbErrors` (engine state
already carries this — see `engine/pipeline.nim`).

This closes a pre-existing inconsistency surfaced by the v2
audit: `db.nim`'s module contract says save errors flow into
`Report.dbErrors`, but the symex layer was propagating them as
uncaught exceptions, aborting the analysis with partial
findings. The RFC fixes this for both the new verdict path and
the existing witness path.

### `SymexFinding.fromCache: bool`

New boolean field on `SymexFinding`:

```nim
type SymexFinding* = object
  targetDesc*:     string
  status*:         SymexFindingStatus
  covered*:        bool
  witnessChoices*: seq[ChoiceNode]
  z3Version*:      string
  fromCache*:      bool   ## NEW — true iff the verdict was loaded
                          ## from the content-addressed cache rather
                          ## than computed cold. Phase 12 future-work
                          ## #6 — observability for users wondering
                          ## "why is my CI still slow?".
```

Set `fromCache = true` on SAT-cache-hit AND verdict-cache-hit
paths; `false` on cold paths. Users can audit:

```nim
let report = symexForAll(s, fn, db)
let hits = report.symexFindings.countIt(it.fromCache)
echo "symex cache hit rate: ", hits, "/", report.symexFindings.len
```

The Phase 12 future-work issue #6 closes with this addition.

### Macro forms

`saveSymexVerdict` / `loadSymexVerdict` mirror the existing
`saveSymexWitness` / `loadSymexWitnesses` shape. `status:
SymexFindingStatus` is a runtime param (not `static`) — the
suffix lookup is runtime-dispatched.

### Layer 1 wire update (with `recordSymexFinding` and `fromCache`)

`symexFindAllWitnesses`'s per-target loop. The macro emits this
inside `runtimeBody` using the existing `progId` and `findingsId`
gensyms (see symex.nim cycle-18 plumbing). The snippet below
uses `prog` and `findings` for clarity; **the actual macro must
use backtick-spliced gensyms to preserve hygiene**:

```nim
var dbErrors: seq[string] = @[]
# ...inside the for t in tsId loop...
var f = SymexFinding(
  targetDesc: describeTarget(t),
  covered:    false,
  z3Version:  z3FullVersion(),
  fromCache:  false)               # default cold
# 1. SAT cache hit?
let cachedSat = loadSymexWitnessesImpl(db, prog, t, settings, dbErrors)
if cachedSat.len > 0:
  f.status = sfSat
  f.witnessChoices = cachedSat[0]
  f.fromCache = true
else:
  # 2. UNSAT / UNKNOWN cache hit?
  let cachedVerdict = loadSymexVerdictImpl(db, prog, t, settings, dbErrors)
  if cachedVerdict.isSome:
    f.status = cachedVerdict.get
    f.fromCache = true
  else:
    # 3. Cold path: invoke Z3 + save the result.
    let raw = runSymex(prog, t, settings)
    f.status = toFindingStatus(raw.status)
    case raw.status
    of sxSat:
      let `witId` {.used.} = raw.witness
      let typedWit: `tupleTy` = `witnessTup`
      f.witnessChoices = renderAsChoices(typedWit)
      saveSymexWitnessImpl(db, prog, t, settings, f, dbErrors)
    of sxUnsat, sxUnknown:
      saveSymexVerdictImpl(db, prog, t, settings, f.status, dbErrors)
# CRITICAL — outside the if/else tree so EVERY path deposits:
recordSymexFinding(f)
findings.add f
# After the for loop: flow dbErrors into accumulator.
# (engine.runForAllPipelineWithPhases threads this through state.acc.dbErrors)
```

Three load attempts cold-cache, one in warm SAT, two in warm
verdict. `recordSymexFinding` is unconditional —
**implementer must not narrow it into a branch.** Cycle 7
test 3 (sink-deposit observable) regression-guards this.

### `canonicalize` extension

`symexCacheKey` continues to return the SHA-1 hash without a
suffix. The `:sat` / `:unsat` / `:unk` suffix is appended at the
call site:

```nim
const
  cacheKeySatSuffix*   = ":sat"
  cacheKeyUnsatSuffix* = ":unsat"
  cacheKeyUnkSuffix*   = ":unk"
  verdictCacheMaxEntries* = 1
```

`SymexSettings.queryTimeoutMs: uint` becomes `queryRLimit: uint`.
The canonical encoding's tag prefix changes from `";to="` to
`";rl="` (no behavioural difference vs. just renaming the
field — both rotate the key — but the tag now reads honestly in
debug dumps). Existing entries under the old encoded key become
invisible (one-time migration; coincides with the :sat suffix
migration in cycle 2 from a user-upgrade perspective if they
upgrade Phase 12 → Phase 13 atomically).

Old SAT entries also rotate via the new `:sat` suffix. One
cold re-derivation on first run after upgrade.

## Slices — 12 cycles

Twelve `/tdd`-ready cycles. Each one RED → GREEN → REFACTOR on a
single observable behavior; no batching.

Test-file naming: `tsymex_phase13_*` per codebase phase
convention.

### A. Z3 bound + naming (1)

**Cycle 1.** Rename `queryTimeoutMs → queryRLimit`, wire Z3
`rlimit` + `random_seed = 0'u` into `trySolve`, add always-on
`symexZ3CallCount*: int` threadvar in `symex.nim` (no compile-
time gate — no convention exists, threadvar increment is cheap
and matches the `symexCapture` precedent), rename canonicalize
tag prefix `";to=" → ";rl="`. **Touch list (exact):**
- `src/nelli/smt/types.nim` — field rename in `SymexSettings`
  (line 364) + `defaultSymexSettings()` body (line 622);
- `src/nelli/smt/canonicalize.nim` — field read + tag rename
  (line 338);
- `src/nelli/smt/runtime.nim` — `trySolve` Z3 params wiring
  (around line 1284); also add `inc symexZ3CallCount` at the
  `s.check()` call site;
- `src/nelli/symex.nim` — declare `symexZ3CallCount*: int`
  threadvar;
- `tests/tsymex_canonicalize.nim` — line 237 mutation site
  rename + line 231 test-title string rename;
- `tests/tsymex_phase7_assertcovered.nim` — line 59 literal
  `SymexSettings` constructor field name;
- `examples/symex_loops.nim` — line 60 literal `SymexSettings`
  constructor field name.

That's the complete cycle-1 GREEN touch list. **RED**: a focused
test asserting `runSymex` with `queryRLimit = 100` on a known-
solvable BV[64] formula returns `sxUnknown` (rlimit exhausted
before solver finishes). GREEN: solver param wiring + field
rename atomic across all 7 sites; existing tests recompile.

### B. DB schema migration (1)

**Cycle 2.** Add suffix constants + `verdictCacheMaxEntries` in
`canonicalize.nim`. Migrate `saveSymexWitnessImpl` to append
`cacheKeySatSuffix` (and the new `errors` parameter — see
cycle 3 for the wrap). Add a new test helper:

```nim
macro symexCacheKeyForFn*(fn: typed, target: static SymexTarget,
                           settings: static SymexSettings): untyped
  ## Test-only helper. Emits a call to `symexCacheKey` with the
  ## parsed-at-macro-time SymexProgram from `fn`. Lets tests
  ## assert the raw key string used by the cache layer without
  ## hand-constructing SymexProgram values.
```

**RED collateral** (corrected from v2 — full list):
- `tsymex_phase12_witnesses.nim:178` ("DB cache: pre-seeded
  witness is returned without re-running symex")
- `tsymex_phase7_assertcovered.nim:238` ("DB round-trip: same
  SUT/target/settings load, distinct SUT does not")
- `tsymex_phase7_assertcovered.nim:257` ("saveSymexWitness
  ignores UNSAT/UNKNOWN findings")

All three fail when `saveSymexWitnessImpl` writes `:sat` but
`loadSymexWitnessesImpl` still reads bare — expected. **Sharp
key-format test added:** uses `symexCacheKeyForFn` to derive
the hash at test time, asserts `db.loadPrimary(H & ":sat")` hits
and `db.loadPrimary(H)` (bare) misses. **GREEN**: mirror
`loadSymexWitnessesImpl` to append the suffix; all three
collateral tests restored.

### C. Verdict primitives (1)

**Cycle 3.** Add `saveSymexVerdictImpl` (with
`maxEntries = verdictCacheMaxEntries` and DbError wrap) and
`loadSymexVerdictImpl` (returns `Option[SymexFindingStatus]`,
never raw seq). **Also wraps the existing `saveSymexWitnessImpl`
in the same try/except + errors-seq contract** — fixes the
cross-layer DB-contract inconsistency. **RED tests:**
- Hand-built call sequence: save UNSAT, load returns
  `some(sfUnsat)`; save UNKNOWN under same H, load still returns
  `some(sfUnsat)` (load-order tie-break).
- **Reverse save order** (the one that actually exercises the
  rule): save UNKNOWN first, then save UNSAT — load returns
  `some(sfUnsat)`. Proves load order alone, not save order,
  determines the outcome.
- Simulated DB failure: `db.save` raises → `errors.len > 0`,
  analysis continues, no findings dropped.
Touches `symex.nim`, new test `tsymex_phase13_verdict_primitives.nim`.

### D. Verdict round-trips (2)

**Cycle 4.** UNSAT verdict round-trips through the
content-addressed key + bare-key migration regression.
- Save UNSAT under prog A; load returns `some(sfUnsat)` under
  prog A.
- Load under a *different* prog returns `none`.
- Pre-seed a bare-key SAT entry (pre-RFC scheme); confirm
  `loadSymexWitnessesImpl` returns `@[]` (migration regression).

**Cycle 5.** UNKNOWN verdict round-trips identically + UNSAT /
UNKNOWN distinguishable. RED: save UNKNOWN, load returns
`some(sfUnknown)`. Same prog, save UNSAT under *different
settings* (different `queryRLimit`); load under each settings
returns the correct verdict.

### E. `acceptUnknownAsCovered` integration guard (1) — moved before Layer 1 wire

**Cycle 6.** Defense-in-depth guard placed BEFORE the Layer 1
wire changes so wire regressions fire immediately. RED: save
UNKNOWN under settings A (`acceptUnknownAsCovered = false`);
load under settings B (`acceptUnknownAsCovered = true`, all else
identical) returns `some(sfUnknown)` from the same cache slot.
GREEN: nothing (canonicalize already excludes the field;
loadSymexVerdictImpl uses it correctly). Pins the wire contract
before it's modified.

### F. Layer 1 wire (3)

**Cycle 7.** `symexFindAllWitnesses` consults verdict cache on
witness-cache miss + `fromCache = true` on hit + `recordSymexFinding`
unconditional. **RED via deliberate wrong-verdict pre-seed**
(this is a *poisoned cache* test pattern — the test is proving
the cache returns whatever was stored, not that the cache
computes truth):
- Pre-seed verdict cache with `sfUnsat` for a target the SUT
  exposes via a TRIVIALLY SAT construct
  (`if x == 1: symexTarget("one")`).
- Call `symexFindAllWitnesses`; assert returned finding has
  status `sfUnsat`, `fromCache = true`, `symexZ3CallCount == 0`
  (cycle 1 instrumentation), AND the finding appears in
  `consumeSymexFindings()` (proves `recordSymexFinding` ran on
  the verdict-cache-hit path).
- Add `SymexFinding.fromCache: bool` field to `engine/types.nim`.
  Update every existing `SymexFinding(...)` constructor in
  `nelli/symex.nim` and `tests/` to default `fromCache: false`.
Touches `symex.nim`, `engine/types.nim`, several test files
mechanically. New test `tsymex_phase13_layer1_wire.nim`.

**Cycle 8.** Cold path saves UNSAT. RED: cold DB; SUT with a
provably-UNSAT target (`if x != x: symexTarget("ghost")`).
First call: status `sfUnsat`, `fromCache = false`,
`symexZ3CallCount == 1`. Second call: status `sfUnsat`,
`fromCache = true`, `symexZ3CallCount == 0` (verdict cache
served it).

**Cycle 9.** Cold path saves UNKNOWN. RED: cold DB; SUT using
walker-decided UNKNOWN (loop-unwind exhaustion pattern from
`tsymex_phase7_assertcovered.nim:43-48` shape):

```nim
proc fn(x: int) =
  var i = 0
  while i < x:
    i = i + 1
  if i == 100:
    symexTarget("deep")
# SymexSettings(maxLoopUnwind: 2, queryRLimit: 0)  # 0 = unbounded
```

Loop-unwind exhausts before reaching `i == 100`; walker sets
`sawUnknown`; UNKNOWN deterministically. Works regardless of
`queryRLimit` configuration (path is walker-decided). First
call: status `sfUnknown`, counter `1`. Second call: `fromCache
= true`, counter `0`.

### G. Macro surface + docs + memory (3)

**Cycle 10.** `saveSymexVerdict` + `loadSymexVerdict` macros
mirror the existing `saveSymexWitness` / `loadSymexWitnesses`
shape. `status: SymexFindingStatus` is a runtime param (not
static).

**Cycle 11.** Docs sweep:
- `docs/symex/determinism.md` — new "Verdict caching"
  subsection covering:
  - Three sibling keys, sentinel encoding, `maxEntries = 1`
    invariant, UNSAT-first load-order tie-break.
  - **`queryRLimit` semantics**: logical step count, NOT
    wall-clock ms; per-`trySolve` budget not per-`runSymex`.
  - **nim-z3 rlimit guarantee**: the default `Z3_mk_solver`
    portfolio honors rlimit cleanly for BV + linear-integer
    formulas (the codebase's walker output); non-linear
    tactics out of scope.
  - **`random_seed = 0` baseline**: overrides any global
    params for reproducibility.
  - **Disclaimer tiering**: UNSAT-stable axes (build flags,
    OS heuristics) vs UNKNOWN-caveated axes (Z3_NUM_THREADS
    if parallel ever enabled, cross-platform Z3 binaries).
  - **Corruption self-heal**: non-empty value at `:unsat`/`:unk`
    treated as miss; Z3 re-runs; correct verdict overwrites.
  - **Stale-sink note**: callers using `symexForAll` in a retry
    loop should `discard consumeSymexFindings()` before each
    invocation (pre-existing Phase 12 property).
  - **Settings-mutation gotcha**: any `SymexSettings` field
    that participates in the key rotates the verdict cache;
    same lesson as the existing strategy-cache caveat.
  - **Multi-process safety**: tmp+rename + idempotent sentinel
    = safe by design (positive property).
  - **DbError flow**: save failures append to `Report.dbErrors`
    via the new `errors` param contract; analysis never aborts
    on cache failure.
- `docs/symex/README.md` — cold-cache latency note refreshed:
  warm-run UNSAT/UNKNOWN drops from `N × queryRLimit-budget`
  to one DB load. User-facing "what happens on upgrade"
  paragraph: "first run after Phase 13 will re-derive all
  cached SAT witnesses (one-time cost); subsequent runs cache
  UNSAT/UNKNOWN too."
- `docs/symex/PHASE12_PLAN.md` — deferral #9 marked closed.
  **Convention**: append "**CLOSED**: see Phase 13 RFC" to the
  item text (no schema change to the table).
- `docs/SYMEX_PLAN.md` — Phase 13 row in the phase-by-phase
  table; design-decision section recording: verdict caching,
  rlimit wiring, `fromCache` field, DbError contract fix,
  naming decision (queryTimeoutMs → queryRLimit).
- Projected test count post-Phase-13: **~53 files, ~225
  tests** (cycle 11 updates SYMEX_PLAN.md's count row).

**Cycle 12.** Memory + plan close-out: update
`/home/corey/.claude/projects/-home-corey-projects-nimlibs-hypothesis/memory/nelli-symex-shipped.md`
(file exists; the v2 audit's "not found" was searching the
repo, but memory lives in the Claude memory directory) to
record verdict caching + rlimit wiring + `fromCache` field
+ DbError contract close; `MEMORY.md` index entry refresh.

## Compatibility on upgrade

| Change | Impact |
|---|---|
| `queryTimeoutMs → queryRLimit` (rename + semantic + canon tag) | One-time cache rotation for ALL Phase 12 entries. Default `queryRLimit: 0` keeps existing callers unbounded — no behavior regression. |
| Bare `"sx:" & H` → `"sx:" & H & ":sat"` (key migration) | Cold re-derivation, same migration window as above (combined when upgrading atomically). |
| New `:unsat` / `:unk` namespace | Didn't exist before; nothing to migrate. |
| New `SymexFinding.fromCache: bool` field | Non-breaking (defaults to false on existing constructors). Test files using `SymexFinding(...)` literals need a one-line addition mechanically. |
| `SymexSettings` field rename | All test files reconstructing `SymexSettings` must update — exact touch list in cycle 1. |
| `saveSymexWitnessImpl` / `saveSymexVerdictImpl` signature change | New `errors: var seq[string]` param. Existing callers are the macro emitters (cycle 7 GREEN), test files using the macro form (unaffected — macro hides the impl-level signature). |

**Rotation event count for incremental developers.** Two sequential
cold-cache events if cycles 1 and 2 ship separately (rename
rotates first; suffix rotates again). Users upgrading Phase 12
→ Phase 13 atomically see one combined rotation.

## What this closes

- Phase 12 deferral #9 (UNSAT findings re-derived on every call).
- Phase 12 future-work #6 (cache hit visibility) via
  `SymexFinding.fromCache`.
- The `queryTimeoutMs` phantom-field issue surfaced by audit
  (becomes a real bound under `queryRLimit`).
- The walker-decided-UNSAT prose-imprecision in determinism.md.
- The pre-existing DB-contract inconsistency between `db.nim`'s
  module promise (errors flow to Report.dbErrors) and the symex
  layer's behavior (errors propagated as exceptions).

## What this opens

- `symexFind` / `assertCoveredBy` verdict-cache integration.
- Z3 internal-error handling policy (currently propagates;
  future hardening could catch-to-sfUnknown).
- `maxFrontierSize` enforcement (declared field, in cache key,
  currently inert).
- Cross-target parallelism (Phase 12 future-work #8).
- Per-tactic Z3 versioning (rejected in determinism.md;
  unchanged).

## Estimated effort

12 cycles, ~16–20 hours total. Cycle 1 (rlimit wiring + rename
+ canon tag) is the largest single touch but the touch list is
now exact (7 sites). Cycle 3 (verdict primitives + DbError
contract fix) is the next-largest. Cycles 7–9 are the most
behaviorally interesting. Remaining cycles are straightforward
by-pattern after Phase 12 cycle-12 and cycle-20 precedent.
