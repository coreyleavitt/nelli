# Phase 12 — `symexForAll` (input-source seeding) build plan

> Closes the **deferred-from-Phase-7 input-source role** of symex:
> lift symex-found witnesses into the random-PBT loop as forced
> seeds, with auto-discovery of every testable target from the
> SUT's IR. Layered API: low-level primitives compose into a
> one-liner sugar macro.
>
> **Revision history**:
> - v1 (pre-cycle-1): audited by parallel review; 20 objective errors found.
> - v2: 20 fixes baked in + 5 round-1 opinion calls (3 layers, `seq[SymexFinding]` Layer-1 return, document strategy-cache caveat, transitive `isCall` scan, fix `renderAsChoices` collection encoding).
> - **v3 (current)**: round-2 review found 25 additional issues (3 compile-blockers, 5 critical structural, 8 design gaps, 10 spec/test gaps + low-severity items). All 25 fixed below. The v2 design-decision deviations (4 opinion-marked items in round 2's first-principles review) are confirmed and held.

## Why we're doing this

Phase 7 shipped the *verifier* role (`assertCoveredBy`) and
explicitly deferred the *input-source* role:

> `withSymexSeeds(strat, fn, targets)` — Phase 7 deferred piece
> (input-source role). Composes on `loadSymexWitnesses` + existing
> `explicit`/`dbReuse` phases. Build when first consumer demands.

Phase 12 builds it. The user-facing primitive:

```nim
proc handle(req: int) =
  if req == 0:           symexTarget("zero")
  elif req mod 13 == 0:  symexTarget("magic-13")
  doAssert req != 7      # doAssert, NOT a symex marker — ignored by scan

let db = newExampleDB("/var/tmp/symex-seeds")
symexForAll(integers(), handle, db = db)
# → symex finds witnesses for "zero" and "magic-13"
# → symex does NOT hunt for AssertionDefects (no symexAssert in body)
# → forAll replays both symex witnesses then does random fuzzing
# → falsification on a symex witness IS shrunk by shrinkPhase
```

Strategies stay pure (random draw). Seeding flows through a
dedicated `symexSeedPhase` inserted between `explicit` and
`random`, enabling shrinker access to symex-derived counterexamples
(Z3 returns *some* satisfying assignment, not a minimal one).

## Architectural sketch

### Auto-discovery via IR scan

| Target | Opt-in marker | Inclusion rule |
|---|---|---|
| `tLabel("name")` | `symexTarget("name")` in fn body | one per `isTargetLabel` |
| `tAssertionViolation()` | `symexAssert(cond)` in fn body | iff any `isAssert` |
| `tIndexError()` | `arr[i]` / `s[i]` / `t[k]` | iff any `isIndex` |
| `tFieldDefect()` | variant arm-field read | iff any `isVariantField` |

The scan is **transitive through `isCall` bodies** via
`ParseCtx.procs` (the macro-time `Table[string, ProcSig]` built by
`parseProc` as it descends into callees). Bound: whatever
`getImpl` can resolve at macro time — same restriction as
`symexFind`/`assertCoveredBy`. Cross-module private callees stop
the scan (Phase 3 deferral #138 limit applies).

Markers in sub-branches after an `isUnsupported` IR node are
invisible to both scanner and walker — the walker stops at the
unsupported node, the scanner walks past it but the IR has no
markers because parsing didn't go past either. Documented as a
known limit (deferral table).

Escape hatch:

```nim
symexForAll(integers(), handle, db = db,
            excludeTargets = [tIndexError(), tFieldDefect()])
```

Constructor-form spelling for consistency with `assertCoveredBy`.
Default empty (auto everything detectable). The macro filters via
`SymexTargetKind` comparison after detection.

### Three-layered API

```nim
# Layer 1 — primitive. Macro-scans fn's IR transitively for all
# auto-discovered targets, runs symex per target (cache-first via
# Phase 10 content-addressed key). Returns a SymexFinding per
# target — includes status, targetDesc, witnessChoices, z3Version.
# Also calls recordSymexFinding for each, so finalizePhase later
# drains them into Report[T].symexFindings via consumeSymexFindings.
macro symexFindAllWitnesses*(fn: typed,
                              db: ExampleDatabase,
                              symexSettings: static SymexSettings = defaultSymexSettings(),
                              excludeTargets: static openArray[SymexTarget] = []
                             ): seq[SymexFinding]

# Layer 2 — engine entry. Lives in nelli/symex.nim alongside
# the macros. Builds a custom pipeline that inserts symexSeedPhase
# between explicit and random; delegates to extracted helper
# runForAllPipelineWithPhases (engine.nim).
proc forAllWithSymexSeeds*[T](seeds: seq[seq[ChoiceNode]],
                               s: Strategy[T],
                               prop: proc(x: T),
                               settings: Settings = defaultSettings()): Report[T]

# Layer 3 — sugar. fn doubles as the property; macro expands to
# Layer 1 + Layer 2. Multi-arg fns emit a destructuring wrapper
# lambda based on getTypeInst inspection.
macro symexForAll*(s: typed, fn: typed,
                   db: ExampleDatabase,
                   symexSettings: static SymexSettings = defaultSymexSettings(),
                   forAllSettings: Settings = defaultSettings(),
                   excludeTargets: static openArray[SymexTarget] = []
                  ): untyped
  # Emitted expression has type Report[T] where T is the strategy's
  # element type. Returns untyped (matches symexFind pattern).
```

### Pre-requisites — three structural cycles before Layer 1

The v2 plan started Layer 1 immediately. Round-2 review found
three structural prerequisites that must land first:

**A. Move symex sink to `engine/types.nim`**. `symexFindings`
threadvar + `recordSymexFinding` + `consumeSymexFindings` currently
live in `nelli/symex.nim`. Layer 1's macro needs to call
`recordSymexFinding` from emitted code that runs in arbitrary
contexts (including inside `engine/phases.nim`). Importing
`symex.nim` from `engine/phases.nim` pulls in z3 + the full SMT
stack — architecturally toxic.

`SymexFinding` and `SymexFindingStatus` already live in
`engine/types.nim`. Move the sink there too. Re-export from
`symex.nim` for backward compat (no caller change).

**B. Flip `Phase[T].run` to `{.closure.}`**. Currently:

```nim
# pipeline.nim:115
run*: proc(state: var EngineState[T]): PhaseAction {.nimcall.}
```

`.nimcall` forbids captures. Layer 2's pipeline assembly needs
`symexSeedPhase(seeds): Phase[T]` to close over `seeds`. Flip to
`{.closure.}`. Every existing phase (`dbReusePhase[T]`,
`explicitExamplesPhase[T]`, etc.) is a top-level proc that coerces
to closure safely — no caller change.

**C. Introduce `renderAsChoicesVersion`**. The v2 plan bumped
`symexWalkerVersion` to invalidate collection witnesses, but
`symexWalkerVersion` participates in EVERY cache key — collection
or not. Non-collection witnesses (int, bool, string, tuple, object,
variant) would also be invalidated unnecessarily.

Add a separate `renderAsChoicesVersion = "1"` constant that
participates in `symexCacheKey` alongside the walker version.
Cycle 6 bumps it to `"2"` (collection encoding change). Walker
version stays at `"3"`. Non-collection witnesses stay warm across
the upgrade. The `symexCacheKey` proc gains a `renderingVersion`
parameter, mirroring how `walkerVersion` is plumbed.

### `runForAllPipelineWithPhases` helper

`runForAllPipeline` (engine.nim) currently hardcodes
`defaultPhases[T]()`. Layer 2 needs to pass a custom phase
sequence. Extract:

```nim
proc runForAllPipelineWithPhases*[T](db: ExampleDatabase,
                                      dbEnabled: bool,
                                      s: Strategy[T],
                                      prop: proc(x: T),
                                      settings: Settings,
                                      explicit: Examples[T],
                                      phases: seq[Phase[T]]): Report[T]
```

Existing `runForAllPipeline` becomes a thin wrapper that passes
`defaultPhases[T]()`. No caller change.

### `symexSeedPhase`

```nim
# nelli/engine/phases.nim — uses closure capture per change (B).
# Records findings via the sink, which now lives in engine/types.nim.
proc symexSeedPhase*[T](seeds: seq[seq[ChoiceNode]]): Phase[T] =
  Phase[T](name: "symexSeed",
    run: proc(state: var EngineState[T]): PhaseAction =
      if state.output.rawFalsification.isSome: return pcContinue
      for seed in seeds:
        let r = evalReplay(state.spec.s, state.spec.prop, seed)
        case r.kind
        of ekFalsified:
          # evalReplay catches AssertionDefect / IndexDefect /
          # FieldDefect as ekFalsified — correct: a symexAssert that
          # the walker proved violable WILL fire at runtime on the
          # witness. Carry the full choice sequence forward so
          # shrinkPhase can minimise.
          state.output.rawFalsification = some(RawFalsification[T](
            value: r.fValue, choices: r.fChoices,
            message: r.fMsg, notes: r.fNotes,
            fromPhase: "symexSeed"))
          return pcContinue
        of ekRejected:
          # evalReplay internally caught `Overrun` (strategy-shape
          # mismatch — seed not compatible with current strategy) or
          # `Rejection` (property called `reject` / `assume`).
          # Either way, drop this seed; emit a warning finding.
          recordSymexFinding(SymexFinding(
            targetDesc:  "<seed-shape-mismatch-or-rejected>",
            status:      sfNotApplicable,
            covered:     false))
          continue
        of ekPassed:
          continue
      pcContinue)
```

Notes incorporated from round-2 review:
- No `except Overrun:` block. `evalReplay` catches `Overrun`
  internally and converts to `ekRejected` (eval.nim:82-83).
- `AssertionDefect` (from `symexAssert` outside symex →
  `doAssert`) is correctly caught by `evalReplay` as `ekFalsified`;
  the witness *is* a real violation and gets shrunk normally.
- `sfNotApplicable` (not `sfUnsat`) for shape-mismatch / rejected
  seeds. `sfUnsat` would falsely claim "searched and proved
  unreachable."
- Inserted between `explicit` and `random` in the custom pipeline.

### Pipeline order

```
dbReuse → explicit → symexSeed → random → targeted → shrink → explain → finalize
```

dbReuse first preserves regression catches. Explicit pinned values
next (user intent, deterministic). symexSeed runs derived
witnesses. Random covers the rest.

**Warm-run behavior** (acknowledged honestly, not buried as a
"rare conflict"): when `dbReusePhase` finds a stored failure, it
sets `rawFalsification` and `symexSeedPhase` self-gates → skipped.
This is the COMMON case in active development. Users who want
symex audit even when dbReuse falsifies must call
`symexFindAllWitnesses` directly (Layer 1).

### `renderAsChoices` collection encoding fix

Current `seq[T]` encoding (symex.nim:62-65):
```nim
elif T is seq:
  result.add integerChoice(int64(w.len), 0'i64, sxLenMax, 0'i64)
  for e in w:
    result.add renderAsChoices(e)
```

Cycle 6 fix:
```nim
elif T is seq:
  for e in w:
    result.add booleanChoice(true, 0.9)  # continue
    result.add renderAsChoices(e)
  result.add booleanChoice(false, 0.9)   # terminate
```

Same shape for `Table`/`HashSet` — BUT both must iterate
**sorted** (by key for `Table`, by element for `HashSet`).
Iteration order on these types is undefined; same logical witness
must produce identical choice sequences across runs (the cache key
depends on choices). Round-2 review (NEW-1, NEW-2) caught this as
a critical bug the original plan introduced.

**Spec correction (logged during cycle 6 RED 1):** the v3 draft
above claimed `readSeqInt` / `readTableStrInt` / `readSetInt` in
`emitTyAndReader` also needed updating. They don't. Those readers
consume `RawWitness` (`smt/runtime.nim:2135-2159`) — the walker's
in-process witness map — and feed macro-emitted code inside
`symexFind` for direct Nim-value reconstruction. They never cross
the `ChoiceNode` boundary; the renderAsChoices choice-replay path
flows through the strategy implementations in
`strategy.nim:406-475`, which were already correct. Cycle 6
touches `renderAsChoices` only.

### `renderAsChoicesVersion` bump on the collection-encoding change

Cycle 6 bumps `renderAsChoicesVersion` from `"1"` to `"2"`. Phase
10/11 collection witnesses become invisible (the old encoding was
unreplayable through standard strategies — invalidation is
correct). Non-collection witnesses stay warm.

### Zero-targets fallback

When the IR scan finds no markers AND no isAssert/isIndex/
isVariantField constructs:

- Layer 1 returns `@[SymexFinding(status: sfNotApplicable, targetDesc: "no-targets-discovered")]`.
- Layer 2 is called with `seeds = @[]`; `symexSeedPhase` is a no-op.
- The user sees the audit entry in `Report.symexFindings` but no
  symex pre-pass runs.

### `sfNotApplicable` enum case

Cycle 5 adds `sfNotApplicable` to `SymexFindingStatus`. Distinct
from `sfUnsat` ("searched, proved unreachable"). Any existing
`case status` exhaustive match must add the branch — cycle 5
greps for these and updates.

### Multi-arg destructuring

Cycle 18: macro for multi-param `fn`. Uses `getTypeInst` (not
`getType`) to match `assertCoveredBy`'s existing
`isStrategyArg` pattern (strategy.nim:286-291). Walks
`nnkBracketExpr[Strategy, …]` to extract the strategy's element
type. Type-checks against `fn.getImpl`'s formal params one-for-one.

`map(s1, s2, ...)` produces an **anonymous positional tuple** —
not named-field. Multi-arg destructuring always splats positionally
(`fn(t[0], t[1])`). Named-field tuples from custom strategies are
out of scope for v1 (deferral).

Macro-time errors:
- `var T` params in fn → `error("var-param fn not supported with symexForAll")`
- Generic fn → `error("generic fn not supported")` (same as
  `symexFind`)
- Param-count or type mismatch between fn and strategy → clear
  `error()` naming both types

## Cycle plan

22 cycles. ~30h estimated. Each cycle: one RED test, one GREEN
fix, no batching.

### A. Pre-requisites (3 cycles)

#### 1. Move symex sink to `engine/types.nim` (≈1h)

- **RED**: existing assertCoveredBy tests still pass after the
  move; engine/phases.nim can now import the sink without
  pulling in symex.nim.
- **GREEN**: move `symexFindings`, `recordSymexFinding`,
  `consumeSymexFindings` from `symex.nim` to `engine/types.nim`.
  Re-export from `symex.nim`.
- **Touches**: `engine/types.nim`, `symex.nim`.

#### 2. Flip `Phase[T].run` to `{.closure.}` (≈30m)

- **RED**: a test phase that captures an external value and
  assigns it to `Phase[T].run` — must compile.
- **GREEN**: change `Phase[T].run` declaration in
  `pipeline.nim`. Verify all existing phases still coerce.
- **Touches**: `engine/pipeline.nim`.

#### 3. Introduce `renderAsChoicesVersion` (≈1h)

- **RED**: `symexCacheKey` test verifies bumping
  `renderAsChoicesVersion` rotates the key independently of
  `walkerVersion`.
- **GREEN**: add `renderAsChoicesVersion = "1"` constant in
  `smt/canonicalize.nim` next to `symexWalkerVersion`. Extend
  `symexCacheKey` to include it. Update existing callers
  (`saveSymexWitnessImpl`, `loadSymexWitnessesImpl`).
- **Touches**: `smt/canonicalize.nim`, `symex.nim`,
  `tests/tsymex_canonicalize.nim`.

### B. IR scan + helpers (1 cycle)

#### 4. IR scan helpers with transitive `ParseCtx.procs` traversal (≈2h)

- **RED**: unit tests on hand-built IR. Specifically a test where
  the marker lives ONLY in a callee's body reached via `isCall`.
- **GREEN**: add `irHasAssert`, `irHasIndex`, `irHasVariantField`,
  `irCollectLabels` in `nelli/smt/scan.nim` (new module).
  Each walks `IRStmt` recursively AND descends into the macro-time
  `ParseCtx.procs: Table[string, ProcSig]` for `isCall` nodes.
- **Touches**: `smt/scan.nim` (new),
  `tests/tsymex_phase12_scan.nim` (new).

### C. Enum + serialization (1 cycle)

#### 5. `SymexFindingStatus.sfNotApplicable` + audit existing matches (≈1h)

- **RED**: construct `SymexFinding(status: sfNotApplicable)`;
  check `$` produces "sfNotApplicable" (distinct from "sfUnsat").
- **GREEN**: add the enum case. `grep -nr "case.*SymexFindingStatus"`
  to find existing exhaustive matches; add the missing branch.
- **Touches**: `engine/types.nim`, plus any file with a `case
  status` (e.g. render/explain paths if present).

### D. renderAsChoices fix + readers (1 cycle, with version bump)

#### 6. `renderAsChoices` continue-boolean for `seq`/`Table`/`HashSet` + sorted iteration + reader fix + version bump (≈3h)

- **RED**:
  - `seq[int]` round-trip: `renderAsChoices(@[5,9])` → choices
    that `lists(integers())` replays as `@[5,9]`. Cycle's
    primary test.
  - Same logical `HashSet`/`Table` constructed via different
    insertion orders produce identical `renderAsChoices` output
    (deterministic encoding).
  - Nested case: `seq[seq[int]]` round-trips through
    `lists(lists(integers()))`.
  - `symexWalkerVersion == "3"` AND `renderAsChoicesVersion == "2"`
    after this cycle (both pinned by assertions).
- **GREEN**:
  - Rewrite the three branches in `renderAsChoices` to emit
    continue-boolean + element, terminated by `booleanChoice(false)`.
  - Sort by element (`HashSet`) / by key (`Table`) before
    iterating.
  - ~~Update `readSeqInt` / `readTableStrInt` / `readSetInt` in
    `emitTyAndReader` to consume the new encoding.~~ Dropped in
    cycle 6 — see spec correction above; readers are on the
    independent `RawWitness` codegen path.
  - Bump `renderAsChoicesVersion = "1"` → `"2"` in
    `smt/canonicalize.nim`.
  - **Explicitly rewrite** the failing test at
    `tsymex_phase7_assertcovered.nim:139-145` ("renderAsChoices:
    seq[int] witness → length + elements"). The old test asserted
    `cs.len == 4` with `cs[0].intVal == toInt128(3)` (length
    prefix). New: `cs.len == 7` (three `bool(true)` + three
    elements + one `bool(false)`).
  - Rename `tsymex_canonicalize.nim` test "Phase 11 walker
    semantics bump" → "Walker version constraints" with positive
    pins.
- **Touches**: `nelli/symex.nim`, `smt/canonicalize.nim`,
  `tests/tsymex_phase7_assertcovered.nim`,
  `tests/tsymex_canonicalize.nim`.

### E. Layer 1 — `symexFindAllWitnesses` (5 cycles)

#### 7. tLabel tracer (≈3h)

- **RED**: SUT with two `symexTarget("a")`/`symexTarget("b")`
  markers + explicit DB; macro returns a `seq[SymexFinding]` with
  two entries (sfSat, witnessChoices populated, distinct
  targetDesc); each finding ALSO appears in
  `consumeSymexFindings()` so finalizePhase later picks them up.
- **GREEN**: macro extracts label names via cycle-4 scan helpers;
  hoists a single `let prog = SymexProgram(…)` (not per-target);
  emits a runtime block that loops over discovered targets
  calling `runSymex` per target. For each result, builds a
  `SymexFinding` and calls `recordSymexFinding(f)` before
  appending to the result seq.
- **Macro-time guards**:
  - `fn.getImpl.kind != nnkProcDef` → `error("expected proc")`
  - any `IRParam.isVar` → `error("var-param fn not supported")`
- **Touches**: `nelli/symex.nim`,
  `tests/tsymex_phase12_witnesses.nim` (new).

#### 8. Auto-include `tAssertionViolation` when `irHasAssert` (≈1h)

#### 9. Auto-include `tIndexError` when `irHasIndex` (≈1h)

#### 10. Auto-include `tFieldDefect` when `irHasVariantField` (≈1h)

#### 11. `excludeTargets` escape hatch (≈1h)

- **RED**: SUT with `arr[i]` + `excludeTargets = [tIndexError()]`
  → no tIndexError finding. The default `= []` value compiles
  cleanly (verify Nim accepts empty static openArray default).
- **GREEN**: filter excluded kinds (compare `SymexTargetKind`)
  before invoking symex.

### F. DB cache integration (1 cycle)

#### 12. Per-target cache load before run, save after (≈2h)

- **RED**: call Layer 1 twice on same SUT/DB; instrument DB to
  count load vs save calls. Second call: all loads, zero saves.
  UNSAT findings re-derived on each call (not cached).
- **GREEN**: per-target `loadSymexWitnessesImpl` first; cache
  hit populates SymexFinding from loaded witness; cache miss
  runs symex and `saveSymexWitnessImpl` on SAT.
- **Honest framing in docs**: UNSAT re-derivation is
  O(`queryTimeoutMs`) per target, not "cheap" — documented at
  cycle 21.

### G. Engine helper extraction (1 cycle)

#### 13. `runForAllPipelineWithPhases` (≈1h)

- **RED**: pass `defaultPhases[T]()` to the new helper → same
  result as existing `runForAllPipeline`.
- **GREEN**: extract preamble (deadline wrap, autoLabel sink,
  coverage mode init) from `runForAllPipeline` into the new
  helper that takes `phases: seq[Phase[T]]`. Existing
  `runForAllPipeline` becomes a one-line wrapper.
- **Touches**: `engine.nim`.

### H. symexSeedPhase + Layer 2 (2 cycles)

#### 14. `symexSeedPhase` (≈2h)

- **RED**: hand-crafted seed + falsifying property; phase replays
  via `evalReplay`, sets `rawFalsification` with the actual
  choice sequence, yields to `shrinkPhase`; final report has a
  SHRUNK counterexample (verified by checking choices length <
  the original seed's choices length).
  - Also test: a seed that triggers `AssertionDefect` (via
    `symexAssert` in the property body) → `evalReplay` catches
    it as `ekFalsified` with a recognizable message.
  - Also test: a seed with the wrong shape → `ekRejected` path
    deposits an `sfNotApplicable` finding, doesn't falsify.
- **GREEN**: implement `symexSeedPhase` per the architectural
  sketch (no `except Overrun:`, check `case r.kind`, use
  `sfNotApplicable` for shape-mismatch).
- **Touches**: `engine/phases.nim`,
  `tests/tsymex_phase12_seedphase.nim` (new).

#### 15. `forAllWithSymexSeeds` in `nelli/symex.nim` (≈2h)

- **RED**: integration test calling `forAllWithSymexSeeds` with
  a hand-crafted seed list + falsifying property; report
  includes a shrunk counterexample with `fromPhase: "symexSeed"`.
- **GREEN**: in `nelli/symex.nim`, assemble:
  `[dbReusePhase, explicitExamplesPhase, symexSeedPhase(seeds), randomPhase, targetedPhase, shrinkPhase, explainPhase, finalizePhase]` (wrap bare procs in `Phase[T](name:, run:)` where needed).
  Delegate to `runForAllPipelineWithPhases`.

### I. Sugar macro (3 cycles)

#### 16. `symexForAll` — single-arg fn (≈2h)

- **RED**: end-to-end. SUT
  `proc handle(req: int) = if req == 0: symexTarget("zero")`;
  `let r = symexForAll(integers(), handle, db = db)`; check
  `r.outcome == otPassed`, `r.symexFindings.len >= 1`, and at
  least one finding's `witnessChoices` decodes to req=0.
- **GREEN**: macro emits a `block:` expression that calls
  Layer 1 + extracts SAT witnesses + calls Layer 2.
  Single-arg fn passes through directly as `prop`. Returns
  `untyped` (matches `symexFind`); emitted expression is
  `Report[T]`.

#### 17. `symexForAll` — multi-arg destructuring (≈5h)

- **RED**: SUT `proc f(a: int, b: bool)` + strategy
  `map(integers(), booleans())`. End-to-end report.
- **GREEN**: macro uses `getTypeInst(s)` to walk the
  `nnkBracketExpr[Strategy, …]` and extract the element type
  tuple. Match element-type one-for-one against `fn.getImpl`'s
  formal params. Emit wrapper:
  `proc(t: (int, bool)) = f(t[0], t[1])`.
- Macro-time errors:
  - element-type vs param-type mismatch
  - any param is `var T`
  - fn is generic (typedesc)
- Named-field tuples explicitly out of scope (deferral).

#### 18. Zero-targets fallback (≈1h)

- **RED**: SUT with no markers / no IR triggers. Layer 1 returns
  one `SymexFinding(status: sfNotApplicable, targetDesc:
  "no-targets-discovered")`. `forAllWithSymexSeeds` runs normally
  with empty seed list. Report's `symexFindings` carries the
  finding.
- **GREEN**: macro short-circuits seed list; Layer 1 deposits the
  finding (and `recordSymexFinding` so it appears in the report).

### J. Derandomize verification (1 cycle)

#### 19. `derandomize=true` interaction with symex seeds (≈1h)

- **RED**: `let s = defaultSettings(); s.derandomize = true; s.testId = "t"`;
  call `symexForAll` with this settings. Verify two consecutive
  runs produce identical reports (deterministic) AND the symex
  seed path still runs (not skipped due to derandomize).
- **GREEN**: nothing if the implementation is right; explicit
  verification only.

### K. Docs + memory (3 cycles)

#### 20. Docs sweep (≈2h)

- `docs/symex/README.md` — new "Input-source seeding (Phase 12)"
  section with auto-discovery table + layered API + warm-run
  behavior note.
- `docs/symex/PHASE12_PLAN.md` — cycle status table.
- `docs/SYMEX_PLAN.md` — Phase 12 row + design-decision section.
- `docs/symex/determinism.md` — TWO updates:
  - Version history table extended with `renderAsChoicesVersion`
    column (new "1" entry for current, "2" entry for cycle 6
    bump) alongside the existing walker-version column.
  - **NEW subsection** "Strategy-cache caveat": document that
    changing a strategy's constraints (e.g.,
    `integers(0, 100)` → `integers(200, 300)`) silently clamps
    cached witness values via DataSource's `permits`/`clamp`
    logic. Workaround: use fresh testId.
  - User-facing upgrade note: "Phase 11 collection witnesses
    cached under walker `"3"` and rendering `"1"` are re-derived
    on first run after Phase 12. Non-collection witnesses
    unaffected."
- Cold-cache latency: explicit "N targets × queryTimeoutMs"
  worst-case note in README.

#### 21. SYMEX_PLAN.md status + Phase 12 design-decision section (≈30m)

- Phase 12 row in status block + phase table.
- Design-decision section recording the role-decomposition
  (Layer 1 verifier-equivalent / Layer 2 input-source /
  Layer 3 sugar) and the `symexSeedPhase` + `renderingVersion`
  decisions.

#### 22. Memory updates (≈30m)

- Update `nelli-symex-shipped.md` for Phase 12.
- Update `MEMORY.md` index entry.

## Total estimate

~33h engineering, spread over 3-4 days focused TDD.

## What this closes

- Phase 7 deferred follow-up: input-source role.
- Latent collection-witness bug in `renderAsChoices` (Phases 10/11
  shipped a broken round-trip for `seq`/`Table`/`HashSet`).
- Non-deterministic iteration of `HashSet`/`Table` witnesses in
  `renderAsChoices` (new bug introduced by v2 plan, caught by
  round-2 review).

## What this does NOT close

- **Async / parallel symex.** Sequential per target for v1.
  nim-z3 contexts aren't thread-safe.
- **Discriminator Z3Int promotion** (Phase 11 deferral #12).
- **Strategy-constraint hashing in cache key.** Strategies are
  closures; stable hashing is intractable. Workaround:
  fresh testId on strategy-constraint change (documented in
  determinism.md).
- **Multi-arg fns with named-field tuple strategies.** `map`
  produces anonymous tuples only; named-field destructuring is
  out of scope for v1.

## Deferrals accumulated during the build

Initialized pre-cycle-1 with items round-2 review surfaced as
known-but-accepted limits.

| # | Item | Cycle introduced | Guard | Trigger to address |
|---|---|---|---|---|
| 1 | Strategy-constraint changes silently clamp cached witness values | Pre-cycle (audit) | Documented in determinism.md (cycle 20) + README; user uses fresh testId | Hash strategy constraints if a stable representation emerges |
| 2 | Cross-module private helpers not visible to transitive scan | Pre-cycle (audit) | Documented; same Phase 3 limit | Phase 3 deferral #138 close-out |
| 3 | Markers in branches after `isUnsupported` IR nodes silently invisible | Pre-cycle (audit) | Documented in README; symptom: missing symex targets when SUT uses unsupported constructs | Phase 3+ expansion of supported fragment |
| 4 | `dbReusePhase` short-circuits if DB has stored failure → symex seeds skipped on warm runs | 14 | Documented honestly; users wanting symex audit + stored failure call Layer 1 directly | A consumer wants both signals concurrently |
| 5 | `var T` params in fn | 7 | Macro-time `error()` | A consumer needs `var T` params under symexForAll |
| 6 | Generic procs / typedesc params in fn | 7 | Macro-time `error()` (same as symexFind) | Phase 13?: generic-aware symex |
| 7 | Cold-cache latency: N targets × queryTimeoutMs | 20 | Doc note in README | Per-target latency budget + parallel symex |
| 8 | `derandomize=true` × symex seeds — verified by RED test in cycle 19 but no architectural guarantee | 19 | Cycle 19 explicit test | If `derandomize` semantics change |
| 9 | UNSAT findings re-derived on every call (not cached) — O(queryTimeoutMs) per target on warm runs | 12 | Documented honestly in README (not "cheap"); could be cached if perf demands | A SUT with many UNSAT-prone targets shows latency on warm runs — **CLOSED in Phase 13** (see [RFC-unsat-caching.md](RFC-unsat-caching.md)). Verdict caching for UNSAT and UNKNOWN under three sibling keys; Z3 `rlimit` wired for deterministic UNKNOWN. |
| 10 | `nnkSym` lookups for callee bodies in transitive `isCall` scan — bounded by `getImpl` (Phase 3 cross-module limit) | 4 | Same Phase 3 limit; documented | Phase 3 cross-module fix |
| 11 | `tables`/`sets` round-trip is value-correct but not trace-equivalent under collision (duplicate-keyed iterations) | 6 | Documented in cycle 20 docs; shrinker may take more iterations on collision-heavy witnesses but result is correct | Trace-equivalent encoding (extra metadata) |
| 12 | Multi-arg fn with **named-field** tuple strategy (e.g. `Strategy[tuple[a:int, b:bool]]`) | 17 | Macro-time `error()` — `map` produces anonymous tuples only; user can write a custom anonymous-tuple strategy | A consumer needs named-field tuple seeding |
| 13 | `symexCapture` not armed inside `symexSeedPhase` — target-reach failures during replay are silent | 14 | `symexAssert` violations still surface via AssertionDefect; documented gap for `symexTarget` hit verification | Layer adds `symexCaptureBegin/End` around `evalReplay`, deposits `sfNotReached` finding |
| 14 | Walker-side `RawWitness` readers (`readSeqInt`/`readTableStrInt`/`readSetInt`) still use a length-keyed map (not the new continue-boolean encoding) | 6 (correction) | Independent codepath from `renderAsChoices`/strategy replay; no observable inconsistency — symex's in-process `symexFind` codegen and the DB-round-trip-through-strategy path do not share an encoding | If `RawWitness` ever becomes a wire format that must round-trip through the choice-IR (no current consumer demands this) |
| 15 | `symexFindAllWitnesses(excludeTargets)` is `seq[SymexTarget]` not `static openArray[SymexTarget]` — Nim 2.2 rejects every viable default expression for a `static seq[T]` param, and a `static openArray[T] = []` default nil-crashes at macro-eval iteration | 11 (correction) | Macro inspects the call-site `NimNode` AST directly to extract excluded kinds; call-site ergonomics unchanged (`excludeTargets = @[tIndexError()]`); silent default still works | Nim toolchain fixes `static seq[T] = @[]` default acceptance OR `static openArray[T] = []` macro-iter nil-crash |

## Compatibility

- **`symexWalkerVersion` stays `"3"`** (Phase 11). Walker
  semantics unchanged.
- **`renderAsChoicesVersion` `"1"` → `"2"`** in cycle 6.
  Collection witnesses (`seq`/`Table`/`HashSet`) cached under
  `"1"` become invisible. Non-collection witnesses (int, bool,
  string, tuple, object, variant) stay warm.
- **`Phase[T].run` calling convention** flips from `{.nimcall.}`
  to `{.closure.}`. Existing top-level phase procs coerce safely;
  no caller change required.
- **`SymexFindingStatus.sfNotApplicable`** added — non-breaking
  enum extension; existing exhaustive `case` matches updated in
  cycle 5.

Three new public surfaces (`symexFindAllWitnesses`,
`forAllWithSymexSeeds`, `symexForAll`); one new pipeline phase
(`symexSeedPhase`); one extracted helper
(`runForAllPipelineWithPhases`); the `engine/types.nim` sink
relocation is internal (re-exports preserve callers).

## Design decisions (committed, not asking)

| Decision | Choice | Why |
|---|---|---|
| Auto-discovery vs. flag | Auto, IR-scan driven, transitive through `ParseCtx.procs` callees | SUT's IR already carries every signal; transitive scan honors what `parseProc` could see (Phase 3 limit applies) |
| Strategy combinator vs. `forAll` variant | `forAll` variant + new `symexSeedPhase` | Strategies stay pure; seeding is engine concern; new phase needed because `explicit` phase discards choice sequences on failure (no shrinking) |
| Defect targets — opt-in or opt-out? | IR-presence-driven (auto when the operation is in the SUT) | Universal markers; `excludeTargets` is the perf escape hatch when user has bounds-guards |
| Cache via Phase 10? | Yes for SAT witnesses; UNSAT/UNKNOWN re-derived (honest about cost) | Content-addressed key handles SAT correctness; UNSAT cost documented in cycle 20 |
| Cache key covers strategy constraints? | No — documented limitation (deferral #1) | Strategies are closures; no stable hash |
| New pipeline phase? | Yes — `symexSeedPhase`. **`{.closure.}` Phase[T].run** required | `explicit` phase contract is "no shrinking"; symex witnesses ARE shrinkable |
| Replay failure handling | `evalReplay` catches Overrun → `ekRejected`; phase deposits `sfNotApplicable` finding; AssertionDefect / IndexDefect / FieldDefect → `ekFalsified` (correct: witness IS a real defect) | Round-2 review verified `evalReplay`'s contract; no `except Overrun:` block needed |
| Three-layered API? | Yes | Layer 2 (`forAllWithSymexSeeds`) has real internal complexity (custom pipeline assembly via `runForAllPipelineWithPhases`) — earns public exposure |
| Layer 1 return type | `seq[SymexFinding]` AND records to sink threadvar | Preserves target identity + audit metadata in return value; sink ensures findings flow into `Report.symexFindings` |
| Sink module location | `engine/types.nim` (moved from `symex.nim`) | Where `SymexFinding`/`SymexFindingStatus` already live; allows `engine/phases.nim` to record without circular import |
| `excludeTargets` spelling | Constructor form (`tIndexError()`) | Consistency with `assertCoveredBy(fn, tIndexError())` |
| `inMemoryDatabase()` default? | No — DB is required | Caching across calls requires explicit DB lifetime; per-call default would silently defeat the cache |
| Multi-arg fn destructuring | Macro inspects `fn.getImpl`'s formal params via `getTypeInst(s)` to match strategy element-type tuple; emits positional splat wrapper; rejects mismatches and named-field tuples at macro time | Matches existing `isStrategyArg` pattern in `strategy.nim` |
| Zero-targets status | `sfNotApplicable` (new enum case) | Distinct from `sfUnsat` ("searched & proved unreachable") |
| `renderAsChoices` collection encoding | Fixed to continue-boolean protocol matching `lists`/`tables`/`sets`, with **sorted iteration** for Table/HashSet | Round-trip is `renderAsChoices`'s purpose; the old encoding was a latent bug; sorting ensures deterministic cache keys for same logical witness |
| Walker version separation | `symexWalkerVersion` (walker semantics) and `renderAsChoicesVersion` (witness encoding) are separate constants, both in cache key | Walker semantics unchanged by Phase 12; rendering changed for collections only — separate versions allow non-collection witnesses to stay warm across the upgrade |
| `Phase[T].run` calling convention | `{.closure.}` (was `{.nimcall.}`) | Pipeline assembly with captured state (seed list) requires closure |
| `forAllWithSymexSeeds` module placement | `nelli/symex.nim` | Public symex entry point; imports `engine.nim` cleanly (no cycle) |
| Pipeline order | `dbReuse → explicit → symexSeed → random → targeted → shrink → explain → finalize` | dbReuse priority preserves regressions; symex seeds before random (derived inputs before exploration) |
| AssertionDefect handling in `symexSeedPhase` | Caught by `evalReplay` as `ekFalsified`; treated as legitimate falsification (witness IS a real violation), shrunk normally; explicit cycle-14 test verifies the message is recognizable | symex's whole purpose is finding witnesses that violate stated invariants |
