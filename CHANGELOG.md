# Changelog

Notable changes to nelli. Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
versioning is [semantic](https://semver.org/spec/v2.0.0.html).

> **Why this file now.** Releases through 0.6.0 carried their notes in the
> release commit message alone. That works while the surface is additive; it
> stops working the moment a downstream maintainer has to migrate. 0.7.0 is
> breaking in three separate ways, and the one real downstream (chapulin) has
> **not yet absorbed 0.6.0's own breaking change** — so it must migrate across
> two releases at once, from a document it can actually find. 0.6.0 is
> reconstructed below from its release commit for exactly that reason.
> RFC-z3-optional S5 adopted this as a deliberate practice, not a one-off.

## [Unreleased] — 0.9.1

The fixes from the wiring audit that ran after the 0.9.0 tag (RFC-0005,
handoff entry "2026-11-03 — Wiring audit", WA-1 to WA-13). Upgrading:
`docs/migration/0.9.1.md`. Three of the fixes are regressions that 0.9.0
shipped against 0.8.0; they come first.

### Fixed — regressions against 0.8.0

- **Seq `items`/`pairs` whose body changes the seq's length** (WA-3). Nim's
  `items` and `pairs` read the length once and assert it is unchanged after
  each step, so a body that grows or shrinks the seq ends the loop in
  `AssertionDefect`. The walk bounded the loop by the live length with no
  assert, so `for _ in s: discard s.pop()` was a clean false `sxSat` for a
  target after the loop and a clean false `sxUnsat` for one in `except
  AssertionDefect`. 0.8.0 gave `sxUnknown` there. Both iterators now use the
  length-assert model `mitems`/`mpairs` already had; in a module where
  `assert` may be compiled out the loop declines, as `mitems` does.
- **`symexFindAllWitnesses` and `symexForAll` see user exception types**
  (WA-1). They built their program without the user exception hierarchy that
  `symexFind` passes. 0.8.0 omitted it too, but 0.9.0 reads an exception type
  it does not know as ⊤ (`eeUnknownExnType`): a named `except` of a user type
  (or `RegexError`) was skipped, and a verdict `symexFind` decided came back
  `sfUnknown` where 0.8.0 gave `sfUnsat`. The cache key now covers the
  hierarchy (below), so a changed parent type is a new key.
- **A witness that ends its process after reaching the target is not run in
  the host** (WA-2). A replay that reached the target and then exited
  (`quit`, a raw `exit`), was signalled or ran past `replayTimeoutMs` was
  confirmed with nothing saying how it ended, and `assertCoveredBy`'s splat
  and `symexForAll`'s seeds then ran the same witness in the calling process,
  which it ended or hung. 0.8.0 replayed nothing and declined such a
  candidate. The claim still stands (the target is reached), but it now
  carries `Soundness.witnessUnsafe` and a `feReplayCrashed` or
  `feReplayTimedOut` hint saying how the child ended and on what input.
  `symexForAll` does not seed such a witness, cold or from the cache.
  `assertCoveredBy` never splats it: with no `testFn`, the confirming replay
  is the coverage and the check passes; with a `testFn`, or on an `sxRaised`
  claim (whose replay targeted the raise, not the check's target), the check
  fails with an `AssertionDefect` that says why.

### Fixed — wrong on 0.8.0 too

- **Float checks in an opaque callee** (WA-4). An inert `{.symexOpaque.}`
  callee's defect scan assumed the default checks. A callee compiled with
  `nanChecks` or `infChecks` on (by `push`, or `floatChecks`) raises
  `FloatInvalidOpDefect` or `FloatOverflowDefect` from float arithmetic, and
  neither was forked: a target in `except FloatingPointDefect` around the
  call was a clean false `sxUnsat`. The scan now reads each scanned routine's
  check options (`routineChecks`), the callee's and every routine it calls. A
  callee compiled with a check OFF now forks a `Defect` it cannot raise; that
  fork carries `feOpaqueEffectHavoc`, so a hit through it is replayed and
  refuted (`sxUnknown`), and an `sxUnsat` stands.
- **Argument order of a statement-position opaque call** (WA-5). The
  statement-position opaque and foreign arm, and the `{.symexTransparent.}`
  fallback beside it, parsed arguments one after another, so a later
  argument's call ran before an earlier argument was read: `opq(v div b,
  bump(b))` with `b == 0` divided by the bumped `b`, a clean false `sxSat`
  after the call and a clean false `sxUnsat` in `except DivByZeroDefect`.
  They now read arguments where Nim's C backend does (`parseOrderedArgs`),
  as the expression-position arm already did.
- **A deleted `{.symexTransparent.}` call keeps its arguments' checks.** A
  transparent call in statement position whose arguments are inert is
  deleted. Its arguments were parsed and their values thrown away, so a check
  an argument carries was never forked: `trv(v div b, 0)` with `b == 0` was a
  clean false `sxUnsat`. Each argument that is not a literal or a variable is
  now bound to a sink `let`, as `discard <expr>` is.
- **A cached `sfRaised` finding is the cold one** (WA-10). A `:raised` hit
  kept only its status and soundness: the `raised(<type>)` descriptor,
  `defectTypeId` and the witness were lost. The `:raised:<type>` sentinel now
  stores the witness and the defect-ness.
- **The no-targets finding carries `soundness`, `gaps` and
  `annotationViolations`** (WA-12), derived from the parse-time errors, as
  every other finding does.

### Changed

- **Lossy clean winners are replayed** (WA-9). A clean winning path whose
  witness renders lossily (a `wfLossy` parameter shape, or a run whose
  extraction substituted a value, `feExtractionFailed`) was `trusted()`
  though nothing had run that witness. It is now replayed as the settle's one
  job. A confirmation makes it `rsConfirmed`; any other outcome, or
  `SymexSettings.replay = false`, leaves it `rsUnconfirmed` (new, below) with
  a hint, and its status stands. **This widens when `fn` runs at verdict
  time** (the S10 execution contract, 0.9.0 migration note §1.1): a clean
  `sxSat`/`sxRaised` with a lossy witness now executes `fn` once, in a child.
- **A run-dependent `:unk` is not cached** (WA-7). A replay left undecided
  for a reason of the run (a child killed at `replayTimeoutMs`, one ended at
  the replay's memory limit, or one that could not be started or handed its
  state at that moment, including a runtime hook the host had set) no longer
  stores a permanent `:unk`; the next run replays again. An `rsUnconfirmed`
  lossy winner left so for such a reason is not stored either.
- **The cache key gains two parts.** `|rm=<mode>` says how the build replays
  (`fork`, `reexec` or `none`, plus `+panics` under `--panics:on`), so a
  database shared across platforms or builds does not serve one build's
  `:unk` to another that would confirm (WA-8). `;uxh=[...]` in the program's
  canonical form keys the user exception hierarchy, and is absent when there
  is none (WA-1).
- **The soundness cache encoding is version 2**
  (`"2:<pathTaint>:<runTaint>:<replay>:<unsafe>"`), which stores
  `witnessUnsafe`. A version-1 entry cannot say a stored witness is safe to
  run, so it is a miss.
- **Walker version 268** (264 in 0.9.0). The cache's key and value changed,
  so every 0.9.0 cache entry is orphaned: a miss, then a cold run.
- `SymexResult.fromCache` is documented as always `false`: `symexFind` has
  no cache. The 0.9.0 migration note (§2) said otherwise. The cache-hit flag
  is `SymexFinding.fromCache`.
- `trustedSat` reads `rsUnconfirmed` as untrusted; `rsNotNeeded` keeps its
  0.9.0 meaning (trusted unless the path is `scSpurious`).

### Added

- **`SymexFinding.hints` and `SymexFinding.diagnostics`** (WA-6). `hints:
  seq[FindingHint]` holds every entry of the run's error list that `gaps`
  leaves out, the replay outcomes among them: `feReplayCrashed` names the
  input the real fn crashed on, and `feReplayDeclined` says why a replay did
  not run (the Windows guidance in the 0.9.0 migration note, §5a and §7, can
  now be followed through `symexForAll`). `diagnostics:
  seq[FindingDiagnostic]` holds the raises the run reached that did not
  decide the verdict, each with its witness. `symexFindAllWitnesses` and
  `assertCoveredBy` fill both, and a cache hit serves the cold run's, from a
  new `:notes` record.
- **Every report format renders them.** A finding with neither renders as
  before. `ofText` (and `ofJunit`'s `<system-out>`, which carries the same
  text): a `hint <kind>: <msg>` line per hint and an `also raised
  <type>[ (defect)][: <msg>] witness=<n> choices` line per diagnostic, under
  the finding. `ofJson`: `"hints"` (`kind`, `severity`, `msg`) and
  `"diagnostics"` (`raisedTypeId`, `isDefect`, `raisedMsg`,
  `witnessChoiceCount`) arrays on every symex finding, `[]` when empty.
  `ofGithubAnnotation`: a `::notice title=symex hint::` line per hint.
- **`Soundness.witnessUnsafe: bool`** (WA-2): the confirming replay's child
  reached the target and then did not finish. Only a replay sets it.
- **`ReplayStatus.rsUnconfirmed`** (WA-9), tail-appended: a clean winner with
  a lossy witness that no replay confirmed. Not `trusted()`. An exhaustive
  `case` over `ReplayStatus` needs an arm.
- New exports, by module:
  - `nelli/engine/types` (so `import nelli`; `nelli/symex` re-exports only
    `SymexFinding`, `SymexFindingStatus`, `FindingGap` and `trusted` from
    it): `FindingHint` (`kind`, `severity`, `msg`, as strings) and
    `FindingDiagnostic` (`raisedTypeId`, `isDefect`, `raisedMsg`,
    `witnessChoices`).
  - `nelli/symex`: `CachedNotes`, `saveSymexNotesImpl` and
    `loadSymexNotesImpl` (the `:notes` record). `CachedRaised` gains a third
    field, `choices` (the stored witness), and `saveSymexRaisedImpl` an
    optional trailing `witnesses`. Neither breaks a call; a positional
    unpack of `CachedRaised` into two names does.
  - `nelli/smt/canonicalize` (import directly): `replayModeSegment`, and
    `symexCacheKey` gains a trailing `replayMode = replayModeSegment()`.
  - `nelli/smt/replayproc` (import directly): `lastReplayEnding`,
    `resetReplayRunDependence`, `replayRunDependent` and `refusedHostHook`;
    `ReplayChild` gains `outOfMemory` and `runDependent`.

### Known limitations

- **macOS and musl report exit code 0 in a replay hint.** Where libc has no
  `on_exit`, the forked child's exit hook is `atexit`, which is not told the
  status, so a `feReplayCrashed` hint reads "exited the process with code 0"
  for any `quit(n)` or C `exit(n)`. The ending and every verdict are right;
  only the code in the message is not. Linux with glibc, and the re-executed
  child (Windows, `-d:nelliReplayReexec`), report the real code.
- The others are tracked in `docs/rfc/0016-native-parity-hardening.md` §5.8
  (INT-22 to INT-27). Two to know about: a clean, faithful winner (one
  nothing replays) that crashes after its target still runs in the host
  through `assertCoveredBy`/`symexForAll`, as on 0.8.0; and under
  `--panics:on` every lossy winner is `rsUnconfirmed`, because nothing
  replays there.

## [0.9.0] — 2026-11-03

RFC-0005, soundness channels. Each symex result now says how far to trust it:
a decline costs only the paths that reach it, an answer the analysis could not
model is checked by running the SUT, and what remains untrusted names its
cause.

Upgrading: `docs/migration/0.9.0.md`. **Read its §1 before you upgrade.** The
symex entry points can now execute your SUT, and that SUT must link and load.
Neither change produces a compile error. Open gaps, including where Windows
answers less than Linux and macOS, are in its §7.

### Changed

- **`fn` is executed at verdict time** (RFC-0005 S10). A witness on a path
  through something the analysis could not model is replayed by calling `fn`
  on it, and it is reported `sxSat`/`sxRaised` only if the real run reaches
  the target. The SUT's side effects happen for real, in a child process
  (below): effects outside it, such as files and sockets, are not undone.
- **`fn` must link and load** into the calling binary when replay is on. An
  undefined `importc` fails the link, and a missing `dynlib` (e.g. PCRE1 for
  `std/re`) fails at start-up. To opt out, set `SymexSettings.replay = false`
  (cache key `;rp=off`).
- **Every replay runs in a child process** (RFC-0005 S8ct), so nothing a
  replay does can end or corrupt the calling process: a `quit`, a raw C
  `exit`, a nil dereference, unbounded recursion or a runaway allocation used
  to end the whole test binary.
  - POSIX forks the child. Windows re-executes the program and hands the child
    the witness and the variables the SUT reaches; what cannot be handed over
    declines (`feReplayDeclined`, message `replay not marshallable: ...`), so
    the same SUT can be `sxUnknown` on Windows and decided on Linux or macOS.
    The shapes are listed in the migration note, §5a.
  - A replay's effects, stdout and stderr stay in the child. Use
    `replayExecutions()` to observe whether a replay ran.
  - A child that ends before reaching the target is `feReplayCrashed`, a hint
    on an `sxUnknown`, never a refutation. `replayTimeoutMs` kills the child.
  - `runReplayBounded`, `replayStackSize`, `replayAbandonedLive`, `ReplayRun`,
    `rrEnded`, `rrContended`, `roContended`, `ptrAimsSnapshot` and
    `ptrAimsAdopt` are removed.
- **Routines compiled with other runtime checks decline** (RFC-0005 S8cu). A
  routine compiled with `fieldChecks`, `overflowChecks`, `rangeChecks`,
  `boundChecks`, `objChecks` or `checks` off, or with `floatChecks`,
  `nanChecks` or `infChecks` on (by `push`, a pragma statement, the command
  line or `-d:danger`), gives `sxUnknown` with `feCheckOption` or
  `feOverflowCheckOption` on the paths that reach it. 0.8.0 gave the checked
  verdict, including raises that never happen. The rule, its spellings and its
  limits are in the migration note, §5.
- **A nil dereference is a crash finding** (RFC-0005 S8cu): an
  `sxRaised NilAccessDefect` at the SUT boundary, whatever `except` or
  `finally` encloses it, as Nim 2.2.10 runs it. In a `--exceptions:setjmp`
  build it declines under a `try` (`heNilDerefMayBeCaught`).
- **Declines are kinded and scoped.** 37 `SymexErrorKind` members are new
  since 0.8.0, each with the `DegradeClass` that names its lever; they are
  listed by class in the migration note, §3.3. A `SymexErrorInfo` built by
  hand needs a `scope` (§1.4).
- **Verdicts are more precise** (RFC-0005).
  - An over-taint-only run proves `sxUnsat`.
  - The blanket decline vetoes are gone, and unreached declines are
    `sevHint`.
  - Many previously declined Nim shapes are modelled.
  - Several Nim-unfaithful semantics are corrected, including float→int,
    `low(T)` negation/`div`, `mod`, slices and `finally`/`defer`.
  - Each moved verdict is listed in the migration note, §4–§5.
- **The cache helpers carry soundness.** `saveSymexVerdict(Impl)` takes a
  `Soundness`. `loadSymexVerdict(Impl)` returns `Option[CachedVerdict]`, and
  `loadSymexWitnesses(Impl)` returns `seq[CachedWitness]`. A custom
  `ExampleDatabase` used with the symex cache must implement
  `saveWithMetaImpl`/`loadPrimaryWithMetaImpl`.
- `RawResult.pathTaint` → `RawResult.soundness.pathTaint`.
- `ResourceBudget.maxBytesEncodingLen` and
  `SymexErrorKind.heRefVariantUnsupported` are removed.
- The walker version bump invalidates every symex cache entry.

### Added

- **`Soundness`** (`pathTaint`, `runTaint`, `replay: ReplayStatus`) on
  `SymexResult` and `SymexFinding` (RFC-0005 S11).
- **`trusted(r)`**: the one predicate to branch on, for results and
  findings.
- **`gaps(r)`**: each cause behind an untrusted result, with the
  `DegradeClass` that names its lever. `SymexFinding.gaps` carries it as
  `FindingGap`s.
- **`SymexResult.bounds`**: the `ResourceBudget` the run used, so an
  `sxUnsat` states the bounds it is a proof under.
- **The annotation-violation channel**: `annotationViolations` on
  `SymexResult` and `SymexFinding` reports a false `{.symexTransparent.}`
  promise without changing the verdict.
- **Symex findings in every report format**:
  - `ofText`: a `[symex]` section;
  - `ofJson`: `symexFindings`;
  - `ofJunit`: `<system-out>`;
  - `ofGithubAnnotation`: an `::error` per violation and a `::warning` per
    untrusted finding.

  Output is unchanged when there are no findings.
- `ResourceBudget.maxSeqLen` and `seqQueryRLimit`, along with
  `symexLoopIterations`, `loopPruneRLimit` and `defaultLoopPruneRLimit`.
- New `SymexErrorKind` members, all tail-appended. They are listed in the
  migration note, §3.3.

## [0.8.0] — 2026-09-08

Upgrading: `docs/migration/0.8.0.md`. **Read it before you upgrade** — this
release changes what existing code *means* without breaking any build, so
neither the compiler nor the version number can tell you which of your call
sites moved.

### Changed

- **A partial object literal now carries its type's defaults.** This is the
  headline and it is a *silent* behaviour change: every literal that compiled
  before compiles after, and means something different. Nim zero-fills the
  fields an object literal does not list, and nelli's configuration objects
  carry meaningful non-zero defaults — so the documented idiom shipped a
  different engine than `defaultSettings()`, with no warning, no error and no
  symptom except worse testing. `Settings`, `SymexSettings`, `ResourceBudget`,
  `BmcSettings`, `IntegerBiasConfig` and `OrchestratorPolicy` now declare their
  defaults on the fields, so `T()` **is** the documented default configuration
  and a partial literal differs from it only in what it lists.

  An explicitly-written zero still means zero. That is what makes this
  mechanism viable where every sentinel and merge scheme failed:
  `maxShrinks: 0` (unbounded), `targetedSAIters: 0` (SA off) and
  `useSA: false` all keep saying what they look like they say.

  **Read `docs/migration/0.8.0.md` before upgrading.** It carries the per-field delta tables, runnable greps and a
  triage recipe. The short version: if you meant the zeros, write them
  explicitly *before* you upgrade.

  The sharpest instances, for calibration:
  - `Settings(maxExamples: 7, seed: 42)` — the README's own example — left
    `maxRejections` at 0, and the first rejection ended the run as
    `otExhausted`. Any filtered or `assume`-using property reported exhaustion
    after about two examples, on a property that holds.
  - The symex suite's ten `const SymexSettings(...)` literals left
    `arithChecks` empty, so no arithmetic defect fork was emitted at all and
    `OverflowDefect`/`DivByZeroDefect`/`RangeDefect` were unreachable.
  - `BmcSettings(maxDepth: 5)` — the idiom `bmc.nim`'s own doc comment
    recommended — left `maxStates` at 0 and returned `bmcExhaustedBudget`
    before expanding a single state.

- **`0` now means unlimited on both `BmcSettings` caps.** It previously meant
  "stop immediately", which is the worst available reading of a value a caller
  might deliberately write. This matches the convention `ResourceBudget`
  documents — a convention the stage-4 review then found `ResourceBudget`
  itself did not keep; see below.

- **`ResourceBudget`'s "0 = unlimited for every field" was false for four
  fields**, and is now true for two more of them. `maxClosureInlineCount` and
  `maxBytesEncodingLen` were missing the `cap > 0 and` guard their siblings
  had, so an explicit `0` exhausted the budget on the *first* use and degraded
  the run to `sxUnknown` — the opposite of what the type promised, and of what
  this release's own migration notes said you could rely on. Both now
  honour `0`.

  Three fields are documented exceptions where `0` does **not** mean
  unlimited. `maxCallDepth` is the one to know about: its check is ordinary
  *native* recursion in the walker, so removing the cap does not widen the
  search, it removes the only thing between the walker and the host stack —
  `maxCallDepth: 0` segfaults on ordinary linear recursion. It exhausts
  immediately by design. Do not assume a large round number is safe either;
  the ceiling bounds native stack depth and was measured near 85 on one
  build, so `maxCallDepth: 1000` crashes. `maxLoopUnwind` (`>= 1`, a
  decidability bound) and `seqInlineThreshold` (a strategy selector, where 0
  means the opposite of unlimited) are the other two. Full table in
  `docs/migration/0.8.0.md`.

- **An explicitly all-zero `IntegerBiasConfig` is honoured rather than
  rescued.** It was a sentinel for "use the library default"; it now means an
  unbiased uniform draw. Only affects callers who wrote the zeros on purpose.

### Deprecated

Warnings, not errors; all removed at the next major.

- `withSymexSettings` — write the `SymexSettings(...)` literal.
- `` `+` `` on `SymexSettings` and `ResourceBudget` — set the field on the base
  value. These had no production callers.
- `resolved()` — now the identity function.
- `orchestratorPolicy()` — write the `OrchestratorPolicy(...)` literal.
- `optimisedSymexSettings()` — byte-identical to `defaultSymexSettings()` since
  the Phase-2 endpoint; its doc comment claimed otherwise until now.
- `looseSymexSettings()` — use the new `looseSymexSettingsPreset` **const**,
  which carries the identical value. This RFC argues against preset *procs*
  as a second construction path beside the literal, and the library was not
  following its own prescription. A rename was unavoidable regardless: Nim
  does not allow a `const` and a `proc` to share an identifier.

`defaultSettings()`, `defaultSymexSettings()`, `defaultResourceBudget()` and
`defaultIntegerBias` are deliberately **not** deprecated yet. Deprecating them
in the same release that already changes what every partial literal means would
be two migrations at once.

### Fixed

- **`given x in <a Strategy type alias>` now fails with a message that names
  the mistake.** `type MyStrat = Strategy[int]` followed by `given x in
  MyStrat` is a typedesc, so the round-D sugar expanded it to
  `arbitrary(Strategy[int])` and the user got "cannot derive a strategy for
  `Strategy[int]`" — advice to write `newStrategy(...)` when the real error
  was passing a strategy TYPE where a strategy VALUE was meant.
- **`ResourceLimits.stdoutBytes` is marked NOT ENFORCED.** It is declared, and
  `FUZZ_PLAN.md`'s D16 describes it as applied via `setrlimit`, but nothing
  reads it — while its siblings `addressSpaceBytes` and `cpuSeconds` genuinely
  are applied. Setting it does nothing and reports no error. Documented rather
  than removed, since the capability is still wanted.

- **`examples/symex_loops.nim` had not compiled since CR-9(b)** moved the
  resource caps onto a `budget` sub-object, and **`examples/symex_oob.nim`
  compiled but failed at runtime** — Phase 15 made an out-of-bounds access a
  raise path, so `tIndexError` yields `sxRaised`/`raisedWitness`, not
  `sxSat`/`witness`. The README's own symex snippet had the same CR-9(b)
  breakage. Nothing compiled `examples/`, and compiling is not running.
- **`validateSymexSettings` is now called.** It was exported, unit-tested and
  invoked by nothing in `src/`. Its "arithChecks is empty" warning is exactly
  the defect above; it now runs at macro time, at zero runtime cost, on every
  entry macro that walks a SUT under caller-chosen settings — `symexFind`,
  `assertCoveredBy`, `concolicCollect`, `concolicFlip`, and
  `symexFindAllWitnesses` (and, transitively, `symexForAll`). A follow-up
  review found the first cut wired only `symexFind`/`assertCoveredBy`, so
  the identical `arithChecks: {}` literal warned there but not on
  `concolicCollect`; all five now share one internal chokepoint so a future
  entry macro gets the check by construction rather than by a call site
  someone remembers to add.
- **`arbitrary`'s "cannot derive" error now says what to do.** It named the
  type and stopped. It now lists what derivation covers, notes that a
  supported-looking type may simply have an unreachable definition, and gives
  the three escape hatches (`newStrategy`, `map`, or defining an `arbitrary`
  overload that every containing type then picks up).
- **Four registered-nowhere symex suites** (`tsymex_phase13_rlimit`,
  `_layer1_wire`, `_acceptunknown_guard`, `_unknown_roundtrip`) are registered
  in `nelli.nimble`, so they run in the sweep and in the `symex-mingw` corpus
  it derives.

### Added

- **`given x in int`** — a `given` binding may name a type instead of a
  strategy, and derives it via `arbitrary`. Mixed bindings work unchanged:
  `given a in int, b in integers(0, 10), c in bool`. (The obvious spelling
  `given x: int` is not the one that landed: the colon produces a different
  AST shape from the `in` infix the parser requires, and `given x: int, y in
  ys` does not parse as intended at all, because the colon swallows the
  remainder.)
- `scripts/sweep.sh` and `scripts/sweep-diff.sh` — a whole-suite parallel
  sweep and a baseline diff. There was previously no command that ran the
  whole suite: `psweep.sh` covers only `tsymex_*`, and `nimble test` is a
  serial loop that includes suites which hang on Linux. The sweep also reports
  registry drift; 92 test files on disk are registered in neither
  `nelli.nimble` nor any CI leg.
- `scripts/check-examples.sh`, plus an examples build step on the
  `symex-mingw` leg. Adding examples to `nimble test` would have bought zero
  CI coverage, because nothing in CI runs that task.

## [0.7.0] — 2026-08-29

Upgrading: `docs/migration/0.7.0.md`.

### Fixed

- **`import nelli` no longer reaches Z3.** v0.6.0's Track-G C4 wiring made
  `fuzzmacro` auto-build a real concolic bridge for every caller, which forced
  `import ./symex` into core and pulled Z3 into the base import surface. That
  silently broke a contract `README.md` documents and `tests/tsmoke.nim`
  asserts — and `tsmoke` sat red for a whole release because no workflow ran
  it. Both the property and its CI pin are restored: a compile-only probe
  (`tests/tz3free_probe.nim`) now runs on both Windows fuzzer legs with every
  config source skipped and the nimblepath withheld, and `tsmoke` runs as a
  named step alongside it.

### Added

- **`nelli/concolic`** — the opt-in door for concolic-assisted fuzzing, and
  the only module in the fuzz stack that imports the walker.
  - `fuzzConcolic(strategy, property, settings)` — the documented default
    form. It names the strategy and property once and generates both uses, so
    the pair the campaign draws from and the pair the assist solves for cannot
    diverge.
  - `concolicAssist(strategy, property, stallRounds = 1, maxBranchAttempts = 8)`
    — builds the assist as a value, for composition.
  - `guardSolverUnavailable` — see *missing libz3* below.
- **`ConcolicAssist`** (in `nelli/fuzz`, Z3-free): a bridge plus the
  activation policy that fires it, as one value.
- **Graceful degradation when `libz3` cannot be loaded.** Previously a failed
  lazy load aborted the entire campaign — an optional feature killing the
  whole run. The assist now catches `SoftlinkError` (and only that; a solver
  that computes something *wrong* still raises), latches so a broken load is
  not retried every stall round, and reports the new `cfoSolverUnavailable`
  outcome while the campaign completes on ordinary mutation.
- **`ConcolicAssistError`** — raised at campaign start for a hand-built
  `ConcolicAssist` that names an activation policy but carries no bridge.

### Changed

- **BREAKING: `import nelli` no longer re-exports `nelli/symex`.** Concolic
  fuzzing needs `import nelli/concolic`; symbolic execution needs
  `import nelli/symex`. Forgetting the import is a compile error, never a
  silent no-op.
- **BREAKING: `GuidanceConfig.stallRounds` and
  `GuidanceConfig.concolicMaxBranchAttempts` are removed.** They were a fossil
  of auto-wiring: while core built a bridge for everyone, bridge presence
  carried no user intent, so a second knob had to. That made either-key
  omission a silent no-op. The policy now travels with the assist, and
  `stallRounds` defaults to the *active* value.
  - Migration: `fuzz(s, p, FuzzSettings(guidance: GuidanceConfig(stallRounds: 1)))`
    → `fuzzConcolic(s, p, FuzzSettings())`. The old spelling is a compile
    error naming the missing field, which is a better diagnostic than any
    runtime warning.
- **BREAKING: `fuzz`'s `concolicBridge` parameter is now `assist: ConcolicAssist`.**
  Affects direct `proc fuzz*[T]` callers only.
  - Migration: `concolicBridge = b` → `assist = ConcolicAssist(bridge: b, stallRounds: 1)`.
- **A non-nil bridge with `stallRounds <= 0` is now coerced active, not
  inert.** Assist present ⇒ assist active; "off" is spelled by passing no
  assist. This inverts the old "opt-in required" behavior *at the `fuzz` entry
  points only* — the raw `newOrchestrator` seam deliberately keeps
  `concolicBridge` and `OrchestratorPolicy.stallRounds` as independent knobs,
  where "bridge configured, `stallRounds` 0 ⇒ inert" remains the contract.
- `symexTarget` / `symexAssert` / `symexAssume` and the `assertCoveredBy`
  capture cluster moved to `nelli/engine/markers`, reachable from bare
  `import nelli`. **No migration needed** in either direction: they resolve
  under `import nelli` and are still re-exported by `nelli/symex`. This is
  what keeps marker-annotated production code compiling without a solver in
  its build.
- `docs/fuzz/INTERFACE.md` is now checked by `tests/tfuzzpackaging.nim`
  instead of being normative by convention. It had drifted.
- The package version is pinned across all three of its sites
  (`nelli.nimble`, `milpa.kdl`, `nelliVersion`), which had drifted to
  0.6.0 / 0.4.0 / 0.1.0.

## [0.6.0] — 2026-08-28

Reconstructed from the release commit (`1f50752`) because chapulin has not yet
migrated across it and 0.7.0 compounds it.

### Added

- RFC-fuzzer-nextgen: the isolated-executor track (process/fork workers, the
  centralized orchestrator, lifecycle and circuit breakers), the coverage and
  cmplog shared-memory transports, the scheduling track (Entropic power
  schedule, UCB1 operator bandit, havoc stacking, corpus culling,
  checkpointing), and the concolic-assist track.

### Changed

- **BREAKING: `FuzzSettings` was regrouped (ADR-0031).** The guided-fuzzing
  knobs moved from the flat settings object onto three nested config objects —
  `ExecutorConfig`, `GuidanceConfig`, `SchedulingConfig`. The core fields
  (`maxIterations`, `database`, `persistKey`, …) stay flat.
