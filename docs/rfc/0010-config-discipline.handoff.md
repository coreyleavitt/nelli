# RFC-0010 config-discipline — handoff

- **Stage:** 2 (design review). **Round 1 done** 2026-09-03, **round 2 done**
  2026-09-04, both on `fable`, five lenses (depth, breadth, design & ergonomics,
  feasibility, liveness).
- **Status:** seed → **draft**. Size raised **S → M** (round 1) → **L**
  (round 2). Value raised **med → high**.
- **Blocked on:** nothing. The mechanism fork closed empirically in round 1; the
  §8 escalation closed 2026-09-04 — Corey chose **(c)**, the riders stay in this
  RFC as a separate trailing round D, never interleaved with A/B/C. Round 2
  raised no forks.
- **Resume:** implementation started 2026-09-04 under `/loop`. See
  **Execution log** below for the live slice states; the ledger further down is
  the round-2 plan as written.
- **Branch:** `rfc-0010-config-discipline`.

## Execution log (2026-09-04, `/loop` + `/tdd`)

- **A0 — done** (`549ef5f`). `scripts/sweep.sh` + `scripts/sweep-diff.sh`.
  Findings that changed the plan:
  - The run set is the **filesystem**, not `nelli.nimble`'s list, because
    **92** `tests/t*.nim` are registered nowhere — not four. Round 2's four
    dark files are a subset of a much larger drift; `sweep.sh` emits a
    `.drift` report so it stays visible.
  - The gate is `sweep-diff` against a recorded baseline, not "the sweep
    passed". The suite is not green on a good day, and asking the binary
    question is how pre-existing red gets read as a regression or a real
    regression gets waved through.
- **A1 groundwork — done** (`58c7bc1`). `tests/tconfigcharacterize.nim` and
  `tests/zerofill.nim`; both deleted by A3.
  - The pin is a macro, not hand-written fields. `zeroFilled(T(a: x))` →
    `var tmp: T; tmp.a = x; tmp`; a bare `var` zero-fills even when the type
    declares field defaults (§3), so the site means the same thing on both
    sides of A2. This makes A1's no-op property **provable by a sweep diff**
    rather than argued per file, and removes the per-literal judgement about
    which omitted fields "matter" — a wrong judgement there surfaces at A2 as
    a red indistinguishable from the mechanism under test.
  - The macro's load-bearing assertion runs against a local type that already
    declares field defaults. `Settings` does not yet, so every assertion
    against it is trivially true today and would stay green against a broken
    macro.
  - Characterization confirmed empirically through `forAll`: the README
    literal gives `otExhausted` in under 10 examples against a filtered
    property that passes 100 under the defaults.
  - **Ordering constraint this creates:** the pins force `integerBias` to an
    explicit zero, which `resolved()` still rescues — but C1 retires
    `resolved()` and honours an explicit zero as the degenerate config. So
    **A3 must complete before C1**. Enforced hard rather than by discipline:
    A3 deletes `tests/zerofill.nim`, so a surviving `zeroFilled(` call does
    not compile.
- **Inventories re-verified first-hand before use:** the `Settings(` literal
  counts per file match §6 exactly (29 in A1a's seven files, 34 + `laws.nim`
  in A1b's four, 52 in A1c's thirteen); round B's ten `SymexSettings` const
  literals across seven files match; `withSymexSettings` is 40 mentions across
  21 files.
- **A2's blast radius confirmed closed**, which round 2 asserted but did not
  check: the only type embedding a `Settings` field is `EngineSpec[T]`
  (`pipeline.nim:71`), and all nine of its construction sites list `settings`
  explicitly. There is no `default(Settings)`, `newSeq[Settings]`,
  `seq[Settings]` or `array[N, Settings]` anywhere, and the only bare
  `var s: Settings` are the two in `tsymex_phase14_b2_forcephases.nim` §7
  already records. So A2 cannot reach a file that has no `Settings(` literal.
- **A1 — done** (`5c8f9cf` A1a, `8947e68` A1c, `8d7bf57` + `4e1e7db` A1b).
  All 115 `Settings` literals across 24 test files pinned, plus `laws.nim`'s.
  Each sub-slice verified by `sweep-diff` against the recorded baseline:
  `regressed=0` every time. A1a and A1c were applied while the baseline was
  still running, which is sound only because every file they touch was already
  recorded in it — `ttarget` was the one that was not, and it waited, as did
  `laws.nim` because src is shared with every remaining compile.
- **A2 — RED committed** (`86365f0`), GREEN pending. 11 failing assertions, 1
  green by design. Confirmed at the entry point rather than structurally: the
  README literal reports `otExhausted` after **2** examples where the defaults
  pass 100.
- **Two tooling defects found and fixed, not tolerated:**
  - `sweep-diff` reported all ~450 untouched baseline entries as GONE when
    diffing a slice-sized run, burying the two lines that mattered. Now `-s`
    plus per-section caps; REGRESSED is never truncated.
  - The pin scanner read Nim's numeric-literal suffix (`seed: 42'u64`) as a
    char literal and scanned to the next `'` in the file. On `tengine.nim`
    that overran the closing paren and **raised rather than mis-wrapping**, so
    it failed loudly. The twenty files pinned before the fix were re-checked
    with the corrected scanner: all 81 literals already wrapped, empty diff.
- **The baseline, and what it found** (`scratchpad/rfc0010/baseline-A0.log`):
  444 pass, 5 fail, 6 skip over 455 files. The five failures were all `rc=137`
  timeout kills at the 300s default and **none is on the documented six-suite
  Linux hang list**: `tsymex_r14_continue_guard`,
  `tsymex_r1b_shortcircuit_oob`, `tsymex_r4_strip`, `tsymex_snd3_loopdegrade`,
  `tsymex_snd4_strindex_oob`. Re-run at 900s, four pass — they are **slow, not
  hanging**, including `tsymex_r4_strip`, which is registered and holds one of
  round B's ten const literals. So A0's 300s default was silently converting
  "slow" into `rc=137`, which reads exactly like the known hang class. Four of
  the five are registered in neither `nelli.nimble` nor any CI leg, so nothing
  had ever run them.
- **RFC corrections made at implementation** (`431b7d7`): A2's "twelve in-`src`
  default-parameter positions" is **nine** — both rounds wrote twelve while
  listing nine. And there is a tenth `Settings` construction in src that
  neither round listed because it is not a default parameter: `dsl.nim:37`
  emits `newCall(bindSym"defaultSettings")` for a `property` block with no
  `with` clause, so it is what every DSL user gets by default.
- **For B2, decided at implementation:** name the symex DoD file
  `tests/tsymex_configdefaults.nim`, not the RFC's `tsymexconfigdefaults.nim`.
  `symex-mingw` derives its corpus by matching `tsymex_*` **with the
  underscore** (`scripts/derive-ci-suites.ps1`), so the RFC's name would be
  invisible to the only CI leg that runs the symex corpus.

## What round 1 changed

The seed was right that this is a live user-facing defect and right that the
general fix is the one worth making. But it **understated the defect**,
**undercounted the surfaces by half**, and **posed a three-way design fork whose
answer is a fourth option the language already provides**.

### The empirical result that closed the fork

Probed on the pinned toolchain (Nim 2.2.10, `localhost/nelli-dev`, via
`scripts/dt-bounded.sh c`), reproduced independently twice in round 1 and a
third time in round 2 against a **full-shape `Settings` replica** rather than a
toy type:

**Nim 2 object field defaults (`x: int = 100` in the type declaration) apply to
partial object literals, and explicitly-written zeros survive.** Also applied
by: `T()`, `default(T)`, `const` / VM evaluation, `newSeq[T](n)`, `new(ref T)`,
nested object fields (recursively), and object-variant branch fields. **Not**
applied by: bare `var v: T`, `array[N, T]`, module-level `var`/`{.threadvar.}`,
`reset(x)`, and a `proc` result never constructed.

That third property — distinguishing *unset* from *deliberately zero* in the
language — is exactly what no sentinel or merge scheme can do, and it is
load-bearing here because zero is a documented user intent across these types
(`maxShrinks: 0` = unbounded, `targetedSAIters: 0` = SA off, and critically
`useSA`/`printEvents`/`autoLabels` are bools defaulting to **true**, so `false`
*is* the zero value — a zero-sentinel merge would make those three impossible to
turn off).

So: **field defaults fix the defect at zero call-site cost**, the README becomes
correct as written, and `resolved()`, `withSymexSettings` and both hand-written
`+` bodies become retirable. The seed's §4 fork (builder vs. derived merge vs.
optional fields) never listed the winner.

`{.requiresInit.}` composes with field defaults and closes the `var v: T` hole
(verified: partial literal stays legal, `var v: T` becomes a compile error).
Deferred, not adopted — see the recommendation in §4.

### Premise corrections (verified against the code, not taken on report)

| Seed claim | Reality | Where |
|---|---|---|
| `defaultSettings()` sets "seven non-zero fields" | **Ten.** Seven is the *delta* against the README literal, mislabelled as a field count. | `engine/types.nim:185-190` |
| §1's consequence table (5 rows) | Missing its two worst rows: `maxRejections` 1000→**0** and `targetedSAIters` 200→**0**. | `phases.nim:295`, `targeting.nim:286-289` |
| — (not claimed) | **`maxRejections: 0` means the *first* rejection ends the run as `otExhausted`.** Measured: a filtered strategy gives `otPassed`/100 examples by default vs `otExhausted`/2 under the README literal. | `phases.nim:295` |
| "unbounded shrink loop" | Unbounded *time*, not non-termination — `shrinker.nim:411` is a `while best != prev` fixpoint. | `shrinker.nim:411` |
| "four answers … five rows" | **Eight** distinct policies across **ten** surfaces (round 2 made it nine across eleven). | §2 table |
| `FuzzSettings` "no default constructor at all" | A *deliberate* zero-is-the-default policy, **pinned by `tests/tfuzzconfigdefaults.nim`** and documented per-field. Conforms via zeros, not unified. | `fuzz.nim:338`, `docs/fuzz/INTERFACE.md:243` |
| `ResourceBudget.+` is "fourteen" comparisons | Thirteen — and there is a **second** copy of the same obligation for `SymexSettings` the seed missed. | `smt/types.nim:2965-2989`, `:2991-3003` |
| "a forgotten line is a silent wrong default" | True, **plus** the partial-as-full-value limitation: both `+`s key on differs-from-default, so the default value itself is unwritable through the merge. | `smt/types.nim:2970` |
| `tdsl.nim:42-44` shows the accidental idiom | **It does not.** It explicitly sets `flakyRetries: 0, maxShrinks: 50, useSA: false, targetedSAIters: 0` — a hand-written workaround by someone who knew. `tengine.nim:28` is the accidental kind. | `tdsl.nim:42-44` |
| "the suite is partly testing a configuration no user intends" | True but **latent**, not live: no assertion currently passes for the wrong reason. | 115 literals / 24 files |
| §5's first slice is "red today" | **Inverted and self-contradictory.** Behaviours *differ* today, so that test is green now and goes red on success. | §5 |
| `given x: int` is "mechanical in `dsl.nim:60-70`" | Not mechanical — the colon produces a different AST shape than the required `nnkInfix(in, …)`, and the mixed form doesn't parse. `given x in int` is the mechanical variant. | `dsl.nim:59-68` |

### The surfaces that were invisible

- **`BmcSettings` (`bmc.nim:50`) — a live instance of the defect whose doc
  comment *recommends* it**: "so users can write `BmcSettings(maxDepth: 5, ...)`
  as an object literal." That leaves `maxStates: 0` and `bmc.nim:86`
  (`explored >= maxStates`) returns `bmcExhaustedBudget` before exploring one
  state. The best single piece of evidence for the RFC and the seed didn't have it.
- **`OrchestratorPolicy` (`fuzz.nim:877`)** — a sixth answer (proc constructor
  with default parameters) whose doc comment diagnoses the general defect
  verbatim. That mechanism is one §4 never listed.
- **The ADR-0031 family** (`ExecutorConfig`/`GuidanceConfig`/`SchedulingConfig`)
  — a seventh answer, and the only structurally safe one: design the knobs so
  zero *is* correct. The seed's taxonomy had no row for it.
- **`laws.nim:35-39`** — the library doing it to itself: an in-`src` hand-copy of
  the defaults that silently omits `autoLabels`.
- **The symex test suite does it to itself too** — ten `const SymexSettings(...)`
  literals that predate `arithChecks`'s all-on default, today silently running
  release-like with no overflow forks and modelling OOM/stack-overflow as raise
  paths.
- **`validateSymexSettings` (`smt/types.nim:3005`)** — cross-field *coherence*
  is a real second axis (on `Settings`: `useSA` needs `targetedSAIters > 0`),
  handled on one surface only.
- **`examples/symex_loops.nim:60-63` does not compile** — sets `queryRLimit` et
  al. flat on `SymexSettings`; they moved to `ResourceBudget` at CR-9(b).
  `examples/` is built by neither CI nor `nelli.nimble`, which is why it rotted.

### The cost the seed had backwards

It worried about breaking call sites. Field defaults break **zero** (measured:
115 `Settings` + 10 `SymexSettings`/`ResourceBudget` + 3 `IntegerBiasConfig`
literal sites, all of which keep compiling and start behaving correctly).

The real cost is the **behavioural fallout of fixing them**: `autoLabels` flips
false→true for 115/115 literals, `printEvents` for 109/115, which turns on the
`auto.*` label sink and appends an `[events]` block to every rendered report
(`render.nim:86`). `useSA` false→true matters only where score labels exist,
which `coverageGuided` runs create. `flakyRetries` 0→5 replays every
falsification up to 5×, which bites tests counting invocations via side-effect
counters.

§6 stages this **pin-then-flip** (A1 makes today's implicit values explicit as a
no-op; A2 flips; A3 un-pins where the default was actually wanted) so the
fallout is drained in advance rather than discovered as a red sweep.

## What round 2 changed

Round 1's verdict was that round 2 was not warranted. That was wrong, and the
reason is worth recording: round 1 rewrote the *premises* and the *mechanism*
rigorously against the source, then authored a slice plan whose inventories were
never checked against the same files. Round 2 found the design sound and the
plan substantially under-specified. **Nothing round 1 closed was reopened.**

### The plan defects (all verified at source)

| Round 1 said | Round 2 found | Where |
|---|---|---|
| B1 pins three fields, then B2 is "a pure flip" | Every one of the ten const literals writes a **partial `ResourceBudget`**, so B2 also flips **nine** omitted nested fields 0→{8,256,64,64,8,32,8,8,64} — where 0 means *unlimited* and all nine are in the cache key. B1 as specified was not a no-op. | `tsymex_phase13_rlimit.nim:15-22`, `smt/types.nim:1656`, `canonicalize.nim:3948` |
| B1 covers "6 test files" | **10 literals across 7 files** — and **four of those files are registered nowhere in `nelli.nimble`**, so they run in no sweep and no CI. The `examples/` rot mechanism, inside the test suite. | `nelli.nimble` |
| §7: A2 "runs the property end-to-end through the real entry point" | §6's A2 RED test is **pure structural equality** — no `forAll`, no entry point. §6 and §7 described two different RFCs; an implementer following §6 ships A2 green with the property never having run. Structural equality provably can't cover this class: `phases.nim:260` applies `resolved()` between the literal and the engine. | §6 vs §7 |
| A2: "run the full PBT sweep" | **No such command exists.** `psweep.sh` sweeps only `tsymex_*`; `nelli.nimble`'s `test` task is a serial loop over ~257 suites including the six `r6` hangers, so it never finishes in-container. Now slice A0. | `scripts/psweep.sh:28`, `nelli.nimble` |
| A1: "~40 literals" in a named suite list | **63** in the named files, plus **52 more in 13 files round 1 never listed**. Two named files (`tshrinker`, `tvariantbind`) contain **zero** `Settings(` literals and cannot be affected at all. | per-file counts |
| §5.2 deletes `resolved()`, `withSymexSettings`, both `+` | All four are **public**. `withSymexSettings` alone has **28 invocation sites across 21 files** plus a README teaching site — an unscheduled round. Round 2 replaces deletion with **deprecation**. | `smt/dsl.nim:9-10`, `README.md:320-323` |
| §5.6 "No compile breaks" | True of the defaults flip, **false of the deletions riding in the same RFC**. | §5.6 |
| B3 derives `+` as a `merged` over `fields()` | `+` has **zero production callers** — the only calls are three tests *of the operator itself*. Round 2 withdraws the derived merge: deprecate, keep the bodies, keep two pins. A naive `fields()` rewrite would also have silently broken nested composition, and B3's specified RED test **passes under that bug**. | `smt/types.nim:2998`, three test sites |
| §7's property: "any settings construction" | **Falsified by a fork this RFC closed.** `var s: Settings` zero-fills and stays legal because `requiresInit` is deferred. Quantifier now scoped, residual recorded. | §3, §7 |
| One DoD file, `tconfigdefaults.nim` | Covering all five surfaces means importing the symex stack, making the definition of done **Z3-linked** — undoing for that file what RFC-0004 made true of `import nelli`. Split in two. | `symex.nim:1092` ff. |
| C3 as one slice | Four unrelated surfaces including a CI change. Split C3a/C3b/C3c. Round 2 compiled all six examples: **only `symex_loops.nim` is broken**, so round 1's single-file claim was right. | `examples/` |
| "Wire `examples/` into CI" | There is **no Linux CI leg at all**, and **nothing in CI runs `nimble test`**. Adding examples to the nimble task yields zero CI coverage. | `.github/workflows/` |
| §5.6 downstream audit, one sentence, no slice | Now C5, with the 0004 model's actual contents enumerated — including that **no runtime detection aid is possible**, because after the flip the language erases set-versus-unset. | `0004-z3-optional.downstream-audit.md` |

### The two new surfaces

- **`ConcolicAssist` (`fuzz.nim:784-844`)** — an eleventh surface and a ninth
  policy: **resolve-at-use coercion** (`stallRounds <= 0` → 1,
  `maxBranchAttempts <= 0` → 8), which makes an explicit zero unrepresentable.
  Deliberate RFC-0004 round-2 design, already pinned at
  `tfuzzconfigdefaults.nim:46-53`. **Exempt and pinned**, not reopened — the
  taxonomy just needed the row.
- **`OrchestratorPolicy` was in the taxonomy and then never disposed of.** §4
  rejects its mechanism for new work while §5 left the existing instance
  untreated — incoherent given §9's thesis. Now slice C4.

### The nesting leak two lenses found independently

`FuzzSettings` embeds `integerBias: IntegerBiasConfig` (`fuzz.nim:371`), so C1's
defaults **recurse into the surface the RFC declares conforming-by-zeros**.
`FuzzSettings()` stops being all-zero. Behaviour is preserved end-to-end
(`resolved(zero)` produced the same values at use) and `tfuzzconfigdefaults.nim`
asserts nothing about `integerBias`, so nothing reds — which is exactly why it
had to be written down. Related: C1's RED test must assert **zero-survival**,
not omission-equivalence, because omission-equivalence is **already green
today** via the sentinel.

### The reframing worth keeping

§0 now states the invariant the ten repairs instantiate: *`T()` is the
documented default; a partial literal differs only in what it lists; any
constructor, builder, sentinel or merge introduced to work around unsafe partial
construction is a defect of this class.* This dissolves the "exemption" — the
ADR-0031 family is not exempt, it **satisfies the invariant with zeros**. One
invariant with two conforming implementations is a design; two policies
reconciled by a test is the thing this RFC exists to end. §7's registry is
correspondingly self-checking rather than enumerative, so a surface added later
cannot conform to neither without failing.

### Forks closed (do not reopen without new information)

- **Mechanism** — declared field defaults. Every alternative refuted in §4:
  proc default params duplicate the defaults in a second location and leave the
  poisoned literal legal beside them; `Option[T]` was already rejected once on
  call-site cost at `distribution.nim:50-54`; the mutator builder is imperative
  and doesn't nest; bare `requiresInit` forces all 17 fields. Round 2 adds:
  no library-level config substrate (it would add interface to hide less
  implementation), and no preset API (`with` already takes any expression, so
  `const quick = Settings(...)` works today).
- **One mechanism or five** — six surfaces unified; the zero-is-correct family
  conforms by zeros and is pinned. Re-framed by round 2 as one invariant with
  two implementations rather than a policy plus an exemption.
- **`{.requiresInit.}`** — deferred, not rejected. The holes it closes have two
  live occurrences, both in tests; field defaults already make the documented
  path *safe*, which is the done-condition.
- **Merge presence-tracking** — no. Round 2 goes further: the merge has no
  production callers, so it is deprecated rather than derived. §4 records why
  keeping differs-from-default keying inside `+` is a *narrowing* of §3's
  disqualification and not a contradiction — two reviewers read it as a
  contradiction, which is why the sentence now exists.
- **The two riders' scope** — closed by Corey 2026-09-04 as option (c): they
  stay in 0010, quarantined to round D, never interleaved with A/B/C. Round D
  may not start until A is green, and blocks nothing if deferred indefinitely.

## Liveness

**Load-bearing property:** any literal, `default(T)`, `const`, `newSeq`, `new`
or nested-field construction reachable through a documented entry point behaves
identically to that surface's defaults in every field not explicitly listed.
Residual recorded in §7: bare `var`, `array[N, T]`, `reset` and unconstructed
proc results still zero-fill (two live occurrences, both in
`tsymex_phase14_b2_forcephases.nim`); deferred `requiresInit` is that hole's
designated closer.

Verified in round 2: no settings type is serialized or crosses the fuzzer worker
process boundary, and nothing parses settings from JSON/TOML/CLI/env — so B2's
persisted symex witness key is the only settings-derived persistence in the
tree.

Behavioural, at the entry point. All five in-scope surfaces admit an end-to-end
behavioural test; none is structural-only. But per-field *behavioural*
equivalence is infeasible (observing `flakyRetries` needs a flaky property), so
the honest criterion is structural equality on every field **plus** behavioural
spot-checks for the headline symptoms — round 1's wording was unfalsifiable.

**Producer-first, with the exception recorded:** A1 is a no-op, so A2 is the
first live slice. Pin-then-flip wins that trade anyway (flipping first costs a
red sweep across two dozen files that conflates fallout with mechanism and
destroys A2's bisectability), and A1 lands the characterization test so the
defect is under observation from slice 1.

**Definition of done** (§7): two commands, `tconfigdefaults.nim` (Z3-free) and
`tsymexconfigdefaults.nim`, covering every in-scope surface's documented idiom
through its real entry point, plus the README's verbatim `Settings` literal, plus
the conforming-by-zeros surfaces pinned as *deliberately* agreeing.

## Slice ledger

| Round | Slice | State |
|---|---|---|
| A | A0 a runnable full-suite sweep (prerequisite — none exists today) | not started |
| A | A1a pin output/event suites | not started |
| A | A1b pin engine suites + `laws.nim` | not started |
| A | A1c the 13 files round 1 never listed (52 literals) | not started |
| A | A2 **the flip** — field defaults on `Settings`, structural + behavioural RED, register in nimble/CI (end-to-end DoD) | not started |
| A | A3 un-pin where the default was wanted (mechanical done-condition) | not started |
| B | B1 pin all twelve fields across 10 literals / 7 files; register 4 dark suites | not started |
| B | B1b per-site review (behaviour-changing, separate commits) | not started |
| B | B2 flip `SymexSettings` + `ResourceBudget` | not started |
| B | B3 deprecate `+` and `withSymexSettings`; forgotten-field + nested-composition pins | not started |
| C | C1 `IntegerBiasConfig` + retire `resolved()` (RED = zero-survival) | not started |
| C | C2 `BmcSettings` — choose defaults, fix the doc, RED on instant-exhaust | not started |
| C | C3a docs (README, fuzz docs, two doc comments, stale `optimisedSymexSettings` comment, `validateSymexSettings` disposition) | not started |
| C | C3b repair `examples/symex_loops.nim` | not started |
| C | C3c examples compile gate (crosses the platform fork) | not started |
| C | C4 `OrchestratorPolicy` field defaults + doc flip + ctor shim | not started |
| C | C5 downstream audit + CHANGELOG + version decision | not started |
| D | D1 `given x in int` (`dsl.nim`) — quarantined, after A | not started |
| D | D2 `derive.nim:511` error message — quarantined, after A | not started |

Notes for whoever picks this up:

- **Start at A0.** Round 1's resume said A1; there is no runnable sweep to
  verify anything against until A0 exists, and A2's stated verification depends
  on it.
- Round B is a **round, not a slice**. B2 moves per-site cache keys
  (`arithChecks` is in the key) but is **not** a `symexWalkerVersion` bump:
  walker semantics are unchanged and the pin tests build from
  `defaultSymexSettings()`. Confirmed at source in round 2 —
  `canonicalize.nim:3873-3958` folds every verdict-relevant field into the key,
  so a changed site gets a cold miss and stale entries can never be reused under
  changed semantics. Name `tsymex_phase15_CR2_cachekey` in B2's verify list as
  the key-stability oracle.
- B2 also invalidates **persisted** symex witnesses (`symex.nim:210,236` store
  them in `ExampleDatabase` under that key). In-tree this is drained by B1; for
  a downstream with partial literals and a witness DB it is an unannounced
  cache flush — witnesses go dark and are re-solved, never reused-wrong. C5's
  audit must say so.
- None of the ten symex literal sites is in the six `tsymex_r6_*` suites that
  hang on Linux/podman, so round B is fully locally verifiable. Don't misread
  those hangs as a regression — see the `symex-r6-linux-hangs` memory.
- Don't run the same test file concurrently under `dt-bounded.sh` — one shared
  binary, and the clobber looks like a flaky product bug.
- Field defaults and `fields()` are front-end/compile-time, so no codegen
  divergence is expected across msvc/mingw/gcc — run `fuzzer-msvc` anyway.
- A new test file runs **nowhere** unless explicitly registered: `nelli.nimble`'s
  list is hand-maintained, `symex-mingw` takes only `tsymex_*` names, and the
  fuzzer legs glob `^(tfuzz|tdb|tengine_)` plus a named contract list.
- RFC-0006's S0c and S1 add `Settings` fields and recorded a soft dep on this
  RFC. After A2 that dep gets *easier*, not harder: a new field with a declared
  default needs no call-site changes anywhere. RFC-0008 is a second, unrecorded
  reverse dependent — it persists effective bounds into `nelli.assurance.json`
  and its scheduler becomes a second writer of `maxExamples`, so landing 0010
  after 0008 would churn every recorded bound. SEED-SET's order already puts
  0010 first; that is now deliberate rather than accidental.

## Review ledger

| Round | Model | Lenses | Findings applied | Forks raised |
|---|---|---|---|---|
| 1 | fable | depth, breadth, design & ergonomics, feasibility, liveness | 12 premise corrections, mechanism settled empirically, surface inventory 5→10, slice plan added, acceptance criterion de-inverted, size S→M, value med→high | 1 (§8 scope split) — **closed 2026-09-04, option (c)** |
| 2 | fable | same five | slice inventory rebuilt against the files (B1's nine missing pins, A1's 52 unlisted literals, B1's 4 dark suites, A0's nonexistent sweep command); §6 reconciled with §7 (structural vs behavioural RED); deletions → deprecations; derived merge withdrawn; DoD split Z3-free/symex; 11th surface (`ConcolicAssist`) and C4 (`OrchestratorPolicy`) added; C5 audit slice added; §0 invariant stated; property quantifier scoped; size M→L | 0 |

Round 2's load-bearing claims were re-verified first-hand rather than taken on
the agents' word — the three lenses reporting `withSymexSettings` call-site
counts disagreed (26/40/six), and the direct sweep settled it at 28 invocations
across 21 files. Also checked directly: the four dark suites are absent from
`nelli.nimble`; `tshrinker`/`tvariantbind` contain zero `Settings(` literals;
`psweep.sh` is `tsymex_*`-only; no workflow runs `nimble test`; `+` has exactly
three call sites, all tests of itself; `README.md:320-323` teaches
`withSymexSettings`.

**Is round 3 warranted?** No, and this time the reasoning is different from
round 1's. Round 1 said no because the design was settled — which was true, and
still is: round 2 reopened nothing and raised no forks. What round 2 actually
fixed was the gap between a settled design and an executable plan, and that gap
is now closed against the real files: every slice has a verified inventory, an
owning file, a RED direction and a done-condition. A third pass over the same
document would re-read the same sources. The next useful signal comes from
executing A0 and A1a, not from another review.
