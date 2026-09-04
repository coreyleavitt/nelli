# RFC-0010 config-discipline — downstream audit for 0.8.0

Follows the `0004-z3-optional.downstream-audit.md` model. That audit's hardest
section was §4, "behaviour change with no compile error", and it ran to five
bullets. **For 0010 that section is nearly the whole document.**

There is no compile break here. Every literal that compiled before compiles
after. What changes is what those literals *mean*, and the change is silent by
construction — which is exactly the property that made the original defect
survive for years.

## The one-sentence version

If a downstream constructs any nelli configuration object with a **partial
object literal**, the fields it did not list used to arrive as zero and now
arrive as that type's documented default. If the zeros were what it wanted, it
must write them explicitly, and it must do so **before** upgrading.

## Consumers

### amoxtli — CLEAR, re-checked 2026-09-04

0004 audited it at stage 2 and found **zero** nelli imports anywhere in the
repo. Re-checked on this host for 0010: unchanged, still zero. Nothing in
0.8.0 can reach it. Recorded rather than carried as an open task.

### chapulin — the real downstream; audit must run there

chapulin is a Windows consumer and is not checked out on this host, so what
follows is a runnable spec, not a result. It uses both `forAll`-side settings
and the symex surface, so every section below applies to it.

## 1. Find the call sites — runnable greps

Run from chapulin's root. These are a **pre-filter, not the audit**: they
locate literals faster than a human can, but nothing here fails a build, so
the compiler will not find them for you. That is the whole problem.

```bash
# Every partial literal of an affected type. A literal that lists EVERY field
# is unaffected; one that omits any field with a non-zero default has changed
# meaning.
grep -rn --include='*.nim' -E '(^|[^A-Za-z0-9_])Settings\(' . \
  | grep -vE '(Symex|Fuzz|Bmc|Law|Resource|Scheduling|Executor|Guidance)Settings\('
grep -rn --include='*.nim' -E '(^|[^A-Za-z0-9_])SymexSettings\('   .
grep -rn --include='*.nim' -E '(^|[^A-Za-z0-9_])ResourceBudget\('  .
grep -rn --include='*.nim' -E '(^|[^A-Za-z0-9_])BmcSettings\('     .
grep -rn --include='*.nim' -E '(^|[^A-Za-z0-9_])IntegerBiasConfig\(' .
grep -rn --include='*.nim' -E '(^|[^A-Za-z0-9_])OrchestratorPolicy\(' .

# Deprecated symbols. These DO announce themselves — as warnings, not errors.
grep -rn --include='*.nim' -E 'withSymexSettings|orchestratorPolicy\(|resolved\(|optimisedSymexSettings' .

# The reader trap in §4. A bare `var` still zero-fills; a literal no longer does.
grep -rn --include='*.nim' -E 'var +[A-Za-z0-9_]+ *: *(Settings|SymexSettings|ResourceBudget|BmcSettings|IntegerBiasConfig|OrchestratorPolicy) *$' .
```

## 2. The field delta table — the only practical detection aid

After the flip the language erases set-versus-unset, so **no runtime
discovery mode is possible**: a value that omitted a field is indistinguishable
from one that wrote the default. There is no flag we could add that would tell
a downstream which of its literals changed. This table is the substitute — for
each type, the fields whose default is not the zero value.

**`Settings`** (`engine/types.nim`)

| field | was (omitted) | now | what it controls |
|---|---|---|---|
| `maxExamples` | 0 | 100 | examples per run |
| `maxRejections` | 0 | 1000 | **0 ended the run as `otExhausted` on the FIRST rejection** |
| `seed` | 0 | `0x1234567890abcdef` | RNG seed |
| `flakyRetries` | 0 | 5 | flakiness detection off at 0 |
| `maxShrinks` | 0 | 500 | 0 means *unbounded* shrink time |
| `useSA` | false | **true** | simulated-annealing escape |
| `targetedSAIters` | 0 | 200 | second, independent SA kill-switch |
| `printEvents` | false | **true** | appends an `[events]` block to rendered reports |
| `autoLabels` | false | **true** | installs the `auto.*` distribution-label sink |
| `integerBias` | all-zero | 30/30/64/50 | see §3 — this one was already rescued at use |

The three bools are the ones to read carefully: their default is `true`, so
`false` **is** the zero value. A downstream that wrote nothing got `false` and
now gets `true`.

**`ResourceBudget`** (`smt/types.nim`) — 11 of 13 fields; `queryRLimit` and
`maxFrontierSize` keep 0, which this type documents as *unlimited*.

| field | was | now |
|---|---|---|
| `maxCallDepth` | 0 | 3 |
| `maxLoopUnwind` | 0 | 5 |
| `maxHeapDepth` | 0 | 8 |
| `maxFreshnessAssertions` | 0 | 256 |
| `maxClosureInlineCount` | 0 | 64 |
| `maxInstantiationsPerProc` | 0 | 64 |
| `maxSplitParts` | 0 | 8 |
| `maxBytesEncodingLen` | 0 | 32 |
| `seqInlineThreshold` | 0 | 8 |
| `maxVariantConstructorForks` | 0 | 8 |
| `maxVariantConstructorFieldAllocs` | 0 | 64 |

Note the direction: **0 meant unlimited on every one of these**, so a partial
budget was asking for an unbounded walker, not a small one.

**`SymexSettings`** (`smt/types.nim`)

| field | was | now |
|---|---|---|
| `integerSemantics` | `isExact` (ordinal 0) | `isOptimised` |
| `defectExclusions` | `{}` | `{dkOutOfMemoryDefect, dkStackOverflowDefect}` |
| `arithChecks` | `{}` | `{acOverflow, acDivByZero, acRange}` |
| `inlinePolicy` | `ipAlwaysInline` (ordinal 0) | `ipHybrid` |
| `budget` | all-zero | `ResourceBudget()` (recursively, per the table above) |

`arithChecks` is the sharpest: empty means **no arithmetic defect fork is
emitted at all**, so `OverflowDefect`, `DivByZeroDefect` and `RangeDefect` are
unreachable. Any downstream symex query written as a partial literal has been
running release-like. If it has assertions of the form "this query returns
`sxUnsat`", some of them may now be `sxRaised` — and that is the correct
answer, arrived at late.

**`BmcSettings`** (`bmc.nim`) — `maxDepth` 0 → 5, `maxStates` 0 → 1000. Both
caps now treat an explicit **0 as unlimited**, which it previously was not:
`maxStates: 0` used to return `bmcExhaustedBudget` before expanding a single
state, so a run that "verified" nothing reported a budget exhaustion.

**`IntegerBiasConfig`** (`datasource/distribution.nim`) — 30/30/64/50. See §3.

**`OrchestratorPolicy`** (`fuzz.nim`) — `reVerifyBudget` 0 → 8, `reproSamples`
0 → 5, `concolicMaxBranchAttempts` 0 → 8. The other six knobs are genuinely
zero-valued.

**`FuzzSettings`** (`fuzz.nim`) — unchanged **except** its nested
`integerBias`, which is an `IntegerBiasConfig` and therefore picks up that
type's defaults recursively. `FuzzSettings()` is no longer all-zero in that one
field. Behaviour is unchanged end-to-end: the value it now carries is the one
`resolved()` produced at the point of use.

## 3. Behaviour changes with no compile error — read these by hand

Everything in §2 is one of these. Four more that the table does not capture:

1. **An explicitly all-zero `IntegerBiasConfig` is now honoured.** It used to
   be a sentinel meaning "use the library default" and was rewritten to
   30/30/64/50 at the point of use. It now means what it says: no boundary
   injection, no small window, no shrink-towards short-circuit — a uniform
   draw. A downstream that wrote the zeros deliberately, relying on the
   sentinel, now gets a different distribution. `resolved()` survives as a
   deprecated identity function, so calling it no longer rescues anything.

2. **Persisted symex witnesses go dark, once.** Symex verdicts are content-
   addressed and every verdict-relevant field folds into the cache key
   (`canonicalize.nim`), and witnesses are persisted into `ExampleDatabase`
   under that key. A downstream whose settings changed meaning gets a *new*
   key, so stored witnesses become unreachable and are re-solved. They are
   never reused wrongly — this is an unannounced cache flush, not a
   correctness hazard. Budget a slower first run.

3. **`var s: Settings` and `Settings()` now disagree.** A bare `var`
   declaration still zero-fills; declared field defaults do not apply to it
   (nor to `array[N, T]`, module-level `var`, `{.threadvar.}`, `reset(x)`, or
   an unconstructed proc result). This is a new reader trap: two spellings
   that used to be equivalent no longer are. `{.requiresInit.}` would close it
   and is deliberately deferred.

4. **`bmcVerified` now asserts more.** With `maxDepth` defaulting to 5 rather
   than 0, a BMC run that previously exhausted its budget immediately now
   actually searches. A green run means "the invariant holds for every plan up
   to depth 5", which is a stronger claim than the previous vacuous one — and
   a slower one.

## 4. The triage recipe

For each site the greps in §1 find:

1. Does the literal list **every** field of its type? If yes, it is unaffected.
2. If not, for each omitted field in §2's tables: **did you mean the zero?**
   - If yes — write it explicitly, **before upgrading**. An explicitly-written
     zero survives the flip; that is the property the whole mechanism is built
     on.
   - If no — do nothing. You are about to get what you meant.
3. If you cannot tell, prefer doing nothing. The defaults are what the library
   documents, and every in-tree instance of this question (115 `Settings`
   literals across 24 files, 10 symex literals across 7) resolved to "the
   author wanted the defaults and did not know they were not getting them".

## 5. Deprecations — warnings, not errors

Nothing below breaks a build in 0.8.0. All are removed at the next major.

| symbol | replacement |
|---|---|
| `withSymexSettings` | write the `SymexSettings(...)` literal |
| `` `+` `` on `SymexSettings` / `ResourceBudget` | set the field on the base value |
| `resolved()` | nothing — it is now the identity |
| `orchestratorPolicy()` | write the `OrchestratorPolicy(...)` literal |
| `optimisedSymexSettings()` | `SymexSettings()` — it has been byte-identical since the Phase-2 endpoint |

`defaultSettings()`, `defaultSymexSettings()`, `defaultResourceBudget()` and
`defaultIntegerBias` are **not** deprecated in 0.8.0. Each is now a second name
for its type's empty literal, and deprecating them in the same release that
already changes what every partial literal means would be two migrations at
once. They go one release later.

`looseSymexSettings` stays. It is a genuine non-default preset.

## 6. Toolchain

Unchanged. Nim ≥ 2.2.10 is still required, and specifically the declared
object field defaults this RFC is built on are a Nim 2 feature — a consumer
pinned below that could not compile the library anyway.

## 7. Release gate

- [ ] Run §1's greps in chapulin; triage per §4.
- [ ] Build chapulin against this branch. Expect **zero** compile errors and
      some deprecation warnings.
- [ ] Run chapulin's suite and read the diff, not the pass/fail: the changes
      here are behavioural, and a suite can stay green while its meaning moves.
- [ ] Bump `nelli.nimble` to 0.8.0 and date the CHANGELOG heading.
