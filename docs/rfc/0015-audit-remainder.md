+++
type    = "rfc"
id      = "0015"
title   = "RFC — audit remainder: documented contracts honoured on a subset of paths"
state   = "seed"
wiring   = "unproven"
stage   = "rfc"
profile = "rfc-flow@3"

[[item]]
id    = "i1"
title = "S3 jitterPoints trailing blocks: leave it warning, or allow-list the"
state = "open"
owner = "corey"
+++

# RFC — audit remainder: documented contracts honoured on a subset of paths

- **Status:** seed — composed 2026-09-20 from the five issues the #161–#163
  audit produced that are not part of RFC-0014 (#164, #165, #170, #171, #172).
  Five independent slices, no internal dependencies, one open fork (S3).
- Category: core
- Size: M
- Value: med
- **Depends on:**
  - none.

## §0 — Thesis, and an honest note about the grouping

**This is not one mechanism, and the doc does not pretend otherwise.** The
README's rule is to group by shared mechanism; three of these five share a
defect *class* and a test *discipline*, and two are hygiene. They are one doc
because each is one or two slices with no design content worth its own number,
and because two of them carry gates (a CI leg, a regenerated warnings baseline)
that want recording somewhere rather than landing as loose commits.

The class the first three share is worth naming, because it is what the audit
was looking for and it is how all three were found:

> A contract that is **documented at an entry point** and honoured on only some
> of the paths behind it. Found by driving the documented door with a real
> input, never by reading the code — every line behind each of these doors is
> correct.

- **#164** — `newReplaySourceFromBytes` documents a fixed-width-per-kind byte
  contract. Two of five draws implement it.
- **#165** — `forAllWithSymexSeeds` takes a `Settings`; its `testId` and
  `dbPath` fields are inert.
- **#170** — `{.jitterPoints.}` documents that it instruments statement
  positions in the annotated body. It skips the body of a trailing-block call,
  which is the commonest real concurrency shape.

Each is invisible to the test suite, because in each case the suite exercises a
path that *does* honour the contract.

## §1 — S1: byte-mode ignores the buffer for three of five draws (#164)

`newReplaySourceFromBytes` documents that each `drawInteger`/`drawFloat`
consumes 8 prefix bytes. Only `drawBoolean` and `drawInteger` have a
`bytesMode` branch. `drawFloat`, `drawBytes` and `drawString` have none.

**Consequence.** A strategy that draws any of those, fuzzed through the
documented libFuzzer/AFL door (`fuzzOnce`), ignores the buffer for those draws
entirely — 256 distinct first bytes through `floats(0.0, 1.0)` produce **one**
distinct float (`scratchpad/bench/probe_floatbytes.nim`). `importCorpusDirAsIR`
decodes a byte corpus through the strategy, so a corpus imported from another
fuzzer silently loses its float/bytes/string values the same way. The
structural loop is unaffected — it replays from the choice sequence, not from
bytes.

**Fix.** Add the missing arms: `drawFloat` reads 8 bytes via `readByteU64BE`
and `cast[float64]`s them before `coerceFloat`, matching the constructor's
documented fixed-width-per-kind contract. `drawBytes`/`drawString` need a
length prefix plus payload; the prefix width is the one real design decision in
this RFC — pick it, and document it beside the others.

**And make the dispatch exhaustive**, which is the durable half. The reason a
documented contract could sit half-implemented is that the dispatch is an
allow-list with a silent fallback: a missing arm returns a default rather than
failing. This is the same structural defect round 13 of the #163 review found
in `{.jitterPoints.}`, and the fix there is the precedent — the fallback was
upgraded from `warning` to `error()`, and that upgrade immediately surfaced
three more gaps nobody had found by reading. Do the same here: a draw kind with
no `bytesMode` arm must be a compile error, not a default value.

**Pin.** Feed 256 distinct first bytes and assert more than one decoded value
*per kind*. The per-kind part matters — an aggregate assertion passes today on
the strength of `drawInteger` alone.

## §2 — S2: `forAllWithSymexSeeds` cannot persist a witness (#165)

`forAllWithSymexSeeds` (`symex.nim`, layer 2) hardcodes `inMemoryDatabase(),
dbEnabled = false` when it builds the pipeline. `testId` and `dbPath` on the
`Settings` it is handed are inert, so a solver witness that falsifies the
property is never written to the example database and does not replay on the
next run.

**The phases already compose.** `scratchpad/bench/demo_one_input.nim` stage 4
gets the witness onto disk by hand-composing `defaultPhases[int]()` with
`symexSeedPhase` inserted after `explicit`, over `directoryBasedDatabase`,
through `runForAllPipelineWithPhases`. That works. Only the convenience wrapper
— the door a user actually goes through — is missing the plumbing.

**Fix.** Have `forAllWithSymexSeeds` honour `settings.dbPath`/`settings.testId`
the way `forAll` does (select `directoryBasedDatabase` when `dbPath` is set,
`dbEnabled = true`), or take an explicit database argument.

**Pin.** Seed a witness; run once with a `dbPath`; run again with
`maxExamples: 1`, a different seed, and no symex seeds; assert `dbReplays == 1`
and the same counterexample. That shape is the point — it proves persistence by
observing a *later* run, which is what the feature is for.

## §3 — S3: `{.jitterPoints.}` and trailing-block calls (#170) — **fork**

`{.jitterPoints.}`'s fallback warns on `nnkCommand`/`nnkCall` nodes carrying a
trailing `nnkStmtList` — the `withLock lock: <body>` shape — and does not
descend. So the commonest real shape for a concurrency SUT gets a warning and
no jitter points inside the critical section.

**Why it was left.** A trailing block's body belongs to whatever macro or
template receives it, which an `untyped`, pre-expansion macro cannot inspect.
Instrumenting is sound for `withLock` specifically and unsound in general: a
macro that pattern-matches its block's exact shape would break.

**Options.** (a) leave it warning — safe, honest, what ships today. (b)
instrument the trailing blocks of an allow-list of known concurrency macros —
targeted and safe, but a stringly-typed macro-name allow-list. (c) blanket
instrumentation — unsound, out.

This turns on risk appetite, not on the quality bar, which is why it is item i1
and not a decided slice. If (b): pin with a `withLock` SUT whose race is only
observable with a jitter point inside the locked region, and assert the existing
"intra-op jitter hook catches a race" test's shape still passes.

## §4 — S4: warning debt (#171)

Making the sweep gate stop discarding compiler stderr (#163 review R13-1)
showed every test compiling with 14–23 warnings attributed to `src/nelli/`.
Sampled over 36 tests: 603 raw occurrences, **40 distinct**
`(file, message, category)` diagnostics. The same noisy modules recompile per
test, which is where the raw-count inflation comes from.

The warnings gate is delta-based against
`nelli-sweep-baselines/base-bbde48c.log.warnings`, so none of this fails
anything. It buries any new actionable warning — the `{.jitterPoints.}`
fallback diagnostic is the motivating case — for anyone reading raw output
rather than the diff.

**S4a — 38 unused imports.** Cosmetic, one chore commit. Top contributors by
raw count: `engine.nim` (180), `engine/targeting.nim` (144), `jsonschema.nim`
(78), `bisim.nim` (52), `engine/phases.nim` (36).

**S4b — stdlib `sha1`.** *One* call site: `canonicalize.nim:4524`,
`"sx:" & $secureHash(canon)` — a cache key, reached from `import
std/[strutils, tables, algorithm, sha1]` at line 19.

Migrate to `checksums/sha1`. Two things make this the clear choice over the
obvious-looking alternative of dropping to `std/hashes`: the relocated module is
the same algorithm, so **the digest is byte-identical and no cache key
changes** — no walker-version bump, no CR2_cachekey churn; and `std/hashes`
would narrow a key that is load-bearing for *correctness* (a collision means
two different programs share a cached verdict) from 160 bits to 64. Check the
added nimble dependency against RFC-0004's import-time constraints before
landing — `checksums` is pure Nim and unrelated to Z3, so the Z3-free `import
nelli` property is untouched, but it is a new unconditional dependency on a
library whose core does not otherwise have one. If that turns out to matter,
escalate rather than silently swapping in a narrower hash.

**S4c — `macros.owner`.** Three call sites — `dsl_parser.nim:3731`, `:3860`,
`:8086` — and they are **the same predicate three times**: *did this symbol
originate in module M?* The guards are `sequtils` for `filter`/`map`/`fold`,
and `unicode` for `runeLen` and the `runes` iterator. Their job is to stop the
walker applying stdlib semantics to a user-defined proc of the same name, which
would be a silent wrong verdict.

So this is not "a replacement per call site whose semantics differ by node
kind" — it is one helper. Extract `originModule(sym): string` (or
`isFromModule(sym, "unicode")`), implement it once on a non-deprecated API, and
have all three guards call it. A correctness-load-bearing guard currently
expressed three times inline becomes testable in one place, which is worth more
than the deprecation fix.

**S4d** — regenerate the warnings baseline and record the new integrity numbers
in `nelli-sweep-baselines/README.md`.

## §5 — S5: the N45 probes run in no Windows leg (#172)

`tests/tn45probe.nim` and `tests/tprobe_n45stats.nim` are registered in
`nelli.nimble` but do not match the `tsymex_*` pattern
`scripts/derive-ci-suites.ps1:60` uses to build the `symex-mingw` corpus, so
they run in no Windows leg. Recommended-not-done across #163 review rounds 11
to 13 only because a Windows leg change could not be verified before the branch
was pushed. The branch is pushed and green, so the verification is now cheap.

Rename both to `tsymex_n45probe.nim` / `tsymex_n45stats.nim` — **and the
`.nim.cfg` sidecar**, which supplies `-d:symexQueryStats` and is matched by
filename, so a rename that misses it silently drops the define and compiles the
`skip()` stub. Update the nimble registration and the comment there about
`tn45probe`'s runtime. Confirm `symex-mingw` picks them up on the next push; if
`tn45probe`'s runtime is too long for the leg, skip-list it there **explicitly**
rather than leaving it unmatched — an unmatched file and a skip-listed one look
identical on the board and only one of them is a decision.

## §6 — Slice plan

No internal dependencies; any order, any parallelism.

| # | slice | issue | gate |
|---|---|---|---|
| S1 | byte-mode arms for float/bytes/string + exhaustive dispatch | #164 | 256 distinct first bytes → >1 decoded value **per kind** |
| S2 | `forAllWithSymexSeeds` honours `dbPath`/`testId` | #165 | second run replays: `dbReplays == 1`, same counterexample |
| S3 | trailing-block instrumentation — **blocked on i1** | #170 | (b) only: `withLock` SUT whose race needs an in-lock jitter point |
| S4 | a–d: unused imports, `checksums/sha1`, `originModule` helper, baseline regen | #171 | warnings delta shows 40 → ~0 distinct; `sha1` digest unchanged |
| S5 | rename the N45 probes + sidecar | #172 | `symex-mingw` runs both on the next push |

Sweep discipline as usual: `scripts/sweep-diff.sh` against
`nelli-sweep-baselines/base-bbde48c.log` per slice. S4 is the exception that
proves the rule — it is the one slice whose *purpose* is to move the warnings
sidecar, so it regenerates the baseline afterwards rather than diffing against
it.

## §7 — Open items

**i1 (S3) — owner: corey.** Leave `{.jitterPoints.}` warning on trailing-block
calls (option a), or instrument an allow-list of known concurrency macros
(option b)?

No lean recorded. This is a genuine fork: (b) buys jitter coverage inside
critical sections — the place races actually live — at the cost of a
stringly-typed list of macro names that is wrong the moment someone writes
their own locking wrapper, and (a) ships a permanent warning on correct code.
The bar does not choose between them; appetite does. S3 stays out of the slice
order until this is answered, and the other four slices do not wait on it.
