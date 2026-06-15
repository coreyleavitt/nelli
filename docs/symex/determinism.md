# Symex determinism + content-addressed cache invalidation

## TL;DR

A persisted symex witness is a function of:

1. The SUT's canonical IR (parameters + body + transitively-reachable
   callees + their `{.symexOpaque.}` status)
2. The symex target (`tLabel(...)` / `tAssertionViolation()` /
   `tIndexError()`)
3. The witness-relevant subset of `SymexSettings`
4. The Z3 build that produced it
5. The Nim compiler version (because the parser/typebridge that
   builds the IR may evolve)
6. The walker version (because the walker's encoding may evolve in
   witness-affecting ways)

When *any* of these changes, the witness can change (or its validity
can lapse) — so the cache key changes too.

This document records the contract: **persisted symex witnesses are
keyed by a content-addressed hash over every input above. Any change
to anything that affects the witness rotates the key, making stale
entries invisible.**

## The contract

```nim
proc saveSymexWitness*(db: ExampleDatabase, fn: typed,
                       target: static SymexTarget,
                       settings: static SymexSettings,
                       finding: SymexFinding, maxEntries = 64)

proc loadSymexWitnesses*(db: ExampleDatabase, fn: typed,
                         target: static SymexTarget,
                         settings: static SymexSettings
                        ): seq[seq[ChoiceNode]]
```

Both are macros that parse `fn`'s typed proc, build a
`SymexProgram` (params + body + transitively-reachable callees),
and delegate to a runtime impl that derives the cache key:

```nim
proc symexCacheKey*(prog: SymexProgram, target: SymexTarget,
                    settings: SymexSettings,
                    z3Version, nimVersion, walkerVersion,
                    renderingVersion: string): string
```

The key is `"sx:" & SHA1(canonical_encoding)` where the canonical
encoding is the deterministic string produced by
[`proptest/smt/canonicalize`](../../src/proptest/smt/canonicalize.nim).
The encoding's invariants:

- **Source locations are never encoded.** Moving code doesn't
  invalidate.
- **Local-variable name spellings are erased.** `let i = 0` and
  `let j = 0` produce identical canonical strings. Locals are
  encoded by positional `$N` slots (de-Bruijn-style); only
  *param* and *callee* names cross the boundary as identifiers.
- **`Table[string, ProcSig]` iteration order is normalised** by
  sorting callees by name.
- **`acceptUnknownAsCovered` is provably excluded** — it
  influences the verifier's raise/pass decision but never the
  walker's output or the persisted witness. (Regression-guarded
  by a test in `tests/tsymex_canonicalize.nim`.)
- **All other `SymexSettings` fields** (`integerSemantics`,
  `queryTimeoutMs`, `maxFrontierSize`, `maxCallDepth`,
  `maxLoopUnwind`) participate in the key.

## What "invalidate" looks like

A `loadSymexWitnesses` call computes the current key and asks the
DB for entries under it. Stale entries from before any of the six
inputs changed live under a *different* key, so they're invisible
to the new query. They aren't deleted — they're just unreachable.
The DB's regular eviction policy eventually reaps them.

## What changes the key (and why)

| Change | Key rotates? | Why |
|---|---|---|
| SUT body | yes | witness depends on the body |
| Param type | yes | witness shape depends on param types |
| Param `var T` flag | yes | mutation propagation differs |
| Param range hint (`Natural`, `range[..]`) | yes | abstraction layer consumes it |
| Callee body | yes | inlining produces different path conds |
| `{.symexOpaque.}` on a callee | yes | toggles the opaque-effectful path |
| Nominal object name (`MyObject` → `YourObject`) | yes | conservative: rename = program change |
| Anonymous tuple field rename | no | positional encoding |
| Local `let` variable rename | no | positional encoding |
| `integerSemantics` | yes | encoding differs |
| `maxLoopUnwind` / `maxCallDepth` / `maxFrontierSize` | yes | affect which paths survive |
| `queryTimeoutMs` | yes | a longer timeout can produce SAT where shorter gave UNKNOWN |
| `acceptUnknownAsCovered` | **no** | provably unrelated to the witness |
| Z3 version | yes | preprocessing tactics evolve |
| Nim version | yes | parser/typebridge may evolve |
| Walker version (`symexWalkerVersion` const) | yes | maintainer-bumped when walker semantics shift. Phase 14 cycle A7b: `"3" → "4"` (Cluster A semantic completeness — itMultiVariant, else: arms, non-enum discs, symbolic-RHS reassign, composite zero-init, Z3Int disc promotion, var T, frontier pruning). Phase 15 cycle F8: `"4" → "5"` (Cluster F float support — float32/64 type-bridge, IEEE literals/arith/compare, int↔float conv, std/math FP ops, bit-exact float witness extraction) |
| Rendering version (`renderAsChoicesVersion` const) | yes | maintainer-bumped when the witness → choice-IR serialisation changes (e.g. Phase 12 collection encoding fix) |
| `Strategy[T].constraintDigest` (Phase 14 B1) | yes | rotates entries derived through standard strategies; empty digest for `newStrategy`-built customs (documented silent-clamp) |

## Why content-addressing and not testId-keyed

The previous design used `<testId>#symex#<z3Version>`. Two tests
calling `assertCoveredBy(handle, tLabel("zero"))` produced two
separate DB buckets — same SUT, same target, same Z3, same
settings, but different testIds. Content-addressing fixes this:
the witness *is* the SUT/target/settings/version tuple; any test
that shares them shares the entry. Storage is deduplicated; cache
hits are correct by construction.

testId-keyed storage also failed to invalidate on SUT refactor:
change the body of `handle`, leave testId the same → load returns
the old witness even though it may no longer satisfy the new body.
The content-addressed key catches this — and every other
witness-affecting input change too.

For *attribution* ("which tests produced or observed this
witness?") the `SymexFinding.discoveredBy: seq[string]` field is
the secondary index. It's not part of the cache key — including it
would defeat content-addressing — but it's available on
in-memory findings and the engine surfaces it via
`Report.symexFindings`.

## Why minor Z3 upgrades can shift witnesses

Z3's default tactics rewrite formulas before the core solver sees
them. The rewrites are deterministic for a fixed build but evolve
across releases:

- BV preprocessing tactics (`propagate-bv-bounds`, `bit-blast`)
  change every few releases as new identities are discovered or
  numerical edge cases get fixed.
- Array theory's instantiation heuristics for `select(store(...))`
  patterns evolve.
- The `model_compress` step folds redundant assignments
  differently across versions, producing structurally-different
  (but equivalent) witnesses.

Two distinct witnesses both satisfy the same path condition;
either is a valid output, but the choice of which one is *the*
witness is not stable across Z3 versions. The Z3-version
component of the cache key ensures a build upgrade rotates the
bucket.

## Why we don't try to be cleverer

Plausible alternative designs we rejected:

| Design | Why we rejected it |
|---|---|
| Re-run symex under the new Z3 and verify the old witness still satisfies | Witness validation under symbolic execution = re-running the walker = expensive. Bucket rotation costs nothing. |
| Per-tactic version fingerprints | nim-z3 doesn't expose a tactic-level version. Patch-level granularity is what we have. |
| Major version only | Z3 has historically shipped semantics-affecting changes in patch releases (e.g. 4.8.5→4.8.6 fixed array-extensionality). Patch-level is the safe granularity. |
| Hash the IR with `std/hashes` | Not stable across Nim versions — `hash(string)` has changed (Farm Hash → Wyhash). SHA-1 is deterministic across builds. |
| Skip the IR hash entirely (only Z3 version) | Doesn't invalidate on SUT refactor. Wrong by construction. |
| Skip the Nim version | Walker's IR can change across Nim versions even with identical source. Honest hashing includes it. |

## Cross-language considerations

`z3FullVersion()` is a runtime FFI call. The string is whatever the
linked `libz3` reports — so an OS package manager bumping
`libz3.so` invalidates witnesses without any rebuild of proptest
itself. This is correct.

`NimVersion` and `symexWalkerVersion` are compile-time constants
embedded in the binary. Rebuilding proptest against a new Nim
version invalidates witnesses produced by the old build. A walker
semantic change requires a manual bump of `symexWalkerVersion` in
`proptest/smt/canonicalize.nim`.

### `symexWalkerVersion` history

| Version | Phase | Reason |
|---|---|---|
| `"1"` | Phases 0-10 baseline | Variants lowered to flat tuples; witness stubbed as `default(Object)`. |
| `"2"` | Phase 11 cycles 1-12 | Variants represented as first-class `itVariant`; walker forks at field access; `tFieldDefect()` target added; witness via case-dispatch construction. Witnesses persisted under `"1"` are correctly invalidated — the old representation was unsound. |
| `"3"` | Phase 11 deferral #5 closed (post-cycle-12) | Plain (non-recCase) fields shared across arms — allocated once and surviving discriminator reassignment, matching Nim's runtime semantics. Witness path layout for plain fields moved from `<base>.@<tag>.<field>` to `<base>.<field>`. Witnesses persisted under `"2"` are correctly invalidated. |
| `"4"` | Phase 14 cycle A7b (Cluster A close-out) | Variant-soundness completeness — `itMultiVariant`, `else:` arms, non-enum discriminators, symbolic-RHS discriminator reassign, composite zero-init, Z3Int discriminator promotion, `var T` params; C3 frontier pruning shares the bump. Witnesses persisted under `"3"` are correctly invalidated. |
| `"5"` | Phase 15 Cluster F close-out (cycle F8) | Float support (F1–F7): `itFloat32`/`itFloat64` + `svFloat32`/`svFloat64` type-bridge, IEEE literals/arith/compare, int↔float conversions, std/math FP-native ops + predicates (`iekMathCall`), eval-side bit-exact witness extraction (`float64Vals`/`float32Vals`). Float SUTs parser-errored or stubbed witnesses under `"4"`, so no stale `"4"` entry can falsely re-hydrate; one bump at Cluster F close-out (v2 Invariant 1) rotates the cache for the multi-cluster session. |
| `"6"` | Phase 15 Cluster S close-out (cycle S11) | Full-string support (S1–S10a): byte-faithful Z3 String model (≤0xFF char-range), len/index/slice/high, find/contains/startsWith/endsWith, replace/split/join, regex match, concat, bytes, `$int`/`parseInt`; S10b adds the `parseInt` raises-path; S11 classifies the immutable-string mutations (`s[i] = c`, `s.add`) as `seUnsupportedStringOp`. One bump at Cluster S close-out rotates the cache so any `"5"`-era string verdict re-solves under the now-complete string semantics. |
| `"7"` | Phase 15 Cluster E close-out (cycle E7) | Exception support (E1–E6): `raise`/`try`/`except`/`finally` IR + walker semantics, the `sxRaised` verdict path (`cacheKeyRaised(typeId)`), first-match handler resolution with subtype catch over the static + dynamic-user exn hierarchy, inter-procedural raise propagation, finally composition on both exit paths (finally-raises-replaces), and `Defect` modeling (`sxRaised{isDefect}` + `defectExclusions`). One bump at Cluster E close-out rotates the cache so any `"6"`-era verdict re-solves under the now-complete exception semantics. (E8 — `getCurrentException` — is additive under `"7"`.) |

### Exceptions: `sxRaised` cache key, `isDefect`, and the handler-stack depth bound (Phase 15 Cluster E)

Exception-raising SUTs participate in the cache key and determinism
contract like every other verdict; the exception-specific guarantees
are:

- **`sxRaised` cache key.** A reachable raise surfaces as an
  `sxRaised` verdict persisted under a dedicated per-type slot keyed
  by `cacheKeyRaised(typeId)` (the `:raised:<typeId>` suffix on the
  content-addressed base key), plus an index slot
  (`cacheKeyRaisedIndex`, the `:raised` suffix) enumerating the
  persisted type ids so a multi-raise SUT's full `seq[RawResult]`
  reloads without a DB key-prefix scan and without re-invoking Z3.
  `saveSymexRaisedImpl`/`loadSymexRaisedImpl` are the round-trip pair.
  The base key includes `symexWalkerVersion`, so a walker bump
  correctly orphans every prior raised verdict.

- **`isDefect` semantics.** A raised type that resolves (via the
  static `exnTypeTable` or the dynamic `userExnHierarchy`) to a
  `Defect` subtype is recorded as `sxRaised{isDefect: true}`. A
  non-excluded defect ALWAYS surfaces (even under a label/non-raise
  search) so a reachable contract violation is never silently
  dropped; a defect whose `DefectKind` is in
  `settings.defectExclusions` (default `{dkOutOfMemoryDefect,
  dkStackOverflowDefect}`) is suppressed. Because `defectExclusions`
  participates in the cache key (it is part of `SymexSettings`),
  changing the exclusion set re-keys the verdict — a previously
  suppressed defect is re-evaluated under the new set.

- **Handler-stack depth bound.** Exception control flow is decided by
  the per-frame `handlerStack` (a try push at `myDepth =
  handlerStack.len`, popped to `myDepth` after the body). Raise
  routing is bounded: `routeRaise` always returns `@[]` on the
  straight-line raise path (it never re-walks the raising statement),
  the depth-tagged `caught`/`pendingRaise` continuations are claimed
  exactly once by the owning `try`, and the `escaped` channel is
  drained exactly once per call descent — so the handler-stack walk
  terminates and the verdict is deterministic (no path explosion, no
  loop through a finally).

### Float type-bridge, NaN/Inf, and rounding modes (Phase 15 Cluster F)

Floating-point SUTs participate in the cache key and determinism
contract exactly like every other type; the float-specific
guarantees are:

- **Type-bridge.** Nim `float`/`float64` classify to `itFloat64`
  (allocated `svFloat64`); `float32` to `itFloat32` (`svFloat32`).
  `float` and `float64` are the same IR type, so they share cache
  entries. Witnesses are read back bit-exactly from the SAT model
  into the two `RawWitness` tables `float64Vals` / `float32Vals`
  (F7) — these tables are part of the canonical witness encoding.
- **NaN / Inf (ADR-0005).** A single canonical NaN, no payload
  bits. IEEE semantics are honored in the solver: `NaN == NaN` is
  UNSAT, all ordering comparisons against NaN are false (`x < x`
  is UNSAT, irreflexive even for NaN), and `±Inf`/`±0.0` are
  distinct extractable witnesses. Z3's `to_ieee_bv(NaN)` is
  *unspecified*, so NaN is detected via the `isNaN` predicate at
  extraction time and emitted as Nim's canonical `NaN` rather than
  round-tripped through a bit-vector. See `ADR-0005-float-nan-inf.md`.
- **Rounding modes (F3 / F5).** Deterministic and fixed, never
  configurable, so the same SUT yields the same verdict everywhere:
  IEEE arithmetic and int→float conversion use round-to-nearest-even
  (`rmRNE`); float→int conversion truncates toward zero (`rmRTZ`).
  std/math ops pick the mode matching Nim's runtime semantics:
  `floor`→`rmRTN`, `ceil`→`rmRTP`, `round`→`rmRNE`, `trunc`→`rmRTZ`,
  `sqrt`→`rmRNE`. Out-of-range float→int overflow is unconstrained
  under the current model (RFC F5 defers range-overflow → RangeDefect);
  round-trip property tests therefore window the input so truncation
  lands deterministically.

### String type-bridge: byte-faithful model + supported ops (Phase 15 Cluster S)

String SUTs participate in the cache key and determinism contract
exactly like every other type. The string-specific guarantees are:

- **Byte-faithful model (ADR-0006).** A Nim `string` is a Z3 String
  (`Z3_mk_lstring`, one Nim **byte** → one Z3 character). Every free
  `string` variable is constrained at allocation to characters
  **≤ 0xFF** (Latin-1 byte range) via a regex-membership assertion
  `s ∈ (re.range '\x00' '\xff')*`. Under that constraint **Z3 position
  == Nim byte index**, so Z3's positional model and Nim's byte model
  *coincide* — there is no divergence, and the witness round-trips
  byte-for-byte to a Nim string. A multi-byte string *literal* like
  `"é"` lowers to its raw UTF-8 bytes `[0xC3, 0xA9]` (length 2, not a
  length-1 scalar), so `mkString(s).len == s.len` (byte count) for all
  `s`.

- **Byte-indexed length / index / slice.** `s.len` (Z3 `str.len`),
  `s[i]` read (via `at(s,i)` → `toCode` → BV8 char bridge), `s[a..b]`
  (Z3 `substr`, byte offsets), and `s.high` (`len-1`) are **all
  byte-faithful and match Nim exactly**. They are NOT classified
  errors. Out-of-range `at`/`substr` yields the empty string per the
  Z3 spec (no crash); `at`-then-`toCode` returns −1 (→ BV8 0xFF) for an
  out-of-range index.

- **Supported ops** (modeled directly on the Z3 String / Sequence /
  Regex theory): `len`, index `s[i]`, slice `s[a..b]`, `s.high`,
  `find` (Z3 `indexOf`, −1 when absent), `contains`, `startsWith`,
  `endsWith`, `replace` (first-occurrence), `split` (special cases —
  see below), `join` (over a concrete `seq[string]`), `bytes(s)`
  (byte-faithful identity view — each char position → its BV8 byte
  value, `len(bytes(s)) == len(s)`), and regex `match`/`contains(re…)`
  (Z3 `seq.in.re` via the S6a Nim-regex → `Z3Regex` parser, byte-range
  character classes). Equality `==`/`!=` (Phase 5 baseline + S1's
  `cmpString`) participate too.

- **`split` is special-cases-only.** The empty-separator case
  (`split("abc","")`) yields single-**byte** parts `@["a","b","c"]`;
  the concrete-inline case (literal receiver AND literal separator)
  computes the parts in Nim with no Z3 quantifier. A *general symbolic*
  split (symbolic receiver or separator) would require a universal
  quantifier over a symbolic `seq[string]` and is conservatively
  classified `seZ3StringIncomplete` → `sxUnknown` (never encoded, never
  a hang). `join` likewise requires a concrete-length receiver
  (`seqLen` a Z3 numeral); a symbolic-length join → `seZ3StringIncomplete`.

- **Classified-unsupported ops + their error kinds.** Each is honestly
  classified `sxUnknown` with a populated error (Invariant 3 — never a
  silent UNSAT, never a crash):

  | Op | Error kind | Reason |
  |---|---|---|
  | `for c in s` | (explicit message, NOT `seByteIterUnsupported`) | unbounded symbolic iteration length — no sound bounded encoding |
  | `s[i] = c` / `s.add(c)` / `s.add(otherStr)` | `seUnsupportedStringOp` | Z3 strings are **immutable** (ADR-0006); classified at S11. `s[i] = c` is detected as an `nnkAsgn` whose LHS is a string-index; `s.add(…)` as an `itString`-receiver `add` call. The reason is immutability, NOT a byte/codepoint mismatch. |
  | `toLower` / `toUpper` | `seUnsupportedStringOp` | no Z3 case-folding primitive (regex-range approx is Phase 16) |
  | `replaceAll` / regex `replace(re…)` | `seZ3VersionMissing` | gated behind `z3WithSeqReplaceAll` / `z3WithSeqReplaceRe`; both **absent on Z3 4.15.0** (this dev image) |
  | general symbolic `split` | `seZ3StringIncomplete` | universal quantifier over a symbolic `seq[string]` — conservatively not encoded |
  | `bytes(symbolic-len s)` | `seBytesSymbolicLength` | byte count is the unknown symbolic length |
  | `bytes(concrete-len > maxBytesEncodingLen)` | `seBytesLengthTooLarge` | exceeds the encoding cap (default 32) |
  | `s.find(re…)` (regex search) | `seUnsupportedRegex` | nim-z3 has no `indexOf`-on-regex API (only substring `indexOf`); deferred |
  | rejected regex (backref `\1`, lookahead `(?=…)`, named groups) | `seUnsupportedRegex` | the S6a parser rejects these families |

  Two error kinds (`seByteIndexUnsupported`, `seByteIterUnsupported`)
  remain in the `SymexErrorKind` enum for forward-compat but are
  **unused** — under byte-faithful, `s.high` IS supported and `for c
  in s` carries an explicit unbounded-iteration message instead.

  **Cluster S op-table COMPLETE (closed at S11).** With `s[i] = c`,
  `s.add(c)`, and `s.add(otherStr)` classified `seUnsupportedStringOp`
  (Z3 string immutability), the byte-faithful supported/unsupported op
  table above is complete for Cluster S: every Nim string surface op the
  cluster targets either lowers to a sound Z3 String / Sequence / Regex
  encoding (the supported list) or is honestly classified `sxUnknown`
  with a populated error kind (the table above). No string op silently
  UNSATs or crashes. The Cluster-S walker version is now `"6"`.

- **Latin-1 witness coverage limitation.** The ≤ 0xFF free-var
  constraint means synthesized witnesses are limited to **one byte per
  character** — Z3 never synthesizes a multi-byte UTF-8 rune for a free
  variable. A multi-byte *literal* (e.g. `"é"`) still works (it lowers
  to its raw bytes and a free var can match those byte values:
  `s == "é"` is SAT at `s.len == 2`), but a free string SUT will only
  ever witness Latin-1 byte sequences, not arbitrary Unicode scalars.
  This is the soundness/coverage trade-off that makes Z3 position ==
  Nim byte hold; it never produces an *unsound* witness (every witness
  round-trips to a real Nim byte string), only a *coverage-limited* one.

- **`$int` / `parseInt` int↔string (S10a, digits-path only).** `$n`
  (`n: int`) lowers to Z3 `(str.from-int n)` (a decimal-string
  svString); `parseInt(s)` lowers to Z3 `(str.to-int s)` (a non-negative
  digits value, or **−1** for a non-digit string) with a leading-`-`
  negative fork (`ite(startsWith(s,"-"), -toInt(substr(s,1,…)), toInt(s))`,
  the negative branch gated `toInt(substr…) >= 0` so a non-digit suffix
  can't produce a false positive). **Pre-E1 unsoundness window:**
  `parseInt` non-digit input returns Z3's unconstrained model (the fixed
  −1) rather than RAISING `ValueError` as Nim does — so a path like
  `parseInt(s) == -1` is sxSat for a non-digit `s` where Nim would have
  raised. Modeling the raise requires the exception walker (E1); until
  **S10b** (post-E1) lands, this gap is flagged with a classified
  `seParseIntPreE` **`sevHint`** (emitted whenever `parseInt` is lowered
  on a not-provably-digit string — a conservative HINT over-emission).
  The hint is `sevHint`, so the path STAYS sxSat and still satisfies the
  Invariant-7 severity contract (only sxUnknown requires a sevError).
  `$float`/`parseFloat` and the raises-path are deferred to S10b.

### `renderAsChoicesVersion` history

Phase 12 introduced a *second* maintainer-bumped version that
participates in the cache key independently of `symexWalkerVersion`.
It covers **how a SAT witness is serialised into the choice IR**
(`proptest/symex.nim:renderAsChoices`), as distinct from how the
walker reasons about the SUT.

The two-version split exists so witness-encoding bumps don't
invalidate witnesses whose encoding didn't change. Example: cycle
6 of Phase 12 fixed the `seq[T]` / `HashSet[T]` / `Table[K, V]`
encoding (from broken length-prefix to working continue-boolean)
— bumping only `renderAsChoicesVersion` left every int / bool /
string / tuple / object / variant witness in the cache warm.

| Version | Phase | Reason |
|---|---|---|
| `"1"` | Phases 7-11 baseline | Length-prefix encoding for seq / HashSet / Table — latent bug, unreplayable through `lists`/`tables`/`sets` strategies. |
| `"2"` | Phase 12 cycle 6 | Per-element continue-boolean encoding matching the strategy contract; deterministic sort by key (Table) / element (HashSet) so the cache key for the same logical witness is stable across Nim's undefined hash-iteration order. Collection witnesses persisted under `"1"` are correctly invalidated. Non-collection witnesses are unaffected. |

## Strategy-cache caveat

Symex witnesses are persisted as `seq[ChoiceNode]` and replayed
through the strategy's `DataSource` at consumption time. Strategy
*constraints* — the `lo`/`hi` range on `integers(lo, hi)`, the
`maxLen` on `lists(elem, maxLen=N)`, the value set on
`sampledFrom(values)` — live inside the strategy *closure* at
runtime; they are NOT included in the content-addressed cache
key.

`DataSource` enforces a `permits`/`clamp` contract on replayed
choices: if the stored choice value lies outside the strategy's
current constraint window, the DataSource silently clamps it to
the nearest in-range value. The witness REPLAYS — but the value
the property sees may differ from the one Z3 produced.

Concretely: a witness saved when the SUT used `integers(0, 100)`
and later replayed when the SUT was changed to `integers(200,
300)` will replay as `200` (clamped), not the original `0`. The
report's outcome may differ — `0` was a counterexample, `200`
may not be.

### Why this isn't fixed in the cache key

Strategies are first-class closures whose state isn't reachable
from outside the `Strategy[T]` object. There is no stable hash
over a closure: equivalent strategies may differ in environment
capture, and equality is undecidable. Hashing the strategy's
*source-position* would invalidate every strategy on every move
(false positives); hashing nothing falls into the silent-clamp
trap (false negatives).

### Workaround

Use a fresh `Settings.testId` (or `inMemoryDatabase()`) whenever
the strategy's constraints change. Content-addressing handles the
SUT-body axis automatically; the testId axis handles the strategy-
constraint axis manually. This composes naturally with the existing
`derandomize=true` workflow — bump the testId, the seed re-derives,
the cache rotates.

Tracked as deferral #1 in [PHASE12_PLAN.md](PHASE12_PLAN.md).

Persisted witnesses across a walker version bump are *correctly*
invisible — same mechanism as a Z3 version bump. There is no
"upgrade path" because the witness representation under the old
version may be structurally incomparable to the new (e.g., flat-
tuple Phase 10 witnesses against case-dispatch Phase 11
witnesses). Re-running symex under the new walker version
re-derives the appropriate witnesses.

## Verdict caching (Phase 13)

Phase 13 extends the content-addressed cache to non-SAT
verdicts. UNSAT and UNKNOWN findings are now persisted alongside
SAT witnesses; warm-run cost drops from
`N targets × per-target solver budget` to `N × one DB load`.

**Phase 14 UNKNOWN sub-cases.** A cached `:unk` entry now covers
three distinct origins, all materially equivalent at cache-read
time but each documented:

1. **Z3-rlimit exhausted** (Phase 13): solver hit its logical
   step budget before deciding sat/unsat.
2. **Walker-loop-unwind exhausted** (Phase 11 baseline): the
   walker truncated a loop at `maxLoopUnwind` and conservatively
   widened the path to uncertain.
3. **Frontier-pruned** (Phase 14 C3, ADR-0004): the walker's
   post-step prune dropped paths to keep
   `paths.len <= settings.maxFrontierSize`; pruned paths set
   `sawUnknown = true` which cascades into the final verdict.

All three set `sawUnknown = true` and cache under the same `:unk`
suffix. The distinction is informational; consumers treating
`sfUnknown` uniformly are correct.

### Three sibling keys

A single content-addressed hash `H` now anchors three sibling
slots under the `"sx:"` namespace:

```
"sx:" & H & ":sat"    → seq[ChoiceNode]   (the SAT witness)
"sx:" & H & ":unsat"  → @[]               (UNSAT verdict sentinel)
"sx:" & H & ":unk"    → @[]               (UNKNOWN verdict sentinel)
```

All three are content-addressed on the same inputs; an input
change (SUT body, target, settings, Z3/Nim/walker/rendering
version) rotates all three keys atomically.

### Sentinel encoding and the `verdictCacheMaxEntries = 1` invariant

UNSAT and UNKNOWN have no witness data, so they store the empty
seq `@[]` as a sentinel. The DB returns `@[@[]]` (one entry,
empty inner seq) on hit vs `@[]` (no entry) on miss, which
`loadSymexVerdictImpl` distinguishes via `len == 1 and result[0]
== @[]`.

The constant `verdictCacheMaxEntries = 1` is **mandatory** at
every `saveSymexVerdictImpl` call site. The default
`maxEntries = 16` allows accumulation, which would push the
sentinel out of position 0 under any stray non-sentinel write
and silently break the load detection. Pinning to 1 makes the
structural invariant unbreakable.

### UNSAT-first load-order tie-break

If both `:unsat` and `:unk` are present for the same `H`
(possible across `queryRLimit` bumps that turned a prior UNKNOWN
into a settled UNSAT), `loadSymexVerdictImpl` checks `:unsat`
first and returns `some(sfUnsat)` on hit. **UNSAT wins**
regardless of save order — it's a stronger verdict.

### `queryRLimit` semantics

Phase 13 renamed `SymexSettings.queryTimeoutMs` to
`queryRLimit` and wired it to Z3's `rlimit` parameter via
`solver.setParams`.

- **Units**: Z3 logical step count, NOT wall-clock milliseconds.
  Deterministic across machines for a fixed Z3 build.
- **Default `0`**: unbounded (Z3's documented behavior).
  Opt-in semantics: callers wanting a bounded UNKNOWN set a
  positive value.
- **Per-`trySolve` budget, not per-`runSymex` total**. A SUT
  with M target labels exercising multiple `trySolve` invocations
  may spend up to `M × queryRLimit` total. Each invocation is
  independently reproducible — the property that matters for the
  verdict cache.

### nim-z3 rlimit guarantee

The default `Z3_mk_solver(ctx)` produces Z3's portfolio solver.
For the BV[W] + linear-integer + Z3 array-theory formulas this
codebase emits (no quantifiers, no non-linear arithmetic),
the portfolio honors `rlimit` cleanly: budget exhaustion
returns `Z3_L_UNDEF` (`zsUnknown`). Non-linear and quantifier
tactics may treat `rlimit` as best-effort — out of scope for
the current walker output.

### `random_seed = 0'u` baseline

`trySolve` sets `random_seed = 0'u` on the solver explicitly.
This overrides any `setGlobalParam("random_seed", ...)` the
calling process may have set elsewhere, so the cache's
determinism guarantee doesn't depend on undocumented Z3
defaults.

### Stability disclaimer tiering

| Stability axis | UNSAT | UNKNOWN |
|---|---|---|
| Nim build flags (`-d:release`/`-d:debug`) | stable | stable (symbolic semantics independent of compilation mode) |
| OS (Linux/Windows/macOS) | stable | stable for fixed Z3 build (`z3FullVersion()` in key) |
| `Z3_NUM_THREADS` / `OMP_NUM_THREADS` env vars | stable | UNKNOWN caching guarantee requires single-threaded solving (the default) — parallel Z3 is nondeterministic. |
| Cross-platform Z3 binaries from different distros | stable | UNKNOWN may differ if build-time tactic configurations diverged. Same Z3 version string + same SHA = same outcome. |

UNSAT is a logical property of the explored fragment — stable
under all of the above (the symbolic walker's IR semantics don't
change). UNKNOWN's stability depends on `rlimit` step counting
being deterministic across configurations, which is Z3's
documented guarantee under the conditions above.

### Corruption self-heal

If a `:unsat` or `:unk` slot contains a non-empty value
(structural corruption from a manual edit or stray write that
bypassed the API), `loadSymexVerdictImpl` treats it as a miss —
the sentinel check (`result[0] == @[]`) fails, the load falls
through to the next suffix, and on full miss `runSymex`
re-derives. The correct verdict overwrites the corrupted slot
on next save. No crash, no false hit.

### Stale-sink note

`recordSymexFinding` deposits into a per-thread sink threadvar
that `consumeSymexFindings()` drains. The sink **survives across
`symexFindAllWitnesses` invocations**. Callers wrapping symex
calls in a retry loop should drain the sink between calls:

```nim
for attempt in 1 .. retries:
  discard consumeSymexFindings()   # clear stale state
  let report = symexForAll(s, fn, db)
  ...
```

This is a pre-existing Phase 12 property, not new in Phase 13;
documented here for completeness.

### Settings-mutation gotcha

Every `SymexSettings` field that participates in the canonical
form (i.e. everything except `acceptUnknownAsCovered`) is part
of the verdict cache key. Mutating any such field between save
and load produces a key rotation and a cache miss — the prior
verdict is invisible, the analysis re-derives. Same lesson as
the strategy-cache caveat above: cache identity is a function
of every input that could change the outcome.

### Multi-process safety (positive property)

The directory backend uses tmp+rename for atomic per-file
writes. Two processes writing the same `:unsat` slot for the
same `H` both write the sentinel `@[]` — semantically identical;
last-writer-wins has no observable effect. Two processes
writing `:sat` and `:unsat` simultaneously target different
files, so there's no race. **The verdict cache is safe under
multi-process concurrent writes** when each process targets the
same content-addressed namespace.

(Exception: `multiplexedDatabase` with a shared/secondary
backend holding verdict entries is undefined. Configuration
invariant: **verdict keys must not appear in shared corpora.**)

### DbError flow

`saveSymexWitnessImpl` and `saveSymexVerdictImpl` accept a
`errors: var seq[string]` accumulator parameter. DB failures
(disk full, permissions, corruption) are caught at the impl
level and appended to `errors`; the call returns normally so
the analysis never aborts on a cache failure. Layer 1
(`symexFindAllWitnesses`) accumulates per-target errors into a
gensymmed `dbErrors` variable that future work (Phase 13
follow-up) will route into `Report.dbErrors`.

This closes a pre-existing cross-layer inconsistency: `db.nim`'s
module promise said errors flow to `Report.dbErrors`, but the
symex layer was propagating them as exceptions and aborting the
analysis with partial findings.

## Future work

- **IR hash compression**. The canonical encoding is the full IR;
  SHA-1 reduces it to 40 hex chars. The encoding itself can grow
  large for big SUTs. Hashing chunks instead of concatenating may
  help if pathological SUT sizes become a problem.
- **Witness validation under upgrade**. Optional flag: re-run symex
  under the new Z3 to confirm the old witness still satisfies. Trades
  cache-miss cost for re-derivation cost. Worth it if witnesses are
  expensive to recompute.
- **DB-level eviction policy for stale buckets**. The current model
  leaves stale entries on disk until the standard eviction policy
  reaps them. A targeted "drop entries whose key doesn't match any
  active SUT" sweep is possible but not urgent.
- **UNSAT / UNKNOWN caching**. Currently re-derived per call —
  `saveSymexWitnessImpl` short-circuits on `status != sfSat`. For
  SUTs with many UNSAT-prone targets the cold-cache cost is
  `N targets × queryTimeoutMs`; caching the UNSAT/UNKNOWN verdict
  under the same content-addressed key would amortise. Workaround
  meanwhile: `excludeTargets` to narrow.
- **Strategy-constraint hashing in the cache key**. Strategies are
  closures with unhashable environment capture; the silent-clamp
  caveat above is the consequence. A stable representation of
  the constraint window (e.g. `lo`/`hi` accessors on numeric
  strategies) would let us include it in the key.
