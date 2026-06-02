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
                    z3Version, nimVersion, walkerVersion: string): string
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
| Walker version (`symexWalkerVersion` const) | yes | maintainer-bumped when walker semantics shift |

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
- **`withSymexSeeds` strategy combinator**. The Phase 7 input-source
  role lifts loaded witnesses into the engine's existing
  `explicit`/`dbReuse` phases. Built when first consumer demands.
