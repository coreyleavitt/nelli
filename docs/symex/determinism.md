# Symex determinism + cross-Z3-version invalidation

## TL;DR

A persisted symex witness is a function of:

1. The SUT's IR (parameter shapes, body, transitively-reachable callees)
2. The symex target (`tLabel(...)` / `tAssertionViolation()` / `tIndexError()`)
3. The `SymexSettings` (integer semantics, unwind depth, call depth, timeout)
4. **The Z3 build that produced it**

When (1)–(3) are unchanged, a fixed Z3 build is deterministic for our queries
(`bv`, `array`, and `int` theories with default tactics). When the Z3 build
changes — minor or patch — the produced witness can differ even on
identical inputs, and any *abstract* judgement (UNSAT/UNKNOWN) can flip if
preprocessing changed.

This document records the contract: **persisted symex witnesses are tagged
with the producing Z3 version. A different Z3 version invalidates them.**

## The contract

```nim
proc saveSymexWitness*(db: ExampleDatabase, testId: string,
                       finding: SymexFinding, maxEntries = 64)

proc loadSymexWitnesses*(db: ExampleDatabase, testId: string,
                         z3Version: string): seq[seq[ChoiceNode]]
```

The `z3Version` carried on `SymexFinding` is `z3FullVersion()` —
nim-z3's wrapper around `Z3_get_full_version()`, returning the vendor-
formatted string (e.g. `"4.13.3.0"`).

Persisted entries are bucketed under a derived key:

    <testId>#symex#<z3Version>

`loadSymexWitnesses(testId, version)` queries exactly that bucket. A version
upgrade therefore rotates the bucket — *stale witnesses become invisible to
the new Z3 build*. The bucket the old Z3 wrote is still on disk; we just
never look at it. This is correct, not lossy: re-running symex under the new
Z3 will repopulate the new bucket with whatever the new build now finds.

The DB layer below this — `proptest/db.nim` — has no symex awareness at all.
The Z3 tag is encoded in the testId, not in the entry schema. This was a
deliberate v1 choice: schema changes to `seq[ChoiceNode]` would propagate to
every consumer of the DB format, and the schema is otherwise stable. The
tradeoff: a `loadPrimary(testId)` call (random-PBT path) cannot transparently
see symex entries — which is also a correctness win, because symex entries
have a hidden Z3-version dependency that random entries don't.

## Why minor Z3 upgrades can shift witnesses

Z3's default tactics rewrite formulas before the core solver sees them. The
rewrites are deterministic *for a fixed build* but evolve across releases:

- BV preprocessing tactics (`propagate-bv-bounds`, `bit-blast`) change
  every few releases as new identities are discovered or numerical edge
  cases get fixed.
- Array theory's instantiation heuristics for `select(store(...))`
  patterns evolve.
- The `model_compress` step folds redundant assignments differently across
  versions, producing structurally-different (but equivalent) witnesses.

Two distinct witnesses both satisfy the same path condition; either is a
valid output, but the choice of which one is *the* witness is not stable
across Z3 versions. For PBT regression-seed semantics, "the regression seed
reproduces what symex found yesterday" is the contract we want; an upgraded
Z3 silently substituting a *different* satisfying input would corrupt the
seed's role as a fixed test case.

## Why we don't try to be cleverer

Plausible alternative designs we rejected:

| Design | Why we rejected it |
|---|---|
| Re-run symex under the new Z3 and verify the old witness still satisfies | Witness validation under symbolic execution = re-running the walker = expensive. Bucket rotation costs nothing. |
| Per-tactic version fingerprints | nim-z3 doesn't expose a tactic-level version. Patch-level granularity is what we have. |
| Major version only | Z3 has historically shipped semantics-affecting changes in patch releases (e.g. 4.8.5→4.8.6 fixed array-extensionality). Patch-level is the safe granularity. |
| Tag with the SUT IR hash instead of (or alongside) the Z3 version | Worth adding once macro-time IR hashing exists. The Z3-version tag is necessary for the version axis even then. |

## Cross-language considerations

`z3FullVersion()` is a runtime FFI call. The string is whatever the linked
`libz3` reports — so an OS package manager bumping `libz3.so` invalidates
witnesses without any rebuild of proptest itself. This is correct.

If a user pins their environment via Nix or a container image, the tag is
stable across runs and CI agents. If they don't, witnesses persisted on one
machine may not reload on another — but they'll be silently re-derived on
the next `assertCoveredBy` call, so this is graceful.

## Future work

- IR hash inclusion in the tag (`<testId>#symex#<z3Version>#<irHash>`) for
  SUT-level invalidation. Requires `macros.signatureHash` or a hand-rolled
  IR hash.
- Witness compaction: the rendered `seq[ChoiceNode]` is a length-prefixed
  linearisation; a Z3-canonical AST hash could deduplicate witnesses across
  isomorphic SUTs, but isn't a v1 concern.
- A `forAllUsing` flow that auto-seeds with symex witnesses from the
  matching bucket. Currently the user calls `loadSymexWitnesses` and feeds
  them into their strategy themselves.
