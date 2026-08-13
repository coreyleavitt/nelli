# ADR-0004 — `maxFrontierSize` enforcement and pruning policy

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-03 |
| **Deciders** | nelli maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [RFC-completeness.md](RFC-completeness.md) C3, [ADR-0003](ADR-0003-variant-soundness.md) (A4 fork interaction) |

## Context

`SymexSettings.maxFrontierSize: int` has been a phantom field since
Phase 10. It participates in the content-addressed cache key
(`canonicalize.nim:339`) but is never read by the walker. Phase 14
makes it behaviorally meaningful so the walker can bound
exploration on SUTs that would otherwise produce unbounded path
explosion — notably symbolic-RHS discriminator reassignment
(ADR-0003 D4) on non-enum discriminators with many `of` arms.

This ADR records the enforcement site, the pruning policy, the
soundness argument, and the relationship to the existing UNKNOWN
sub-cases documented in `determinism.md`.

## Decisions

### D1. Enforcement site: inline in `walkBlock`, not via a `WalkCtx` field

The walker's frontier is the `paths: seq[Path]` argument that flows
through `walkBlock`'s inner loop (`runtime.nim:1421-1426`):

```nim
proc walkBlock(stmts: seq[IRStmt], paths: seq[Path],
               w: var WalkCtx): seq[Path] =
  result = paths
  for s in stmts:
    if w.shouldStop: return
    result = walk(s, result, w)
    if result.len == 0: return
```

There is no `WalkCtx.currentFrontier` field today, and adding one would
duplicate the in-flight `seq[Path]` already threading through the
recursion. The enforcement site is the inner loop: after each
`walk(s, result, w)` call, check `result.len` against
`w.settings.maxFrontierSize`. If exceeded, prune in place and set
`w.sawUnknown = true`.

### D2. Pruning policy: highest-uncertainty-first via the binary `Path.uncertain` flag

The `Path` object carries one binary uncertainty signal:
`Path.uncertain: bool`. The walker sets this when a path encounters
walker-internal uncertainty (loop-unwind exhaustion, opaque calls,
`isUnsupported` nodes). There is no numeric uncertainty score; the
flag is binary.

The pruning policy is operationalized as:

1. **Sort certain paths before uncertain ones** (stable sort —
   preserves declaration order within each tier).
2. **Truncate to `maxFrontierSize`** entries from the front.
3. **Set `w.sawUnknown = true`** unconditionally when any pruning
   occurs (the pruned paths might have led to a SAT witness; that
   possibility is now unverified).

Practical consequence: certain paths are preserved when possible;
uncertain paths are pruned first when the limit is exceeded; ties are
broken by declaration order so pruning is deterministic.

**`maxFrontierSize = 0` means unlimited** (Phase 11 default). No
pruning occurs at zero — preserves backward compatibility with users
who never set the field.

### D3. Soundness: frontier-pruned walks produce `sxUnknown`, not `sxUnsat`

When pruning occurs, `w.sawUnknown = true`. At the end of `runSymex`
(runtime.nim:2121-2128), the verdict resolution is:

```
if w.found.isSome:    sxSat
elif w.sawUnknown:    sxUnknown
else:                 sxUnsat
```

A pruned walk therefore produces `sxUnknown` whenever the walker did
not happen to find SAT before pruning. **This is the only sound
behavior.** A pruned-and-finished-without-SAT walk did not exhaustively
explore the path space — some pruned path might have led to SAT — so
"no SAT exists" is not a defensible verdict.

The cached result lands in the `:unk` slot, joining the existing
walker-decided UNKNOWN (Phase 11: maxLoopUnwind / maxCallDepth /
opaque calls / Z3 zsUnknown) and Z3-rlimit UNKNOWN (Phase 13). All
three sub-cases set `sawUnknown = true` and all three cache under the
same key (with different `maxFrontierSize` / `queryRLimit` values
producing distinct keys, as content-addressing demands).

### D4. UNSAT is monotone with respect to `maxFrontierSize`; the cache is over-conservative

Mathematical observation: an UNSAT verdict produced under
`maxFrontierSize = N` is also UNSAT under `maxFrontierSize = M < N`.
Fewer explored paths cannot contain SAT instances that a larger
exploration missed.

The current cache key includes `maxFrontierSize` (canonicalize.nim:339),
so a query with `maxFrontierSize = 100` will miss a cached UNSAT under
`maxFrontierSize = 200` and re-run Z3 cold. **This is over-
conservative** — sound but suboptimal. Optimizing cache lookup to
share UNSAT entries across smaller budgets is left to a future
optimization RFC.

This monotonicity does NOT extend to UNKNOWN verdicts: a cached
UNKNOWN under `maxFrontierSize = 100` could become SAT or UNSAT under
`maxFrontierSize = 200` (more exploration might find SAT or
exhaustively rule it out). Cache rotation on `maxFrontierSize` change
is correct for UNKNOWN; the over-conservatism only applies to UNSAT.

### D5. Pruning is post-fork, not pre-fork

For ADR-0003 D4 (symbolic-RHS reassignment fork) on a discriminator
with many `of` arms (e.g., 50), the fork creates 50 paths atomically
inside a single `walk(isVariantReassignSymbolic)` call. Pruning runs
**after** the walk call returns, not during. The transient peak
allocation is bounded by the SUT's arm count (parser-fixed), not by
`maxFrontierSize`.

For pathological SUTs with very many arms (e.g., `case kind: uint8`
with 100+ explicit arms), the transient allocation is the arm count;
the persistent allocation after the prune is at most
`maxFrontierSize`. This is acceptable: a 256-path transient
allocation is well within process memory; the user gets correct
behavior bounded by their configured limit.

A pre-fork guard (refuse to fork beyond `maxFrontierSize`) is
**rejected**: it would silently truncate exploration in a way that
breaks the symbolic-RHS soundness argument, since the truncated arms
might have led to SAT. Post-fork pruning preserves the "all arms
considered, some discarded" semantic.

## Consequences

### Soundness

UNSAT under frontier pruning is sound because UNSAT requires
`sawUnknown = false`, which is incompatible with any pruning. A
walker that prunes always produces UNKNOWN or SAT, never UNSAT.

### New UNKNOWN sub-case

The walker now has three documented UNKNOWN sub-cases (updated in
`determinism.md` cycle 24 of Phase 14):

1. **Walker-decided UNKNOWN** (Phase 11): maxLoopUnwind /
   maxCallDepth / opaque calls / `isUnsupported` / Z3 zsUnknown.
2. **Z3-rlimit UNKNOWN** (Phase 13): `queryRLimit` exhausted during a
   `trySolve` call.
3. **Frontier-pruned UNKNOWN** (Phase 14, new): `maxFrontierSize`
   triggered pruning during `walkBlock`.

All three set `sawUnknown = true`, all three cache under `:unk`, and
all three are subject to content-addressed key participation of their
respective settings fields.

### Cache rotation

The walker version bumps `"3" → "4"` at the end of Cluster A
(Phase 14), which covers the C3 semantic change among other walker
changes. Existing cached entries with `maxFrontierSize` participating
in the key are rotated correctly.

### Performance

For SUTs that don't use any patterns producing path explosion (i.e.,
nearly all SUTs that worked under Phase 11), the new enforcement is
a per-`walk`-call comparison against `maxFrontierSize`. The overhead
is one int comparison per stmt-walk; negligible.

For SUTs that DO produce explosion (symbolic-RHS reassignment with
many arms), the user can now set `maxFrontierSize = N` and get
bounded exploration with a deterministic prune policy and a sound
UNKNOWN verdict.

## Alternatives considered

### A1. Numeric uncertainty score for fine-grained prune ordering

Rejected for now. `Path.uncertain: bool` is the existing infrastructure;
adding a numeric score requires defining what "more uncertain" means
(path-condition complexity? Path length? Number of opaque calls
encountered?). Each definition has trade-offs and tests would be hard
to write without a clear semantic. The binary policy is simpler and
matches the existing walker model. A score-based policy is a future
refinement RFC if a real consumer demands it.

### A2. Pre-fork guard (refuse to fork beyond budget)

Rejected. Silently truncating the arm-set of a symbolic-RHS
reassignment would break the soundness argument from ADR-0003 D4 (each
arm represents a possible reassignment outcome; discarding arms
without consideration is unsound). Post-fork pruning preserves the
"all arms considered" semantic at the cost of a transient memory
spike bounded by arm count.

### A3. Remove `maxFrontierSize` from the cache key

Rejected. After C3 enforcement lands, different values of
`maxFrontierSize` can produce different UNKNOWN verdicts (a smaller
frontier triggers pruning where a larger one doesn't). The key must
participate in cache identity.

### A4. Use a stochastic prune policy (random with seed)

Rejected. Determinism is a Phase 13 contract (verdict cache requires
identical inputs → identical outputs). Stochastic pruning would break
content-addressed caching unless the seed is included in the key,
which is brittle. Deterministic stable-sort pruning is the right call.
