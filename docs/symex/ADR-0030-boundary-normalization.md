# ADR-0030 — Boundary normalization: the walker's input language is defined by what the boundary emits, not what the compiler can produce

| | |
|---|---|
| **Status** | Partial — D1 Accepted; D2, D3 reserved (land with A2a, C1/C2) |
| **Date** | 2026-08-13 |
| **Deciders** | nelli maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [RFC-parser-normalization.md](../RFC-parser-normalization.md) (#146), [RFC-parser-normalization.handoff.md](../RFC-parser-normalization.handoff.md), [ADR-0008](ADR-0008-generic-instantiation.md) (generic instantiation — D3 threads its `GenericDescriptor` consumers), [ADR-0009](ADR-0009-closure-encoding.md) (closure encoding — shares the amendment-in-place pattern this ADR follows) |

## Context

The symex parser (`nelli/smt/dsl_parser.nim`) consumes Nim's typed surface
AST directly, so its effective input language is every shape the compiler
can emit for the same *meaning*. Each shape variant a consumer site does not
anticipate is a latent crash, hard error, or silent misclassification. Two
independent failure classes surfaced against shipped 0.3.4 from one external
harness (the chronos `CallbackQueue` proofs): routine-kind multiplicity
(`func` lowering to `nnkFuncDef` where sites expected only `nnkProcDef`) and
operand-shape sensitivity (compound operands mis-lowering where a
let-hoisted twin proves). RFC-parser-normalization (#146) generalizes the
parser's existing per-arm rescue technique (R1's `isDeref` rewrite, this
ADR's sibling ADR-0010's heap model) into a **boundary guarantee**: the
walker should see one small, normalized language, not the compiler's full
output space.

This ADR is the durable record of that guarantee's design, authored in
lettered sub-decisions matching the amendment-in-place pattern ADR-0008 and
ADR-0009 already establish (each sub-decision lands with the RFC slice that
implements it, not all at once). **D1** lands with slice N1 (this commit).
**D2** and **D3** are reserved stubs — their headings exist so later slices
amend this file in place rather than opening a parallel document — and are
filled in when A2a (D2) and C1/C2 (D3) land.

## Decisions

### D1. Kind vocabulary + resolution policy map: one nil-core, three policy wrappers

**The nil-core.** `walkableRoutineKinds* = {nnkProcDef, nnkFuncDef}`
(`dsl_parser.nim`) is the routine-kind vocabulary the walker's boundary
accepts — defined exactly once. `resolveRoutineImpl*(sym: NimNode): NimNode`
is the shared nil-core: `sym.getImpl`, returning the impl node when its kind
is in `walkableRoutineKinds`, `nil` otherwise. **It never raises, never
degrades, and carries no policy of its own.**

**Invariant-3 (load-bearing, survives every consolidation in this cluster):**
the per-site failure policies that consume this core are deliberate and
distinct, and consolidating the *predicate* must never collapse them into
one merged *behavior*:

| Policy | Consumer class | Example sites |
|---|---|---|
| **Hard-error** | Public API entry macros — a non-routine `fn` argument is a caller mistake, reported at macro-expansion time | `resolveEntryImpl` (N1) — wraps all 9 `symex.nim` entry macros |
| **Classified-degrade** | Internal resolution during a walk — an unresolvable callee degrades the *run* to `sxUnknown` via the v67 classified-degrade mechanism, never a crash or silent wrong answer | `ensureProcRegistered` (N2 migrates this call site onto the core) |
| **Boolean-false** | Structural/pragma predicates — "is this a borrow op / opaque / generic" questions where a non-routine node simply means "no" | `hasBorrowPragma`, `hasGenericParams`, `isStdMathProc`, and peers (N2 migrates these) |

N1 ships exactly one policy wrapper concretely — `resolveEntryImpl(fn,
apiName): NimNode`, the hard-error wrapper, `error(apiName & ": expected a
\`proc\` symbol", fn)` on a `nil` core result — and threads it (plus its
`parseProc`-composing sibling `parseEntryImpl`) through all nine
`symex.nim` entry macros: `symexForAll`, `symexFind`, `assertCoveredBy`,
`symexCacheKeyForFn`, `saveSymexWitness`, `loadSymexWitnesses`,
`saveSymexVerdict`, `loadSymexVerdict`, `symexFindAllWitnesses`. The
classified-degrade and boolean-false wrappers already exist at their
respective call sites (`ensureProcRegistered`'s existing classified-degrade
arm; the existing boolean-returning predicates) — N2's job is migrating
*those* call sites' bare `{nnkProcDef, nnkFuncDef}` kind checks onto
`resolveRoutineImpl`, not inventing new policy shapes. No sub-decision here
changes what any site's failure policy *is* — only what all of them share
underneath.

**Error-text unification (deliberate, the one intentional behavior change
in this otherwise behavior-identical slice).** All nine hard-error macros
now share identical compile-error text. `symexForAll`'s historical
`" for \`fn\`"` suffix is dropped: it disambiguated nothing (`symexForAll`
has exactly one `typed` parameter; `assertCoveredBy`, which has two, never
carried a suffix), and no test or downstream harness depends on the exact
compile-error string — negative coverage uses the repo's `not compiles(...)`
idiom exclusively (see `tests/tsymex_phase15_N1_resolution_gates.nim`).

**Confinement consequence (sets up D3).** Because `resolveRoutineImpl` is
now a real, callable core rather than prose, a future re-treeing of accepted
routines to a single canonical shape (D3 / RFC Cluster C's C1) has exactly
one body to change.

### D2. Operand ANF scope (reserved — lands with A2a)

Will record: the atomized operand families, the short-circuit exclusion
predicate (never atomize across a `bAnd`/`bOr` boundary under `itBool`, nor
a `uNot` operand that is itself such an infix), defect-fork evaluation-order
preservation, and the `ctx.inGuardCond` loop-guard carve-out (RFC §Resolved
forks F3). See RFC §Cluster A for the mechanism this sub-decision will
transcribe once A2a lands.

### D3. Canonical routine shape + generic-param descriptor (reserved — lands with C1/C2)

Will record: the re-treeing of every accepted routine to `nnkProcDef`
canonical form inside `resolveRoutineImpl`'s body (C1, confined there by
construction once N2's migration removes every other `impl.kind` branch),
and the `GenericDescriptor` threading that replaces the generic-param
dual-location lookup's four independent probe sites with one
(`resolveGenericDescriptor`, introduced in N1 — see RFC §Cluster N N1/C2).
See RFC §Cluster C for the decisions this sub-decision will transcribe once
C1/C2 land.

## Consequences

### Intended (D1)

- One kind vocabulary, one nil-core predicate; nine entry macros share one
  hard-error wrapper instead of nine independent `getImpl` + bare-kind-gate
  + `error(...)` copies.
- Adding a hypothetical future accepted routine kind (RFC §Non-goals notes
  `iterator`/`converter`/`method` are explicitly not being added here, only
  made cheap to add) is a one-line change to `walkableRoutineKinds` plus
  tests, not a re-audit of every call site.
- Invariant-3 stays provable rather than assumed: the policy map above is
  the acceptance criterion N2's permanent audit test checks against.

### Accepted as cost (D1)

- The unified error text is a user-visible (compile-error-message) change
  for `symexForAll` callers who pass a non-routine `fn`. No test or
  documented consumer depends on the old text; this is recorded, not
  hidden.

### Deferred

| Topic | Future home |
|---|---|
| Operand ANF chokepoint (`parseAtomicOperand`) | D2, lands with A2a |
| Canonical `nnkProcDef` re-treeing | D3, lands with C1 |
| `GenericDescriptor` threading through `gatherTypeSubst`/`parseCalleeImpl` | D3, lands with C2 |
| Full migration of the remaining ~13 `dsl_parser.nim` resolution sites onto `resolveRoutineImpl` + the permanent kind-audit test | N2 (this ADR is amended, not re-opened, when N2 lands) |
| Reconciling the two divergent routine-shaped-node sets (`RoutineNodes`) | N3 |

## Validation

D1 is validated by `tests/tsymex_phase15_N1_resolution_gates.nim`:
excluded-kind rejection (`template` symbol, `let`-bound closure/lambda
variable, first-class `{.closure.}` iterator symbol) pinned via
`not compiles(...)` against both `resolveEntryImpl`- and
`parseEntryImpl`-routed macros; positive smoke proving an ordinary `proc`
AND `func` are both still accepted (behavior identical to pre-N1); a
`symexWalkerVersion >= "71"` floor pin (no bump — this slice is
behavior-identical, proven by no-drift on the existing corpus, including
`tsymex_phase15_CR2_cachekey.nim`'s canonical `== "71"` pin staying
unchanged).
