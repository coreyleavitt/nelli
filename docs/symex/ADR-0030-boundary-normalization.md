# ADR-0030 — Boundary normalization: the walker's input language is defined by what the boundary emits, not what the compiler can produce

| | |
|---|---|
| **Status** | Accepted — D1, D2, D3 all landed |
| **Date** | 2026-08-13 (D1/D2); 2026-08-14 (D3) |
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

### D2. Operand ANF scope: one chokepoint, two structural exclusions, one carve-out

**The chokepoint.** `parseAtomicOperand(n, preamble, ctx): IRExpr`
(`dsl_parser.nim:1204`) is the only way `dsl_parser.nim` obtains an operand
for a non-short-circuit binary/comparison/unary operation. It parses `n` via
`parseExpr`; if the result is already atomic (`isAtomicIR` — literal,
`iekVar`, or an existing temp), it returns that result unchanged; otherwise
it binds a fresh `let` into `preamble` and returns a `mkVar` reference, so
`lower`/`lowerBool` never see a compound expression tree in operand
position, only atoms. A2a (commit `2982597`) routed 13 call sites across 8
atomized families through it — string-concat (`&`), the `{.borrow.}`
intercept, nil-compare (the non-nil side), the general infix `else`
(comparisons/arithmetic/`shl`/`shr`/`xor`), unary `not` (non-boolean-infix
operand), unary minus, `pred`/`succ`, and the rune-compare intercept. A2b
(commit `d128dc0`) added a 9th family — bitwise `and`/`or` — bringing the
total to 15 call sites; see below. The permanent regression audit
(`tests/tsymex_phase15_A2a_chokepoint_audit.nim`) pins this exact site and
family inventory, scanning for the marker-comment convention
(`## A2a chokepoint (<family>)` / `## A2b chokepoint (<family>)`) N2's
kind-audit test established, so a future edit that reverts one site to a
bare `parseExpr` fails loudly rather than silently reopening the shape
sensitivity this ADR exists to close.

**The short-circuit exclusion predicate (constraint 1).** Nim spells the
BOOLEAN and BITWISE forms of `and`/`or` with the identical identifiers —
only the surface-node's classified type disambiguates them
(`isBooleanShortCircuitInfix`, `dsl_parser.nim:1192`: `nnkInfix` with
operator `and`/`or` AND `classifyType(n).ty.kind == itBool`). Two sites must
never atomize a boolean short-circuit operand: `not`'s prefix arm (a boolean
`and`/`or` operand under `not` stays on plain `parseExpr` — eagerly hoisting
it would evaluate the RHS unconditionally, the exact violation D1c exists to
prevent) and the bitwise/boolean `and`/`or` split itself (below).

**A2b typedness finding.** The naive disambiguator used elsewhere in this
file (`n.typeKind == ntyNone`) is UNSOUND specifically for `and`/`or`:
probed empirically (`scratchpad/probe_typekind.nim`/`probe_typekind2.nim`),
the compiler treats these as magic boolean control-flow operators and
assigns even a genuinely-untyped `and`/`or` node a bogus non-`ntyNone`
`typeKind` (observed `ntyCString`), so that check would let an untyped node
reach `classifyType(n)` and hard-error — reproducing issue #156 rather than
avoiding it. The reliable signal A2b settled on is the operator node's own
kind: `n[0].kind == nnkSym` (`dsl_parser.nim:1602`) holds only on the
production, typed-macro path, where overload resolution has bound `and`/`or`
to a concrete proc symbol; the untyped isolation entry point (below) leaves
`n[0]` a bare, unresolved `nnkIdent`. A2b restructures the block to evaluate
this boolean-vs-bitwise decision FIRST — pre-A2b, both operands were parsed
once, shared, before the `itBool` branch, so there was no bitwise-only parse
to reroute without also touching the short-circuit path — then branches into
two genuinely separate parses: bitwise `and`/`or` atomizes both operands
unconditionally into the outer preamble (Nim's bitwise `and`/`or` has no
short-circuit semantics, so no guard could ever apply); boolean `and`/`or`
(itBool, or untyped) keeps D1c's fast/guarded machinery verbatim, gated on
`rhsPreamble.len == 0 and not rhsHasInlineDefectFork(rhsIR)`. Branch
exclusivity then makes cross-branch leakage — a bitwise operand reaching
D1c's guard code, or a boolean operand reaching `parseAtomicOperand` —
structurally impossible rather than a case-by-case invariant to re-verify.

**Defect-fork ordering (constraints 2+3).** Hold by construction, not by a
separate ordering pass: `n`'s own inline defect-fork deposits happen inside
the `parseExpr` call `parseAtomicOperand` wraps, landing in `preamble`
*before* the proc's own hoisted `let` (if any) is appended right after — so
a caller that parses operands in Nim's left-to-right order via successive
`parseAtomicOperand` calls never reorders a fault relative to the op it
guards, and multi-fault expressions still raise the same defect first.

**The guard-cond carve-out (constraint 4, RFC §Resolved forks F3).**
`parseAtomicOperand` no-ops (returns the plain `parseExpr` result, no hoist)
whenever `ctx.inGuardCond` is set — the flag both `nnkWhileStmt` arms feeding
`mkShortCircuitWhile` set before parsing a `while` guard condition. The
guard machinery routes the Case-1b/4 fast paths vs. the R14 sound-degrade on
preamble EMPTINESS; a guard temp must re-run every iteration, and with
`continue` present there is no safe refresh, so unconditionally hoisting
would flip previously-proving `continue`-bearing loops into a spurious
`sxUnknown` — over-degrading, not hardening. **Issue #155 residue (as-built,
pinned by A1, unaffected by this carve-out):** independently of Cluster A,
semcheck already wraps some compound guards in
`nnkStmtListExpr(Empty, ...)`, whose existing CR-1b handling emits one no-op
preamble statement — so "compound fault-free guard + `continue`" was already
in the R14 Case-3 sound-degrade at HEAD, before any Cluster A code ran. The
carve-out does not fix that pre-existing residue; it only stops the
chokepoint from *widening* the degrading class to every compound guard.

**The untyped-isolation carve-out.** `parseAtomicOperand` also no-ops when
`n` carries no semchecked type (`n.typeKind == ntyNone`): hoisting needs
`classifyType(n)` to declare the fresh `let`'s `IRType`, and
`classifyType`/`getTypeInst` hard-error at compile time on an untyped node —
the same pre-check idiom this file already used before every other
`classifyType` call on a not-necessarily-typed node. This is load-bearing,
not merely defensive: `dsl_parser.nim`'s own isolation entry point
(`parseExpr(n: NimNode): IRExpr`, no `preamble`/`ctx` params, ADR-0002)
feeds genuinely untyped AST fixtures straight into this parser
(`tests/tsymex_phase1_dsl.nim`) and hard-errors itself if any preamble
content appears, so an untyped compound operand must stay un-atomized here,
exactly as it was pre-A2a. Every real (typed-macro) entry point
(`symexTarget`/`symexAssert`/`symexFind`/…) always supplies fully-typed
nodes, so this carve-out never fires on the production path the chokepoint
exists for.

**Cache-key blast radius (consumer-facing; RFC §Cache-key honesty).**
`canonicalize.nim` renders locals as positional slots, and inserting an
`isLet` for a hoisted operand renumbers every subsequent local — so the
canonical form, and therefore the content-addressed cache key, changes for
**every program with a compound operand of an atomized family anywhere**,
not only the shapes that previously mis-lowered. `symexWalkerVersion` bumped
71→72 at A2a and 72→73 at A2b (`tsymex_phase15_CR2_cachekey.nim`'s `==` pin
updated both times). Expect broad, one-time witness/verdict cache staleness
on upgrade to walker 73 — the verdicts and witnesses themselves are
unchanged, only their cache keys rotate. See the README's symbolic-execution
section ("Upgrading") for the consumer-facing form of this note.

### D3. Canonical routine shape + generic-param descriptor

**Canonical routine shape (C1, commit `<this slice>`).** `resolveRoutineImpl`
(D1's nil-core) now re-trees an accepted `nnkFuncDef` impl to `nnkProcDef`
before returning it — confined entirely to that one proc's body, per the
RFC's confinement invariant: every resolution site reads `impl` by fixed
child index after N2's migration removed every other `impl.kind` branch in
the file, so nothing downstream needed to change. The vocabulary
(`walkableRoutineKinds`) is unchanged — `func` is still accepted wherever
`proc` is — but every consumer past the boundary now sees ONE routine kind
by construction, not two.

The re-tree is mechanical, not reconstructive: `newTree(nnkProcDef, kids)`
over the SAME child `NimNode` objects the original impl held (no deep copy,
no per-field rebuild), with line info copied from the original. This is
sound only because `func` and `proc` are shape-identical at the AST level —
not folklore, evidence-obligated and probe-verified
(`scratchpad/probe_c1_dumptree2.nim`, `probe_c1_dumptree3.nim`,
`probe_c1_retree.nim`, 2026-08-14): across three body shapes (bare-expression
implicit-result, multi-statement with explicit `return`, `void`/`discard`),
a `func` and its `proc` twin have the SAME child count and the SAME
per-index child KIND at every position, differing only in whether index 4
(pragmas) is populated — because `func` compiles through the identical
routine-node constructor as `proc` in the Nim compiler; there is no real
compiler output where the two diverge in shape. A defensive arity floor
(`routineImplMinArity = 7`, the fixed `RoutineNodes` layout's floor observed
across every shape probed) guards the re-tree per the RFC's totality
clause: below that floor, `resolveRoutineImpl` returns `nil` — the SAME
degrade every other rejection path here already takes — rather than
re-treeing and returning something malformed. This branch is unreachable
for real compiler output for the reason above; no negative test is
constructible without hand-building a synthetic `NimNode`, which is outside
this proc's contract (real compiler output only).

**Cache-key evidence (RFC §Resolved forks F2).** The premise a naive re-tree
plan would risk — "changing the local impl tree changes the cache key for a
`func` callee" — is empirically false: `bodyHashPart` keys off
`symBodyHash(calleeSym)`, a compiler-computed hash over the SYMBOL
(signature + module + body), never over the local `impl` NimNode the
re-tree rewrites. Verified directly, not inferred: `symexCacheKeyForFn`
dumped for a func callee (interprocedural registration path) and a func
direct target (`resolveEntryImpl` path), before and after the re-tree, in
the same working tree (`scratchpad/probe_c1_cachekey.nim`) —

| | before | after |
|---|---|---|
| func callee | `sx:987F96499E0A96FDD8D1D1D23E2D0E4FEB6828E0` | `sx:987F96499E0A96FDD8D1D1D23E2D0E4FEB6828E0` |
| func direct target | `sx:2995095F49640C6841AA5153575B9CDE178BEABC` | `sx:2995095F49640C6841AA5153575B9CDE178BEABC` |

— byte-identical in both cases. C1 is therefore a **behavior-identical,
no-bump** slice: `symexWalkerVersion` stays 73, and the canonical
`tsymex_phase15_CR2_cachekey.nim` `==` pin is unchanged.

**Generic-param descriptor threading (C2, commit `428d99c`, landed before
this D3 write-up).** `resolveGenericDescriptor` (introduced in N1) is now
the SOLE site holding both the `impl[2]`-vs-`impl[5][1]` dual-location
lookup and the `nnkIdentDefs` walk that derives each generic param's name,
`isStatic` flag, and constraint expression. All four probe sites the RFC's
round-1 audit found now consume the resulting `GenericDescriptor` instead of
re-deriving it: `hasGenericParams`/`genericParamsNode` (rebased in N1), and
`gatherTypeSubst` plus `parseCalleeImpl`'s `captureConstraints` (migrated in
C2) — the round-2 audit additionally caught a THIRD undercounted
identDefs re-walk in `staticParamNames`, also migrated. `instKeyFor` is
descriptor-backed transitively through these. Behavior-identical — no
verdict or key drift on the existing corpus — so C2 needed no version
bump either.

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

### Intended (D2)

- The walker's `lower`/`lowerBool` arms see only atomic operands at every
  atomized family — the shape sensitivity that let a let-hoisted twin prove
  where the inline form degraded is closed by construction, not by a
  per-shape rescue.
- Hoisted and inline forms are provably interchangeable: the A1
  characterization corpus (8 context files, informative cells only) asserts
  twin equality of verdict AND witness, plus no new degrade vs. the HEAD
  baseline, for every atomized family across both A2a and A2b.
- Existing consumer-side defensive let-hoists (written before this ADR, to
  work around the shape sensitivity) remain correct and become
  unnecessary — droppable at the consumer's convenience, never required to
  drop. See the README's symbolic-execution section.
- The chokepoint is a single audited proc, not per-arm discipline: the
  permanent chokepoint audit test fails loudly if a future edit reverts any
  of the 15 call sites to a bare `parseExpr`, the same institutionalization
  pattern N2 established for the kind vocabulary.

### Accepted as cost (D2)

- One-time cache-key blast radius: every program with a compound operand of
  an atomized family gets a new canonical form and therefore a new content
  hash on upgrade to walker 73, even though its verdict is unchanged —
  broad witness/verdict cache staleness the first time a consumer runs
  against the new walker version. See "Cache-key blast radius" above and the
  README's "Upgrading" note.
- Issue #155 (compound fault-free guard + `continue` degrading via the
  pre-existing `nnkStmtListExpr` no-op-preamble artifact) is pinned as
  known, as-built behavior, not fixed by this ADR — the guard-cond carve-out
  only prevents Cluster A from widening that class.

### Intended (D3)

- Every consumer past `resolveRoutineImpl` sees exactly one routine kind —
  `nnkProcDef` — by construction. A hypothetical future consumer written
  without knowledge of `nnkFuncDef`'s existence cannot silently
  misclassify a `func`: there is nothing past the boundary left to widen.
- The re-tree is confined to one proc's body, provably (`git diff --stat`
  at C1's landing touches only `resolveRoutineImpl` in `dsl_parser.nim`,
  plus tests/docs) — the confinement claim D1's own write-up predicted
  ("a future re-treeing... has exactly one body to change") holds exactly
  as designed.
- The generic-param dual-location lookup and its `nnkIdentDefs` walk each
  exist in exactly one place (`resolveGenericDescriptor`); all four
  consumer sites the RFC's round-1 AND round-2 audits found (including the
  undercounted third `staticParamNames` re-walk) now read the parsed
  descriptor instead of re-deriving it.

### Accepted as cost (D3)

- None identified. Both the routine-shape re-tree and the
  `GenericDescriptor` threading are behavior-identical consolidations,
  proven by no-drift on the existing corpus (twin-equality characterization
  for C1: `tests/tsymex_phase15_C1_canonical_kind.nim`; audit-extension
  RED→GREEN for C2) rather than by argument.

### Deferred

| Topic | Future home |
|---|---|
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

D2 is validated by three layers, all green on both backends at the Cluster A
acceptance run (walker 73): the 8-file A1 characterization corpus
(`tests/tsymex_phase15_A1_{bitwise,comparison,arithmetic,boolean,loopguard,
unary,callarg,assertarg}.nim`) proving twin equality of verdict and witness
plus no baseline regression across atomic, inline-compound, call-result, and
nested-mixed operand shapes — including the chronos-faithful `slotIndex`/
`capMask` depth-2 cells (`tsymex_phase15_A1_bitwise.nim` cell 6), the in-repo
floor for the CallbackQueue harness pending its external durability (RFC
§Open items); `tsymex_phase15_A2a_atomize.nim` and
`tsymex_phase15_A2b_bitwise.nim` demonstrating the post-atomization and
post-restructure invariance directly against the bypass-site classes
(borrow, rune-compare, nested pow2-mask) with the D1c fast/guarded-path
decision pins; and the permanent `tests/tsymex_phase15_A2a_chokepoint_audit.nim`
regression audit (15 call sites across 9 families, both documented
exclusions, `symexWalkerVersion >= 73`).

`isAtomicIR`'s own membership (`dsl_parser.nim` ~:1200-1253) is a fourth,
narrower validation layer within D2: unlike the chokepoint-site inventory
above, its allowlist grew twice by empirical accretion (`iekStrAt` for
CR-17(a)'s `s[i]`-ordering guard; `iekStrLen`/`iekSeqLen` for D1c's
`rhsPreamble.len == 0` fast-path pollution) with no completeness audit
either time — a gap code review round 1 finding H1 (#146) named and a
verifier confirmed concrete: `rhsHasInlineDefectFork` clears `iekField`,
`iekIndex`, and `iekContains` for bare-var/literal receivers by the same
zero-fault-compound-shape reasoning, yet `isAtomicIR` admits none of the
three, so each is hoisted (manufacturing a `rhsPreamble` entry, flipping
D1c's fast path) whenever it sits as a comparison operand under a boolean
`and`/`or` RHS. This is now closed by
`tests/tsymex_phase15_A2a_atomicir_audit.nim`: a characterization corpus
(twin verdict/witness equality for all three kinds, confirming the hazard
is latent-but-benign at HEAD) plus a permanent `staticRead`-based scan of
`runtime.nim`/`runtime_strings.nim` requiring every subfield IR-kind
shape-peek to sit in `isAtomicIR`'s allowlist, the always-atomic
literal/var set, or a documented exemption — RED-probed against an
injected non-allowlisted shape-peek to confirm the scanner actually fires,
then reverted clean. `isAtomicIR`'s widened membership is coupled to
walk-time shape-matches by construction (D2's whole premise), so this
audit is what keeps that coupling honest going forward, the same
institutionalization pattern N2 established for the routine-kind
vocabulary and A2a established for the chokepoint-site inventory.

D3 is validated by `tests/tsymex_phase15_C1_canonical_kind.nim`: five
func-vs-proc twin categories (borrow op, proc-as-value capture,
string-param disambiguation, generic monomorphization, plain
interprocedural call) each proving verdict AND witness equality between
spellings, plus a well-formed/non-colliding cache-key check per pair via
`symexCacheKeyForFn`; a `symexWalkerVersion >= "73"` floor pin (no bump).
The file is green both against the pre-retree tree and the post-retree
tree (run both ways at C1's landing) — the confinement/invisibility claim
made machine-checkable, not merely argued. C2's threading is covered by
its own audit extension in `tests/tsymex_phase15_N2_kindgate_audit.nim`
(the `nnkGenericParams`-scan pattern, RED before C2, GREEN after).
