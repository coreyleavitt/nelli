# RFC — parser-boundary normalization (#146)

Retire surface-AST shape fragility in the symex parser: normalize at the
boundary so the core walker handles a small language, instead of guarding
per-arm against every shape the compiler can emit for the same meaning.

## Status

| | |
|---|---|
| **Stage** | 2 (architecture review) — **rounds 1 AND 2 applied** (round 1: 39 findings, both round-0 forks resolved; round 2: 4 lenses re-run against the round-1 material — N0 premises corrected (:1048 double gate; borrow severity), guard-cond carve-out replacing constraint 4, `resolveRoutineImpl` core made real, audit tests institutionalized — see §Resolved forks F3/F4). **Ready for stage 3.** |
| **Umbrella** | issue #146; sub-issues #147 (DONE, incompletely — see N0), #148, #149, #150 |
| **Scope** | `src/nelli/symex.nim` + `src/nelli/smt/dsl_parser.nim` boundary; one walker-input normalization pass (Cluster A); a chronos exit gate (X1). Out of scope: `coverage.nim:292` and `mutation.nim:123` routine-kind sets (§Non-goals) |
| **Handoff** | `docs/RFC-parser-normalization.handoff.md` |
| **Relation to other work** | chapulin round-6 Track A/B **parked** (Corey 2026-08-13); see §Cross-RFC handoff. #138 stays separate; benefits from Cluster N. |
| **Open items** | 1 — chronos harness durability (external-repo action, §Open items) |

## §0 — Thesis

The parser consumes Nim's typed surface AST directly, so its effective input
language is every shape the compiler can emit for the same meaning. Each shape
variant a consumer site does not anticipate is a latent crash, hard error, or
silent misclassification. Two independent failure classes surfaced from one
external harness (the chronos CallbackQueue proofs) against shipped 0.3.4:
routine-kind multiplicity (`func` → `nnkFuncDef`) and operand-shape
sensitivity (compound operands mis-lowering where the let-hoisted twin
proves).

The parser already A-normalizes where a specific arm needed rescue (R1's
`isDeref` rewrite, ADR-0010). This RFC makes the technique a **boundary
guarantee**: one routine-kind vocabulary defined once (Cluster N), operands
atomized through one chokepoint (Cluster A), one canonical routine shape and
one generic-param location by construction (Cluster C).

**Invariant-3 constraint (load-bearing, survives every consolidation):** the
per-site failure policies are deliberate and distinct — API entry macros
hard-error, `ensureProcRegistered` does the v67 classified degrade to
`sxUnknown`, pragma/generics predicates return false. Consolidation means one
*predicate* with per-policy wrappers, never one merged *behavior*.

## Ground truth at HEAD (799b0bc, walker v70) — probed + audited 2026-08-13, round 1 verified

Probes: `scratchpad/probe_146_anf.nim`, `probe_146_anf2.nim` via
`scripts/dt-bounded.sh`, **both backends**; site audit via bare-kind grep;
archaeology via git history.

1. **#147 is landed but INCOMPLETE.** `799b0bc` widened 19 sites, but a
   grep-based audit (round 1) found **three live unwidened sites** in
   `dsl_parser.nim`, all Invariant-3-class:
   - `borrowInfoFor` (**:855**): bare `impl.kind != nnkProcDef` in front of
     the already-widened `hasBorrowPragma` → a `func` borrow operator
     classifies `isBorrow: false` and falls to the ORDINARY infix path.
     **Round-2 severity correction:** the fallthrough is verdict/witness-
     INERT at HEAD — the ordinary arithmetic/comparison arms eject both
     operands unconditionally (`runtime.nim:3476/:3396`), computing the
     same base result; the only delta is the skipped `reboxDistinct`,
     whose minted distinct const is never constrained and never read
     (`ejectBase` and witness extraction both read `distinctBaseSym`). A
     type-tag loss and a latent hazard, not a wrong verdict. Untested
     either way: `tsymex_phase15_g5_distinct_borrow.nim` uses only `proc`
     borrows.
   - C3 proc-as-value (**:1048 + :1050**): round-2 correction — the gate
     that actually excludes a `func`-valued capture (`let g = someFunc`)
     is `symKind(n) == nskProc` at :1048 (`func` symbols are `nskFunc`, a
     distinct symbol kind); the `impl.kind == nnkProcDef` check at :1050
     is unreachable for `func` until :1048 widens. Pre-fix observable
     (traced): the capture falls to bare `mkVar` → env `KeyError` at walk
     time → the outermost classified net → `sxUnknown` with
     `weInternalWalkerFault` (the v69 sibling-bug mechanism, :1022–1032)
     — a classified degrade, not a crash and not a silent SAT.
     Symbol-KIND (`nsk*`) gates are a second bare-kind inventory class
     the round-1 node-kind grep never covered (repo census: exactly this
     one site).
   - G8 string-op disambiguation (**:2083**): `getImpl.kind == nnkProcDef` —
     a user `func` with a string-typed first param misclassifies as
     `seUnsupportedStringOp` (false degrade).
   Lesson institutionalized: site inventories are **found by grep, never by
   list** (the same rule the chapulin RFC already applies to version pins).
2. **The #149 crash is root-caused and already fixed — at v64, before this
   RFC.** Commit `a0bfeff` (walker v64, 2026-08-06) both contains the era of
   the cited raw assert AND fixes the cause: "the D1c short-circuit lift
   fired for BITWISE and/or (same Nim identifiers as the boolean forms),
   binding a BV LHS into a tBool temp and crashing … now gated on the infix
   classifying itBool." That is exactly the `(cap and (cap - 1)) == 0` shape.
   Confirmation at HEAD: the issue's verbatim reproducer and chronos-faithful
   depth-2 shapes all prove clean `sxUnsat`, both backends, zero degrade
   records. `lowerBool` itself degrades in-band since v64 (classified
   `weInternalWalkerFault`, never a native crash). **Cluster A's motivation
   is therefore the shape-invariance guarantee and the reachable degrade
   class** (the v64 arm exists because it was hit; abstraction can
   BV-allocate under `bAnd`/`bOr` — the `toZ3Int` hazard), **not a live
   crash.** See §Resolved forks F1.
3. **C1's assumed cache-key risk is likely nil.** `bodyHashPart`
   (`dsl_parser.nim:4717`) keys off `symBodyHash(calleeSym)` — a compiler
   magic computed from the *symbol* (signature + module + body), not from the
   local `impl` tree a re-tree would rewrite; the fallback path uses
   filename + name, also kind-blind. See §Resolved forks F2.
4. **The Q1 scan recognizer is safe from Cluster A by construction.**
   `tryRecognizeScanIdiom` (`dsl_parser.nim:2850`) matches the **raw
   `nnkWhileStmt` NimNode before any `parseExpr`** on its children; A2 hoists
   at IR emission and never rewrites the surface tree. A1 pins this with a
   regression test anyway (belt for the R1b/R14-class interaction history).
5. **Fork deposits and guard routing (round 2 — load-bearing for Cluster
   A's shape).** Inline defect forks already deposit into `preamble`
   during `parseExpr` (D1c exists because of it — :1266–1275), so operand
   hoisting changes WHERE the value binds, not whether forks fire. And
   the while-guard machinery (`mkShortCircuitWhile`, :3144–3200) routes
   on preamble EMPTINESS: the Case-1b/4 fast paths require a pristine
   parse; non-empty preamble + `continue` in the body = the R14
   sound-degrade. Any normalization that manufactures guard-cond
   preambles regresses continue-bearing loops that prove today — hence
   Mechanism constraint 4's carve-out. (A1 as-built addendum: semcheck's
   `nnkStmtListExpr` artifact ALREADY manufactures a no-op preamble for
   some compound guards, which therefore degrade with `continue` at HEAD
   — pre-existing residue, issue #155; the carve-out still prevents the
   class from widening to ALL compound guards.)

## Cluster N — routine-impl resolution consolidation (#148, + completing #147)

### Slices

- **N0 — complete the widening (kind-gate fixes + pins).** Three sites,
  two test framings (round-2 corrected — the round-1 "RED test each" was
  wrong for the borrow site):
  - `borrowInfoFor` (:855): one-line widen. Test is a **characterization
    pin**, not a promised RED — the fallthrough is verdict/witness-inert
    at HEAD (§Ground truth 1), so the test pins `proc`-vs-`func` borrow
    twin equality (verdict AND witness; arithmetic + comparison borrows)
    and goes RED only if a rebox-sensitive divergence exists after all.
  - C3 proc-as-value: widen **BOTH** gates — `symKind(n) in {nskProc,
    nskFunc}` at :1048 AND `impl.kind` at :1050 (widening :1050 alone is
    a no-op — :1048 excludes `func` first). RED test: a `func`-as-value
    capture asserts pre-fix `sxUnknown` carrying
    `weInternalWalkerFault`, post-fix the real verdict.
  - G8 (:2083): widen the positive match. RED test: user `func` with a
    string first param asserts pre-fix the `seUnsupportedStringOp` false
    degrade, post-fix the real verdict.
  Audit: full-repo grep for BOTH bare-kind classes — node kinds
  (`nnkProcDef` comparisons/membership) AND symbol kinds
  (`nskProc`/`nskFunc` gates; census today: only :1048) — recorded in the
  test header (residue: `coverage.nim:292`, `mutation.nim:123`, §Non-
  goals). **Explicit line items (not inherited from the DoD section):**
  update the `tsymex_phase15_CR2_cachekey` `==` pin in this slice (first
  SW bump of this RFC — the known D1c-era miss pattern); promote
  `psweep.sh` from gitignored `scratchpad/` into tracked `scripts/` (it
  is DoD tooling for every SW slice; a fresh checkout must have it).
  **Ver: SW** (verdict changes for previously-degraded `func` programs).
  Size S–M.
- **N1 — resolution helpers + `symex.nim` migration.**
  - `const walkableRoutineKinds* = {nnkProcDef, nnkFuncDef}` — exported from
    `smt/dsl_parser.nim`.
  - `resolveRoutineImpl(sym): NimNode` — **THE shared nil-core (round-2
    addition; C1's prose previously referenced this function as if it
    existed — it did not, anywhere):** `getImpl` + `kind in
    walkableRoutineKinds` → the impl node, else nil. This is the literal
    "one predicate" of the Invariant-3 constraint; every policy is a
    wrapper over it, and C1 later re-trees inside THIS body (§Cluster C).
  - `resolveEntryImpl(fn, apiName): NimNode` — the hard-error policy
    wrapper: `resolveRoutineImpl` + `error(apiName & ": expected a
    \`proc\` symbol", fn)` on nil. Named to avoid the codebase's
    load-bearing `target`/`SymexTarget` vocabulary. **Error text UNIFIED
    (round-2 decision, §Resolved forks F4):** all 9 macros get the
    identical base text; `symexForAll`'s historical `" for \`fn\`"`
    suffix is dropped — it disambiguates nothing (`symexForAll` has one
    typed param; `assertCoveredBy`, which has two, never used a suffix)
    and no test or harness depends on compile-error text. The itemized
    9-site inventory documents the deliberate change; automated negative
    tests use the repo's `not compiles(...)` idiom only.
  - `parseEntryImpl(fn, apiName, maxInst): ParseResult =
    parseProc(resolveEntryImpl(fn, apiName), maxInst)` — renamed from
    round 1's `parseEntryTarget`, which reintroduced the exact "Target"
    collision `resolveEntryImpl` was renamed to avoid; the family is now
    resolve\*→NimNode / parse\*→IR with no "Target" noun. Collapses the
    **three-step** ritual (getImpl → gate → parseProc) duplicated across
    SIX macros (`symexCacheKeyForFn`, `saveSymexWitness`,
    `loadSymexWitnesses`, `saveSymexVerdict`, `loadSymexVerdict`,
    `symexFindAllWitnesses`). Round-2 precision: the fourth step
    (destructure into `paramsExpr`/`bodyExpr`/`procsExpr` +
    `rebuildTargetNode`) is shared by only FIVE of the six —
    `symexFindAllWitnesses` consumes `parsed` directly — so destructuring
    stays per-consumer; do not fold it in. (Implementation-time check:
    `quote do` backtick interpolation may accept `parsed.paramsNimNode`
    directly, eliminating the destructure locals — verify by compiling,
    not assumed here.) `symexFind`/`assertCoveredBy` use
    `resolveEntryImpl` + their own `.params` consumption (different
    downstream shape); `symexForAll` uses bare `resolveEntryImpl` and
    **deliberately never parses** (it defers to `symexFindAllWitnesses`'s
    expansion — document this so nobody "fixes" it into a double parse).
  - `GenericDescriptor` — designed HERE (the end-state interface), plumbed
    fully in C2. **Round-2 deepening: fully-parsed data, not a raw
    node** — `GenericParam = tuple[name: string, isStatic: bool,
    constraint: NimNode]`; `GenericDescriptor` carries `params*:
    seq[GenericParam]` (empty if non-generic), produced by one
    `resolveGenericDescriptor(impl)` holding BOTH the
    `impl[2]`-vs-`impl[5][1]` dual-location trick AND the single
    `nnkIdentDefs` walk. Rationale: round 2 traced the four consumers —
    `gatherTypeSubst` (:4636) and `parseCalleeImpl` (:4897) each re-walk
    the identDefs structure (names resp. constraints); a raw-node
    descriptor would collapse only the location lookup and leave that
    walk duplicated twice post-C2 (the same shape of problem N3 fixes
    for kind sets). `hasGenericParams` becomes `params.len > 0`;
    `staticParamNames` becomes a filter; `constraint` stays a raw node
    (arbitrary type expression — only the identDefs walk stops being
    repeated). N1 ships type + resolver and rebases
    `hasGenericParams`/`genericParamsNode`; C2 threads the rest.
  - Negative tests: each policy's failure mode pinned on a non-routine
    symbol (`template` sym, `let`-bound closure var, and an `iterator` sym —
    excluded-kind behavior is an explicit acceptance criterion, not an
    assumption).
  Behavior-identical ⇒ **no SW bump**, proven by no-drift on the existing
  corpus. Size M. Depends: N0.
- **N2 — `dsl_parser.nim` migration.** Route all RESOLUTION sites through
  `resolveRoutineImpl` + their policy wrappers — the original 10 (incl.
  `isStdMathProc:965`, previously uninventoried; policy bucket:
  boolean-false) plus N0's three; membership-only checks on
  already-obtained nodes use `walkableRoutineKinds` directly. Acceptance
  is a **permanent audit test, not a one-time grep** (round-2
  institutionalization — the TOT-1 corpus header states the rationale
  verbatim: a slice-close audit catches no future regression): a
  committed test `staticRead`s the sources and asserts zero inline
  `{nnkProcDef, nnkFuncDef}` membership literals, zero bare
  `impl.kind ==/!= nnkProcDef` comparisons, and zero `nskProc`/`nskFunc`
  gates in `src/nelli/` outside the const/core definitions and the
  documented §Non-goals exclusions (pure-Nim string scan — portable, no
  shell dependency). Behavior-identical ⇒ **no SW bump**. Size S–M.
  Depends: N1.
- **N3 — routine-shaped-node set reconciliation.** The interior spells TWO
  divergent wider "routine-shaped node" sets, both copy-pasted and mutually
  inconsistent (round-1 verified):
  - 7-elem `{…, nnkIteratorDef, nnkMethodDef, nnkConverterDef,
    nnkTemplateDef, nnkMacroDef}` (no `nnkLambda`) at **1682/2285/4136**
    (closure-call detection);
  - 6-elem `{…, nnkIteratorDef, nnkLambda, nnkTemplateDef, nnkMacroDef}`
    (no method/converter) at **2733/2747/2762/2791** (scope-boundary for the
    `hasYieldShallow`/`hasReturnShallow`/`hasKindShallow`/
    `substIteratorParams` scanners).
  Neither matches `std/macros.RoutineNodes` (both omit `nnkDo`). The
  divergence is a latent misclassification: a `method`/`converter` nested in
  a scanned body does NOT stop the 6-elem scanners' descent. Collapse both
  into named, audited consts defined against `macros.RoutineNodes` (each
  deliberate exclusion commented); fix or explicitly accept the
  scope-boundary gap. Acceptance grep: zero inline routine-kind-set literals
  of length > 2 outside the shared consts. **Ver: SW if the audit changes
  any verdict, else —.** Size S–M. Depends: N2.

**Cluster acceptance:** one definition of each kind vocabulary; one
nil-core (`resolveRoutineImpl`) under every policy wrapper; the nine
entry macros share one resolver; six share `parseEntryImpl`; adding a
hypothetical next kind is a one-line change plus tests; suites green.

## Cluster A — operand ANF before SMT lowering (#149)

Atomize compound operands of non-short-circuit operations so
`lower`/`lowerBool` only ever see atomic operands. Post-round-1 this is a
**refactor-with-characterization-net** (the crash is fixed — §Ground truth
2): A1's corpus is the safety net, A2 is the structural guarantee, and A2's
acceptance is invariance (net stays 100% green; new demonstration shapes
prove where none proved before or degrade where they crashed), NOT a
RED→GREEN transition.

**Mechanism (round-1 chokepoint; round-2 hardened):** the naive plan
("hoist in the general infix arm") reproduces the per-arm-rescue pattern §0
exists to kill — EIGHT operand-construction sites consume raw `parseExpr`
operands and would bypass it (round-2 census; round 1 found six and
mislabeled two constructors): `&` string-concat (~1179 — constructs
`mkStrOp`, NOT `mkBinop`), the `{.borrow.}` intercept (~1192 — constructs
`mkBorrowOp`; a compound operand of a borrowed op is exactly the #149
shape class), nil-comparison (~1226), the general `bAnd/bOr` path + `else`
fallthrough (~1276–1318), `pred`/`succ` arithmetic (~2263), the
rune-compare intercept (~2278), plus the two `nnkPrefix` arms round 1
missed: `not` → `mkUnop(uNot, parseExpr(...))` (:1322) and unary minus →
`mkUnop(uNeg, ...)` (:1355). The `uNot` case matters doubly: prefix `not`
carries the same boolean/bitwise overload as `and`/`or` (the v64-hardened
walker arm), so it inherits constraint 1. The acceptance target is
therefore "any IR-constructing consumption of a `parseExpr` operand
result" (`mkBinop`/`mkUnop`/`mkStrOp`/`mkBorrowOp`), not
`mkBinop`/`mkUnop` alone.

**Rejected alternatives (round-2 evaluated; recorded so they stay
rejected):** (a) a post-parse IR→IR normalization pass is structurally
impossible as scoped — `IRExpr` carries no type tag, and D1c's fast path
emits the IDENTICAL `mkBinop(bAnd, ...)` shape for boolean and bitwise
forms, so the itBool disambiguation constraint 1 requires exists ONLY on
the surface NimNode (`classifyType`, :1293); recovering it post-parse
means typing the whole IR — an unscoped rewrite. This, not taste, is the
decisive argument for a parser-side chokepoint. (b) Type-level
enforcement (`mkBinop` requiring a distinct `AtomicOperand`) punishes the
20+ pure IR-SYNTHESIS `mkBinop` sites (loop bounds, switch dispatch,
index increments) that are not part of the surface boundary; a parallel
constructor family doubles the surface for a guarantee the audit test
provides more cheaply.

```nim
proc parseAtomicOperand(n: NimNode, preamble: var seq[IRStmt],
                        ctx: ParseCtx): IRExpr =
  ## The ONLY way to obtain an operand for a non-short-circuit binary/
  ## comparison/unary op. Parses n; if not already atomic (literal/var/
  ## temp — the isDeref precedent), binds a fresh let into `preamble` and
  ## returns the reference. No-ops (plain parseExpr) when
  ## ctx.inGuardCond — see constraint 4. Boolean short-circuit and/or
  ## callers MUST NOT use this (they own D1c's guarded handling).
```

The delta is smaller than it looks: inline defect forks ALREADY deposit
into `preamble` during `parseExpr` (§Ground truth 5), so for
fault-bearing operands the chokepoint adds only the value-binding; for
pure compound operands it adds the canonical atom. That is the point —
the walker's input language shrinks — and it is why no verdict change is
expected outside the cache-key bump.

Acceptance is a **permanent audit test** (same round-2
institutionalization as N2, same `staticRead` mechanism): every
operand-construction site in `dsl_parser.nim` either consumes an operand
atomic by construction or routes through `parseAtomicOperand`; zero
bare-`parseExpr` operand consumptions at those sites outside the two
documented exclusions (boolean `bAnd`/`bOr`; guard-cond parses).

**Hard semantic constraints (each a known past failure mode):**

1. **Never atomize across a short-circuit boundary.** Checkable predicate,
   not prose: never call `parseAtomicOperand` on an operand of an `nnkInfix`
   whose `binopForInfix` result is `bAnd`/`bOr` AND whose
   `classifyType(n).ty.kind == itBool` — nor on a `uNot` operand that is
   itself such an infix (round-2 extension: eagerly hoisting `a and b`
   under `not` deposits the RHS fork unconditionally — the same
   violation). The enum does not separate boolean from bitwise — the
   type check is the only disambiguator (:1293, v64 commit).
2. **Defect-fork ordering preserved.** A hoisted operand that deposits an
   inline defect fork (`s[i]`, `div`, `parseInt`) binds inside the same
   guard context, before the consuming op.
3. **Left-to-right evaluation order.** Hoisted temps bind in Nim's operand
   order so multi-fault expressions raise the same defect first.
4. **Guard-cond carve-out (round-2 REPLACEMENT of round 1's "hoist into
   guardPre").** The chokepoint MUST NOT fire anywhere inside a
   `while`-guard condition parse (a `ParseCtx` flag, `ctx.inGuardCond`,
   set by both `nnkWhileStmt` arms feeding `mkShortCircuitWhile`).
   Round 2 traced the guard machinery (:3144–3200): it routes on
   preamble EMPTINESS — a pure hoist flips `continue`-bearing loops from
   the Case-1b/4 fast paths into the R14 sound-degrade, turning
   previously-proving programs `sxUnknown` (the exact over-degrade
   regression the block's own comment warns about, pinned by
   `tsymex_r1_draingap`). The deeper reason round 1's version was wrong:
   a guard temp must re-run every iteration, and with `continue` present
   there IS no safe refresh — that is precisely the hazard R14 degrades.
   Pure compound guard operands stay embedded, which is already sound:
   the walker re-lowers the guard's expression tree fresh each iteration
   (`lowerBoolInExpr`). Fault deposits inside guards keep today's
   behavior (Cases 1/2/3 unchanged). Considered-and-rejected: routing
   the Case-3/4 split on fork-presence instead of emptiness — rotation
   with a pure-let preamble is still stale under `continue`; unsound,
   not merely risky (§Resolved forks F3).

### Slices

- **A1 — operand-shape characterization corpus (test-only, lands first).**
  Table-driven over **informative cells only** (round-2 pruning: the
  round-1 5×4×3×2 grid contained 30 degenerate cells — an atomic shape's
  "let-hoisted twin" is byte-identical to itself — and 120+ hand-written
  procs is 4–8× the largest existing test file; each cell needs a
  distinct top-level proc because entry macros take a `typed` symbol).
  Cells: contexts {bitwise, comparison, arithmetic, boolean, loop-guard,
  **unary `not`/`-`** (round-2 addition), **call-argument position**,
  **assert/assume direct-argument position**} × compound shapes
  {inline-arith, call-result, nested-mixed} × let-hoisted twin pair; the
  interprocedural depth axis {0, 1, 2} applies only to call-bearing
  shapes; atomic shapes appear once per context (coverage, no twin).
  Target ≈60–70 procs across per-context files (~12/file, within the
  `tsymex_phase15_F8_smoke` precedent). If hand-writing fights, a
  corpus-emitting macro (proc defs + twin assertions from a compile-time
  table) is the sanctioned alternative — sized as its own step, not
  absorbed silently. Call-argument and assert-argument positions are
  themselves OUT of chokepoint scope (an argument is not a binop
  operand; inner infix arms still route through it) — their rows pin
  that the boundary guarantee composes into those positions, and the
  scope statement lives here so their absence from the Mechanism is a
  decision, not an oversight.
  Asserts (a) no crash, (b) classified-only degrades, (c) twin equality
  of **verdict AND witness** (in A1, not deferred to A3 — a witness
  divergence must not first surface after the SW-bumping slice shipped),
  and (d) — round-2 strengthening — **no new degrade vs the HEAD
  baseline**: a twin pair that agrees by BOTH degrading fails the corpus
  if HEAD proved that shape (twin equality alone would have silently
  normalized the guard-routing regression constraint 4 now prevents).
  **As-built correction (A1 implementation, 2026-08-13):** the
  demonstrative loop-guard cell does NOT prove at HEAD — semcheck wraps
  some compound guards in `nnkStmtListExpr(Empty, ...)`, whose CR-1b
  handling emits one no-op preamble statement, so "compound fault-free
  guard + `continue`" lands in the R14 Case-3 sound-degrade TODAY
  (issue #155; without `continue` it proves). The corpus pins that
  actual baseline (no-continue → proves; with-continue → classified
  degrade); constraint 4's carve-out is unaffected — it keeps A2a from
  WIDENING the class. Includes the #149 reproducers, the
  chronos-faithful shapes, compound operands of borrowed ops and
  rune-compares (the bypass-site classes), `not ((cap and (cap-1)) ==
  0)`-class unary cells, and the Q1-recognizer pins (`while i < s.len
  and s[i] != c` hits the closed form; **as-built correction:** a
  compound bound (`s.len - 1`) is NOT recognized — narrow-by-design,
  pinned as such, not a regression).
  **Runtime discipline (F5 precedent — this corpus deliberately stresses
  mixed-theory territory):** one file per context, independently bounded
  via `dt-bounded.sh` with an explicit raised timeout and cheap cells
  ordered before depth-2 nested-mixed, so one pathological cell can't
  mask the rest. **TOT-1 relationship (principled split):** A1 owns
  *comparative* invariance (twin equality + baseline); TOT-1 owns
  *absolute* totality (classified-degrade). Any A1 shape that surfaces a
  degrade is ALSO promoted into `tsymex_tot1_totality_corpus.nim`; A1
  never duplicates TOT-1's existing rows. No version bump. Size M–L.
- **A2a — chokepoint + isolated families.** Introduce
  `parseAtomicOperand` + the `ctx.inGuardCond` carve-out flag; atomize
  operands for the families in the clean `else` branch (~1315–1318:
  comparisons, arithmetic, `shl`/`shr`, `xor`), the non-infix bypass
  sites (borrow intercept, rune-compare, nil-compare, `pred`/`succ`,
  string-concat), and the two prefix arms (`not`/unary-minus, with
  constraint 1's uNot exclusion). Round 2 KILLED the round-1 "preamble
  availability audit" prep step: all sites are arms of the single
  `parseExpr(n, preamble: var seq[IRStmt], ctx)` proc (:988) — the
  plumbing exists by construction, and the CR-2b precedent was a
  typebridge-context problem that does not transfer. Ships the permanent
  chokepoint audit test (see Mechanism). **Ver: SW.** Size M.
  Depends: A1.
- **A2b — bitwise `and`/`or` (D1c-entangled).** Round-2 correction: the
  slice CANNOT simply "atomize within the `classifyType != itBool` path"
  — the block parses BOTH operands once, shared, BEFORE the itBool
  branch (:1277–1279 precede :1293), so there is no bitwise-only parse
  to reroute. Named implementation step: evaluate `classifyType(n)`
  FIRST (legal — it needs only the typed node), then branch into two
  genuinely separate parse paths — bitwise → `parseAtomicOperand`,
  boolean → plain `parseExpr` preserving D1c's decision (whose fast-path
  predicate is `rhsPreamble.len == 0 and not
  rhsHasInlineDefectFork(rhsIR)`, :1296 — not bare `len == 0` as round 1
  wrote). Post-reorder, branch exclusivity makes cross-branch leakage
  structurally impossible; the dedicated A1 subset proves the D1c
  decision fires identically post-hoist. **Ver: SW.** Size M.
  Depends: A2a.
- **A3 — invariance acceptance + downstream unblocking.** A1 corpus green
  with twins identical AND zero baseline regressions (clause (d));
  chronos hoist-shapes prove in both spellings
  (replicated in-repo); document that consumer let-hoists are droppable;
  consumer-facing note on **cache-key blast radius** (see below); README
  docs-refresh (`func` support from #147/N0 + the shape-invariance
  guarantee — the repo has no changelog; README is the consumer surface).
  Test/doc only. Size S. Depends: A2b.

**Cache-key honesty (round-1 addition):** A2a/A2b change the canonical form
— `canonicalize.nim` renders locals as positional slots, and inserting an
`isLet` renumbers every subsequent local — so cache keys change for **every
program with a compound operand of a non-short-circuit op anywhere**, not
just previously-failing shapes. Expect broad one-time witness-cache
staleness on the SW bump; A3's consumer note covers it.

**Cluster acceptance:** hoisted and inline forms produce identical verdicts
and witnesses; no crash (AssertionDefect escape) and no degrade reachable
from operand shape alone where the hoisted twin proves; **no verdict or
degrade regression vs the HEAD baseline anywhere in the A1 corpus**; the
permanent chokepoint audit test is green and committed.

## Cluster C — canonical shape at parse entry (#150)

- **C1 — canonical routine kind.** Re-tree accepted routines to
  `nnkProcDef` inside `resolveRoutineImpl`'s body — the shared nil-core
  that N1 introduces and N2 migrates every resolution site onto.
  (Round-2 fix: round 1 referenced this function as if it existed; it
  existed nowhere — without N1/N2 introducing the core, C1 had nothing
  to attach to and its confinement claim was unimplementable as
  written.) **Confinement invariant (now real, an acceptance
  criterion):** post-N2 every resolution site reads `impl` by fixed
  index after the gate — none branches on `impl.kind` — so C1 changes
  ONLY `resolveRoutineImpl`'s body; zero call-site diffs. Grep acceptance rescoped honestly: `nnkFuncDef` remains at the
  structural-shape sites N3 named (lambda-literal arm ~1077, the N3 consts)
  — those answer "is this AST fragment routine-shaped," not "resolve this
  symbol," and are out of a symbol-resolution boundary's reach by
  construction; the acceptance is "only the boundary + N3's named consts."
  **Totality clause:** an `nnkFuncDef` whose child arity/shape deviates from
  the proc layout degrades classified (`ensureProcRegistered` path), never
  proceeds malformed. **Evidence obligations:** (a) container
  `dumpTree`-diff a `func` vs `proc {.noSideEffect.}` and cite it (the
  "layout-identical" claim is currently folklore; no current consumer
  infers purity from node kind — keep it that way); (b) empirical
  cache-key check — dump `symexCacheKeyForFn` for a `func` callee before/
  after; expected UNCHANGED per the `symBodyHash` mechanism (§Ground truth
  3). **Ver: — expected; SW only if the key-diff or any verdict changes.**
  Size M. Depends: N3.
- **C2 — generic-param descriptor threading.** Thread N1's fully-parsed
  `GenericDescriptor` through the remaining consumers — the full
  inventory is FOUR probe sites (round-1 verified), not three:
  `hasGenericParams` (:4589, rebased in N1), `genericParamsNode` (:4600,
  rebased in N1), `gatherTypeSubst`'s inline re-derivation (:4636 — which
  also falsifies `hasGenericParams`'s "shared by" doc comment; fix the
  comment), and `parseCalleeImpl`'s fourth copy (:4897).
  `gatherTypeSubst` and `parseCalleeImpl` iterate `descriptor.params`
  (names resp. constraints) instead of re-walking identDefs;
  `staticParamNames`/`instKeyFor` read the descriptor. Acceptance: BOTH
  the dual-location logic AND the `nnkIdentDefs` walk exist in exactly
  one place (`resolveGenericDescriptor`); behavior-identical ⇒ **no
  bump**. Size M. Depends: N1 (descriptor exists); C1 independent.

## Cluster X — consumer exit gate

- **X1 — chronos verification gate (recurring).** The motivating harness
  exists and is committed — but only on chronos's unmerged
  `contextvars-rebase` branch (`verify/callbackqueue_model.nim` +
  `symex_checks.nim`, commit `3188180`), not on chronos main. Once durable
  (§Open items), re-run it after every SW-bumping slice (N0, A2a, A2b, C1
  if bumped) — the INT-1 analog. Each run STARTS with a Z3-version-parity
  check between the chronos environment and this repo's container
  (round-2 addition — the established cross-repo failure mode:
  unreproducible divergence traced to Z3 skew). Until durable, the
  fallback gate is A1's replicated shapes, documented as weaker (they pin
  the shapes, not the consumer's real build). Size: first run M
  (cross-repo checkout + toolchain/parity validation), S per run after.

## Slice inventory

| ID | Slice | Issue | Size | Hard deps | Ver |
|----|-------|-------|------|-----------|-----|
| F0 | `nnkFuncDef` acceptance, 19 sites — **LANDED `799b0bc`** | #147 | S | — | — |
| N0 | complete the widening: `borrowInfoFor` pin + C3 (:1048 AND :1050) + G8; CR2 pin; psweep → `scripts/` | #147/#148 | S–M | — | SW |
| N1 | `walkableRoutineKinds` + `resolveRoutineImpl` core + `resolveEntryImpl` + `parseEntryImpl` + `GenericDescriptor` + 9 gates + ADR-0030 stub | #148 | M | N0 | — |
| N2 | full migration through the core (13 sites incl. `isStdMathProc`) + permanent kind-audit test | #148 | S–M | N1 | — |
| N3 | reconcile the two divergent routine-shaped-node sets (audited consts on `RoutineNodes`) | #148/#150 | S–M | N2 | SW? |
| A1 | characterization corpus: 8 contexts, pruned informative cells, twins, verdict+witness+baseline | #149 | M–L | N0 | — |
| A2a | `parseAtomicOperand` chokepoint + guard carve-out + isolated families + prefix arms + audit test | #149 | M | A1 | SW |
| A2b | bitwise `and`/`or`: classify-first restructure of the D1c block | #149 | M | A2a | SW |
| A3 | invariance acceptance (incl. baseline) + consumer cache note + README refresh | #149 | S | A2b | — |
| C1 | canonical routine kind (confined to `resolveRoutineImpl`; key-diff evidence) | #150 | M | N3 | —/SW |
| C2 | `GenericDescriptor` threading (4 probe sites → 1) | #150 | M | N1 | — |
| X1 | chronos verification gate (recurring per SW bump; Z3-parity check each run) | — | M then S | harness durable | — |

Sequencing: N0 → N1 → N2 → N3; A1 after N0 (needs the fixed borrow/value
paths to characterize `func` shapes honestly); A2a → A2b → A3 after A1;
C1 after N3, C2 after N1; X1 recurring. A and C are otherwise independent —
**SW-bumping slices need no fixed landing order**: whichever lands second
rebases its bump against the live tip (per the discipline below); a ready
slice is never blocked by an unready sibling. **Soft order (round 2):**
land N2 before A2a when both are ready — they edit the same
borrow-intercept/infix neighborhood of `dsl_parser.nim` (~:1170–1320) and
the reverse order buys nothing but rebase churn; this is churn avoidance,
not a hard dependency.

## Version-pin & DoD discipline (inherited from the chapulin RFC, binding)

- SW (`symexWalkerVersion`, `canonicalize.nim:127`, currently **70**) bumps
  on any verdict **or cache-key** change; RC on witness-serialization shape
  changes (none expected). A bumping slice updates the canonical
  `tsymex_phase15_CR2_cachekey.nim` `==` pin in the same slice and
  serializes its literal against the live base (`symex-version-bump-cr2`
  memory). Incidental pins stay `>=` floors.
- Every slice: both-backend green on touched-path suites; new test files
  registered in `nelli.nimble`; full sweep before commit for SW-bumping
  slices (`psweep.sh` — today in gitignored `scratchpad/`, promoted into
  tracked `scripts/` by N0 since DoD tooling must be a repo asset; watch
  the sweep-waiter-self-match hazard); bounded runs only
  (`scripts/dt-bounded.sh`).
- The Windows CI leg (`.github/workflows/symex-windows.yaml`) is a
  hand-curated test array, not nimble-driven (round-2 finding): N0's
  regression pins are candidates for that array (platform divergence is
  the class it exists for); A1's corpus stays Linux/podman-only — its
  degrade-surfacing rows reach Windows via TOT-1 promotion (TOT-1 is
  already in the leg).
- Standing round-6 DoD clauses carry over: typeKind-guard, switch-fan-out,
  docs-refresh (ADR + status entries land in the introducing slice).
- Behavior-identical slices (N1, N2, C2, C1-if-unbumped) must *prove* it:
  no verdict or key drift on the existing corpus. Compile-error text is
  the one DELIBERATE exception: N1 unifies the 9 gate texts (§Resolved
  forks F4); the itemized inventory documents the change; automated
  tests use the `not compiles` idiom.

## Release planning

No-bump slices (N1, N2, C2, A1, docs) ride the next patch release.
SW-bumping slices (N0, A2a, A2b, N3/C1 if bumped) target **0.3.5** (or the
then-next patch). **0.4.0/0.5.0 stay reserved** for the parked chapulin
RFC's Track A/B exit releases — do not collide with those labels.

## ADR plan (house `D`-lettered convention)

**ADR-0030** (round-2 pinned — the next free number after ADR-0029; the
stub file lands with N1 so interleaved work, e.g. a chapulin resume,
cannot claim it while D2/D3 are still pending) — *boundary normalization:
the walker's input language is defined by what the boundary emits, not
what the compiler can produce* — with lettered sub-decisions, matching
the ADR-0008/0009 amendment pattern:
- **D1** (lands with N1): kind vocabulary + resolution policy map (the
  Invariant-3 three-policy constraint).
- **D2** (lands with A2a): operand ANF scope — atomized families, the
  short-circuit exclusion predicate, defect-fork ordering, loop-guard
  cadence.
- **D3** (lands with C1/C2): canonical routine shape + generic-param
  descriptor.

## Cross-RFC handoff (for chapulin Track B's resume)

This RFC lands first; chapulin's resume must re-read, against the then-live
tree: `tryRecognizeScanIdiom` (raw-AST match is preserved by A2 by
construction — pinned in A1), the bracket-expr/index parsing sites B1 plans
to collapse (A2a may route their operands through `parseAtomicOperand`),
and the `ensureProcRegistered`/`parseCalleeImpl`/`instKeyFor` registration
pipeline (reshaped by N1/N2/C2 — B1's `IRParam.isStringBacked` threading
lands on the consolidated API, which should make it easier, not harder).
Cross-RFC SW serialization: rebase-against-live-tip, as within-RFC.

## Resolved forks (round 1 — recorded, no longer open)

- **F1 — Cluster A disposition (was: repro gap).** RESOLVED by archaeology:
  the #149 crash was root-caused and fixed at v64 (`a0bfeff`, D1c bitwise
  lift gated on itBool) — the consumer-env-parity question is moot; the
  issue's reproducer was stale when filed. Disposition: **proceed** —
  restructured as A1 (net) → A2a → A2b with the chokepoint mechanism; the
  justification is the invariance guarantee §0 argues for plus the six
  live bypass classes (borrowed-op/rune-compare compound operands) A1 will
  characterize. If A1 unexpectedly surfaces a live failing shape, it slots
  in as a RED test and strengthens the case; nothing gates on it.
- **F2 — C1 cache-key handling.** RESOLVED by mechanism correction: the
  premise ("re-tree flips func-keyed entries") was wrong — keys derive from
  `symBodyHash(sym)`, not the local tree. C1 carries an empirical key-diff
  obligation; expected outcome is **no bump**; if the diff disagrees, bump
  honestly (the fallback recommendation from round 0 still applies).
- **F3 — guard-cond hoisting (round 2).** RESOLVED against round 1's own
  constraint 4: hoisting inside while-guard conds flips the R14 routing
  (preamble-emptiness dispatch, :3144–3200) and degrades
  `continue`-bearing loops that prove today; with `continue` present
  there is no sound refresh mechanism, so "hoist into guardPre" was not
  hardening — it was the R14 hazard restated. Disposition: carve-out
  (`ctx.inGuardCond`), Mechanism constraint 4. Considered-and-rejected:
  routing the Case-3/4 split on fork-presence instead of emptiness
  (rotation with a pure-let preamble is still stale under `continue` —
  unsound, not merely risky).
- **F4 — entry-macro error-text asymmetry (round 2).** RESOLVED: unify.
  `symexForAll`'s `" for \`fn\`"` suffix is a historical accident that
  disambiguates nothing, and compile-error text has zero test/harness
  dependents. The `detail` param round 1 designed to preserve it is
  dropped.

## Open items (awaiting Corey)

- **Chronos harness durability (external repo).** The CallbackQueue
  verification harness lives only on chronos's unmerged `contextvars-rebase`
  branch. X1 (the recurring exit gate) needs it durable — merged to chronos
  main or relocated somewhere stable. This is a chronos-repo action outside
  this RFC's authority; until done, X1 runs against the branch checkout and
  A1's replicated shapes are the in-repo floor.

## Non-goals

- #138 cross-module private-helper resolution (`getImpl` visibility).
- Modeling new routine kinds (`iterator`, `converter`, `method`) — this RFC
  makes adding them cheap, it does not add them. Excluded-kind behavior at
  the boolean-false sites is pinned by N1's negative tests.
- `coverage.nim:292` (`{nnkProcDef, nnkFuncDef, nnkLambda}`) and
  `mutation.nim:123` (`{nnkLambda, nnkProcDef, nnkDo}` — note: no
  `nnkFuncDef`; a `func` there is rejected loudly by `expectKind`, not
  silently) — different subsystems with their own vocabularies; documented
  here so the N2 repo-wide grep has named, justified exclusions. If the
  mutation-subsystem gap ever bites a consumer, it gets its own issue.
- Any change to a site's Invariant-3 failure policy.
