# RFC — chapulin consumer-hardening — handoff

- **Stage:** 3 (tdd grind) — IN PROGRESS   •   Architect rounds 1&2 done; fork resolved
- **Resume:**
  `/loop implement the next unimplemented RFC slice with /tdd, following the standing
  rules; after each slice report one progress line; stop when every slice is done`.

## Stage-3 grind ledger
Slices land serially (each SW bump serialized against a live base). Sweep = all
`tsymex_*.nim` × {c,cpp} via `scripts/dt-bounded.sh`.
**Cluster 2 COMPLETE. M1, M2, M3 landed.** Next unimplemented slice: **M4** (string
`.add`/`&=` → model both as `iekStrConcat`; `&=` is the SND-1 Class-B silent-no-op→
false-sxSat case; needs a type-classify branch — string LHS→mkStrOp, else mkBinop —
NOT a set edit; `binopForInfix` has no `"&"` case; depends on SND-1✓; size S–M).
Slice order: SND-1✓ SND-1b✓ SND-2✓ CR-1a✓ CR-1b✓ CR-1c✓ CR-2a✓ CR-2b✓ CR-2c✓ M1✓ M2✓ M3✓
→ **M4** → M5 M6 → P/Q/TOT/INT/F/C. 12/27 done, 15 remaining.
Versions now: symexWalkerVersion **"49"**, renderAsChoicesVersion **"5"**; only
`tsymex_phase15_CR2_cachekey.nim` pins either with `==`.

| # | Slice | Commit | walker ver | Sweep | Notes |
|---|-------|--------|-----------|-------|-------|
| 1 | SND-1 | `84668ab` | 37→38 | 388/388 ✓ | isUnsupported taints Path.uncertain. Fallout: added no-op parse arm for assert-scaffolding `nnkConstSection`/`nnkBindStmt`/`nnkMixinStmt` in dsl_parser (else every assert degraded). Legit soundness corrections: a3_closure_iterators T5/T6 sxSat→sxUnknown (accidentally-correct false-sxSat SND-1 closes). New test uses `>=`-floor pin idiom; 7 legacy `==` pins bumped to "38". |
| 2 | SND-1b | `bc2c8d9` | 38→39 | 390/390 ✓ | `applyClosureGround` skips `assertArm` for uncertain closure-body sub-paths (both return channels), pushes new `ceClosureBodyUncertain` (sevError) → existing `closureForcedUnknown` whole-run degrade fires. ADR-0018 in SYMEX_PLAN. Fixed fork-registry comment (descentBase = 2nd raw `Path(`). **One-time SW pin-idiom migration executed**: canonical CR2_cachekey stays `== "39"`; 6 incidental pins → `>=`-floor. Strong-form test checks error-kind, not just verdict. Subagent died on API error post-sweep; control loop verified + committed. |
| 3 | SND-2 | `0a156c7` | 39→40 | 392/392 ✓ | `isAssume` promoted from bool flag to distinct `IRStmtKind` (`mkAssume` ctor, own render arm). 12 switch sites: 10 uniform `of isAssert, isAssume:`, 2 non-uniform — canonicalize renders distinct `St<Am:…>` vs `St<At:>` (avoids `symexCacheKey` collision → silent wrong answer), walker dispatch shares steps 1/2/4 but omits step 3 `forkDefect`. Round-2 fix: `collectAssertRanges` had `else: discard` silently dropping isAssume range facts → now included. `symexAssume(cond)` lowers to `mkAssume` not `mkAssert`. ADR-0019 in SYMEX_PLAN. 7-test strong-form suite (flagship verified genuinely RED). CR2 pin → `== "40"`. Subagent committed itself; control loop verified (both backends green, ADR landed, only CR2 as `==`). |
| 4 | CR-1a | `ee9763c` | 40→41 | 394/394 ✓ | bitwise `and`/`or`/`xor` on a Z3-Int-sorted operand (`.len`/`.find`/`.indexOf`/`parseInt` — unconditionally svInt, no BV-promotion choice) hard-raised `ValueError: bitwise op on promoted Z3Int` (native crash). New `svIntToBV` (runtime.nim ~1980) bridges the Int operand to BV via `Z3_mk_int2bv` (unsigned; values always non-negative); former crash arm (~2977) dispatches through existing `binBV` → SOUND sxSat/sxUnsat (NOT degrade). Width follows the BV operand, BV64 default (native int) when both Int-sorted. No new ADR (bug fix at existing locus). Strong-form test (SAT witness-parity + load-bearing UNSAT `and 1==2`/`xor self==1`; and/or/xor). CR2 pin → `== "41"`. Subagent stalled on detached-sweep pattern; control loop verified (diff-review + 394/394 both backends) + committed. |
| 5 | CR-1b | `5fc018e` | 41→42 | 396/396 ✓ | tail-return-of-local KeyError (`runtime.nim` `of iekVar: env[e.vname]`) was a SYMPTOM — **true fault at PARSE time**: `dsl_parser.nim`'s `nnkPar`/`nnkStmtListExpr` arm did `parseExpr(n[^1])`, silently dropping every LEADING statement (`let hi = ...`) of an implicit-tail-return body (`result = (let hi=…; hi+1)`). Fix: parse each leading child as a statement into the existing `preamble` accumulator (mirrors `nnkLetSection` A-normalization) before the tail child. **runtime.nim untouched** — fixed at the true lowering site per DoD, NOT by soft-failing the read. Strong-form test: SAT w/ load-bearing witness replay (`data[o] mod 256==4` ∧ `f==5`) + UNSAT `==300` (rules out dropped-local-as-free-symbol false positive). No new ADR. CR2 pin → `== "42"`. Subagent blocked in-turn correctly + self-committed; control loop verified (runtime untouched, both backends green, only CR2 `==`). |
| 7 | CR-2a | `3f01b1f` | 43→44 | 400/400 ✓ | `parseExpr` catch-all `else:` (dsl_parser.nim ~1866) `error()`ed at MACRO-EXPANSION on any unhandled NimNode kind → aborted compilation (worse than sxUnknown). Converted to the A7-S3 `mkUnsupported`-degrade idiom: new `feUnsupportedExprKind` (types.nim, enum tail) sevError + `preamble.add mkUnsupported` + type-correct dummy via new `zeroValueForType(classifyType(n).ty)` (returns Nim's guaranteed ZERO default for int/bool/float/string — sound for read-before-write per Inv-3; nil→`mkIntLit(0)` fallback for aggregates under SND-1 taint). Depends on SND-1✓ (dummy never yields a witness; also Class-A → capForcedUnknown backstop). RED = compile-abort on `(if c:1 else:2)+1` (nnkIfExpr nested as `+` operand). Strong-form 6-test incl load-bearing CR-2a-2 (dummy 0 would trivially-SAT `y==1` ∀x but SND-1 → sxUnknown≠sxSat). No new ADR (idiom reuse). CR2 pin → `== "44"`. Subagent stalled on detached-sweep (4th); control loop verified diff+test, then subagent's Monitor resumed it + self-committed (5 files, no race); control loop re-verified 6/6 both backends + 400/400. |
| 8 | CR-2b | `6c9210d` | 44→45 | 402/402 ✓ | Parameter-type macro-`error()` → whole-run forced-`sxUnknown`. `classifyType`'s resolved-type-name text-match catch-all (`dsl_typebridge.nim:452`) `error()`ed at macro-expansion on an unmodeled SUT PARAM type (RED: `cstring`), aborting compilation before any body was walkable. Option 2 (control-loop-resolved, mirrors `__ownership:`): catch-all now returns `unranged(tUninterp("__unsupported:" & s))`; allocateSym gains a `"__unsupported:"` prefix branch raising CR-1c's `SymexClassifiedDegradeError` carrier with new `feUnsupportedParamType` kind (types.nim, enum tail) → caught at runSymex boundary → whole-run sxUnknown. **Second crash-trap found + fixed (in-scope, not a fork):** `emitTyAndReader` (symex.nim) builds a witness-reader for every param at macro-expansion; its itUninterp catch-all knew only `"__closure"` — an `"__unsupported:"` name fell through to an uncaught ValueError in the NimVM (relocated the abort). Added a placeholder-int/`{.warning.}` branch mirroring `__closure`; placeholder never evaluated (sxSat/sxRaised codegen arms unreachable once allocateSym forces sxUnknown). Carrier REUSED (no new exception type). Strong-form test asserts KIND + `status != sxSat && != sxUnsat` (no silent wrong verdict, no walk-time crash) both backends. CR2 pin → `== "45"`. Subagent blocked in-turn + self-committed; control loop verified independently (commit/tree/pin/version + CR-2b test 4/4 green BOTH backends + diff-reviewed carrier reuse & second-trap fix). |
| 12 | M3 | `5be3310` | 48→49 | 410/410 ✓ | `s.rfind(sub)` (strutils) modeled as a near-clone of `s.find(sub)`: new `iekStrRfind` IR kind lowering to nim-z3's native `lastIndexOf` (Z3 `seq.last_indexof`, `_deps/z3/src/z3/sequence.nim:199`) instead of find's `indexOf` — NOT bounded-scan, NOT Q1/Q2 hang class. New `smkStrRfind` recognizes `"rfind"`; smk→iek map + runtime_strings lowering (`svInt zi: lastIndexOf(recv,sub)`) + every exhaustive iek case set (abstraction/canonicalize/runtime/probeProto) gained the kind alongside iekStrFind. canonicalize renders a DISTINCT cache key from find (test-asserted via `symexCacheKeyForFn` — closes SND-2-class silent-collision risk). Bumps SW 48→49; RC stays "5" (int witness). Strong-form 6-test: **load-bearing rfind≠find** (doubled substring: rfind=last=5, find=first=1, both round-tripped vs real Nim) + -1 not-found parity + UNSAT soundness + cache-key distinctness. Subagent detached sweep + stopped (8th); control loop verified 6/6 BOTH backends independently, blocked to 410/410, committed. |
| 11 | M2 | `f9b64c1` | 47→48 | 408/408 ✓ | `parseBiggestInt(s)` modeled by routing to the SAME `iekStrToInt` IR as `parseInt`. Two callee-name guards in dsl_parser (expression match ~1537 + discarded-call raise fork ~2955) extended `"parseInt"` → `{"parseInt","parseBiggestInt"}`. **runtime.nim UNTOUCHED** — `iekStrToInt`'s ValueError raise-path (runtime.nim:1930/1966) already models malformed-input failure → failure-mode parity automatic. RED empirically = `sxUnknown` (seUnsupportedStringOp via string-call fallthrough), NOT compile-abort (CR-2a removed that). strOp label keeps actual callee name → distinct cache key from parseInt. Bumps SW 47→48 (verdict sxUnknown→real); RC stays "5". CR2 pin walker→"48". Strong-form 8-test: happy (incl −42) ground-truthed vs real Nim `parseBiggestInt`; **load-bearing M2-3 failure-parity** (`"abc"`→sxRaised+ValueError, identical to parseInt); UNSAT (s="100"≠42); discard-raise fork parity + soundness; valid-discard regression. Unblocks chapulin v2 B4. Subagent detached sweep + stopped (7th); control loop verified 8/8 BOTH backends independently, blocked to 408/408, committed. |
| 10 | M1 | `f2b41ee` | 46→47 (+RC 4→5) | 406/406 ✓ | `seq[byte]`/fixed-width-int witness readers. `emitTyAndReader`'s `itSeq` arm (symex.nim) rendered only `seq[int64]`/`f32`/`f64`/`ref T` → every other elem type degraded to sxUnknown via CR-2c's gate. Widened reader + read-helpers (runtime.nim `readSeq*`) to the full fixed-width-int family (int8/16/32/64, uint8/16/32/64; byte=uint8 alias). **Walker already allocated/constrained these seqs** (extractSeqElements/allocateSeqDataRaw/seqElemAt dispatch on every (signed,width) since Phase 15 C4) — ONLY the post-solve reader was missing → M1 is reader-only (scope confirmed). **`isRenderableSeqElemTy` (types.nim) widened in EXACT lockstep** so CR-2c stops demoting these; composes through recursive `isRenderableWitnessTy` → nested `tuple[a:seq[byte]]` renderable too. Bumps BOTH renderAsChoicesVersion 4→5 (new witness shape) AND symexWalkerVersion 46→47 (verdict sxUnknown→sxSat; precedent canonicalize.nim:496). CR2 pin → walker `== "47"` + RC `== "5"`. Strong-form 12-test: exact byte/uint/int witnesses incl boundary 255 (no trunc) + NEGATIVE sign-extended int8/16/32 + load-bearing UNSAT (byte≤255) + nested tuple[seq[byte]] sxSat + regression seq[string]/seq[Widget] still sxUnknown. Subagent detached its sweep + stopped (6th); control loop took over: verified M1 test 12/12 BOTH backends independently, blocked on sweep to 406/406, committed. |
| 9 | CR-2c | `25ebf9c` +`0007b03` | 45→46 | 404/404 ✓ | Third macro-`error()` class: post-solve witness-reader codegen `emitTyAndReader` (symex.nim:716/727/735) `error()`ed at macro-expansion on unmodeled witness shapes (seq non-scalar/ref elem, Table≠string-int, HashSet≠int) → whole-file compile abort. Degrade at `parseProc` TOP-LEVEL SUT-param loop via new `demoteUnrenderableWitnessTy` (dsl_parser) → `tUninterp("__unsupported_witness:" & s)`; allocateSym `__unsupported_witness:` branch raises CR-1c's `SymexClassifiedDegradeError` carrier w/ new `feUnsupportedWitnessType` (types.nim, enum tail) → whole-run sxUnknown. **Scoped to params, NOT classifyType** (naive classifyType-gating over-triggered on internal non-witness types e.g. in-body `seq[byte]` helper — broke S5_strops/S7a_bytes; caught by sweep, rescoped; dsl_typebridge reverted clean). **Control-loop caught a completeness gap in core `25ebf9c`:** top-level-only check missed NESTED unrenderable shapes (`tuple[a:seq[Widget]]` etc.) because emitTyAndReader recurses into aggregate fields → still compile-aborted (confirmed repro). Handed back → follow-up `0007b03`: new RECURSIVE `isRenderableWitnessTy*` (types.nim) mirroring emitTyAndReader's whole type-tree (distinct/tuple/array/seq-ref/variant arms), reusing the 3 leaf predicates as single source of truth; demotes whole param iff any leaf unrenderable. Carrier reused (no new type). Strong-form test: 5 top-level + 4 nested (tuple/array/variant-arm/double-nested `seq[tuple[seq[Widget]]]`) RED→sxUnknown+kind, +4 flat +3 renderable-NESTED regression guards stay sxSat (no over-demotion). NO SW re-bump for follow-up (nested sigs had zero cache entries). CR2 pin → `== "46"`; RC stays "4". Both subagent runs blocked in-turn + self-committed; control loop verified independently BOTH backends (17/17 + clean tree at 0007b03) and diff-reviewed the recursion + param-only scoping. |
| 6 | CR-1c | `505354c` | 42→43 | 398/398 ✓ | §0 last-resort walker-fault safety net. New `SymexClassifiedDegradeError{kind: SymexErrorKind}` generic carrier + distinct `weInternalWalkerFault` kind → `sxUnknown`. **⚠ DESIGN DEVIATION FROM RFC (sound, resolved not a fork):** RFC specified a catch "around per-statement dispatch" — that PER-FRAME placement caused a **C-backend SIGSEGV** (per-frame try/except interacting with ORC destructor-unwind of `walkBlock`'s live `seq[Path]` whose elements hold refcounted Z3 ASTs w/ destructors; heisenbug, C-only, b7258f7 divergence class). 1st subagent impl shipped this regression + stalled; control loop caught it (E8_getcurrentexn + S11_mutation SIGSEGV), handed back. Fix: moved catch to the SINGLE already-existing `runSymex` boundary `try/except` (no new try, per-frame reverted 0 refs) — unanticipated native unwinds naturally (sound, as pre-CR-1c) → caught ONCE → classified. Coarser: whole-run sxUnknown on unforeseen fault vs per-path (conservative/safe). Anticipated carriers consumed by their arms first; Defects still crash loudly. Fault-injection test via companion `.nim.cfg` (`-d:symexTestInjectWalkerFault`) — **found `.cfg` was gitignored** (`tests/t*[!.]`, no `.nim.cfg` negation); added `.gitignore` `!tests/*.nim.cfg` negation. ADR-0020 (rewritten for boundary design). CR2 pin → `== "43"`. Control loop verified: E8/S11/CR1c-fault green BOTH backends, 398/398, .cfg in commit, walk case un-try-wrapped. |

## Round-2 architecture review — applied (2026-07-12)
Second 4-agent team (depth/breadth/design/feasibility), all grounded in the code.
Round 2 CONFIRMED round-1's core claims (SND-1 chokepoints, ADR-0012 D2 precedence,
call-cache uncertain-gate, 12-switch count) and surfaced new material work:
- **SND-1b (NEW, CRIT):** closure ground-axiom path (`applyClosureGround`,
  runtime.nim:6244-6531) bypasses `Path.uncertain` — folds closure-body returns into
  GLOBAL `currentClosureCallAxioms` (drained into every solve) with no uncertain-gate.
  SND-1's fix doesn't reach it. New slice; reuse `closureForcedUnknown` whole-run
  degrade. Fork-registry comment (4409-4454) stale re raw `Path(` at 6381.
- **CR-2c (NEW):** third macro-`error()` class — `emitTyAndReader` witness-reader
  codegen (symex.nim:697/708/716). §0 widened to THREE site classes.
- **SND-2 cache-key collision (CRIT catch):** blanket "render isAssume==isAssert"
  would collide `symexCacheKey` (canonicalize.nim:684) → silent wrong answer. Needs
  distinct tag `Am:` vs `At:` + test. Also `collectAssertRanges` (abstraction.nim:324)
  has `else: discard` silently dropping assume range facts — DoD'd.
- **CR-2b crash-risk closed:** `tUninterp("__unsupported_")` → uncaught ValueError in
  allocateSym (only `__ownership:` guarded). Needs new prefix guard OR capForcedUnknown
  + explicit ctx-threading decision.
- **CR-1c open item RESOLVED:** chapulin config has NO `-d:danger`/`--panics:on`
  (checked nim.cfg/chapulin.nimble) → catch approach viable. Depth nuance: `--panics:on`
  hits only Defect; CR-1a/b (ValueError/KeyError=CatchableError) unaffected. HARD RULE:
  `try/except` never `try/finally` (commit b7258f7 = C-backend-only silent sxUnsat);
  regression must diff both backends.
- **TOT-1 rescoped generative→table-driven:** all symex entry points need `fn: typed`;
  fuzz.nim generates values not AST. Fixed hand-authored §0-invariant corpus. (3 of 4
  agents independently proved this.)
- **Design:** 18 near-identical exception carriers exist; CR-1c/CR-2b use ONE generic
  `SymexClassifiedDegradeError{kind}`, name the 18 as incremental debt.
- **Sizing/process:** P2→P2a(value)+P2b(ref,L; variant excluded); Q1=timeboxed spike
  (may have no viable encoding); INT-1 recurring per-SW-slice + rollback clause;
  SYMEX_PLAN.md ADR-landing + stale-status obligation; `(t)` RED-state instruction;
  M4 `&=` is a type-classify branch not a set edit (binopForInfix has no `&`).

## RESOLVED FORK (Corey 2026-07-12) — SW version-pin idiom
**Synthesis chosen:** canonical `tsymex_phase15_CR2_cachekey.nim` pin stays `==`
(conscious-bump gate per [[symex-version-bump-cr2]]); incidental feature-test pins
convert to tolerant `>=`-floor (`check parseInt(symexWalkerVersion) >= N`). Kills ~200
pin touches + the parallel-worktree literal collision, keeps one loud drift gate.
Serialize-against-live-base rule still applies to the canonical `==` pin. Now recorded
in the RFC's §Version-pin discipline as a settled decision, not a fork.

## Round-1 architecture review — applied (2026-07-12)
4-agent team (depth/breadth/design/feasibility), all grounded in the actual code.
No genuine forks surfaced — every finding had a goal-determined best answer;
applied all directly. Corey's mega-RFC scope preserved (Clusters 6-7 annotated a
**decoupled track**, not split out). Material changes now in the RFC:
- **SND-1 re-scoped L→S:** mechanism already exists (`Path.uncertain`,
  runtime.nim:376-378, consumed at both `w.found` producers). Fix = taint the
  `isUnsupported` arm; **no ADR-0012 D2 amendment** (only a new taint producer).
  Added Class-A/B taxonomy (Class-A already immune via `capForcedUnknown`).
- **CR-1 is NOT a sweep:** split CR-1a (#3 fixed at abstraction/BV-ban locus,
  matches [[symex-abstraction-bv-ban-toz3int]]), CR-1b (#4 tail-return lowering),
  CR-1c (one narrow last-resort catch, distinct `weInternalWalkerFault` kind).
  Respects the documented "ValueError/AssertionDefect must surface" crash-doctrine.
- **CR-2 split by error() class:** CR-2a expression-position (dep SND-1), CR-2b
  parameter-type-position (uses already-sound `capForcedUnknown`, no SND-1 dep).
- **New slices:** TOT-1 (generative totality harness — operationalises §0),
  INT-1 (chapulin workaround-removal exit gate).
- **Version-pin discipline** now a cross-cutting section (TWO consts:
  `symexWalkerVersion` + `renderAsChoicesVersion`); per-slice `Ver` column added.
- Corrections: M1 dep on CR-1 dropped (class-C, symex.nim); M3 de-risked S
  (nim-z3 `lastIndexOf`); SND-2 = 12 exhaustive switches (+ scan.nim found[0] trap
  test, + keep assert raise-forks steps 1/2/4, drop only forkDefect step 3);
  Q2 re-scope-after-SND-2.
- **Open verification for round 2 / CR-1c:** confirm chapulin build flags — under
  `-d:danger`/`--panics:on` a failed doAssert is uncatchable; CR-1c would then need
  raise-guards, not a catch.
- **Verified finding set:** consolidated in session scratch `verify_results.md`
  (4 agents, all findings re-checked @ 99fa2db). RFC reflects it.
- **★ Key architectural insight for the architect rounds:** hard dependency
  **SND-1 ≺ CR-1/CR-2** — the crash-degrade work must NOT ship before the
  mkUnsupported-statement soundness fix, else it trades visible crashes for silent
  false-`sxSat` (worse under Invariant 3). SND-1 amends ADR-0012 D2 precedence.
- **Biggest scope changes from verification:** #5/#11/#7-symptom/pred/succ/`..<`
  HEALED (dropped); #3/#9 narrowed; SH1 does-not-repro (deferred); **NEW CRIT
  soundness bug SND-1** found (silent mis-mutation → false sxSat, general).

## Scope decision (Corey, 2026-07-12)
**ONE mega-RFC covering ALL chapulin findings**, across every subsystem (symex
walker/parser/solver + fuzz + shrinker + coverage). Corey chose this over the
recommended "symex-RFC + route-the-rest" split. Mitigation for coherence: the
single doc is organized into **per-subsystem clusters** (Phase-15/16 cluster
style), each independently sliceable. Unifying thesis: *everything chapulin's
v1/v2 verification harness surfaced*, with the §0 "walker never crashes /
Invariant-3 totality" invariant as the marquee cross-cutting cluster.

Source findings: `/mnt/c/Users/corey/projects/chapulin/docs/proptest-findings.md`
(pinned at proptest `99fa2db` = current HEAD; `file:line` refs align).

## Prerequisite: verify-at-HEAD pass (IN PROGRESS)
Some findings are already HEALED by A7/A8/A9 (confirmed pre-fan-out: #7's
`toLowerAscii` symptom works now; #3 bitwise-plain-int doesn't repro in the
simple shape). Don't slice healed work. Four background verification agents
(sonnet, verify-only, no fixes) each re-check a cluster and return a
LIVE/HEALED/PARTIAL table with evidence + fix locus + size:
- **A** — §1 walker crashes: #3, #4, #5, #11. (Known: #4 KeyError = LIVE-CRASH.)
- **B** — §2 model gaps: #1 seq[byte] reader, #7 toLower/probeProto, #8 rfind,
  #10 string.add, parseBiggestInt, min/max.
- **C** — §3 parser (#2 tupleConstr, objConstr, seq-slice, pred) + §4 solver
  (#6 dependent loops, #9 loop+string-param, symexAssume==symexAssert).
- **D** — §5 fuzz/corpus/DB, §6 coverage, §7 shrinker Int128 compile bug.

## Confirmed-live so far (pre-verification spot-checks)
- **#4** implicit tail-return referencing a local → uncaught `KeyError` at
  `runtime.nim:2629` (`env[e.vname]`), native crash. **LIVE-CRASH.** Flagship of
  the §0 "walker never crashes" invariant.
- **#7** symptom HEALED (A9), but a real latent bug remains: `probeProto`
  (`runtime.nim:1763` `StrOpKinds - {...}` catch-all) returns `none` for the
  A7/A8/A9 string ops (`iekStrToLower/Upper`, `iekRadixFmt`, `iekRuneToStr`) —
  missing from its modeled subset. Masked by a lowering fallback today.

## Open forks (awaiting Corey)
- (none blocking — scope decided; drafting proceeds after verification)

## Key decisions (this session)
- Mega-RFC scope (above). • Verify-at-HEAD before drafting (drop healed findings).
- Non-symex findings STAY in this RFC (per mega-RFC choice) as their own clusters,
  rather than routing fuzz→FUZZ_PLAN.

## Review ledger (stage 4) — not started
