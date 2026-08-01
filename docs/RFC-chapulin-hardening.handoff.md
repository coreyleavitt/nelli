# RFC — chapulin consumer-hardening — handoff

## Stage 4 — /code-review — ✅ CLOSED 2026-07-30 (floor reached: 0 Crit/High/Med open)
**Outcome:** 6 mandated findings R1-R6 fixed + R1b (pre-existing v59 bug found en route) + R14 (Crit introduced by R1b's fix, closed with the faithful short-circuit desugaring). 2 adversarial re-review rounds → floor. Commits: c75285f (R1+R5+R1b, SW61) · 46b0ac3 (R4) · 3428987 (R3) · 4fea3da (R2+R6, SW62) · 98f4564 (R14, SW63) · 7c3a16d (Low batch, no bump). Every step swept both backends. **Deferred Lows subsequently fixed 2026-08-01** (Corey: "fix lows now"): R7 + R8 (aab18ce, no SW bump) and R9 + R11 (9be7b5a, doc-only); R10 + R12 were already closed in the Low batch (7c3a16d). Full symex sweep 452/452 green both backends after the fixes (one c-only rc=1 was a parallel-load compile flake — confirmed rc=0 standalone). **Case-2 precision deliberately NOT fixed** — it is already sound (degrades to sxUnknown for the exotic `(a div b)>i and s[i]` + continue shape, never a wrong verdict, pinned by tsymex_r14_case2_degrade), and re-review round 2 explicitly recommended against a 5th short-circuit-dispatch revision (re-touching the engine's most delicate code for zero soundness gain). **All review findings now closed; only Case-2 precision remains as an accepted-sound non-issue.** Next process step: INT-1 (blocked on a proptest release) then done.

## ⏳ SIDE-TASK IN FLIGHT (2026-08-01, not part of the RFC): milpa manifest+lock migration
Corey: "add a milpa.kdl and lock file for the current version" → new milpa (github coreyleavitt/milpa, local ~/projects/milpa) has progressed a lot; migrate to current format.
**Done (uncommitted):** proptest `milpa.kdl` (+`version "0.1.0"`), `milpa.lock` regenerated via new milpa `fetch` (new format: `dag-sha256` identity, `declared_version_source`, `provenance.origin`; graph = softlink 0.11.1 + z3 2.2.0, NO stale proptest self-pin); `scripts/{dt,dt-bounded,runtest}.sh` gained `-v $HOME/projects/nimlibs:$HOME/projects/nimlibs` mount (milpa `local=` dep = absolute symlink `_deps/z3 → ~/projects/nimlibs/nim-z3`, spec S4 §4.3, must be mounted like the CAS already is). nim-z3 `milpa.kdl`: proptest moved `deps`→`dev-deps` (test-only in nim-z3; removes the z3→proptest back-edge that was pulling a stale proptest@99fa2db self-pin into proptest's lock) + re-locked nim-z3 `milpa.lock`.
**Key facts:** new milpa runs on host via `uv tool install git+https://github.com/coreyleavitt/milpa.git#subdirectory=impls/python` (the old "never run host milpa" memory is SUPERSEDED — that was the old tool vs the then-committed lock). `_deps/`+`nim.cfg` are gitignored (regenerated on `milpa fetch`); only milpa.kdl+milpa.lock committed. `milpa lock`=lock-only; `milpa fetch`=_deps+nim.cfg+lock.
**✅ DONE — git-ref milpa migration committed (proptest `0e149fb`; nim-z3 `ca4fe77` pushed).** nim-z3 had been moved externally to `~/projects/nim/libs/nim-z3` (dangling the old `local=` symlink). Resolution: (1) nim-z3 `proptest` deps→**dev-deps** (test-only), pushed to github `ca4fe77` — stops proptest's git-ref z3 from dragging a stale `proptest@github-main` self-copy onto nim.cfg; (2) proptest `milpa.kdl` z3 `local=`→`git=(url)"…/nim-z3.git" ref="main"` + `version "0.1.0"`, both deps now CAS-admissible so the temporary `~/projects/nimlibs` harness mounts were REVERTED; (3) `milpa.lock` regenerated in current `dag-sha256` format, clean 2-dep graph (z3@ca4fe77 v2.2.0, softlink@main 0.11.1), no self-pin. **Validated: symex 452/452 + fuzz/cov/db 62/62 green both backends.** Committed proptest `milpa.kdl`+`milpa.lock` only (scripts reverted, NOT committed). NOT pushed. Memory `nimz3-ffi-vendoring` rewritten for the git-ref model + sanctioned new milpa host tool. **Nothing outstanding on the milpa side-task.**

## Stage 4 — /code-review ledger (opened 2026-07-29; scope = full RFC diff 99fa2db→HEAD src/, 4007+/382-)
5 review agents (symex-core, parser/IR, fuzz/cov/db, security, design) + 5 adversarial verifiers.
Presented to Corey 2026-07-29; **Corey approved the default mandate (fix through Medium, leave Lows).**

### Fix loop — IN FLIGHT (2026-07-29)
Ordering constrained by: R1/R3/R5 all touch runtime.nim (serialize); R1 & R2 both bump SW+CR2 pin (serialize SW).
- **Wave 1:** R4 ✅ DONE (fuzz.nim nil-guard — gates loadCorpus/saveCorpus on their OWN *CorpusImpl fields; new tests/tfuzzcorpus_nilguard.nim RED=SIGSEGV→GREEN both backends; uncommitted). R1+R5 SPLIT after subagent ab7cd7cf DIED on an API error mid-compile:
  - **R5 ✅ SALVAGED** (control loop): subagent had cleanly parameterized the 4 drain procs into `genRaiseForkDrain(procName,field,gate,defectType,msg)` template but it didn't compile (died on it). Control loop fixed 2 compile bugs: (1) bare `{}` gate inferred `set[empty]` → added `const noArithGate: set[ArithCheck] = {}` (∅⊆arithChecks ⇒ vacuously-true ⇒ unconditional drain, the intended semantics — NOT a `when` guard); (2) the sibling `genSyncRaiseCond` template broke forward-decls (sync procs fwd-declared ~909-943; template procs can't satisfy fwd decls) → REVERTED that half, kept 4 explicit sync procs (only 6 lines each; the 230-line DRAIN dedup is the real R5 value). Verified compile+behavior-preserving BOTH backends: snd4(uncond), R16_3_divzero + R16_4_overflow(gated). NO SW bump (behavior-identical). Uncommitted in runtime.nim.
  - **R1 IMPLEMENTED but BLOCKED on a newly-discovered Critical** (subagent a155ad01 added drains at all 5 arms + tsymex_r1_draingap.nim + SW 60→61 + CR2 pin→61; targeted tests green). **Control-loop sweep (442 pairs) found 4 fails, both backends (NOT flakes):**
    - `tsymex_phase3_summarization` — SOUND CORRECTION: `helper(x)=x+1` (direct return) now correctly forks an OverflowDefect (default acOverflow), so its return survivor carries a defect-survivor fact → summarization cache-eligibility (runtime.nim:6483, "only cache a clean defect-free single return") correctly declines → walked==2/cacheHits==0. Pre-R1 cache-hit relied on the DROPPED overflow. Needs test migration (run under overflow-off settings to still exercise the cache, or assert the new sound stats).
    - `tsymex_q1_scanlift` Q1-4a — **FALSE POSITIVE (R1 unsound at isWhile):** `while i<s.len and s[i]==' '` now returns false `sxRaised(IndexDefect)`. Root cause CONFIRMED by probes: short-circuit `and` in IF-conditions IS desugared into guarded path-splits (isIf var-index bounded → sxSat, correct), but a WHILE-guard keeps `and` FLAT, so `s[i]`'s OOB is deposited UNGUARDED and R1's isWhile drain forks it even though real Nim short-circuits (`i<len` false ⇒ s[i] never read). Ubiquitous idiom (`while i<len and s[i]…`); mostly Q1-lifted, but unlifted forms (==/skip-while) hit it. Other 4 arms are fine (isReturn's drain even surfaced the legit overflow above).
    - **Corey chose: fix while-guard short-circuit properly (option A).** ROOT CAUSE (fully confirmed by probes, deeper than R1): a PRE-EXISTING SND-4 (v59) soundness bug — `rhsHasInlineDefectFork` (dsl_parser.nim:581) handles `iekStrAt` only by recursing into strArgs, never SELF-REPORTING true like `iekBinop{bDiv,bMod}` (line 549). So SND-4's `s[i]` OOB fork doesn't trigger D1c's short-circuit guard (dsl_parser.nim:1187-1219) → `A and s[i]` lowers as flat `bAnd`, OOB deposited UNGUARDED → false `sxRaised(IndexDefect)` for bounded `i<len and s[i]` whenever no reachable target masks it (proven: `if`/`let` forms with a tRaisedExn(IndexDefect) search both false-raise TODAY, pre-R1). R1 extended it to while-guards (q1_scanlift Q1-4a).
    - **THE FIX (delegated, subagent):** (1) `rhsHasInlineDefectFork`: `iekStrAt` self-reports `true` → D1c guarded path fixes if/let/assign/return (once-eval arms) immediately. (2) while-guard: when D1c preamble `wp` non-empty, restructure `wp; while cond: body` → `while true: wp; if not cond: break; body` so the guard (incl. D1c short-circuit) re-runs each iteration (also fixes a latent stale-sc for div/etc. in while-guards). Q1-lifted scans bypass (recognizer runs first). MUST keep: unbounded `while s[i]` STILL raises (real OOB). (3) migrate phase3_summarization (isReturn overflow sound-correction) — run its cache test under acOverflow-disabled settings so `x+1` stays clean+cacheable. SW stays 61 (part of R1 landing). Then control-loop FULL sweep.
    - **R1b landed (uncommitted) + completeness follow-up IN FLIGHT (subagent ad9502e0):** Part1 (iekStrAt+iekStrToInt self-report) + Part2 while-restructure done in the parseStmtInner while-arm (~2979); new tests/tsymex_r1b_shortcircuit_oob.nim (17 checks) + phase3 migrated (noOverflowSettings) + Q1-4a restored, all targeted green both backends. GAP found by control loop: the SECOND nnkWhileStmt arm (~2665, parseIterBodyStmt / while-in-for-body) still had the stale-hoist pattern → resumed subagent to extract a shared `mkGuardedWhile(cond,body,guardPre)` helper and route BOTH arms through it + add a while-in-for-body regression test. Then control-loop FULL sweep (prior sweep bufxwww9u was killed mid-run since the tree was about to change; also cleaned up ~8 orphaned sweep-waiters from earlier sessions).
    - **R1b COMPLETE (both arms, uncommitted).** Shared `mkGuardedWhile(cond,body,guardPre)` helper (dsl_parser.nim ~2591) routes BOTH nnkWhileStmt arms. Subagent made an autonomous design change (sound, control-loop reviewed OK): NOT `while true: guardPre; if not cond: break; body` (that blows up the path frontier when nested in another k-unrolled loop → hang at unwind=5), but a DO-WHILE LOOP ROTATION `guardPre; while cond: (body; guardPre)` — keeps a real SAT-able guard, composes under nesting. Correctness: the duplicated `let sc` is an env overwrite (flat env), refreshed sc flows to next guard check via body output paths — verified nested case both backends. tsymex_r1b_shortcircuit_oob extended with for-nested-while cases (run at maxLoopUnwind=3 — nested defect-guarded scans are inherently costlier now: the s[i] fork re-fires inner×outer). All targeted tests green both backends; SW stays 61.
    - **FULL SWEEP IN FLIGHT: `scratchpad/r1b_final_sweep.log` (background butlyabrg, 220s timeout, 442 pairs).** WATCH: a 137 (hang) on any existing test with a defect-guarded while nested in another k-unrolled loop at default unwind=5 — the soundness fix makes that shape correct-but-expensive; if one hangs, investigate (bump that test's unwind / accept / reconsider), do NOT wave through.
    - **RESUME after sweep:** tally r1b_final_sweep.log (438+ rc0; any 137 → investigate per above; any rc=1 → sound-correction vs regression analysis). If clean → commit R4 (fuzz.nim + tfuzzcorpus_nilguard.nim) separately, then R5+R1+R1b (runtime.nim + dsl_parser.nim + canonicalize.nim + CR2 pin + phase3 migration + tsymex_r1_draingap + tsymex_r1b_shortcircuit_oob) as one "R1 Critical + R5 refactor" commit (SW 60→61). Then fcsweep for R4. Then Wave 2: R2+R6 (dsl_parser.nim Q1 recognizer: reject loop-counter-dependent bound + sameSymbol; SW→62, rebased on committed R1) ∥ R3 (runtime.nim forkPath/forkPathTainted split, no SW bump). Ledger R1..R6 in the table above.
- **Wave 2 (after R1 lands, rebased on its SW):** R2+R6 (dsl_parser.nim: reject loop-counter-dependent bound + sameSymbol identity, SW→62) ∥ R3 (runtime.nim forkPath→forkPath/forkPathTainted split, no SW bump; disjoint files from R2).
- **RESUME:** await wave-1 subagent completions → review diffs (esp. did the 5-site drain flip any existing test = soundness correction vs regression?) → `scripts/psweep.sh` ONE both-backend sweep (watch [[sweep-waiter-self-match]]) → commit R4 and R1+R5 separately → launch Wave 2 → re-review changed scope (standing Security+Design agents too) → loop to floor (0 Crit/High/Med). Ledger below tracks status.

| id | sev | finding | status | proof / verifier |
|----|-----|---------|--------|------------------|
| R1 | CRIT | scalar-raise sinks (strIndexOob + parseInt/div/overflow) NOT drained at 5 walk arms; lowerInExpr resets sink on entry → silent discard → false sxSat past a real IndexDefect. **+ exposed a pre-existing (v59) short-circuit false-sxRaised: `A and s[i]` forked OOB unguarded (rhsHasInlineDefectFork didn't self-report iekStrAt/iekStrToInt); fixed via self-report + mkGuardedWhile do-while rotation on both while-arms (R1b).** | **FIXED c75285f** (SW 61) | drain at 5 arms + R1b short-circuit guard; tsymex_r1_draingap + tsymex_r1b_shortcircuit_oob; phase3 migrated (overflow-off); FULL sweep 444/444 both backends |
| R2 | CRIT | Q1 `tryRecognizeScanIdiom` accepts non-loop-invariant bound; closed form evals bound once at entry → `while i<(n-i)` mis-rewritten → witness divergence | **FIXED 4fea3da** (SW 62) | CONFIRMED a6aa79cd; refersToSym gate; tsymex_r2_scanbound RED sxSat→GREEN sxUnknown both backends |
| R3 | HIGH | `Path.uncertain` taint convention-based: forkPath bool 4th arg, ~45 sites; `forkPath(…,false)` silently drops taint → latent false sxSat | **FIXED 3428987** | forkPath/forkPathTainted + internal forkPathWithTaint; 45 sites (37 propagate/7 tainted/1 computed-bool); behavior-identical, no SW bump, sweep green |
| R4 | MED | fuzz.nim `dbActive` (gates on saveImpl only) drives loadCorpus/saveCorpus through un-nil-guarded new fields → minimal custom ExampleDatabase nil-crashes under fuzz() | fixed (uncommitted, fcsweep verifying) | gate on loadCorpusImpl/saveCorpusImpl own nil-ness; tfuzzcorpus_nilguard RED=SIGSEGV→GREEN both backends |
| R5 | MED | raise-fork drain family = 4 near-identical templates (SND-4 added 4th verbatim) → parameterize `genRaiseForkDrain` | **FIXED c75285f** | genRaiseForkDrain template + noArithGate const; behavior-identical both backends (folded into R1 commit) |
| R6 | MED | Q1 recognizer identifies "same var" by `.strVal` not symbol identity → template/gensym mis-match | **FIXED 4fea3da** | sameSym (macros.== on nnkSym) at 3 recognizer sites |

**✅ ALL 6 mandated findings (R1-R6) FIXED + committed** (c75285f R1+R5+R1b · 46b0ac3 R4 · 3428987 R3 · 4fea3da R2+R6). Wave-2 combined sweep 445/446 (1 c-only z3_infra parallel-load flake cleared standalone). Working tree clean; stale stash@{0} dropped.
**RE-REVIEW ROUND 1 RESULTS:** security CLEAN, design CLEAN (2 Low polish), correctness found **R14 (CRIT, introduced by R1b)**: mkGuardedWhile do-while rotation is NOT continue-safe — trailing guardPre (guard refresh) is skipped when body hits `continue` (walkBlock stops on the zero-path return) → stale `sc` → false verdict. CONFIRMED by probe (fCont continue-loop gives sxUnknown, real Nim sxSat). 2nd subtle failure of the parse-time rotation approach.
**✅ R14 FIXED + COMMITTED 98f4564 (SW 62→63).** Full sweep 447/448 (1 c-only z1_canary parallel-load flake cleared standalone); new tsymex_r14_continue_guard 10/10 + all R1b/Q1/R2/snd4/draingap green both backends. Control loop reviewed mkShortCircuitWhile dispatch + hasContinueShallow as sound.
**✅ RE-REVIEW ROUND 2 DONE — FLOOR REACHED (0 Crit/High).** correctness (a99fdc4c): R14 mechanism verified sound (continue-safe by construction, break/nesting correct, `continue` is the only hazard); one MEDIUM = Case-2 sound over-degrade (`while (a div b)>i and s[i]` + continue → sxUnknown via degrade because LHS hoists a no-op artifact preamble so `preA.len==0` gate misses it; NEVER a wrong verdict — Inv-3 holds; recommended+accepted as sound Low, don't do a 5th while-guard revision). design/security (a11b78c8): CLEAN; one Low = hasContinueShallow dups hasBreakContinueShallow.
**Corey chose: FLOOR + BATCH THE SAFE LOWS.** Low-cleanup batch IN FLIGHT (subagent a16028e1, NO version bump — all behavior-identical/doc/test): (1) hasContinueShallow+hasBreakContinueShallow → shared hasKindShallow (dsl_parser); (2) genRaiseForkDrain gate set→Option[ArithCheck], drop noArithGate (runtime; fallback = fix stale `card` comment if static Option won't compile); (3) svIntToBV doc fix (parseInt negative ok via mod-2^W); (4) NEW tsymex_r14_case2_degrade pinning the sound degrade; (5) coverage.nim registerEdgeSource/edgeSources internal-doc note; (6) db multiplexedDatabase carry secondary meta when primary meta empty.
**BATCH DONE (subagent a16028e1, all 6 items, uncommitted, no SW bump). Symex sweep 450/450 CLEAN (bzrjx9yss); fcsweep running (bqi69ivoi).** Item 2 took the Option[ArithCheck] path (compiled clean, noArithGate deleted). **RESUME: tally fcsweep → if clean `git add` the 5 batch files (dsl_parser.nim, runtime.nim, coverage.nim, db.nim, tests/tsymex_r14_case2_degrade.nim) + commit `refactor+docs(symex,fuzz): batch low-severity code-review cleanups (hasKindShallow, Option gate, docs, meta-fill, case2 pin)` → update ledger to CLOSED → report final /code-review outcome to Corey. THEN the whole /code-review is COMPLETE (floor reached, all Crit/High/Med fixed, safe Lows batched, R7/R8/R11 tracked follow-ups).**
**TRACKED FOLLOW-UP LOWS (deliberately deferred, not in batch):** R7 Q1 AST-unwrap dup→unwrapHidden · R8 P2a omitted-non-scalar→weInternalWalkerFault telemetry hygiene · R11 C1 edgeSourceTable unguarded-global/redundant-reregister · Case-2 precision (inert-preamble detection, if ever wanted).
**[impl detail] R14 FIX IMPLEMENTED (subagent ad1221c0):** dispatch reviewed sound by control loop — mkShortCircuitWhile: Case1 clean and-split (continue-safe by construction) / Case1b flat / Case2-3 rotation-if-continue-free ELSE sound mkUnsupported degrade / Case4 plain mkWhile (incl. unbounded `while s[i]` still raises). hasContinueShallow verified correct (stops at nested loops + routine boundaries). mkGuardedWhile DELETED. SW 62→63, CR2 pin 63, r1b `==` pin converted to `>=` floor (only CR2 is live == pin now; the 4 other grep hits are `##` comment prose). Subagent self-caught + fixed an over-degrade (nnkStmtListExpr artifact preamble ≠ fault; gated on continue not preamble-shape; regression caught by tsymex_r1_draingap whileDivZero). New tsymex_r14_continue_guard 10/10 + all R1b/Q1/R2/snd4/draingap re-run green both backends (targeted). **RESUME: tally r14_sweep.log (446+ pairs; verdict flips = sound-correction analysis; commit R14 as its own fix commit SW 62→63) → then re-review ROUND 2 on the R14 diff (Step 7 loops till clean) → floor = report Lows.**
**[superseded detail] R14 FIX (Corey: "best-in-class design"):** replace mkGuardedWhile with FAITHFUL short-circuit desugaring at the loop level: `while (A and B): body` → `while A: (Bpre; if not B: break; body)`. B (with its s[i] fault) lowers INSIDE the body where guard A holds → the OOB fork is `pc∧oob=(i<len)∧(i≥len)`=UNSAT, guarded FOR FREE by loop semantics (no sc temp, no D1c-for-while). continue-safe by construction (continue re-checks A + re-runs Bpre at top); no blowup (A is a real SAT-able guard, not `while true`); handles hoisted stmts. or-with-fault/nested → sound mkUnsupported degrade (Inv-3). Deletes mkGuardedWhile. SW 62→63. New tsymex_r14_continue_guard; also converts the stray tsymex_r1b `==` pin to a `>=` floor. Then control-loop FULL sweep + ANOTHER re-review round (the fix changes code → re-review again per Step 7).
**RE-REVIEW ROUND 1 (Step 7 termination check) — done, reopened by R14:** 3 agents (correctness a7ec8401 / design a97d14f6 / security a1111c6e) on `git diff 485eced HEAD -- src/`, hunting bugs the FIXES introduced (hardest look: mkGuardedWhile do-while rotation's duplicated `let sc`; 5-arm drain survivor threading). If nothing above Low → floor hit → report Lows + stop. Any Crit/High → adversarial-verify, fix, re-review again.
**Remaining Lows (from initial review, deferred per mandate):** R7 Q1 AST-unwrap dup→unwrapHidden · R8 P2a omitted non-scalar→weInternalWalkerFault telemetry hygiene · R9 coverage.nim public-surface leak · R10 svIntToBV doc comment wrong · R11 C1 edgeSourceTable unguarded/redundant-reregister · R12 multiplexedDatabase drops secondary meta on collision · R13 F2 seed-replay coverage-credit (wontfix). Plus tiny cleanup: tsymex_r1b uses a 2nd `==` SW pin (should be `>=` floor per convention).
| R7 | LOW | Q1 AST-unwrap idiom duplicated ~10× inline → unwrapHidden helper | **fixed** | aab18ce — unified 10 blind-peel sites into `unwrapHidden`; subtle ref/ptr-deref sites deliberately left; pure refactor, no SW bump; sweep 452/452 both backends |
| R8 | LOW | P2a omitted non-scalar field → mkIntLit(0) mismatch → caught ValueError → sxUnknown (NOT a crash) but pollutes weInternalWalkerFault telemetry; classify at construction | **fixed** | aab18ce — kind-correct `unsupportedFieldPlaceholder`; verdict stays sxUnknown (taint owns it), only error KIND cleaned; new tsymex_r8_omitted_field_degrade.nim; no verdict/witness flip → no SW bump |
| R9 | LOW | coverage.nim exports macro-plumbing procs (registerEdgeSource/edgeSources) beside the one real entry point uncoveredSources | **fixed** | 9be7b5a — kept exported (tcovsourcetable.nim uses them directly; macro uses bindSym so export not needed for it); corrected the inaccurate doc rationale |
| R10 | LOW | svIntToBV doc comment "always non-negative" false for parseInt("-5"); mechanism sound (int2bv mod 2^W) — doc fix | **fixed** | 7c3a16d (Low batch) — doc corrected |
| R11 | LOW | C1 edgeSourceTable unguarded global + redundant per-eval re-registration | **fixed** | 9be7b5a — documented single-threaded-by-contract + idempotent set-merge invariants on the global; no lock/guard added (dead weight); doc-only |
| R12 | LOW | multiplexedDatabase drops secondary backend metadata on choice-seq collision (db.nim:658-664) | **fixed** | 7c3a16d (Low batch) — secondary meta carried forward when primary meta empty |
| R13 | INFO | F2 up-front seed-replay credits a crashing seed's coverage without surfacing in irCrashes (documented intentional) | wontfix | fuzz reviewer |

**Verified CLEAN:** DB v2→v4 parse (bounds-checked, safeLen 64MiB cap → DbCorrupt); Z3 FFI lifetimes; heap-snapshot 2-axis recursion bound; cache-key distinctness (3-arg find/assume/tupleLit) + full version-pin discipline; SND-1/SND-3/Cluster-H taint+chokepoints; Q1 start-offset threading; corpus channel independence; metadata stickiness; collision honesty; no exploitable security findings.

**Synthesis:** R1 (live) + R3 (latent) + R5 (duplication) are three faces of ONE root flaw — soundness-critical per-path bookkeeping threaded by site-local convention with no structural enforcement. Fixing R1 via a central per-statement drain chokepoint + R5 parameterization + R3 forkPath split = one systemic close, not three patches.

---


- **Stage:** 3 (tdd grind) — **AUTONOMOUS GRIND COMPLETE 2026-07-26; then Q1 spike + SND-3 soundness fix (post-grind, with Corey)**   •   Architect rounds 1&2 done
  - **✅ SND-3 (finding-B fix) LANDED `5dd965a`** (SW 57→58, RC stays 7; full symex sweep 436/436 both
    backends — the two augmented_assign pairs that hung under accidental 3×-concurrent-sweep contention
    re-verified passing STANDALONE; new test 8/8 both backends). New soundness slice (NOT in original
    RFC — surfaced by the Q1 spike). Fixed the C-backend false `sxUnsat`. Subagent
    `a2b5d4dce3ec39bd9` implemented (detached on sweep, 14th stall); control loop verified independently
    + swept + committed: runtime.nim mechanism = in-band degrade at 3 loop-reachable lowering raise-sites
    (CR-17(a) char-ordering, cmpString string-ordering, iekContains non-int64-set membership) →
    threadvar sinks (`loweringDegradeErrors`/`loweringDidDegrade`) → per-path `uncertain` taint at
    `drainPendingLowerEffects` (fork-before-mutate) + `w.sawUnknown` + dedup-drain into errors. NOT a
    bare sawUnknown (would fabricate false sxSat — the crux). Left `allocateSym` param-alloc raises
    (safe, pre-walk). SW 57→58, RC stays 7, CR2 pin→58. ADR-0023 + RFC SND-3 row added.
    New `tests/tsymex_snd3_loopdegrade.nim` 8/8 BOTH backends (tracer + per-path-no-false-sxSat trap +
    no-over-degrade + non-loop regression + classified-kind + equality regression). probe5778
    (walk-arm Table raise) showed NO divergence → not an additional hole. **RESUME: tally
    `scratchpad/snd3_sweep.log` (via `scratchpad/psweep.sh`, expect 436=218×2 all rc0; re-verify any
    lone c rc=1 standalone), then `git add -A` (runtime.nim, canonicalize.nim, CR2 pin, RFC.md,
    SYMEX_PLAN.md, new test — NOT scratchpad/NOT handoff) + `git commit --no-verify` "feat(symex):
    SND-3 — loop-guard lowering degrades taint in-band (fix C-backend false sxUnsat)".**
  - **DECISION (Corey 2026-07-27): build Q1 + finding A together.** Sequenced A→Q1 (SW-bump
    serialization: both bump SW + touch CR2 pin; AND Q1's scan-then-OOB test depends on A's IndexError
    modeling).
  - **✅ SND-4 (finding A) LANDED `39953ff`** (SW 58→59, RC stays 7; full symex sweep 438/438 both
    backends = 219 files ×2; new test 6/6 both backends). Subagent `a14135c5fe7db76ef` implemented
    (detached on sweep, 15th stall); control loop verified + swept + committed. **Control loop caught +
    fixed an unmigrated flip the subagent's detached sweep missed:** `tsymex_snd2_assume` flipped
    sxUnsat→sxRaised because its SUT indexed `s[0]` on a FREE string (`s==""` → real reachable
    IndexDefect, which SND-4 correctly now forks → sxRaised dominates sxUnsat per D1a). This is a genuine
    soundness catch, NOT a regression — migrated the unreachable condition to `s.len==3 and s.len==4`
    (no OOB, preserves the symexAssume-masking test intent). S3 `s[5]` test also migrated (→sxRaised).
    ADR-0024. Mechanism below:
  - **[landed, detail]** SND-4 (finding A). String char index reads
    (`iekStrAt`, `runtime_strings.nim:114-127`) have ZERO IndexError modeling (OOB silently returns
    0xFF per its own comment) → `tIndexError()` over `s[i]` falsely returns sxUnsat. FIX: mirror the
    parseInt/divByZero lowering-sink→drain-fork-raise machinery (new `strIndexOobConds` sink +
    `syncStrIndexOobCond` + `drainStrIndexRaises` folded into `drainScalarRaiseForks`; deposit
    `oob=(i<0 or i>=len)` in iekStrAt lowering, fork IndexDefect at the drain — NOT a fork from
    lowering, the SND-3 anti-pattern). Continuing path gains `not oob` (may migrate string-index
    tests — bounds corrections). SW 58→59, RC stays 7, CR2 pin→59. New ADR (after 0023) + RFC SND-4
    row. **RESUME: verify subagent (tracer sxRaised, scan-then-OOB A4 repro sxRaised, bounds-safe
    sxUnsat, migrations sane), ONE clean psweep 436/436 both backends, commit if subagent didn't.**
  - **✅ Q1 LANDED `260267d`** (subagent self-committed after its stall cleared; SW 59→60, RC stays 7,
    CR2 pin 60, ADR-0025). **🎉 Q1+A PAIR COMPLETE.** Control loop verified: Q1 test 13/13 (subagent
    counts 15 incl. version pins) both backends; SW/pin/ADR confirmed in committed tree; E5_finally +
    the other 4 exception-test 137s from the sweep = -P6 contention flakes, re-verified rc0 standalone
    (subagent + control loop). Full sweep 440 pairs, 435 rc0 + those 5 flakes cleared; an earlier
    control-loop partial reached 291/438 clean independently. **No final full clean re-sweep run** —
    convergent evidence (partial-clean + Q1 green + flakes-cleared) deemed sufficient for a doc/verify
    close; if belt-and-suspenders wanted, run `scratchpad/psweep.sh <log> 200` ONCE (host is slow —
    ~30s/compile; watch [[sweep-waiter-self-match]]). Implementation detail below:
  - **[landed, detail]** Q1. SW 59→60, RC stays 7, CR2 pin→60,
    ADR-0025 + RFC Q1 row updated to LANDED. **New `tests/tsymex_q1_scanlift.nim` 13/13 BOTH backends**
    (control loop ran standalone): P1a/b (3-arg find honors start + UNSAT companion), Q1-1 tracer scan
    lift sxSat +Q1-1b UNSAT clamp companion, Q1-2 chained/dependent scan +Q1-2b UNSAT (j<i impossible),
    Q1-3 scan-then-OOB sxRaised (end-to-end w/ SND-4), Q1-4a/b/c scope trip-wires (==-guard, char-class,
    non-inc body all stay sxUnknown → recognizer proven NARROW), Q1-5 plain loop still k-unrolls.
    Mechanism (control loop reviewed): `tryRecognizeScanIdiom` (dsl_parser.nim) called in BOTH
    nnkWhileStmt arms before mkWhile; matches `while i<bound and s[i]!=lit: inc i` (validates every
    node's type/sym identity; handles `!=`→not(==) desugar; body exactly inc/+=1), emits closed form
    `i = (let p=s.find($lit,i); if p==-1 or p>=bound: bound else: p)`; ANY mismatch → mkWhile untouched.
    3-arg `iekStrFind` (optional strArgs[2] start → nim-z3 `indexOf(a,sub,start)`), cache-key distinct
    (canonicalize renders all strArgs), ALSO fixed a latent start-drop unsoundness. **Sweep status
    2026-07-28:** a partial sweep reached 291/438 CLEAN (only augmented_assign cpp 137 = known
    load/contention flake, passes standalone) before a self-perpetuating waiter orphan
    [[sweep-waiter-self-match]] confounded process-counting; killed all, RE-RUNNING one clean sweep →
    `scratchpad/q1_sweep2.log` (200s/test). **RESUME: tally that log** (438=219×2 all rc0; re-verify any lone non-zero standalone), then
    `git add -A` the 7 changed/new files (dsl_parser.nim, runtime_strings.nim, types.nim,
    canonicalize.nim, CR2 pin, RFC.md, SYMEX_PLAN.md, tests/tsymex_q1_scanlift.nim — NOT scratchpad,
    NOT handoff, NOT the stray tests/probe_q1 binary [already rm'd]) + `git commit --no-verify`
    "feat(symex): Q1 — lift bounded scan-to-delimiter loops to closed-form indexOf".** That COMPLETES
    the Q1+A pair. Then only INT-1 (blocked on release) → Stage 4 /code-review.
  - **[SUPERSEDED — Q1 done above]** Q1 QUEUED after SND-4 (rebase on SW 59→60). GREEN/buildable per spike. Core: (1) proper
    3-arg-find IR path (distinct kind + parser arity dispatch, NOT the spike's `iekStrFind` strArgs
    overload trick — nim-z3 `indexOf(a,sub,start:Z3Int)` @ sequence.nim:180 already exists) + (2) the
    idiom-RECOGNIZER at the `nnkWhileStmt` parse site (`dsl_parser.nim:2498`/`2805`): match
    `while i<bound and s[i]!=lit: inc i` (single + dependent chains) → rewrite to `indexOf(s,lit,start)`
    closed-form instead of mkWhile k-unroll. Scope LOCKED to literal/substring delimiter scans; predicate/
    char-class scans stay degraded (Phase-C boundary). Headline test = scan-then-OOB found (needs SND-4).
  - **After Q1:** INT-1 (blocked on release) is the last item; then Stage 4 `/code-review`.
  - **✅ CLUSTER H COMPLETE (2026-07-25):** named ref-object HEAP IDENTITY fully delivered.
    A `d85f0f7` (nominalId) → B `ddc9196` (refPointeeTypeId) → C `40ed16f` (heap identity: aliasing/
    identity real verdicts) → H_containers `5f4639c` (seq/array/tuple of Node) → H_witness `2244d1b`
    (recursive cycle-safe heap-snapshot) → closeout `46c7b80` (verification + ADR-0022 marked LANDED).
    Final versions **SW 57, RC 7**; 432/432 both backends. No bugs found in verification. Supersedes
    P2b value-model `42eafde`. **NEXT: base clusters Q → TOT → INT → F → C** (see slice order below).
  - **✅ TOT-1 LANDED `85603f5`** (test+cfg only, no version bump): 9-item table-driven §0-totality
    corpus across the 3 open surfaces (CR-2a parser catch-all; CR-2b/2c type+witness classifier;
    SND-1/1b/CR-1c taint+fault), each asserted to degrade to a CLASSIFIED sxUnknown. Backstop VALIDATED
    (reverting SND-1's taint made the corpus fail → restored; control-loop confirmed the revert did NOT
    leak into the commit — runtime.nim byte-identical vs 46c7b80). Documents historical repros excluded
    as now-modeled (&=→M4, if-expr→M5, bitwise→CR-1a). 434/434 (lone phase13_macro c flake re-verified
    standalone). No §0 blocker found.
  - **🎯 MILESTONE: the entire soundness/crash-totality/model-gap/parser/heap-identity/totality CORE of
    the mega-RFC is COMPLETE and green.** Landed: Clusters 1-4 (SND-1/1b, SND-2, CR-1a/b/c, CR-2a/b/c,
    M1-M6, P1, P2a) + Cluster H (P2b heap-identity, 6 slices) + TOT-1. **REMAINING work splits:**
    (a) **needs-Corey / non-autonomous:** INT-1 (chapulin pin-bump + workaround removal — cross-repo
    exit gate, external `/mnt/c/.../chapulin` repo + its harness; the recurring per-SW-slice smoke runs
    were NOT done during the grind, so this is a batch exit-gate now); Q1 (dependent-bounded-loops
    research SPIKE, may have no viable encoding); SH1 (does-not-repro-at-HEAD, deferred pending
    chapulin's exact repro). (b) **decoupled autonomous-able Fuzz/Coverage track (lower-stakes polish,
    do NOT gate on soundness):** F1 (L, non-pruned coverage-corpus channel), F2 (M), F3-F5/F8 (S),
    F6/F7 (M), C1 (L, slot→file:line:col side-table), C2 (S doc-only).
  - **DECISION (Corey, 2026-07-26): grind the F/C decoupled track.** INT-1/Q1 deferred for deliberate
    handling with Corey. **F1 IN FLIGHT** (subagent `afd4941f8af443a66`): non-pruned coverage-corpus
    channel separate from dbReusePhase's prune-on-pass (engine/phases.nim + db.nim + fuzz.nim). Fuzz/DB
    subsystem — NO symex version-pin obligation. Regression gate = the tdb*/tfuzz*/tcov*/tengine suite
    both backends. Order after F1: F2 → F3 → F4 → F5 → F6 → F7 → F8 → C1 → C2.
  - **✅ F1 LANDED `422869a`:** dedicated never-pruned `corpus` DB section (3rd alongside primary/
    secondary), saveCorpus/loadCorpus, on-disk format v2→v3 w/ backward compat; fuzz.nim persists there
    (not primary). tfuzzpersist migrated (loadPrimary→loadCorpus); new tfuzzcovcorpus proves pass/reject
    retained-in-corpus-but-pruned-from-primary + channel independence + round-trip. 46/46 real
    fuzz/db/cov/engine tests both backends. **F/C-track regression gate helper: `scratchpad/fcsweep.sh
    <log> [timeout]`** (globs the 23 real tdb/tfuzz/tcov/tengine .nim sources, both backends — do NOT
    hand-list DB test names: `tests/tdbgc*`/`tdbg_e4a*` are STRAY GITIGNORED BINARIES, not sources).
  - **✅ F2 LANDED `dd0f14d`:** up-front coverage-replay of preloaded seeds (fuzz.nim, `preloadedCount`
    guard excludes the fallback seed → no-seed path unchanged; reuses newReplaySource→generate→run;
    frontier.admit up front). New tfuzzseedcov (7). 48/48 both backends.
  - **✅ F3 LANDED `eb09f70`:** exported `minimalCovering*` (pure export, no behavior change). New
    tfuzzmincover (3, greedy set-cover pins). Both backends.
  - **✅ F4 LANDED `3562ff8`:** `FuzzSettings.stopOnFirstCrash` (default false); break in the generic
    `fuzz()` crash-recording block gated on `isNewCrash = not seenCrashKeys.containsOrIncl(key)` (first
    NEW de-duped crash; byte-mode `fuzzWithBytes` has no de-dup → out of scope); post-loop bookkeeping
    (minimizeCorpus/iterations/coverageHits) preserved. New tfuzzstopcrash (6). 52/52 both backends.
  - **✅ F5 LANDED `01fb3a8`:** doc-only — documented `dedupPrepend`/`applySave` newest-first
    insertion-order contract (prepend@0, truncate TAIL→evict-oldest, re-save moves to front, reload =
    reverse-insertion order which dbReusePhase relies on). Order already pinned by tdb.nim (20/20).
  - **✅ F6 LANDED `0307b3d`:** per-primary-entry metadata slot — `PrimaryEntry` tuple +
    `Table[string,string]` meta (mirrors secondary's label table, string-valued for witnesses; FUZZ_PLAN
    defines no payload → bare extensibility slot, goal-determined by precedent). Format v3→v4 backward
    compat (v1-3 read empty, upgrade on write; parseContents now lists v3 explicitly). API additive:
    `save(...,meta)` overload + `loadPrimaryWithMeta`; `save`/`loadPrimary` unchanged. Sticky dedup
    (plain re-save preserves meta; explicit non-empty meta overwrites). New tfuzzprimarymeta (15). 54/54
    both backends. **6 F-slices done (F1-F6).**
  - **✅ F7 LANDED `d1a431d`:** documented the 2N+1 choice-IR draw protocol on the lists combinator
    (N+1 continue-gates interleaved with N element draws; nested strategies recurse) + added
    `FuzzReport.droppedSeeds` (counts PRELOADED seeds — initialIRCorpus + DB loadCorpus — that fail
    captureIR; fallback random seed doesn't count). New tfuzzdroppedseed. Green both backends (lone
    tfuzzloop c sweep failure = parallel-load flake, re-verified passing standalone). **7 F-slices done.**
  - **✅ F8 LANDED `ee70ce0`:** `sectionSizes(db, testId): tuple[primary, secondary, corpus: int]` —
    thin wrapper over load* counts (all backends, no new plumbing). New tfuzzsectionsize (7). Green both
    backends (tfuzzdroppedseed/tfuzzstopcrash c sweep failures = parallel-load flakes, re-verified
    standalone). **✅ ALL 8 FUZZ SLICES DONE (F1-F8).**
  - **✅ C1 LANDED `5da1e20`:** slot→`file:line:col` side-table at `{.cover.}` expansion. The pragma
    hashed each branch's `(file,line,col)` into the 8192-slot bitmap and discarded the location; C1
    emits the other half — a module-global (NOT threadvar — static program structure) `Table[int,
    OrderedSet[string]]` slot→locations populated at expansion, plus `registerEdgeSource`/`edgeSources`/
    `uncoveredSources` (the source-mapped gap report: registered slots whose bitmap byte is 0, ascending
    slot order). Collisions handled honestly (OrderedSet; slot reads covered iff any colliding loc hit),
    NOT disambiguated. proc/func emit regs as sibling stmts; lambdas wrap regs+lambda in nnkStmtListExpr
    (no `newStmtListExpr` convenience in std/macros → built via `nnkStmtListExpr.newTree`). NO version
    pins (leaf module, not symex, not DB-persisted). New tests/tcovsourcetable.nim (7). Both backends
    GREEN; control loop independently ran tcovsourcetable+tcoverage+tcoveragemode+tcovguided ×2 (all rc0);
    subagent fcsweep 60/60.
  - **✅ C2 LANDED `a2ab210`:** doc-only — module-header note "Why 8192, and how it converges (#C2)":
    power-of-2 for `and`-mask + contiguous 8KiB + hash-pure slot (no global counter); occupancy
    `M·(1−e^(−E/M))`, collision-free only while `E ≪ √M≈90`, converges toward M as E→M; `currentCoverage`
    is a monotone LOWER bound + colliding edges indistinguishable; non-issue at proptest per-SUT scale;
    **C1's side-table (not a bigger map) is the lever** that makes collisions visible/nameable. Pure
    additive comments (34 insertions), compiles clean both backends. Documentation DoD.
  - **🏁 ENTIRE AUTONOMOUS-ABLE RFC COMPLETE.** All of Clusters 1–4 + H + TOT-1 + F1–F8 + C1–C2 landed
    and green. **ONLY INT-1 + Q1 REMAIN — BOTH STRUCTURALLY NEED COREY, NOT the /loop:**
    (a) **INT-1** = chapulin cross-repo exit gate: build + smoke-run the EXTERNAL `/mnt/c/Users/corey/
    projects/chapulin` repo + its harness against hardened proptest, then remove chapulin's workarounds +
    bump its proptest pin. The per-SW-slice smoke runs were deferred during the grind, so this is a BATCH
    exit-gate now. Cannot run in an unattended /loop (drives another repo). (b) **Q1** = dependent
    bounded-loops research SPIKE (Solver, L); RFC says it "may have no viable sound-and-fast encoding" and
    "names no candidate encoding" → may dead-end with nothing committable; poor unattended fit — handle
    deliberately with Corey. **SH1 deferred** (does-not-repro-at-HEAD; needs chapulin's exact repro/bisect).
    **LOOP STOPPED here (2026-07-26) — the grind is done; INT-1/Q1 are a deliberate, with-Corey decision,
    not a next /loop iteration.** Original F7-cluster line: (choice-IR
    2N+1 draw-order protocol doc + surface `captureIR` dropped-seed count in FuzzReport,
    `strategy.nim:451-480`+`fuzz.nim:262-277`, M) → F8 (corpus section-size introspection helper,
    `db.nim:83-101`, S) → C1 (slot→file:line:col side-table at {.cover.} expansion,
    `coverage.nim:85-88`, L) → C2 (doc-only: 8192-bitmap convergence, `coverage.nim:23`, S).
    **F/C regression gate: `scratchpad/fcsweep.sh <log> [timeout]`** (globs real tdb/tfuzz/tcov/tengine
    sources both backends; NEVER hand-list — `tests/tdbgc*`/`tdbg_e4a*` are stray gitignored BINARIES).
    Trivial doc/export S-slices done inline; M/L slices delegated to sonnet subagents.
    **After F/C: INT-1 + Q1 remain (both NEED Corey — external chapulin repo / research spike).**
  - **⚠ Q1 REORDERED AFTER TOT (control-loop judgment, note for Corey):** Q1 (dependent bounded
    loops, Solver, size L) is a **timeboxed RESEARCH SPIKE** the RFC says "may have no viable
    sound-and-fast encoding" and "names no candidate encoding" — a poor autonomous-grind fit (may
    dead-end with no committable slice). RECOMMEND handling Q1 deliberately (likely with Corey) rather
    than in an unattended /loop iteration. Doing TOT-1 (high-value, buildable, all deps met) first.
  - **H_containers LANDED `5f4639c`** (SW 57, RC 6; 428/428 both backends; storeSeqElem itRef arm +
    iteSV svRef un-stub for array indexing; Table/HashSet stay degraded).
  - **H_witness LANDED `2244d1b`** (RC 6→7, SW stays 57; recursive cycle-safe heap-snapshot;
    430/430 — the lone `phase12_sink` cpp sweep failure was a parallel-load compile flake,
    control-loop re-verified GREEN standalone [trivial import-smoke test, touches zero heap/witness
    code]). Two support fixes surfaced: emitIRType `isPlaceholder` round-trip (dsl_parser),
    emitTyAndReader itSeq `nameIsRefAlias` special-case (symex). **H_verification+H_final closeout CODE-COMPLETE but
    UNCOMMITTED** (subagent `afc32c9dd9dfd7c9a`): TEST+DOC ONLY — new `tests/tsymex_h_verification.nim`
    (identity transitivity +UNSAT companion, mixed param↔constructed-node aliasing, nil edges,
    variant field-access exclusion [precisely: single-axis itVariant read SUPPORTED, MULTI-axis
    itMultiVariant read EXCLUDED via heRefVariantUnsupported], deep-chain verdict) + `docs/SYMEX_PLAN.md`
    ADR-0022 "Cluster H LANDED" status note. **NO production code, NO version bump** (SW 57, RC 7
    unchanged); **no bug found** (verification passed — Cluster H sound). Full sweep running →
    `scratchpad/sweep_hverification.log` (waiter `blc3hh3pe`); as of last check ~349/432, lone failure
    `phase14_b2_forcephases` cpp — a parallel-load compile flake (this slice touches ZERO production
    code so cannot regress phase14). **RESUME: confirm sweep 432/432 (re-run any lone cpp rc=1
    standalone to confirm flake — `scripts/dt-bounded.sh cpp tests/<file> 240`), then `git add -A`
    the new test + SYMEX_PLAN.md (NOT scratchpad/, NOT handoff) and `git commit --no-verify`
    "test(symex): Cluster H verification + closeout — aliasing/identity/nil/variant edge cases".**
    That CLOSES Cluster H. Then base clusters Q/TOT/INT/F/C.
  - **[SUPERSEDED — H_witness landed]** H_witness IN FLIGHT (subagent `a62841603bee24ed1`): recursive pointsTo, ADR-0010 inv#4 —
    buildHeapSnapshot/pointeeRendering descend into ref-typed fields + container elements bounded by
    maxHeapDepth, cycle-safe via visited-set. Code WRITTEN + UNCOMMITTED (runtime.nim, types.nim
    [HeapSnapshotEntry format], new `tests/tsymex_h_witness.nim`); **RC 6→7, SW STAYS 57** (witness-only,
    verdicts unchanged); CR2 pin set (SW==57, RC==7). Full sweep NOT yet run at last check. **RESUME:
    if subagent didn't finish — confirm the new witness test GREEN both backends (esp. the CYCLE
    termination test: a ring/self-cycle must not hang), run full sweep both backends (expect ~430=215×2),
    then commit "feat(symex): Cluster H H_witness — recursive heap-snapshot witness (ADR-0010 invariant #4)".**
    Then verification → H_final, then Q/TOT/INT/F/C.
  - **[SUPERSEDED — H_containers landed]** In flight: Cluster H **H_containers CODE-COMPLETE but UNCOMMITTED** (subagent
    `a5f795775ca45f18c`). Diff: `runtime.nim` two arms — (1) `storeSeqElem` itRef/itPtr (raw
    `Z3_mk_store` into the `Z3Array[Z3Int,Ref_T]` for seq[Node] literals) + (2) `iteSV` svRef/svPtr
    un-stub (value-level `Z3_mk_ite` over two same-sort Ref_T addresses — needed for array[N,Node]
    INDEXING, discovered via RED test) — plus `canonicalize.nim` SW 56→57 (RC STAYS 6, seq elem
    witness is the pre-existing length-only R3 stub) + CR2 pin (SW==57) + new `tests/tsymex_h_containers.nim`
    (seq/array/tuple-of-Node real sxSat each w/ load-bearing UNSAT companion; Table/HashSet stay
    sxUnknown guards). array[N,Node]/tuple[a:Node] were already structurally reachable (only indexing
    + seq-literal-store needed code). Diff reviewed clean. Full both-backends sweep running →
    `scratchpad/sweep_hcontainers.log` (waiter `beiz81w24`); as of last check ~301/428, 0 failures,
    **all ref/heap regression tests green (r5/r6/r7/r9/r10/r11/r11b/rectify) — iteSV un-stub did NOT
    regress**. **RESUME: confirm sweep 428/428 both backends (all rc=0), then `git add -A` the 3 changed
    files (runtime.nim, canonicalize.nim, CR2 pin) + new tsymex_h_containers.nim (NOT scratchpad/) and
    `git commit --no-verify` "feat(symex): Cluster H H_containers — seq/array/tuple of named ref-objects".**
    After it lands: **H_witness** (recursive pointsTo, ADR-0010 inv#4) → verification → H_final, then
    Q/TOT/INT/F/C.
  - **Pause state:** autonomous /loop STOPPED (no wakeups armed). **Step C (atomic H1) LANDED
    `40ed16f`** — named ref-object HEAP IDENTITY: classifyType flip (both nnkObjectTy + nnkSym
    branches → itRef) + real mkNewT+mkFieldDerefWrite construction + universal isNew zero-write
    + witness provenance flag + isHeapRef/isRecursionPlaceholder + 3 carve-outs deleted +
    buildHeapSnapshot for named-alias svRef params; **SW 55→56, RC 5→6**; CR2 pin both. Full
    sweep **426/426 both backends**. Migrated (re-derived): p2b (P2b-9/10 flip), r9/r10/r11b,
    and **r6 test 3 — an UNTRACKED regression the ADR's "5-test" impact list missed** (Corey
    approved the migration): local `new(T)` fields now zero-init (Nim-faithful), so a write
    through p is NOT observable through a distinct fresh q (`q.x==42` unsat) — the pre-Step-C
    free-field model asserted `q.x==7` reachable, an UNSOUND false-SAT the zero-write corrects.
    Verified by probe: `q.x==0` sat + `q.x==42` unsat = genuine zero-init, no aliasing bug.
    New flagship `tests/tsymex_h_stepC_heapidentity.nim` (aliasing sxSat + load-bearing UNSAT
    companion, identity, sym-indirection, zero-field Token). **REMAIN STOPPED.** To resume the
    grind (**H_containers** [storeSeqElem itRef arm for seq[Node] literals + seq/array/tuple
    tests; own SW bump] → **H_witness** [recursive pointsTo, ADR-0010 inv#4] → verification →
    H_final, then Q/TOT/INT/F/C): re-run the `/loop` command below. Do NOT auto-start new
    slices until re-invoked.
- **Resume:** The autonomous grind is COMPLETE — do NOT re-fire /loop expecting more slices (it
  would find nothing implementable unattended). Only **INT-1** and **Q1** remain, both with-Corey:
  - **INT-1** (BLOCKED — needs a proptest RELEASE first, Corey 2026-07-26): batch chapulin cross-repo
    exit gate — build + smoke-run `/mnt/c/Users/corey/projects/chapulin` + its harness against hardened
    proptest (HEAD `a2ab210`), then remove chapulin's proptest-bug workarounds + bump its proptest pin.
    Cannot start until proptest cuts a release chapulin can pin to. Deferred behind that release.
  - **Q1** (timeboxed research spike, with Corey — DESIGN ANALYSIS DONE 2026-07-26, see below).

## Q1 design analysis (2026-07-26, control-loop + Corey discussing; NO code yet)
Q1 = chapulin finding #6 "chained bounded scans (2nd scan's bound = 1st's symbolic result) → sxUnknown"
(repro `/mnt/c/.../chapulin/.../t_symex_decode.nim:210-253`). Sibling #9 (Q2) = "ANY loop + string
param → sxUnknown" (`t_symex_uri.nim:65-100`).
- **ROOT-CAUSE MECHANISM (diagnosed from code, not RFC framing):** the isWhile walker
  (`runtime.nim:5616-5651`) is EAGER FINITE PATH-UNROLLING: fork the guard `maxLoopUnwind`(=5)×; any
  path whose guard is STILL SAT after k iters → `w.sawUnknown=true` (line 5646) → whole-run sxUnknown.
  When the trip-count is bounded by a SYMBOLIC quantity (`while i < s.len …`, s.len free), the
  continuation guard `i < s.len` is SAT at EVERY k (always a longer string) → `active` never empties →
  degrade fires regardless of k. THIS is why the finding is "independent of maxLoopUnwind (2 & 5)."
  Finite unrolling STRUCTURALLY cannot decide a loop with symbolic-unbounded-above trip count. Full
  "dependent bounded loops" is undecidable; `∀k.inv(k)` over Z3 Sequence theory = the dt-bounded-reject
  trap the RFC feared ("names no candidate encoding").
- **RECOMMENDED DIRECTION — loop summarization by idiom recognition.** Don't target arbitrary loops;
  target the DECIDABLE ubiquitous fragment the findings are actually about: the bounded-sequence-scan
  idiom `while i<n and pred(s[i]): inc i` IS a `find`/`indexOf`, closed-form
  `i' = (if ∃k∈[start,n):pred(s[k]) then min-such-k else n)`. The codebase ALREADY lowers find/rfind to
  Z3 `seq.indexof`/`seq.last_indexof` (M2/M3) and those are PROVEN fast + explicitly NOT hang-class.
  So: recognize the scan/span pattern at IR level, LIFT it to those Sequence primitives, ELIMINATE the
  loop. Kills #6 (chained scans → nested indexof w/ dependent start offset — no unroll, no 2^k paths)
  AND the scan-slice of #9 (loop gone → no Sequence×unwind interaction). Sound+complete FOR THE
  RECOGNIZED CLASS; everything else keeps today's k-unroll+degrade (Invariant 3 preserved). Principled
  decidability-boundary, not a hack.
- **Alternatives rejected:** universal invariant `∀k.inv(k)` (quantifier over Sequence → dt-reject,
  not fast); loop acceleration/widening (sound over-approx → sxUnknown for defects → finds no real
  defects); concolic length-concretization (only proves chosen s.len → UNSOUND universal claim →
  violates Inv-3). 
- **GATING EMPIRICAL QUESTION (the spike):** does CHAINED `indexof` w/ dependent offsets stay
  dt-bounded-GREEN both backends? (single indexof known-fast; composed-with-dependent-offset is the
  unknown.) ~1-session spike: (1) minimal tsymex repros of #6 + #9-scan, CONFIRM they degrade today +
  confirm symbolic-bound mechanism (vary maxLoopUnwind 2/5/8, stays sxUnknown); (2) prototype narrowest
  recognizer (`while i<len and s[i]!=lit: inc i` → indexof), re-run dt-bounded tight-timeout c AND cpp;
  (3) green → real feature slice (SW bump, versioned); any 137 → close Q1 as documented negative result
  ("confirmed no viable sound-and-fast encoding for the chained case") — legit per RFC line 616-617.
  **OPEN with Corey:** run the spike now, or first pin idiom-recognition SCOPE (bare find-shape only vs.
  also `while i<n: if s[i]==c: break; inc i` vs. span/skipWhile).
- **SPIKE RAN 2026-07-26 → VERDICT GREEN (control-loop independently re-verified both backends).**
  Prototype = throwaway 3-arg-find lift (`iekStrFind` honoring `strArgs[2]` via nim-z3's
  `indexOf(a,sub,start)` overload); REVERTED after measuring (tree clean, no code kept). Evidence:
  - Phase B (mechanism): B1 single-scan + B2 chained-scan → sxUnknown at maxLoopUnwind ∈ {2,5,8} on
    BOTH c+cpp (12/12 cells). Confirms symbolic-bound degrade is unwind-independent exactly as diagnosed.
  - Phase A (crux): A1 offset-0 find = sxSat; **A2 chained-dependent find = sxSat BOTH backends**;
    **A3 chained-UNSAT-soundness = sxUnsat BOTH backends** (load-bearing — proves real modeling, not a
    masked degrade); full suite ~8–13s wall, 60s bound never approached, zero hangs. Chained/dependent
    indexof composes cleanly through Z3 Sequence theory.
  - Phase C (boundary): char-class/predicate scans (digit run) do NOT lift (no Sequence primitive for
    "first predicate-violating position") → stay OUT of scope, keep degrading.
  - **CONCLUSION: Q1 is a real, buildable small-to-MEDIUM slice.** Core = (1) a proper 3-arg-find IR
    path (distinct IR kind + parser arity dispatch, NOT the spike's overload trick) + (2) the
    idiom-RECOGNIZER (the bulk): pattern-match the canonical loop `while i<bound and s[i]!=lit: inc i`
    (single + chains where each scan's start derives from the prior result) in the walker/parser and
    rewrite to `indexOf(s, lit, start)` instead of unrolling. SW bump (verdict surface changes). Scope
    LOCKED to literal/substring delimiter scans; predicate/char-class = explicit follow-up, not Q1.
- **TWO COLLATERAL FINDINGS surfaced by the spike (NEW, not in RFC — need Corey routing):**
  1. **String index reads have ZERO IndexDefect wiring.** `iekStrAt` (`runtime_strings.nim:114-127`)
     never calls `forkDefect`, unlike seq/array/table indexing. So a `tIndexError()` search over `s[i]`
     returns sxUnsat ("no OOB reachable") even when an OOB IS reachable (spike A4 + A4b control both
     sxUnsat, both backends). This is a FALSE-NEGATIVE on defect finding for string code — a soundness
     under-approximation for defect targets (claims safe when unsafe). Independent of Q1, but it means
     Q1's find-lift makes string-scan REACHABILITY (tLabel) provable while the OOB-DEFECT half stays
     blind until this is fixed. Candidate its own §0/CR-class slice. RECOMMEND treating as a real finding.
  2. **Backend-divergent verdict on a multi-condition while-guard → C-BACKEND FALSE sxUnsat.
     ROOT-CAUSED + FIX VALIDATED 2026-07-26 (Corey chose "triage B first").**
     - **Localization:** NOT 3-way-ness, NOT loops-in-general. Trigger = a RELATIONAL (`<`/`<=`/`>`/
       `>=`) comparison on a string-indexed char (`iekStrAt`) INSIDE A LOOP GUARD. Equality (`==`) is
       fine (v2 sxSat); pure-int relational is fine (v4 sxSat); the SAME relational char-index OUTSIDE a
       loop degrades to sxUnknown on BOTH backends (p1, sound); a LET-bound char relational works
       (p3 sxSat). Only the inline-relational-char-index-in-loop-guard diverges: **c=sxUnsat (false
       "unreachable"), cpp=sxUnknown.**
     - **ROOT CAUSE:** the CR-17(a) defensive guard (`runtime.nim:3069-3074`) RAISES
       `SymexUnsupportedStringOpError` from deep inside expression lowering to avoid a String+Int+BV
       ordering hang. Outside a loop that raise propagates cleanly to the runSymex boundary catch
       (`7437`) → sound sxUnknown. INSIDE a loop guard the raise unwinds through the walk's live
       `seq[Path]` machinery and is SILENTLY LOST on the C backend's goto-exception model (the exact
       b7258f7/CR-1c divergence class the file's own comments at 7595-7624/7844 warn about) → the walk
       continues with a mis-lowered guard → false sxUnsat. cpp native exceptions propagate → sxUnknown.
     - **FIX VALIDATED (experiment, reverted):** replacing the `raise` at 3071 with an IN-BAND degrade
       (return a fresh unconstrained `allocateSym(tBool(),...)` bool instead of raising) ELIMINATED the
       divergence — v1/v3/v5 went sxSat on BOTH backends, c=sxUnsat gone. Confirms the raise was the
       sole cause. The PROPER fix also sets `sawUnknown=true` for an HONEST sxUnknown (not sxSat with a
       possibly-bogus char witness) — needs a lowering-callable sawUnknown helper (WalkCtx is defined at
       4444, BELOW the lowering code at 3071, so the 7406-style `cast[ptr WalkCtx](currentWalkCtxPtr)`
       isn't in scope there → forward-declare a tiny `noteSawUnknownFromLowering()` helper).
     - **⚠ SYSTEMIC (high-confidence, by construction — the mechanism is exception-propagation-through-
       loops, not CR-17-specific):** EVERY expression-lowering degrade-`raise` reachable inside a loop
       is the same latent C-backend false-verdict hole. Candidates below WalkCtx in the lower/lowerBool
       path: `2539` (unsupported string op), `1703` (table val-type), `1716`/`2985` (set-char interop),
       `3071` (CR-17, manifested). PARAM-ALLOCATION raises (1438/1452/1479 in allocateSym, run before
       the walk) are safe. **The sound systemic fix = SND-1 philosophy applied to LOWERING-time
       degrades: taint sawUnknown in-band, never `raise` from lowering that can run inside a loop.**
     - **SEVERITY: HIGH.** Live unsoundness (false "unreachable"/"no-defect" — the dangerous direction)
       on the C backend, triggered by ORDINARY code (a char range-check in a loop — ubiquitous in
       parsers/decoders, exactly chapulin's domain). RECOMMEND this JUMPS AHEAD of Q1 (soundness hole in
       shipped behavior > capability add). A proper slice: (1) lowering-callable sawUnknown helper, (2)
       convert CR-17's raise → in-band taint, (3) audit + convert the other in-loop lowering raises,
       (4) both-backend regression pinning c==cpp on the repro set. Bumps SW (verdict surface changes).
  - Minor: `{'0'..'9'}` set-membership `contains` doesn't compile through the parser (`getImpl for
     callee contains` gap) — a distinct small parser gap, noted only.

## Stage-3 grind ledger
Slices land serially (each SW bump serialized against a live base). Sweep = all
`tsymex_*.nim` × {c,cpp} via `scripts/dt-bounded.sh`.
**Clusters 2 & 3 COMPLETE (M1–M6); Cluster 4 P1 (`ad6c46c`, v52) + P2a (`4292f4c`, v53) landed.**
**GRIND PAUSED — P2b REOPENED by Corey (2026-07-23) for a heap-identity redesign.**
The value-modeled P2b (`42eafde`, v54, ADR-0021, 422/422) is committed+green but being
SUPERSEDED. Corey scrutinized it; control loop empirically confirmed it is SOUND (aliasing
`q=p;q.val=99;p.val==99` AND identity `p==q` both degrade to `sxUnknown`, never a false
verdict) but does NOT model ref identity/aliasing. Corey chose to invest in true heap
identity. Exploration (see below) reframed it: the value-model of named ref-object aliases
is NOT a deliberate lock — it's Phase-14 `classifyType` legacy (`dsl_typebridge.nim:195-213`,
"#136 unwrap ref T", comment "Aliasing tracking is a follow-up") predating the heap model;
heap-identity was always the intended follow-up. The full heap machinery (svRef identity,
field-split heap, refEq, freshness, heapSnapshot alias-group rendering) already exists +
is tested for INLINE `ref T` (Cluster R: R6/R7/R9); named aliases just don't route to it.
**Design written: ADR-0022 in SYMEX_PLAN.md** (lines 765-873; Cluster H — named-ref heap
identity; classifyType policy flip → itRef + ~10 dsl_parser routing sites + real heap
construction + variant stays excluded + RC bump 5→6; sliced H1–H7).
**ARCHITECT REVIEW ROUND 1 COMPLETE** (Corey invoked `/architect docs/SYMEX_PLAN.md`
2026-07-23; 4-lens team). Finding: ADR-0022's original H1 was **self-contradictory** — the
empty `namedRefPlaceholder` is load-bearing for Z3-sort identity ($-structural keying) yet
3 consumers (construction, witness reader, new-zero-init) need the FULL field list off the
same pointee. **Fixes APPLIED to ADR-0022** (see "ADR-0022 Round-1 architect review"
subsection, SYMEX_PLAN.md after line 873): resolution = key sort identity on a canonical
NOMINAL type-id (name+generic-args, symbol-unique) not `$fields` → bare symbol gets FULL
pointee, recursive field keeps placeholder, both share the sort. Plus: universal isNew
zero-write (closes a false-SAT hole), preserve variant detection, H2/H3/H5 reframed as
verification (routing auto-activates), RC+SW bump AT H1, container types (seq[Node]) added,
isHeapRef predicate + delete 3 bare-symbol carve-outs, +3 regressing tests (r10/r11b/
rectify_refs). Consolidated notes: `scratchpad/adr0022_review_consolidated.md`.
**3 GENUINE SCOPE FORKS AWAITING COREY** (below in Open forks). **RESUME: get Corey's answer
on the 3 forks + H1 green-light, then implement the revised H1 (atomic: classifyType→itRef
full-pointee + nominal sort-id + H1a/b/c + isNew zero-write + variant-detect + SW/RC bump).
Do NOT implement until he signs off.** Remaining after Cluster H: Q/TOT/INT/F/C.
P2b detail: (`ref object` expression-position allocation — genuinely NEW
capability, needs a preamble `isNew` + field-writes, NOT a P1/P2a clone; `isNewCall`
(dsl_parser.nim:805-821) documents `new T` is handled ONLY at let-statement level today
("no expression-context model for allocation"). **Variant construction EXCLUDED** per round-2
(field-split heap declines variant *reads* via `heRefVariantUnsupported` dsl_parser.nim:1299-1305;
adding variant *writes* needs its own ADR revisiting that read gap). Depends on SND-1; CR-2a
`Soft(t)` backstop. **Likely needs its own ADR** (object construction as expressions vs the
field-split heap model). Bumps SW; RC per the same construction-only test as P1/P2a. Size L.
Watch: P2b's ref-object return may surface the same `retBindEq` composite-return gap below.)
Then Q/TOT/INT/F/C.
Slice order: SND-1✓ SND-1b✓ SND-2✓ CR-1a✓ CR-1b✓ CR-1c✓ CR-2a✓ CR-2b✓ CR-2c✓ M1✓ M2✓ M3✓ M4✓ M5✓ M6✓ P1✓ P2a✓
→ **P2b** → Q/TOT/INT/F/C. 17/27 done, 10 remaining.
Versions now: symexWalkerVersion **"56"**, renderAsChoicesVersion **"6"**;
only `tsymex_phase15_CR2_cachekey.nim` pins either with `==`.
**Cluster H sub-track (supersedes P2b `42eafde`): Step A LANDED `d85f0f7`** — added
`IRType.nominalId` field + recursive `nominalId(NimNode)` helper (signatureHash;
bracket-arg recursion for generics), populated at the 3 named-object `tTuple`
sites; PURE no-op (field unread → no version bump), 424/424 both backends. **NEXT:
Step B** (flip `refPointeeTypeId` to prefer nominalId, fallback `$`; SW 54→55;
verify inline-ref R6/R7/R9/R12 + watch mixed-naming sort-mismatch) → Step C (atomic H1).
**Discovered gap (P1, not yet sliced):** a value-returning HELPER proc that *returns* a
tuple (`makePair(x): (int,int) = (x,x+1)`) still degrades to sxUnknown via `retBindEq`
(runtime.nim: "composite-typed proc return not yet wired — got svTuple"), safely caught by
CR-1c (no crash). This is the call/RETURN-binding path, distinct from P1/P2a's CONSTRUCTION
arm — documented in-code in tsymex_p1_tupleconstr_expr.nim. A future return-binding slice
(not currently an RFC row) would close it; P2b's ref-object return may surface the same.
NOTE for P2a/P2b (and any witness-shape slice): bump SW always (verdict surface changes);
bump RC **only if a genuinely NEW witness SHAPE is introduced** — P1 showed the tuple/object
witness *reader* already existed (built for variant/object values), so a construction-only
slice reuses it and RC stays "5" (a spurious RC bump needlessly invalidates every cached
witness). Update the CR2 pin's `== "<sw>"` (and `renderAsChoicesVersion == "<rc>"` iff bumped);
re-grep `== "` set each time. Witness-shape slices that make previously-degraded types
renderable ALSO tend to require widening CR-2c's `isRenderableWitnessTy` (types.nim) in
lockstep — for P1 no change was needed (itTuple already recursed). Check P2a's object shape.

| # | Slice | Commit | walker ver | Sweep | Notes |
|---|-------|--------|-----------|-------|-------|
| 17 | P2a | `4292f4c` | 52→53 (RC stays 5) | 420/420 ✓ | Value-object (non-ref) `nnkObjConstr` in EXPRESSION position (`let p=Point(x:a,y:b)`, object return). Before P2a, nnkObjConstr recognized only inside `newException(...)`; any other value-object construction fell to CR-2a → whole-run sxUnknown. **REUSES P1's `iekTupleLit` wholesale — NO new IR kind** (types/runtime/abstraction untouched): a value object's IRType is itTuple-shaped (`classifyType` yields tTuple w/ objectName populated), lowers to the same svTuple, and every existing iekTupleLit dispatch site + the itTuple/svTuple witness reader transfer for free (objects already render as SUT params). Only `dsl_parser.nim` gets the `of nnkObjConstr:` arm + `canonicalize.nim` SW bump + CR2 pin. **Field ordering/omission** (the one real diff from tuples): builds a name→value map from present fields (skip n[0]=type symbol; each field is nnkExprColonExpr), walks the TYPE's declared `fieldNames` order. **Omitted field** → `zeroValueForType(fields[i])` (genuinely SOUND — Nim zero-inits omitted value-object fields, NOT a degrade); omitted field whose type has no clean zero (nested seq/tuple/variant/ref) → SND-1 degrade via feUnsupportedExprKind+mkUnsupported (never a guessed-zero false sxSat). Present field parses via ordinary parseExpr recursion → unsupported field degrades same way (Invariant 3). lowerTupleLit's per-field proto (from ttupleTy.fields[i]) gives heterogeneous fields (`Point(a:x, b:5'u8)`) their declared width. Bumps SW 52→53 only; CR2 pin `== "53"`, RC stays `== "5"` (construction-only, no new witness shape — per P1). No CR-2c change (itTuple already renderable). 14-test strong-form (basic/out-of-order/omitted/heterogeneous + UNSAT soundness each, newException regression, SND-1 soundness×2, `>=` floor pins), verified GREEN both backends in isolation. Subagent `aa4d3f9f` implemented (elegantly, reuse-not-new-kind per brief) then stopped post-sweep without committing (13th detach); control loop verified diff independently + ran clean 420/420 sweep + committed. |
| 16 | P1 | `ad6c46c` | 51→52 (RC stays 5) | 418/418 ✓ | General N-ary `nnkTupleConstr` in EXPRESSION position (`let t=(a,b)`, `return (a,b,c)`, named `(x:a,y:b)`). Before P1 only the narrow `yield (e1,e2)` special-case recognized nnkTupleConstr; any other tuple-constructor expr fell to the CR-2a catch-all → whole-run sxUnknown. New `iekTupleLit` IR kind (types.nim: telems + whole `ttupleTy`, heterogeneous — carries full itTuple type not one elemTy; `mkTupleLit` ctor with arity/kind doAsserts + render arm) lowering to `svTuple` via new `lowerTupleLit` (runtime.nim). **Construction-only** — the itTuple/svTuple witness *reader* (emitTyAndReader itTuple arm, isRenderableWitnessTy itTuple recursion) already existed for variant/object values; field *reading* (`t[0]`/`t.x`) already supported. parseExpr `of nnkTupleConstr:` unwraps `nnkExprColonExpr` for named tuples, parses each element via ORDINARY parseExpr recursion → an unsupported field independently hits CR-2a → SND-1 taint → whole-run sxUnknown (Invariant 3: never false sxSat from a field dummy). **lowerTupleLit derives per-field proto from `ttupleTy.fields[i]`** so a heterogeneous field (`(x,5'u8)`) lowers at declared width, not default signed BV64. abstraction.nim (tryEvalInterval non-int + collectVarRefs), probeProto (none — own kind always svTuple), collectSetLitMembers/collectTableLitKeys, emitExpr, rhsHasInlineDefectFork all got iekTupleLit arms (all `else`-terminated sites). **RC-stays-5 is a resolved decision** (brief said bump both; subagent correctly identified no new witness shape — control loop verified & concurs). Bumps SW 51→52 only; CR2 pin `== "52"`, RC pin stays `== "5"`. P1 test uses `>=` floors. No CR-2c change (itTuple already renderable). Subagent detached-sweep + re-armed poll (12th); control loop verified diff independently (all 4 core files + abstraction), ran own confirming sweep. |
| 1 | SND-1 | `84668ab` | 37→38 | 388/388 ✓ | isUnsupported taints Path.uncertain. Fallout: added no-op parse arm for assert-scaffolding `nnkConstSection`/`nnkBindStmt`/`nnkMixinStmt` in dsl_parser (else every assert degraded). Legit soundness corrections: a3_closure_iterators T5/T6 sxSat→sxUnknown (accidentally-correct false-sxSat SND-1 closes). New test uses `>=`-floor pin idiom; 7 legacy `==` pins bumped to "38". |
| 2 | SND-1b | `bc2c8d9` | 38→39 | 390/390 ✓ | `applyClosureGround` skips `assertArm` for uncertain closure-body sub-paths (both return channels), pushes new `ceClosureBodyUncertain` (sevError) → existing `closureForcedUnknown` whole-run degrade fires. ADR-0018 in SYMEX_PLAN. Fixed fork-registry comment (descentBase = 2nd raw `Path(`). **One-time SW pin-idiom migration executed**: canonical CR2_cachekey stays `== "39"`; 6 incidental pins → `>=`-floor. Strong-form test checks error-kind, not just verdict. Subagent died on API error post-sweep; control loop verified + committed. |
| 3 | SND-2 | `0a156c7` | 39→40 | 392/392 ✓ | `isAssume` promoted from bool flag to distinct `IRStmtKind` (`mkAssume` ctor, own render arm). 12 switch sites: 10 uniform `of isAssert, isAssume:`, 2 non-uniform — canonicalize renders distinct `St<Am:…>` vs `St<At:>` (avoids `symexCacheKey` collision → silent wrong answer), walker dispatch shares steps 1/2/4 but omits step 3 `forkDefect`. Round-2 fix: `collectAssertRanges` had `else: discard` silently dropping isAssume range facts → now included. `symexAssume(cond)` lowers to `mkAssume` not `mkAssert`. ADR-0019 in SYMEX_PLAN. 7-test strong-form suite (flagship verified genuinely RED). CR2 pin → `== "40"`. Subagent committed itself; control loop verified (both backends green, ADR landed, only CR2 as `==`). |
| 4 | CR-1a | `ee9763c` | 40→41 | 394/394 ✓ | bitwise `and`/`or`/`xor` on a Z3-Int-sorted operand (`.len`/`.find`/`.indexOf`/`parseInt` — unconditionally svInt, no BV-promotion choice) hard-raised `ValueError: bitwise op on promoted Z3Int` (native crash). New `svIntToBV` (runtime.nim ~1980) bridges the Int operand to BV via `Z3_mk_int2bv` (unsigned; values always non-negative); former crash arm (~2977) dispatches through existing `binBV` → SOUND sxSat/sxUnsat (NOT degrade). Width follows the BV operand, BV64 default (native int) when both Int-sorted. No new ADR (bug fix at existing locus). Strong-form test (SAT witness-parity + load-bearing UNSAT `and 1==2`/`xor self==1`; and/or/xor). CR2 pin → `== "41"`. Subagent stalled on detached-sweep pattern; control loop verified (diff-review + 394/394 both backends) + committed. |
| 5 | CR-1b | `5fc018e` | 41→42 | 396/396 ✓ | tail-return-of-local KeyError (`runtime.nim` `of iekVar: env[e.vname]`) was a SYMPTOM — **true fault at PARSE time**: `dsl_parser.nim`'s `nnkPar`/`nnkStmtListExpr` arm did `parseExpr(n[^1])`, silently dropping every LEADING statement (`let hi = ...`) of an implicit-tail-return body (`result = (let hi=…; hi+1)`). Fix: parse each leading child as a statement into the existing `preamble` accumulator (mirrors `nnkLetSection` A-normalization) before the tail child. **runtime.nim untouched** — fixed at the true lowering site per DoD, NOT by soft-failing the read. Strong-form test: SAT w/ load-bearing witness replay (`data[o] mod 256==4` ∧ `f==5`) + UNSAT `==300` (rules out dropped-local-as-free-symbol false positive). No new ADR. CR2 pin → `== "42"`. Subagent blocked in-turn correctly + self-committed; control loop verified (runtime untouched, both backends green, only CR2 `==`). |
| 7 | CR-2a | `3f01b1f` | 43→44 | 400/400 ✓ | `parseExpr` catch-all `else:` (dsl_parser.nim ~1866) `error()`ed at MACRO-EXPANSION on any unhandled NimNode kind → aborted compilation (worse than sxUnknown). Converted to the A7-S3 `mkUnsupported`-degrade idiom: new `feUnsupportedExprKind` (types.nim, enum tail) sevError + `preamble.add mkUnsupported` + type-correct dummy via new `zeroValueForType(classifyType(n).ty)` (returns Nim's guaranteed ZERO default for int/bool/float/string — sound for read-before-write per Inv-3; nil→`mkIntLit(0)` fallback for aggregates under SND-1 taint). Depends on SND-1✓ (dummy never yields a witness; also Class-A → capForcedUnknown backstop). RED = compile-abort on `(if c:1 else:2)+1` (nnkIfExpr nested as `+` operand). Strong-form 6-test incl load-bearing CR-2a-2 (dummy 0 would trivially-SAT `y==1` ∀x but SND-1 → sxUnknown≠sxSat). No new ADR (idiom reuse). CR2 pin → `== "44"`. Subagent stalled on detached-sweep (4th); control loop verified diff+test, then subagent's Monitor resumed it + self-committed (5 files, no race); control loop re-verified 6/6 both backends + 400/400. |
| 8 | CR-2b | `6c9210d` | 44→45 | 402/402 ✓ | Parameter-type macro-`error()` → whole-run forced-`sxUnknown`. `classifyType`'s resolved-type-name text-match catch-all (`dsl_typebridge.nim:452`) `error()`ed at macro-expansion on an unmodeled SUT PARAM type (RED: `cstring`), aborting compilation before any body was walkable. Option 2 (control-loop-resolved, mirrors `__ownership:`): catch-all now returns `unranged(tUninterp("__unsupported:" & s))`; allocateSym gains a `"__unsupported:"` prefix branch raising CR-1c's `SymexClassifiedDegradeError` carrier with new `feUnsupportedParamType` kind (types.nim, enum tail) → caught at runSymex boundary → whole-run sxUnknown. **Second crash-trap found + fixed (in-scope, not a fork):** `emitTyAndReader` (symex.nim) builds a witness-reader for every param at macro-expansion; its itUninterp catch-all knew only `"__closure"` — an `"__unsupported:"` name fell through to an uncaught ValueError in the NimVM (relocated the abort). Added a placeholder-int/`{.warning.}` branch mirroring `__closure`; placeholder never evaluated (sxSat/sxRaised codegen arms unreachable once allocateSym forces sxUnknown). Carrier REUSED (no new exception type). Strong-form test asserts KIND + `status != sxSat && != sxUnsat` (no silent wrong verdict, no walk-time crash) both backends. CR2 pin → `== "45"`. Subagent blocked in-turn + self-committed; control loop verified independently (commit/tree/pin/version + CR-2b test 4/4 green BOTH backends + diff-reviewed carrier reuse & second-trap fix). |
| 15 | M6 | `b369168` | 51 (no bump) | 416/416 ✓ | probeProto svString-proto for `iekStrToLower`/`iekStrToUpper`/`iekRadixFmt`/`iekRuneToStr`. Catch-all `StrOpKinds - {…}` (runtime.nim:1827) returned `none` for these 4 string-producing ops; moved into the svString-proto arm (:1820). **Defensive/inert — NO version bump** (v51 stays). Inertness is STRUCTURAL not just empirical: `lowerStrArm` (runtime_strings.nim:88) never threads `proto`; `lower()` dispatch (runtime.nim:2775) doesn't pass proto to it → probeProto's StrOpKind return can't affect any lowering today (bEq/bNe probe-miss fallback recovers). Subagent verified pre/post byte-identical `[OK]` diff both backends. Test (10) is HONEST regression-protection (explicitly NOT RED→GREEN — documented): all 4 ops via real surfaces (toLowerAscii/toUpperAscii=A9, toHex=A8, `$Rune`=A7-S2), `==`/`!=`, + compound cross-op comparisons (the site where proto would first matter if path went live). Subagent ran ~6h (thorough inertness investigation + detached-sweep stall, 11th) but self-committed b369168 correctly; control loop verified independently (416/416, walker 51, binary gitignored, test honesty). |
| 14 | M5 | `153f7dc` | 50→51 | 414/414 ✓ | `nnkIfExpr` in `parseExpr` + min/max. parseExpr had no nnkIfExpr arm → if-EXPRESSION as a sub-expr (operand, let-rhs, or inlined if-expr-bodied proc body like `max(a,b)=if a<b:b else:a`) hit the CR-2a catch-all → sxUnknown. Added an nnkIfExpr arm to parseExpr (dsl_parser.nim:1880) that A-normalizes via synthetic let+read (hoist into preamble reusing statement-if lowering, each branch tail → temp; return read of temp). min/max work via proc inlining, no dedicated modeling. Bumps SW 50→51; RC stays "5". Strong-form 10-test: if-expr-subexpr BOTH arms modeled (exact witnesses) + UNSAT soundness + let-rhs if-expr + max/min SAT+UNSAT both directions + symbolic max(a,b). **Migrated `tsymex_CR2a_expr_catchall.nim`** (its RED repro WAS an if-expr subexpr): SUT1 `(if x>0:1 else:2)+1==1` flips sxUnknown→genuine **sxUnsat** (y∈{2,3}); SUT2 let-rhs→genuine **sxSat** x>0; catch-all MECHANISM + SND-1 soundness retargeted to still-unsupported `cast[int32](x)+1` (nnkCast verified still hits catch-all) keeping dummy-would-sat framing — control loop reviewed as principled/strengthened, NOT gutted. Subagent detached sweep + stopped (10th); control loop verified M5 10/10 + CR-2a 7/7 BOTH backends, **removed leftover `zzrepro_cast` ELF scratch (not gitignored)**, blocked to 414/414, committed. |
| 13 | M4 | `3688a84` | 49→50 | 412/412 ✓ | String `.add`/`&=` modeled via existing `iekStrConcat`. `s &= x` (augmented-assign) was SND-1's Class-B silent-no-op→false-sxSat: `binopForInfix` has no `"&"` case → `else: error()`. Fix (RFC round-2 mechanism, NOT a set edit): augmented-assign lowering gains a TYPE-CLASSIFY branch — string LHS stores `lhs := mkStrOp(iekStrConcat,"&",@[lhsRead,rhs])` (mirrors binary `s & x` at dsl_parser:1081); every other LHS keeps existing mkBinop path. Did NOT add `"&"` to binopForInfix (concat ≠ numeric IRBinop). `s.add(x)` string receiver → same in-place concat-assign; char-arg `s.add('c')` deliberately kept sxUnknown (char=itInt/uint8, no char→string; documented follow-up, S11 addChar asserts it still degrades); `seq[T].add` untouched (receiver type-classified). Bumps SW 49→50; RC stays "5" (string witness). Strong-form new test (12): &= happy/UNSAT, .add happy/UNSAT, symbolic-param LHS + symbolic RHS operand (round-tripped vs real Nim `&`), seq.add regression. **Migrated 3 existing tests** (SND-1/SND-1b/S11 used `&=` as unsupported-drop vehicle): the `&=` repro flips to correct sxSat; taint-mechanism SUTs retargeted to still-unsupported `/=` — control loop reviewed the diffs (principled, NOT gutted). Subagent detached sweep + stopped (9th); control loop verified 12/12 + 3 migrated tests BOTH backends, distinguished a concurrent-binary-write race (spurious "Permission denied") from real failure, blocked to 412/412, committed. |
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
- (none blocking) — all Cluster H scope RESOLVED. Round-2 decisions (2026-07-23): generics →
  DEFER to Cluster G (keep sxUnknown + guard/test; no live collision); witness → INCLUDE
  recursive-pointsTo work as slice **H_witness** (implement ADR-0010 invariant #4). Baked into
  ADR-0022. Earlier scope holds: containers in-cluster (Table/HashSet stay degraded — orthogonal
  limits); unify all refs on nominal sort-id. **Corey green-lit building Step A.**
  **ROUND 2 COMPLETE — findings applied to ADR-0022** ("ADR-0022 Round-2 architect review"
  subsection). VERDICT: **buildable** — the nominal-id primitive (recursive `signatureHash`)
  was empirically verified on the dev toolchain. Consolidated notes:
  `scratchpad/adr0022_round2_consolidated.md`. Key applied refinements: nominal-id = recursive
  signatureHash as a first-class `IRType.nominalId` field via ONE shared helper (classifyType
  + namedRefPlaceholder), change `refPointeeTypeId` only (not `$`); **H1 folds in H4 core**
  (real mkNewT+mkFieldDerefWrite — else P2b-1..8 regress to sxUnknown; H4 eliminated as a
  separate slice); H1 also patches the `nnkSym` sym-indirection branch (`type NodeRef = ref
  Obj`); witness needs a provenance flag (zero-field `type Token = ref object` else
  mis-renders nil); drop double zero-write; Table/HashSet stay degraded (orthogonal limits);
  storeSeqElem needs an itRef arm for seq[Node] literals. **Landing order (de-risked): Step A**
  (add nominalId field+helper, pure no-op, macro-time testable) → **Step B** (flip
  refPointeeTypeId, verify inline-ref R6/R7/R9/R12 green) → **Step C = atomic H1** (classifyType
  flip both branches + classifyObjectRecordFields + real construction + isNew zero-write +
  provenance flag + isHeapRef/isRecursionPlaceholder + delete 3 carve-outs + SW54→55 + RC5→6)
  → H_containers → verification → H_final. **Step A LANDED `d85f0f7`** (nominalId field+helper, pure no-op, 424/424).
  **Step B LANDED `ddc9196`** (refPointeeTypeId prefers nominalId; SW 54→55; CR2 pin "55";
  424/424 both backends, all inline-ref heap tests green — mixed-naming risk did NOT
  materialise). **NEXT: Step C = atomic H1** (SW **55→56** + RC **5→6**; Step B already took
  54→55). See ADR-0022 for the full H1 spec: classifyType flip (BOTH the named-alias
  `nnkObjectTy` branch AND the `nnkSym` sym-indirection branch → `itRef(full pointee)`) +
  classifyObjectRecordFields shared core + widen the ~10 dsl_parser construction/routing gates
  + real heap construction (`mkNewT`+`mkFieldDerefWrite`, folds in H4 core — value-arm 42eafde
  replaced) + universal `isNew` zero-write (every field, closes false-SAT) + variant detection
  preserved (stays excluded) + provenance flag so zero-field `type Token = ref object` witnesses
  don't mis-render nil + `isHeapRef`/`isRecursionPlaceholder` predicates + DELETE the 3
  bare-symbol carve-outs (dsl_parser.nim:1327-1331, refExprClassify:2436, :2106) + buildHeapSnapshot
  populates for named-alias svRef params. VERIFY: P2b-1..8 now real heap verdicts (aliasing
  `q=p;q.val=99;p.val==99` → sxSat, identity `p==q`), +3 regressing tests (r9/r10/r11b re-derived
  not relabeled), full sweep both backends. RESUME context below (superseded).
  **[SUPERSEDED — Step B done]** Step B CODE COMPLETE but UNCOMMITTED in the working tree (control loop verifying):
  `refPointeeTypeId` (runtime_heap.nim:25-33) flipped to PREFER `pointeeTy.nominalId` for a
  named-object `itTuple` (non-empty nominalId), else `$pointeeTy` fallback; SW bumped 54→55
  (canonicalize.nim:104); CR2 pin → `== "55"` (verified the only `==` pin); RC stays 5. Diff
  reviewed clean. A FULL both-backends sweep is running → `scratchpad/sweep_stepB.log`; as of
  last check 337/424 with 0 failures (mixed-naming risk NOT materialised — no heap/ref-test
  regression). **RESUME: confirm the sweep hit 424/424 both backends (tally
  `scratchpad/sweep_stepB.log`: all rc=0, no 137/124 hangs), then `git add -A` the 3 changed
  files (canonicalize.nim, runtime_heap.nim, tests/tsymex_phase15_CR2_cachekey.nim — NOT
  scratchpad/) and `git commit --no-verify` as "feat(symex): Cluster H Step B — refPointeeTypeId
  prefers nominalId". Then Step C (atomic H1).** If the sweep shows a heap-test regression, it
  is a mixed-naming site: populate the missing nominalId construction path or report. Full
  slice specs in ADR-0022's two review subsections. Use `scripts/dt-bounded.sh`; both backends; `git commit --no-verify`; no
  Claude trailer. Remaining after Cluster H: Q/TOT/INT/F/C.

## Key decisions (this session)
- Mega-RFC scope (above). • Verify-at-HEAD before drafting (drop healed findings).
- Non-symex findings STAY in this RFC (per mega-RFC choice) as their own clusters,
  rather than routing fuzz→FUZZ_PLAN.

## Review ledger (stage 4) — not started
