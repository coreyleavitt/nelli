# RFC — parser-boundary normalization (#146) — handoff

- **Stage:** 4 review — **COMPLETE 2026-08-14, floor reached at round 5**
  (0 Critical/High/Medium open; only Lows remain, listed in the ledger).
  Fix mandate (fix through Medium, leave Lows) executed across rounds
  1-4: 13 fix commits c1637e2..fe609ab on top of the 12 stage-3 commits
  (25 local commits total, NOTHING PUSHED). Walker stays 73 throughout
  (no fix required a bump; CR2 pin now actually runs in CI). Full sweep
  at fixed HEAD (524 runs): residue = #152 pair (g8/g10, both backends)
  + r4_strip exit-137 under 6-way load only, solo-green both backends
  immediately after (the documented load-flake).
  New issue filed during review: #157 (CR-1b guard-preamble deposit,
  pre-existing, same family as #155).
- **Round 6 (Lows) COMPLETE 2026-08-14** (Corey extended the mandate:
  "fix lows now"). Seven commits, all verified single-file-scoped:
  L1 `14440e1` (dt-bounded.sh filename passed as data — argv, not
  string splice; exit-0/exit-1 propagation validated incl. known-red
  g8); L2 `d850a25` (psweep exit-contract header comment); L4 `4d30b6c`
  (ADR dates: D1 08-13, D2/D3 08-14); L6 `8ed28d5` (fresh-shell
  decision recorded in resolveRoutineImpl — memoization rejected,
  NimNode aliasing hazard); L7 `04d3c0e`
  (tests/tsymex_phase15_C2_staticparams.nim: 3 cells, mixed static/
  generic positions both orders + scalar-static instKeyFor arm,
  RED-proven by verdict flip; the impl[5][1] dual-location branch has
  no reachable surface construct — stated in the header, not guessed);
  R2-4 `266bd38` (audit allowlist now guarded against isAtomicIR drift
  via staticRead extraction, RED-proven); R4/R5 `cc47945` (multi-name
  include parsing + permanent unit assertion + comment truth).
  No action: L3/L5 (closed by M1/H1), L8 + R2-3
  (documented-by-design). **Review fully closed: 0 findings open at
  any severity.**
- **Orchestration incident (recorded in memory):** parallel fix agents
  share the git INDEX even on disjoint files — one transient
  staging collision occurred (self-healed by reset+recommit; history
  verified clean). Serialize commits or use worktrees next time.
- **SHIPPED 2026-08-14:** pushed main `8a3b6d3..c75cfdf` (32 commits)
  + annotated tag `v0.3.5` (release commit `c75cfdf`, version bumped in
  nelli.nimble + milpa.kdl, house pattern per v0.3.4). #156 confirmed
  auto-closed by the push. **RFC #146 is DONE end to end** (stages 1-4
  + Lows round + release).
- **X1 disposition (Corey, 2026-08-14):** the verify harness belongs in
  the chronos repo, not here — confirmed. Nothing chronos-related lives
  in nelli beyond A1's chronos-faithful test shapes (which stay). X1
  gates whenever `verify/` becomes durable on chronos main; that action
  happens in the chronos repo.
- **#154 CLOSED not-reproducible (2026-08-14, post-release):** Corey
  asked "issue here or in nim-z3 first" — answer: NEITHER, currently.
  Exhaustive reconstruction (minimal 2-proc declared-only + queried-first
  siblings, full A1 corpus with (c)/(d) reverted to `':'`, cell (e)
  isolated at runtime) does NOT reproduce at HEAD nor at the A1 commit
  65f5e5d, c and cpp, with the IDENTICAL milpa.lock (nim-z3 ca4fe77
  unchanged) and container image (built before the observation, never
  rebuilt). Structural audit: recognizer pure/ctx-local, no
  compile-time mutable parser state, fresh Z3Context + threadvar reset
  per query. Attributed to transient authoring-session build state.
  Shipped commit `b059473` (pushed): permanent guard pin
  `tests/tsymex_q1_sibling_collision.nim` (both collision shapes,
  green both backends, registered in the nimble test task) + RESOLUTION
  paragraph in the A1 corpus note. Issue closed with the evidence
  table; reopen requires a concrete failing probe.
- **Remaining (not this RFC):** engine defects #152, #153 (soundness,
  highest priority), #155, #157; downstream (chapulin/amoxtli) +
  registry aliasing from the nelli rename; the parked chapulin round-6
  RFC (0.4.0/0.5.0 reserved). #154 closed not-reproducible (above).
- **Next-work triage (Corey, 2026-08-14, this session):** chapulin
  round-6 RFC + its defect family (#152 via A5, #155/#157 via Track B,
  #153) is assigned to the WINDOWS side — do not pick those up here.
  Corey asked for the next tracking-issue-with-subissues craftable into
  an RFC on this side: answer is **#124 Shape A umbrella** (subissues
  #125–#132; the only open umbrella with real sub-issue structure —
  #112 has none filed, #151 is a checklist). Recommended clustering:
  (1) #125/#128/#132 (where-strategies + verifyAll + classification —
  thin wrappers over the mature symexFind surface), (2) #126/#131
  (SMT shrink/polish at the choice-seq shrinker seam), (3) deferred
  #127/#130 (+#129) sequenced last to avoid walker-guts collision with
  the Windows-side RFC. Caveat flagged: #124's own status gates on
  concrete user demand — Corey's gate to lift. **Awaiting Corey's go**;
  on go, resume command: `/rfc-flow` → draft the Shape A RFC from
  #124's sub-issue table with the clustering above, then architect
  review rounds.
- **Fuzzer next-gen grill IN PROGRESS (2026-08-14, `/grill-me ideal:`)**
  — Corey pivoted to the fuzzer ("other projects report it's limited").
  Explore-agent map done (fuzz.nim/fuzzir.nim/coverage.nim/FUZZ_PLAN):
  mutation core (choice-IR ops, span crossover) is strong; gaps ranked =
  (1) spawn-per-exec external model (no forkserver/shm, ~100-1000x
  throughput), (2) no cmp/value-profile guidance (RedQueen class),
  (3) uniform mutator choice (no bandit/MOpt), (4) admission-only
  coverage (no Entropic-style energy), (5) no worker pool; symex↔fuzz
  bridge is green-field. Ideal 5-tier sketch presented (forkserver+shm
  floor; trace-cmp → IR-RedQueen + auto-dict; symex concolic bridge;
  Entropic energy + operator bandit; worker pool + unified frontier
  with forAll's coverageGuided). **Resolved so far:** (1) the
  "in-process only" complaint confirmed real in BOTH readings —
  external tier is `when defined(posix)` (fuzz.nim:858, Windows gets
  nothing) AND the structure-aware IR path has no crash isolation
  (engine.nim:54-60, Defect/segfault kills the campaign) — missing
  quadrant = structure-aware × crash-isolated; (2) **Windows is
  FIRST-CLASS** — executor = portable persistent worker pool
  (CreateProcess-once + IPC input stream + shm coverage + worker
  recycling + pristine-worker re-verification of every
  admission/crash; POSIX fork() demoted to a cheap per-input
  recycling policy of the same seam — fork-vs-CreateProcess
  semantics explained and accepted); (3) consumer reports are NOT
  drivers — mandate is best-in-class PhD-level design; hybrid
  (greybox mutation + concolic symex over choice sequences, Z3
  models materialize as choice sequences) explained and is the
  novelty core; overlap with Shape A #127/#130 noted. **Open on Q3
  (re-asked, awaiting answer): scope = (a) world's best
  structure-aware fuzzer (Nim-native tier is the product, external
  tier inherits infra, no AFL++ byte-parity chase — RECOMMENDED) vs
  (b) dual-domain parity incl. byte-level RedQueen/WinAFL-class
  external fuzzing.**
- **Fuzzer grill COMPLETE (2026-08-14) — all forks resolved, synthesis
  delivered in-session.** Decisions: scope=(a1) structure-aware product,
  external tier un-gated to Windows (instrumentation-required, NO DBI;
  stretch path to (b) = trace-cmp → auto-dict → TinyInst recorded);
  executor = portable persistent worker pool (CreateProcess+pipes+shm,
  Job Objects, recycling, pristine re-verification; POSIX fork = cheap
  recycling policy); hybrid = CHOICE-SPACE concolic bridge (draws are
  symbolic roots, aggressive concretization, models ARE choice
  sequences, replay-validated; symexFind untouched, new walker mode;
  value-space+inversion REJECTED); guidance/scheduling = IR-level
  cmp-correspondence, Entropic energy, operator bandit, havoc
  stacking; identity = two front doors one engine (forAll gains
  replay-only fuzz-corpus reads, contracts stay distinct); Shape A:
  fuzzer RFC owns the bridge, #127/#130 thin surfaces later —
  SUPERSEDES #124 as next-work; program = one RFC, Tracks E→G then
  S/U; evaluation = committed CI ablation benchmark w/ per-track exit
  gates + informal scoreboard + one-time byte sanity comparison at E
  exit (no standing external baseline). Risks logged: stage-1
  concolic yield bounded by walker closure coverage; contamination
  mitigated-not-eliminated; MSVC /fsanitize-coverage needs Track-E
  verification; harness maintenance. **Resume command: `/rfc-flow` →
  draft the fuzzer RFC from the synthesis table in this session
  (Tracks E/G/S/U + stretch-(b) appendix + evaluation harness as
  first-class deliverable), then architect review rounds.**
- **FUZZER RFC FIRST PASS WRITTEN (2026-08-14):** synthesis is now
  `docs/RFC-fuzzer-nextgen.md` (+ its own handoff
  `docs/RFC-fuzzer-nextgen.handoff.md`). Claims ADR-0031. Tracks
  E→G→S/U as above. **This is now the active RFC** — further fuzzer
  work tracks in ITS handoff, not this one. Next command:
  `/architect docs/RFC-fuzzer-nextgen.md round 1` (after Corey reviews
  the first pass). Three open forks recorded in the new handoff
  (umbrella issue; parallel-campaign v1 scope; concolic-yield framing).

## Round-2 outcomes (what changed in the RFC)
- **N0 premises corrected (depth lens, both verified in code):**
  (1) `borrowInfoFor` fallthrough is verdict/witness-INERT at HEAD
  (ordinary arms eject both operands; the skipped rebox mints a dead
  unconstrained const) — test reframed characterization pin, not RED.
  (2) The C3 gate that excludes `func` is `symKind(n) == nskProc` at
  :1048, NOT :1050 (unreachable for func) — fix widens BOTH; pre-fix
  observable is `sxUnknown` + `weInternalWalkerFault` (KeyError net).
  `nsk*` symbol-kind gates added as a second bare-kind grep class.
- **F3 (new resolved fork) — guard-cond carve-out:** hoisting in
  while-guard conds flips R14 routing (preamble-emptiness dispatch,
  :3144–3200) and degrades `continue`-bearing loops that prove today;
  constraint 4 REPLACED with `ctx.inGuardCond` carve-out. A1 gains
  baseline-non-regression clause (d) + the "compound fault-free guard +
  continue" pin cell.
- **F4 (new resolved fork) — error text unified:** `symexForAll` suffix
  dropped; `detail` param deleted from `resolveEntryImpl`.
- **`resolveRoutineImpl` made real:** it existed only in C1's prose. Now
  the N1-introduced nil-core (the Invariant-3 "one predicate"); N2
  migrates resolution sites onto it; C1's confinement invariant holds
  as written.
- **Bypass census corrected:** 8 sites not 6 — the two `nnkPrefix` arms
  (`not` :1322, uNeg :1355) added; constructors correctly named
  (`mkStrOp`/`mkBorrowOp`, not all `mkBinop`). Constraint 1 extended to
  uNot operands. IR-pass alternative recorded as structurally impossible
  (IRExpr carries no type tag); type-enforced chokepoint recorded
  rejected.
- **Audit tests institutionalized:** N2's kind grep and A2a's chokepoint
  grep become permanent committed `staticRead`-based tests (TOT-1's own
  header rationale).
- **A2b restructure named:** the bAnd/bOr block parses both operands
  BEFORE the itBool branch — slice must classify first, then split parse
  paths; fast-path predicate quoted correctly (:1296).
- **A1 resized honestly:** degenerate cells pruned (atomic twins),
  depth axis only for call-bearing shapes, 3 new contexts (unary,
  call-arg, assert-arg), ≈60–70 procs, Size M–L; corpus-emitting macro
  named as sanctioned fallback.
- **A2a resized down (M):** round-1 "preamble availability audit" killed —
  all sites are `parseExpr` arms; plumbing exists by construction.
- **Renames:** `parseEntryTarget` → `parseEntryImpl`; `GenericDescriptor`
  now fully-parsed `seq[GenericParam]` (name/isStatic/constraint).
- **Logistics:** ADR-0030 pinned (stub with N1); psweep promoted
  scratchpad→scripts/ in N0; Windows CI leg mapping stated; X1 gains
  Z3-parity step, first run M; soft order N2-before-A2a.

## Slices
- [x] F0 — #147 (landed `799b0bc`, completed by N0)
- [x] N0 — DONE, commit `3994272` (2026-08-13). SW 70→71, CR2 pin
  updated, `tests/tsymex_phase15_N0_kindgate_widen.nim`, psweep promoted
  to `scripts/`. Sweep exception: g8_multi_param + g10_smoke are
  PRE-EXISTING known-red at base (compile-time "node has no type",
  `dsl_typebridge.nim:337`) — tracked as **issue #152**; slices do not
  gate on them until fixed.
- [x] N1 — DONE, commit `641b8f6`. walkableRoutineKinds +
  resolveRoutineImpl nil-core + resolveEntryImpl (unified error text, F4)
  + parseEntryImpl (6 macros; destructure stayed per-consumer — the
  quote-interpolation micro-improvement CRASHES the compiler for
  func-targeted SUTs via saveSymexWitness/saveSymexVerdict/
  symexCacheKeyForFn, types.nim:1530 case-object branch conflict;
  reverted per RFC caveat, do not re-attempt without investigating) +
  GenericDescriptor (hasGenericParams/genericParamsNode rebased) +
  ADR-0030 (D1 accepted, D2/D3 reserved) + 32-run validation green,
  CR2 pin unchanged. No SW bump.
- [x] N2 — DONE, commit `8f81ff8`. 11 sites migrated (incl. rune-compare
  intercept :2353, found by grep, absent from the RFC list); permanent
  audit test `tests/tsymex_phase15_N2_kindgate_audit.nim` (RED at base
  with exactly the inventory, GREEN post-migration); C3's symKind
  pre-filter dropped — probe-verified behavior-identical (getImpl on
  nsk{Param,Let,Var,ForVar,Result} never yields a walkable kind). 13×2
  validation green, CR2 pin unchanged, no SW bump. N3's set literals
  now at :1751/2360/2808/2822/2837/2866/4211.
- [x] N3 — DONE, commit `8defbf9`. Probes: nested method/converter
  ILLEGAL at non-top-level; `do:` rewrites to nnkLambda pre-semcheck →
  both set gaps unreachable → behavior-identical, NO SW bump (still 71).
  Consts: `routineShapedForClosureDetect = RoutineNodes - {nnkDo,
  nnkLambda}`, `nestedRoutineScanBoundary = RoutineNodes - {nnkDo}`; 7
  literal sites migrated; audit test extended (pattern d, multi-line
  sets); `tests/tsymex_phase15_N3_scan_boundary.nim` pins the lambda
  boundary (only end-to-end-testable member; nested proc/func/iterator
  statements degrade for an orthogonal pre-existing reason, documented).
  32/32 validation green, run FOREGROUND (first background attempt died
  silently at launch — lesson: verify backgrounded runs are alive, or
  run bounded calls foreground).
- [x] A1 — DONE, commit `65f5e5d`. 8 corpus files, 45 cells / 82 SUT
  procs, all green both backends (300s bound); CR2 unchanged ("71").
  THREE engine findings surfaced (issues filed, none block A2a):
  **#153** mod lowered as Euclidean (false sxRaised for negative x;
  arithmetic cell 2 domain-restricted as workaround), **#154**
  SOUNDNESS: byte-identical while-loop AST in a never-invoked sibling
  proc flips another proc's verdict sxUnsat→sxSat (Q1 path implicated;
  loop-guard cells use distinct delimiters as workaround), **#155**
  compound fault-free guard + continue degrades TODAY (CR-1b
  StmtListExpr no-op-preamble artifact → R14 Case-3) — RFC A1/GT5 text
  corrected as-built; the A2a carve-out is unaffected. Q1 compound
  bound NOT recognized (by design, pinned).
- [x] A2a — DONE, commit `2982597` (control loop finished it after
  agent takeover). SW 71→72, CR2 pin updated, chokepoint + guard-cond
  carve-out + UNTYPED-node carve-out (ADR-0002 isolation entry),
  permanent chokepoint audit test. Endgame history: sweep failures
  snd3_loopdegrade/r4_slice_binding fixed by agent triage; r4_strip
  137s = 6-way load contention (green solo + final sweep);
  **phase1_dsl = PRE-EXISTING break at shipped 0.3.4** (bisect-verified
  at 799b0bc; v64's unconditional classifyType in the bAnd/bOr block
  kills the untyped isolation layer; exposed by the promoted
  scripts/psweep.sh's wider coverage) — filed **issue #156**; sweeps
  now have THREE known-reds: g8_multi_param + g10_smoke (#152) +
  phase1_dsl (#156).
- [x] A2b — DONE, commit `d128dc0`. Classify-first split (typedness
  signal: `n[0].kind == nnkSym` — typeKind is UNSOUND for untyped
  and/or, bogus ntyCString, probe-verified); bitwise → chokepoint;
  boolean D1c verbatim; SW 72→73 + CR2 pin. **Fixed #156** (phase1_dsl
  green in full sweep). Latent twin bug documented dormant in
  isBooleanShortCircuitInfix. Sweep residue = #152 pair only (+
  r4_strip load-flake, solo-verified clean twice). Known-reds
  remaining: #152 pair.
- [x] A3 — DONE, commit `9a06a92`. Cluster A ACCEPTED: 11 corpus files
  × 2 backends green at walker 73; chronos hoist-shapes twin-identical
  sxUnsat; ADR-0030 D2 written; README gains routine-coverage +
  shape-invariance + upgrading (cache blast radius) notes.
- [x] C2 — DONE, commit `428d99c`. THREE consumers migrated
  (gatherTypeSubst, parseCalleeImpl captureConstraints, AND
  staticParamNames — a third identDefs re-walk the RFC's tally
  undercounted); instKeyFor descriptor-backed transitively; audit
  extension (nnkGenericParams scan) RED→GREEN; CR2 unchanged ("73").
- [x] C1 — DONE, commit `53ae99d`. Re-tree confined to
  resolveRoutineImpl (+routineImplMinArity totality guard); layout
  identity probe-verified (3 body shapes, pragma-slot-only delta);
  cache keys byte-identical before/after (F2 confirmed); NO bump
  (walker stays 73); ADR-0030 D3 written, status Accepted. N2's audit
  test caught the first-draft bare-kind gate (working as designed).
- [!] X1 — BLOCKED external (unchanged): chronos verify harness lives
  only on the unmerged `contextvars-rebase` branch. In-repo fallback
  (A1 chronos-faithful shapes, twin-identical sxUnsat) delivered and
  documented in A3. When Corey makes the harness durable: run it
  against walker-73 HEAD with the Z3-parity check first (X1 spec in
  the RFC), then after every future SW bump.
- [ ] N1 → N2 → N3; A1 → A2a → A2b → A3; C1 (after N3), C2 (after
  N1); X1 recurring. Soft order: N2 before A2a. See RFC inventory table.

## Open items (awaiting Corey)
- Chronos harness durability: merge `contextvars-rebase`'s `verify/` to
  chronos main (or relocate) so X1 can gate on it. External-repo action.
  (Unchanged from round 1 — still the only Corey-blocked item.)

## Review ledger (stage 4, round 1 — 2026-08-14)
Six review lenses (correctness, quality, security, design, RFC-fidelity,
test-coverage) over 799b0bc..53ae99d; all C/H + disputed findings
adversarially verified by independent agents.

| id | sev | finding | status | proof / reason |
|----|-----|---------|--------|----------------|
| C1 | Crit | tsymex_phase15_CR2_cachekey.nim (the canonical `== "73"` walker-version pin) is not registered in nelli.nimble's test task — it never runs in CI; pre-existing (v64–70 drifted the same way) but this RFC re-points every slice at it | fixed `c1637e2` | registered + green both backends; stale comment updated |
| H1 | High | isAtomicIR (dsl_parser.nim:1200) is an empirically-accreted allowlist with no completeness audit; residual hazard CONFIRMED concrete: iekField/iekIndex/iekContains are zero-fault compound kinds (rhsHasInlineDefectFork clears them for bare-var receivers), NOT allowlisted, reachable via the general-infix chokepoint, and mechanically flip D1c's `rhsPreamble.len == 0` fast path (downstream defeat unproven by any test — same "open, unswept" class the doc comment names) | fixed `9a5c707` | tests/tsymex_phase15_A2a_atomicir_audit.nim: 3 twin-pair characterizations (iekField/iekIndex/iekContains under and-RHS) ALL AGREE both backends — hazard latent-but-benign, no bump; subfield-kind-peek audit over runtime{,_strings}.nim RED-probe-verified; isAtomicIR comment + ADR-0030 D2 updated (also closes L5) |
| H2 | High | ctx.inGuardCond carve-out has NO behavioral test — deleting `ctx.inGuardCond or` from parseAtomicOperand:1310 passes every committed test (only the marker-count audit exists). Verified HOLDS-NARROWED: the demonstrative sxSat→sxUnknown flip is not witnessable in the current corpus (A1_loopguard cell (b) is already sxUnknown via bAdd's inline defect fork, unrelated); a FAULT-FREE compound guard operand (e.g. bitwise) + continue would witness it and is the regression test to add | fixed `ce7b64a` | tests/tsymex_phase15_A2a_guardcond_pin.nim: `(i and 3) < 3` + continue pins sxSat; RED-verified against carve-out deletion. NEW LANDMINE documented in-test: a `!=` guard degrades even WITH the carve-out (desugars to `not (a == b)`, prefix traversal deposits a guard preamble independently) — flag for re-review |
| M1 | Med | symexFind (symex.nim:1105) and assertCoveredBy (:1240) hand-inline the resolve→parseProc ritual parseEntryImpl exists to collapse; the exclusion comments (:1101/:1237) are FALSIFIED by symexFindAllWitnesses (:1654), which routes through parseEntryImpl while consuming .params at macro time — drop-ins are byte-identical | fixed `1adcd33` | drop-ins applied, comments rewritten; green: N1_resolution_gates + phase7_assertcovered + tot1 corpus, both backends. Leftover: parseEntryImpl docstring in dsl_parser.nim still names old exclusion — M3 agent reconciles |
| M2 | Med | N2/A2a audit greps have named blind spots: single-line-only substring match on one spacing (`{nnkFuncDef,nnkProcDef}` respaced or line-wrapped evades pattern a), and a new 2-element `of nnkProcDef, nnkFuncDef:` case arm evades all patterns (>2 threshold on pattern d) | fixed `b47d129` | token-walk scanner (any spacing/order/wrap) + 2-element case-arm pattern with fingerprinted exemption; 3/3 injected probes tripped RED, green at HEAD both backends |
| M3 | Med | isBooleanShortCircuitInfix (dsl_parser.nim:347) still uses the typeKind signal A2b proved UNSOUND for and/or; two non-equivalent predicates answer the same boolean-vs-bitwise question; known fix (n[0].kind == nnkSym) not applied to the sibling; zero coverage on the untyped not(p and q) path. Tempered: correctness traced the failure is a hard error pre- AND post-diff (Invariant-3-compliant), not silent corruption | fixed `4c642ea`+`d422c72` | REFIT: claimed failure mode empirically REFUTED (grammar forces nnkPar around not-wrapped and/or; the nnkInfix conjunct fails before typeKind is reached — landmine never reachable via natural source). Shipped as refactor-under-green: shared isResolvedBoolAndOr predicate, byte-identical typed path (De Morgan), 2 characterization pins in phase1_dsl, comments corrected, no SW bump (CR2-confirmed both backends). d422c72 also closes M1's docstring leftover |
| M4 | Med | N1 negative-kind rejection (template/lambda/iterator) pinned for only 2 of 9 entry macros (symexFind, symexCacheKeyForFn); the other 7 have no rejection test. Mitigation: all nine route through the same resolveEntryImpl wrapper (triple-confirmed), so residual risk is per-site routing regressions only | fixed `aed294e` | 7 new suites / 21 tests, all nine macros pinned via not-compiles; green both backends |
| L1 | Low | dt-bounded.sh:27 splices $test_file unquoted into bash -c (injection point OUTSIDE this diff); psweep.sh widens exposure by auto-globbing tests/ into it | open | security; psweep's own xargs argv-passing is safe |
| L2 | Low | psweep.sh always exits 0 regardless of test failures (run_one ends in echo); intentional (outlog is source of truth) but undocumented — add a header comment | open | quality |
| L3 | Low | ADR-0030:58 credits parseEntryImpl with "all nine" macros (currently 6; fixing M1 makes it true) | open | subsumed by M1 fix |
| L4 | Low | ADR-0030:6 header dates D2 as 2026-08-13; A2a landed 2026-08-14 | open | git log %ad |
| L5 | Low | isAtomicIR's StrAt/StrLen/SeqLen widening documented only in-code, not in ADR-0030 D2 normative text | open | largely subsumed by H1 fix |
| L6 | Low | resolveRoutineImpl re-tree runs unmemoized (N allocations for N call sites; shared children, correctness-neutral) | open | perf only |
| L7 | Low | staticParamNames (C2's third consumer) has no dedicated new test; covered only indirectly via pre-existing g7/g10 (g10 known-red #152) | open | test-coverage |
| L8 | Low | A2a marker audit detects regression at known sites only, never omission at NEW sites (inherent to marker-comment technique; acknowledged in test header) | open | documentation-only |

### Round 2 (2026-08-14) — re-review of the 8 fix commits (53ae99d..HEAD)
Lenses: security + design (standing) + correctness. Full sweep running
in parallel.

| id | sev | finding | status | proof / reason |
|----|-----|---------|--------|----------------|
| R2-1 | Med | 4c642ea inverted the untyped and/or routing: `if not isResolvedBoolAndOr(n)` sends untyped (n[0] not nnkSym) to the BITWISE branch, opposite of the documented carve-out; behaviorally inert only via two uncoordinated safety nets (parseAtomicOperand ntyNone no-op; isolation entry preamble hard-error); typed path genuinely byte-identical | fixed `11c72cf` | one-line explicit gate (`n[0].kind == nnkSym and not isResolvedBoolAndOr(n)`); untyped → boolean branch as documented; 6-file validation matrix green both backends, walker 73 confirmed |
| R2-2 | High | atomicir audit scans only 2 files (scope inherited from the verifier's one-time inventory); runtime_heap.nim:578/654/663 + abstraction.nim:307-325 already contain the policed pattern (allowlisted kinds only today, so no live violation) | fixed `a5e1a7e` | scan widened to 5 downstream consumers with the producer-exclusion principle documented; RED-probe in abstraction.nim tripped, reverted clean, green both backends; zero new exemptions needed |
| R2-3 | Low | N2 audit case-arm exemption fingerprint is refactor-brittle by design (disclosed trade-off; a future audit RED at that site may be the fingerprint, not a violation) | wontfix (informational) | design lens |
| R2-4 | Low | isAtomicIRAllowlist in the audit test is a hand-copied mirror of isAtomicIR, sync-by-comment | deferred (Low, mandate) | design lens |
| R2-5 | — | `!=` guard landmine (from H2): traced to the PRE-EXISTING CR-1b nnkStmtListExpr unconditional leading-statement deposit — byte-identical at base 799b0bc; ctx.inGuardCond did not exist pre-RFC; A2a NARROWED the pre-existing surface | filed **#157** | correctness lens trace; not an RFC regression |

### Round 3 (2026-08-14) — re-review of 11c72cf + a5e1a7e
Security: CLEAN (algebra hand-verified incl. untyped short-circuit; all
5 audit files wired correctly). Design: 3 findings.

| id | sev | finding | status | proof / reason |
|----|-----|---------|--------|----------------|
| R3-1 | Med | 11c72cf restored the load-bearing conjunct as an anonymous inline expression — the exact shape that let 4c642ea drop it invisibly; should be a named complement (isResolvedBitwiseAndOr) beside isResolvedBoolAndOr | fixed `ce72e60` | named complement + load-bearing-conjunct doc comment citing the regression history; naming only, green both backends |
| R3-2 | High | audit's "every downstream consumer" claim false: runtime.nim textually includes 5 fragments; staticRead sees only the directives — runtime_floats/exceptions/closures unscanned (all 3 verified zero live peeks today; control-loop grep confirmed) | fixed `0e22976` | 3 fragments added to the scan, zero new exemptions needed; header claim replaced with honest disposition list |
| R3-3 | Med | no structural guard against scanned-set drift (hand-maintained list); fix = include-graph guard derived from runtime.nim's own staticRead content + honest disposition list for standalone modules (staticExec off-limits: Windows container) | fixed `0e22976` | include-graph guard asserts every runtime.nim include fragment is scanned; RED-proven by dropping runtime_floats from the list |

### Round 4 (2026-08-14) — re-review of ce72e60 + 0e22976
Security: CLEAN (extraction char-identical, single call site; include
parser correct on all real formats; latent Low noted: comma-form
`include "a", "b"` would evade the guard — no such form exists).
Design: 1 finding.

| id | sev | finding | status | proof / reason |
|----|-----|---------|--------|----------------|
| R4-1 | Med | include-graph guard asserts membership in a bare parallel name list, not actual scan coverage — a hurried "append the name" fix to a RED guard reproduces R3-2 behind a green test | fixed `fe609ab` | single scannedFiles table now feeds both the scan loop and the guard; parallel list deleted; RED-proven by dropping runtime_floats entry; green both backends |

Round-4 clean otherwise: disposition list verified complete and honest
against all 16 smt files (spot-checked scan.nim/stdlib_models.nim/
types.nim exclusion rationales — all hold); named-predicate pair
coherent, no drift.

### Round 5 (2026-08-14) — convergence check of fe609ab: CLEAN
Verified: all 8 entries survived the restructure, guard tied to scan
coverage by construction, no stale references, header mechanically
accurate. Sub-Medium notes (not findings): cosmetic comment
overstatement at audit :331; theoretical fabricated-content gap
(no structural fix available without disproportionate macro machinery).

**FLOOR REACHED: round 5 surfaced nothing above Low. Review loop
terminated per the stage-4 contract.**

Remaining Lows (reported, not fixed, per mandate): L1 (dt-bounded.sh
unquoted splice — outside this RFC's diff), L2 (psweep exit-0
undocumented), L4 (ADR D2 date off by one), L6 (re-tree unmemoized),
L7 (no dedicated staticParamNames test), L8 (marker-audit omission
limitation, inherent), R2-4 (hand-mirrored isAtomicIRAllowlist const),
R4 latent (comma-form include would evade guard; no such form exists).
L3/L5 became true/closed via the M1/H1 fixes. R2-3 wontfix
(informational by design).

Round-2 clean: parseEntryImpl routing (verbatim apiName/maxInst, no
dangling impl refs), all new tests non-vacuous, N2 exemption fingerprint
matches the real site, staticRead paths literal/safe, cache-key
derivation untouched, no script changes.

Refuted/dropped during verification: correctness reviewer's defense of
the symexFind/assertCoveredBy exclusion ("different downstream shape")
— refuted by symexFindAllWitnesses precedent. H2's original
"regresses every continue-bearing loop" blast-radius framing —
narrowed as above (gap real, illustration not witnessable at HEAD).

Verified-correct highlights (round 1): all four RFC hard constraints
hold in shipped code; C1 cache-key safety independently confirmed
(key derives from symBodyHash, upstream of the re-tree — no
funcDef/procDef aliasing possible); three failure policies remain
separated with no leak into the nil-core; GenericDescriptor abstraction
complete (single dual-location lookup site); N2 migration complete
(remaining raw getImpl calls all correctly out of scope); no
Invariant-3 violation path found; no exploitable security issue in the
diff; version-bump bookkeeping consistent everywhere.

## Key decisions (this session, 2026-08-13)
- chapulin round-6 Track A/B PARKED (Corey) — this RFC runs first.
- Round-2 forks F3/F4 resolved with code evidence per the standing fork
  filter (as F1/F2 were in round 1) — none escalated.
- Audit acceptance = committed tests, never one-time greps
  (institutionalized in N2/A2a).
