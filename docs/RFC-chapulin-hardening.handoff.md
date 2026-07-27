# RFC — chapulin consumer-hardening — handoff

- **Stage:** 3 (tdd grind) — **AUTONOMOUS GRIND COMPLETE 2026-07-26**   •   Architect rounds 1&2 done; fork resolved
  - **Only INT-1 + Q1 remain, both with-Corey (see Resume at bottom). Next process step: Stage 4 `/code-review` once INT-1/Q1 are settled.**
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
  2. **Backend-divergent verdict on a multi-condition while-guard (potential b7258f7-class soundness
     bug).** A 3-way-conjunction guard `while i<s.len and s[i]>='0' and s[i]<='9': inc i` targeting a
     REACHABLE label gave c=sxUnsat vs cpp=sxUnknown (divergent). c=sxUnsat for a reachable target =
     false "unreachable" = the dangerous direction. Unrelated to Q1's find path (never calls find).
     NOT root-caused (spike timebox). RECOMMEND separate triage — backend verdict divergence is the
     exact class dt-bounded/both-backend discipline exists to catch.
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
