# S8bp -- DONE

- **sha:** 79037e478ef5eed63e6d90fe5c67d601467c5759 (branch `rfc-0005-s8bp`)
  - 2852f5a docs(rfc): RFC-0005 S8bp -- add the slice row
  - b0e9941 perf(symex): RFC-0005 S8bp -- every checkCapped search and the kind probes in contexts of their own
  - 035e3a2 fix(symex): RFC-0005 S8bp -- decide a string's regex memberships with a negated one as one
  - 79037e4 docs(rfc): RFC-0005 S8bp -- as landed (row flipped to done)
- **base:** origin/rfc-0005-s8bm at 14d7e81 (based on 621af8f, walker 214).
- **walker:** 214 -> 219 (provisional). The CR2 `==` pin is updated and passes (6/0 on both Z3 versions), and `>= 219` is pinned in the S8bp suite.

## A spec assumption that did not hold (not a BLOCKER: it widens item 1, the design does not fork)

S8bm's note and the job say that the facts-first check, (1b) and (1c) are "theory-free and small", leaving only (2), the uncapped (3) and `plain` to isolate. They are not small: a theory-free step holds all of the query's arithmetic. With S8bm's perturbation probe (30 unrelated constants before each query), every one of them moved by up to 3x on both Z3 versions (table below). In one case the outcome changed, not just the cost: under a cap of 8, `x * x * x == 1030301 * s.len` was SAT in 4,712,338 units in (1b) as is, and ran out at 20M when perturbed (Z3 4.13.4). So item 1 isolates **every** `checkCapped` step.

## Design

**Item 1: every step searches in a context of its own.**
- `ownContextSolver(ctx, roots, rlimit, seqTheory)` translates the query into a fresh context and returns `querySolver`'s solver there. A theory-free step gets the simple solver where `theoryFreeSimple` requires it.
- That covers the facts-first check, 1, 1b, 1c, 1c-capped, 2, 3 and `plain`. Step 2's assumption literal is made in its own context and the caps are translated into it. Models are translated back to the walk context.
- **Spend accounting is exact.**
  - `ownContextCheck` (which now takes assumptions) adds each context's whole `rlimit count` to `ownContextUnits`.
  - No search is left in the walk context, so `solveTargetHit` reads the spend as `ownContextUnits` grew. `rlimitCountNow` is deleted.
  - The stats `rlimitDelta` and `rlimit` read the same total. S8ac's `queryRLimitBefore`/`Pending`/`Solver` and `noteQueryRLimitBefore` are deleted, because no walk-context solver is built any more.
- **Instrumented build only:**
  - `symexStepStats` records each step's name, status and units.
  - `symexPerturbConsts` makes N unrelated Int constants in the walk context before each query (S8bm's probe, now a test switch like `symexFactsFirstOff`).

**Item 2: the kind probes run in their own context.**
- `probeContext()` creates a fresh context without making it current. `seqCapKinds()`, `ensureByteDomainKinds()`, `ensureIntDivDeclKinds()`, `heapChainDepth`'s probe and `theoryFreeSimple()` build their terms there; the procs that only probe no longer take a `ctx`.
- `heapChainKinds` (S8bd) is a fifth probe that the job did not list; it is moved too.
- Decl kinds belong to the linked Z3 build, so they are the same in any context.

**Item 3: regex memberships with a negated one are merged.**
- Z3 decides each membership on its own. Probed in fresh contexts on 4.13.4:
  - the query as lowered: UNSAT in 6,693,587 units under the 128 cap, unknown at 20M without it;
  - with `substr` removed (no merge): 5,139,521 capped, unknown at 20M uncapped;
  - as one membership `s in R1 & comp(R2)`: UNSAT in 1,392 units (1,611 capped).
- **`lowerRegexEntry` from a literal start 0** (`contains` and `match` with no start) reads `s` itself. It drops `str.substr(s, 0, len(s) - 0)` and the range test, so the negated `contains` becomes a membership literal of `s`. This is required: without it there is nothing to merge.
- **`mergeMemberships`** (in `checkCapped`'s `rootsIn`, so every path including `plain`):
  - For a string term with two or more memberships among the roots' top-level conjuncts, at least one negated, it replaces them with one membership of the intersection (a negated one enters as `comp(R)`).
  - The models are the same.
  - Byte-domain constraints stay as they are, and roots with no such group are untouched.
- S8ay's `endsWithRun` drops its `s.len <= 8` bound, restoring the original pin.

## RED / GREEN observed

1. **Per step, as is vs perturbed** (suite (1), three walks covering all eight steps).
   - RED on both Z3 versions, at 0120f56 (item 2 only) and again at that code with the final test file; the numbers are in the table below.
   - GREEN: every step's status and units are identical, on both versions.
2. **Exact spend** (per-step units = per-query `rlimitDelta` sum = target-hit units).
   - RED at 0120f56 (only step 1 isolated), on 5.1: 839,015 / 840,025 / 840,388.
   - GREEN: 1,106,184 for all three (5.1); 1,499,189 for all three (4.13.4).
3. **A thread's first walk vs its second** (`lastNl`, cap 8, on a fresh thread).
   - RED on 5.1: step 3 took 482,126 units in the first walk and 85,882 in the second (facts-first 146,229 vs 222,919, 1b 352,184 vs 177,008). 4.13.4 was already equal, so it has no RED there.
   - GREEN: identical on both versions. This was GREEN after the probe move alone, before item 1.
4. **Unbounded `s.endsWith(re"b+") and not s.contains(re"b")`.**
   - RED on 4.13.4: `sxUnknown`, 11,234,812 units (`beSolverUndef`, cap in step 2's core).
   - GREEN: `sxUnsat` in 4,733 units on 4.13.4 and 4,785 on 5.1. The ceiling is 20,000 on both.
5. **Victim found by Windows CI**: `tsymex_rfc0005_s8ar_remainder`'s `iMid` pin, on Z3 4.13.4. Reproduced locally (4.13.4 49/1), then fixed (50/0 on both versions). See "Soundness bugs found".

## Before and after (units, Z3 5.1 / Z3 4.13.4)

Per step, as is / perturbed (30 unrelated constants):

| Step (SUT) | before 5.1 | after 5.1 | before 4.13.4 | after 4.13.4 |
|---|---|---|---|---|
| factsFirst (`preSufNl`) | 369,908 / 327,761 | 366,523 / 366,523 | 242,158 / 202,281 | 212,551 / 212,551 |
| 1b (`preSufNl`) | 191,428 / 43,221 | 366,363 / 366,363 | 397,981 / 221,844 | 212,482 / 212,482 |
| 1c (`preSufNl`) | 114,891 / 350,726 | 366,523 / 366,523 | 398,245 / 202,116 | 212,551 / 212,551 |
| 1c-capped (`preSufNl`) | 412,527 / 199,445 | 366,535 / 366,535 | 398,240 / 202,103 | 212,562 / 212,562 |
| 2 (`preSufNl`) | 401,123 / 231,590 | 401,129 / 401,129 | 238,219 / 327,223 | 250,485 / 250,485 |
| 3 (`lastNl`, cap 8) | 85,882 / 322,405 | 154,580 / 154,580 | 207,893 / 464,636 | 330,859 / 330,859 |
| plain (`plainNl`) | 124,550 / 92,799 | 46,746 / 46,746 | 74,780 / 94,956 | 46,624 / 46,624 |
| 1 (S8bm; `preSufNl`) | 372,262 / 372,262 | 372,343 / 372,343 | 250,672 / 250,672 | 250,753 / 250,753 |

Whole walks (sum of steps): `lastNl` 1,106,184 (5.1) and 1,499,189 (4.13.4); `preSufNl` 2,253,830 and 1,365,507; `plainNl` 47,284 and 47,152. Each is identical as is, perturbed, and as a thread's first or a later walk.

Item 3, the unbounded endsWith run:

| | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| before | sxUnsat, 5,758 | sxUnknown, 11,234,660 (11,234,812 in the suite) |
| after | sxUnsat, 4,785 | sxUnsat, 4,733 |
| `len <= 8` twin, after | 5,325 | 5,097 |

**Cost (wall time; loads noted).**
- A fresh context plus solver plus translation costs about 8-10 ms (300-iteration probe under load 14-15, both versions). Most queries open two contexts (facts-first, then step 1).
- Built binaries run side by side against S8bm head 14d7e81:
  - `r4_strip` (5.1): 193 s and 190 s base against 244 s and 247 s (load 12-13).
  - `s8ae_remainder` (4.13.4, compile included): 229 s against 225 s (load 14).
- `r4_strip`'s time is one 20M-unit budget-out (strip idempotence; every other walk takes under 0.3 s), and its units are equal (20,031,338 vs 20,031,194).
  - Its step 3 took 135 s in its own context and 58.5 s in the walk context, for the same 10M units (local `-d:zz` toggle, not committed): Z3's wall time per unit follows term order.
  - The walk alone, side by side: 177 s and 152 s base against 168 s and 143 s new (load about 8).
- The suite binary runs in 4.5 s (5.1 c), 6.4 s (4.13.4 c), 4.7 s (cpp 5.1) and 4.7 s (cpp 4.13.4). Wall time including compile is 51-60 s (c) and 83 s (cpp), compile-dominated.

## Suites (ok/failed, c backend; identical on Z3 5.1 and 4.13.4; 75 runs at 28676e0 = code of the final head, except s8ar)

The list is the job's named suites plus every file from `command grep -l 'units\|rlimit' tests/tsymex_*.nim` (32 files), plus four for the regex lowering and query shapes:

| suite | 5.1 | 4.13.4 |
|---|---|---|
| s8ae_remainder | 16/0 | 16/0 |
| r4_strip | 5/0 | 5/0 |
| g1b_concolic | 15/0 | 15/0 |
| s8ax_remainder | 52/0 | 52/0 |
| g2_flip | 8/0 | 8/0 |
| phase13_rlimit | 1/0 | 1/0 |
| phase15_CR2_cachekey | 6/0 | 6/0 |
| r6_b5_chained | 9/0 | 9/0 |
| r6_n36_raise_degrade | 8/0 | 8/0 |
| s1b_kinds | 18/0 | 18/0 |
| s1c_verdict | 24/0 | 24/0 |
| s8ac_remainder | 19/0 | 19/0 |
| s8ad_remainder | 13/0 | 13/0 |
| s8ag_indexsplit | 15/0 | 15/0 |
| s8aj_remainder | 21/0 | 21/0 |
| s8aq_remainder | 13/0 | 13/0 |
| s8au_remainder | 35/0 | 35/0 |
| s8av_remainder | 19/0 | 19/0 |
| s8aw_remainder | 31/0 | 31/0 |
| s8ay_remainder | 40/0 | 40/0 |
| s8ba_remainder | 32/0 | 32/0 |
| s8bd_remainder | 23/0 | 23/0 |
| s8bm_stability | 4/0 | 4/0 |
| s8bp_isolation | 8/0 (cpp 8/0) | 8/0 |
| s8k_bounds | 19/0 | 19/0 |
| s8o_termination | 14/0 | 14/0 |
| s8q_termination | 10/0 | 10/0 |
| s8r_theoryfree | 3/0 | 3/0 |
| s8t_termination | 20/0 | 20/0 |
| s8v_termination | 7/0 | 7/0 |
| s8y_budget_decline | 8/0 | 8/0 |
| snd3_6_equality_loop | 3/0 | 3/0 |
| snd3_loopdegrade | 7/0 | 7/0 |
| phase15_S6b_regex | 5/0 | 5/0 |
| phase15_S7b_smoke | 8/0 | 8/0 |
| s5_str | 35/0 | 35/0 |
| s8w2_hotfix | 4/0 | 4/0 |

`s8bp_isolation` and `phase15_CR2_cachekey` were re-run at the final code (c896190): 8/0 and 6/0 on both versions. `s8ar_remainder` (fixed in this slice) is 50/0 on both.

**Wider check on 5.1.** I ran the 392 tsymex suites not listed above at c896190, because every query's model can move. Windows `symex-mingw` covers all of them on 4.13.4. Result: all 392 pass (rc=0, 3,676 tests OK, 0 failed). This run was paused by the gate sweep. My first runner checked the pause flag only before waiting for a slot, so 3 runs launched about 6 s after the flag went up. The cleanup then killed those 3 in-flight runs (rc=143) instead of letting them drain. `slot.sh` now re-checks the flag immediately before every launch. The 44 remaining suites, including those 3, re-ran after the flag cleared, all green.

## Soundness bugs found

None. One model-specific pin moved: `tsymex_rfc0005_s8ar_remainder` "insert in the middle shifts the tail" read `r.witness[1] == 1`, but `iMid` reaches its label with (v=10, i=0), (any v, i=1) and (v=20, i=2). Z3 4.13.4 now returns (10, 0), which is a genuine witness: `@[10,20,30].insert(10, 0)` gives `@[10,10,20,30]`. The SUT now excludes v in {10, 20}, so the middle insertion is the only way in. The fix is folded into the perf commit.

## Windows CI

Runs for c896190. Its code tree is identical to the head 79037e4: the head differs only in `docs/rfc/`, and the workflows' `paths-ignore: docs/**` skips docs-only pushes, so the head has no runs of its own.

| leg | run id | result |
|---|---|---|
| symex-mingw | 37126510248 | success |
| fuzzer-mingw | 37126510207 | success |
| fuzzer-msvc | 37126510190 | success |

Earlier shas:
- At 28676e0 and ba1bdfd (WIP), symex-mingw failed on the `s8ar_remainder` `iMid` pin (runs 37120679400 and 37120101378). The fix is folded into b0e9941.
- The runs for ec42c10 were cancelled as superseded.

## Different mechanisms, reported and not fixed here (also in the RFC's "As landed (S8bp)")

- **PRECISION: the concolic scratch solves still check in the walk's context.** These are `concreteBranchOutcome`, `concretelyInfeasible`, and `runConcolicCollectImpl`'s concrete-inputs check. They belong to concolic collection, not the walker's search, and run under `concreteBranchRLimit`. One that runs out degrades to "not determined", and how much it spends can follow what the context holds.
- **PRECISION: after a facts-first SAT, steps (1b) and (1c) repeat a check whose answer is already known.**
  - (1c) is the facts-first query under a larger budget, so in a fresh context it is the same search to the same SAT.
  - (1b) asserts a subset of the same terms, so it is SAT too.
  - Cost when step 1 then fails: `lastNl` (5.1) spends 295,900 + 311,463 of its 1,106,184 units there.
- **PRECISION: Z3's wall time per unit follows term order.** Units are now a function of the query alone, but a translated context's term order is not the walk's. `r4_strip`'s budget-out step 3 took 135 s here against 58.5 s in the walk context, for the same 10M units.
- **PRECISION: `mergeMemberships` reads top-level conjuncts only.** A negated membership under a disjunction or an `ite` (`a or not s.contains(re"b")`) is still decided one membership at a time.

## Tree state

- Worktree `/home/corey/tmp-usage/work/wt/s8bp` is clean at the head.
- The baseline worktree `wt/s8bp-red` (14d7e81, for the RED and perf baselines) has been removed.
- Probes, logs and runners are in `/home/corey/tmp-usage/work/s8bp-work/`:
  - `probe*.nim`, `raw/`, `v/<tag>/summary.txt`;
  - before: `raw/p1-*`, `p3-*`, `p5-*`; after: `raw/after-*`.
