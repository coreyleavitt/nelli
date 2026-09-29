# RFC-0005 branch-scoped-degrade (soundness channels) — handoff

- **Stage:** 3 (implementation, `/tdd` under `/loop`), started 2026-09-25.
  Design rounds 1–2 done 2026-09-20 (see below).
- **Branch:** `rfc-0005-soundness-channels` (the `rfc-*` name triggers the
  three Windows legs). Base `6cbfe8f`. Rounds 1–2 committed at `c59d7ea`.
- **Scope:** fork i1 **resolved by Corey 2026-09-25** — "til done, do not defer
  anything": full scope, SAT replay half included, one RFC. Open forks i2
  (`blocked_by` edge — tracker metadata, blocks nothing) and i3
  (transparent-pragma companions — blocks **S8 only**).
- **Working-tree hazard:** the checkout carries ~676 spurious filesystem mode
  flips (100644→100755). Always stage with `git -c core.fileMode=false add
  <paths>`; never `git add -A`.
- **Baseline:** sha-pinned sweep of `6cbfe8f` in a scratch worktree →
  `scratchpad/baseline-6cbfe8f.log` (gate every semantics-bearing slice with
  `scripts/sweep-diff.sh` against it). **Recorded 2026-09-25: pass=489 fail=0 skip=7
  total=496, drift 0, warn_total=7437** (c backend, -j 3, 900s timeout).
- **Shared slice brief** for every implementing agent:
  `scratchpad/SLICE-BRIEF.md` (session scratchpad).

## Current position (refreshed 2026-09-29 13:04Z)

- **Slices done:** 12 of 15 — S0 (`8a7384b`), S0b (spike), S1 (`d2c2226`),
  S1b (`a898905`), S2 (`48c30d6`, merged `1519608`), S1c (`489a1e7`),
  S3 (`e37c3b7`), S4 (`e7d3c7b`), S5 (`c2beefd`), S6a (`a82ed95`),
  S6b (`11e0f83`, confirm sweep regressed=0), S7 (`69a86a8`). Walker 146.
- **Order change:** S8 hard-pauses on fork **i3**; S10 has no dependency on S8/S9,
  so **S10 (opus) runs now**; S8 -> S9 -> S11 follow once i3 is answered.
- **Branch vs main:** `main` is still `6cbfe8f`; lands by fast-forward (no PR).
- **S10 landed `fbbc373`** (walker 147) per Corey's link-contract decision; pushed
  04:15 -- Windows CI running (first run of the new pcre64.dll step).
- **S1c "hang" corrected:** the N36 shape takes ~234s (six tainted queries each
  to the full 20M rlimit), not infinite; ~12s at 1M. Recorded in RFC §4.2.
- **Windows CI:** Corey approved the push; branch pushed 2026-09-26 04:44Z at
  `969d59c` (S0-S7). Runs: fuzzer-msvc 36218721870, fuzzer-mingw 36218721921,
  symex-mingw 36218721869 -- **all three green** (S0-S7 Windows-verified, incl.
  the Linux-hanging `b7r2_pathscope`). All three legs already use the patched-Nim OCI
  artifact (`setup-nim-artifact`), containerless.
- **i3 decided by Corey 2026-09-26: neither option -- a separate channel.**
  `feTransparentResultUsed`/`feTransparentArgNotInert` are not declines (nothing is
  approximated; soundness already comes from `feOpaqueCallUnmodelled` path taint);
  they report a false user `{.symexTransparent.}` claim. Move them out of
  `SymexErrorKind` into a separate annotation-violation channel on the result:
  error-severity, loud, verdict-neutral, no classOf/DeclineScope. S8 builds the
  split (and sets i3 `resolved` in the fence + writes the resolution into §13.3);
  S11 renders the channel. DeclineScope totality then holds with no special case.
- **Plan change -- S8b added (opus, after S8, before S9):** three pre-existing
  silent-substitution soundness bugs found during S6b/S10, all RFC-0005 §2.2-class
  (a site substitutes without recording taint) and so in scope, not deferred:
  (1) a call to a bodiless `importc` proc is analysed as an empty body -> default
  `false` -> **false sxUnsat with no errors** (repro at `969d59c`); (2)
  `parseInt` digits branch: target reachable only via `parseInt("+5")` -> false
  sxUnsat; (3) `exn_hierarchy.nim` lacks `ArithmeticDefect`, so `except
  ArithmeticDefect` misses DivByZero/Overflow -> false sxRaised.
- **Slices done:** 13 of 15 (S10 added).
- **S8 landed `654263b`** (walker 148; pushed). Sweep `s8-sweep.log`:
  unchanged=496 regressed=0 new-failing=0 new-ok=13. i3 resolved in the fence.
  DeclineScope gained an extra kind `dskWalkSite` (walker-made records; RFC §2.5
  "As landed"). Bucket-4 = 0. One verdict flip: sxUnknown -> sxSat off the
  over-claimed call's path (i3 split; clean rule-1 hit). Notes for S9: reach means
  *walked* not feasible; `dedupedByMsg` collapses same-text markers (dedup on
  msg+scope before relying on the reach join); Class-B sites have only the walk
  record; S7's capMutNeg false sxSat must be handled before deleting the veto.
- **S10 Windows CI (`fbbc373`): all three green** -- fuzzer-mingw 36228767377,
  fuzzer-msvc 36228767379, symex-mingw 36228767383 (first pcre64.dll run).
- **S8b landed `6004832`** (walker 149; pushed). Sweep: unchanged=496 regressed=0
  new-failing=0 new-ok=14 (complete-run diff). Windows CI on `dde01b4`: **all three green**
  (fuzzer-mingw 36238010826, symex-mingw 36238010682, fuzzer-msvc 36238010758). Fixed: bodiless importc/importcpp/dynlib callee ->
  fresh result + walk-site `feOpaqueCallUnmodelled`; `parseInt` now exact vs
  `rawParseInt` ('+', lone sign raises, out-of-range raises), `_` strings continue
  tainted (`seParseIntLaxSyntax`, dcFreshSymbol); `exn_hierarchy` audited against
  the compiler's `system.nim` at compile time (12 missing types, 2 wrong chains);
  **4th bug found and fixed:** exception *aliases* (`type E = ArithmeticDefect`,
  deprecated `DivByZeroError`) used the alias name as type id -> false sxRaised.
  S9 note: handler-side user exn capture (`collectUserExnAncestors`) skips
  `nnkType` except types -- do not rely on it.
- **S8c landed `3a95844`** (walker 150; pushed). Sweep -j 2: unchanged=495
  regressed=1 (test-only: a raise-site count 20->18 after the `bytes` model's two
  raises were deleted; count updated, test re-run green) new-failing=0 new-ok=15.
  Builtin models now apply only when the resolved callee is declared in Nim's lib
  dir; user overloads/converters are walked; markers match by module. Removed:
  name-only `replaceAll` (real `strutils.replace` now all-occurrence; on this Z3
  build it records `seZ3VersionMissing`, replay-confirmed; first-match model
  deleted), the `bytes` model (+ `maxBytesEncodingLen` budget field), the
  `hePtrArith` guard. Retired kinds: `seBytesSymbolicLength`,
  `seBytesLengthTooLarge`, `hePtrArith`. **S11 migration note must list:** the
  `ResourceBudget.maxBytesEncodingLen` removal (and its cache-key segment),
  `replace` all-occurrence, the three retired kinds.
- **S8d landed `f83e785`** (walker 151; pushed). Final sweep: unchanged=496
  regressed=0 new-failing=0 new-ok=16 (second run; the first found two r6 tests
  relying on a name-only `WeakRef` arm, which was deleted -- Nim's lib has no
  WeakRef). Type-head models apply only when `isStdlibTypeSym` (compiler builtin
  or declared under lib/); user types with stdlib names are classified by
  structure or declined (`feUnsupportedParamType`). S11 migration: user types
  named like stdlib types now get sxUnknown+feUnsupportedParamType (enums: real
  verdict); `WeakRef` arm gone.
- **Slices done:** 18 of 20 (S0-S10 incl. S8b/S8c/S8d; S8e added).
- **S8d Windows CI (`a95bb69`): all three green.** S0-S8d + S10 Windows-verified.
- **S9 landed `9ce6dba`** (walker 152; pushed 21:50Z). Final sweep `s9-sweep2.log`:
  unchanged=496 regressed=0 new-failing=0 new-ok=17. Both
  vetoes are deleted. What changed:
  - Reach join: an unreached anchored parse decline becomes `sevHint` with a
    suffixed msg. `dedupedByMsg` keys on msg+scope.
  - An unplaced decline sets `reachUnknown`, which blocks both directions.
  - `capMutNeg` is fixed. A closure re-reads its `var` captures in its
    constructing frame. Out of frame, or when the body writes a capture, it
    records the new kind `ceCaptureByRefUnmodelled` (dcSubstituted).
  - Renames: `rfc0005UnvetoedStatus` is now `rfc0005RawStatus`, and
    `decideVerdict`'s `vetoed` is now `reachUnknown`.
  - Flips: S0 pins 2 and 3 and S8 (c) go to sxSat. The by-reference SUTs and
    the dead-handler SUT move as listed in the RFC §2.5 "As landed (S9)"
    table.
  - Sweep 1 had one test-only regression: the N27 audit flagged
    `sameSymVal`, which is now tagged and the count is 67 -> 69. Sweep 2
    re-ran after that comment-only src change.
  - Found, not fixed: shadowed names share one env slot (an inner `var k`
    aliases the outer `k`). This is S8e-shaped.
  - S11 migration must list: unreached declines are now `sevHint`; the new
    kind; the two renames; twin anchored declines now keep one walk record
    each.
- **S9 Windows CI (`23692b2`): all three green.** S0-S10 (incl. S8b-S8d) Windows-verified.
- **S8e landed `f5a654c`** (walker 153; pushed). Final sweep: unchanged=496
  regressed=0 new-failing=0 new-ok=18 (first sweep's 4 regressions -- `new(T)`/
  `default(T)` on a typed-AST type symbol -- fixed, re-swept from scratch).
  New `scoped_names.nim` gives shadowing locals unique names `k__scN` (fixed 13
  false verdicts); `monomorphize` keeps node types (no more "node has no type");
  witness emitters bind names by symbol (`bindSym`, user types by their symbol,
  enums as `T(ord)`) -- also fixed a *silent* wrong-type witness bound to a
  caller-local `Color`. S11 migration: `name__scN` in messages/cache keys;
  formerly-aborting code now walks (recorded declines); witnesses no longer need
  `std/tables`/`std/sets` in the caller.
- **Slices done:** 20 of 23 (S8f done; S8g, S8h added).
- **S8e Windows CI (`93b74ac`): all three green.** S0-S10 incl. S8b-S8e Windows-verified.
- **S8f landed `f5e618a`** (walker 154; sweep2 regressed=0 new-failing=0,
  unchanged=496 new-ok=19). Table/HashSet len tied to present keys; seq witness
  uncapped (was 64) + ref-element cells; variant reassignment now Nim-2-faithful
  (branch change raises FieldDefect, ADR-0003 amended); runtime-discriminator
  constructor arm fields default (ADR-0029 amended); range-discriminator else arm
  renders; float default 0.0. **Replay NOT extended to clean candidates** (on
  evidence: it would refute 4 true claims -- analysis declares unchecked ints vs a
  checked SUT build -- and cannot catch ref witnesses, which S10 marks
  inconclusive); fixes are by construction. S11 migration: cache keys change
  (reassign IR branch grouping, walker 154); branch-changing reassignment ->
  sxRaised FieldDefect; runtime-discriminator ctor arms default; untouched float
  result binds 0.0; full Table/set/seq witness contents; OrderedTable/CountTable
  still decline.
- **S8f's audit found a remainder that still violates "a non-reproducing witness
  is never reported sxSat".** Resolved (not a fork -- "do not defer anything"
  plus Nim-faithfulness to the pinned toolchain) as two new slices, both before S11:
  - **S8g** (opus): float->int conversion never raises in Nim 2.2.10 (R16-2
    RangeDefect fork is fictional; reverse it -- out-of-range result is C UB, so
    model it soundly, not as a hardcoded `low(int)` unless proven); `-low(int)`
    OverflowDefect unmodelled; `split(s, "")` is `@[s]`; `new int` not
    zero-inited; slice/`seq.del` OOB is RangeDefect not IndexDefect; symbolic
    reassignment never tries the `else:` arm (false-sxUnsat risk).
  - **S8h** (opus): ref witnesses -- nil top-level ref renders non-nil; aliased
    params render distinct; live recursive ref field renders nil; ref inside a
    by-value field not rendered (ADR-0010 heap-witness programme).
- **S8g landed `b744fcd`** (walker 155; re-sweep regressed=0 new-failing=0,
  unchanged=496 new-ok=20; sweep started after the last src edit). ADR-0011
  R16-2 reversed: float->int never raises in 2.2.10; out-of-range is fresh +
  `feConvFloatToIntUndefined` (dcFreshSymbol); range targets fork RangeDefect.
  Also unary-neg overflow, `split(s,"")`, `new T` default, slice/del defect
  table, `^k` string-slice bound bug, reassignment else-arm, three dropped
  raise-fork drains. Full notes in RFC §2.5 "As landed (S8g)". S11 migration:
  float->int no longer sxRaised; new kind `feConvFloatToIntUndefined`;
  `heNewFieldZeroUnsupported`; slice/del defect classes changed; walker 155.
- **S8i added** (S8g's different-mechanism findings, not deferred): `low(int)
  div -1` / `mod -1` unmodelled; uint64->float treated as signed; int->range
  conversion is a pass-through; symbolic reassignment of a declined
  construction hits an internal assertion; concolic if-walker never drains
  scalar raise forks.
- 18:10Z weekly-Opus-limit pause (S8g agent died mid-wait; its sweep had already
  finished green and I landed it). Corey said continue at 18:20Z.
- **S8g Windows CI (`dea297f`): all three green.**
- **S8h landed and pushed.** `4cfa655` (walker 156) gated from worktree
  `scratchpad/wt-s8h`: regressed=0, sole new failure `tsymex_rfc0005_s2_replay`
  (S8h's intended fidelity change: `ref int`/`ptr int` witnesses are now
  faithful). Re-pinned test-only in `3e62bae` (lossy case moved to a `ref` of an
  object with a `string` field, unexecutable case to `ptr string`); rerun at
  `3e62bae` 15/15 OK. Branch pushed at `3e62bae`; Windows CI running
  (fuzzer-mingw green). `scratchpad/wt-head` may now be deleted.
- **S8h Windows CI (`3e62bae`): all three green.**
- **S8i landed `d1aff36`** (walker 157): feature `3dacacd`, fix `607e8d9`
  (array index is not a range conversion; reassignment decline kind), test
  `d1aff36`. Re-gate at the pre-rebase sha `8c878de` (tree identical but for this
  handoff): pass=511 fail=0 skip=7, regressed=0 new-failing=0. Pushed;
  **Windows CI (`d1aff36`): all three green.**
- **Fence grew S8j + S8k (`3d7dd06`)** from S8i's different-mechanism findings
  (none deferred). **S8j** (opus, running in `scratchpad/wt-s8j`, branch
  `rfc-0005-s8j`): SUT top-level `return` lowering + raise drain (false sxUnsat),
  inline `ref <case object>` field through a ref (false sxUnsat), narrowing int
  conversion as a RangeDefect fork, single range check on plain assignment;
  walker 158; self-gates -> `scratchpad/s8j-gate.log`. **S8k** after S8j:
  long-string Z3 queries that ignore rlimit (bounded decline to sxUnknown),
  concolic closure-condition resolution, `renderAsChoices` over ref params.
- **S8j landed `7d2c2d7`** (walker 158; fix `e70786a`, re-pin `7d2c2d7`):
  gate at `ef5f6d4` (tree = landed but for this handoff) regressed=0
  new-failing=0 new-ok=23. Pushed. **Windows CI (`7d2c2d7`): fuzzer legs green,
  symex-mingw RED** on `tsymex_r6_b7r_bytescan` B7R-LEG2-3 -- a Linux-skipped
  hanger that pinned `char(<int32>)` as the old B2 narrowing decline; S8j
  models it (sxSat, witness 65). Re-pinned test-only in `91b6d25` (standalone probe OK);
  **Windows CI at `a7ac700`: all three green.**
- **S8l landed `e8fc9dd`** (walker 159; feat `01defe9`, s6b re-audit
  `e8fc9dd`): re-gate at `e0ce94a` pass=513 fail=0, regressed=0 new-failing=0
  new-ok=24 (tree = landed but for this handoff and the Windows-only
  `b7r_bytescan` re-pin). Linux-skipped hangers checked by the agent: nothing
  touched. Pushed; **Windows CI (`e8fc9dd`): all three green.**
- **S8m landed `a696d80`** (walker 160; feat `e544c45`, fix `a696d80`): re-gate
  at `6b0cd1e` (tree = landed but for this handoff) regressed=0 new-failing=0
  new-ok=25. `heRefVariantUnsupported` removed (breaking for exhaustive
  matches); new `eeFinallyJumpOnRaise`; every Z3 error now forces sxUnknown.
  Pushed; **Windows CI (`a696d80`): all three green.**
- **Fence regrouped (`6556a23`)** from S8m's findings: **S8k = termination and
  resources** -- long-string Z3 queries rlimit does not bound, loop-unroll
  feasibility pruning (20GB at unwind 5; dead label after a loop is
  sxUnknown), replay SIGSEGV on a real nil write in debug builds. **S8n =
  precision** -- concolic closure conditions, `renderAsChoices` over ref
  params, a callee reading `result` before writing it, a closure returning a
  variant. **S8k (opus) running** in `scratchpad/wt-s8k`, branch
  `rfc-0005-s8k`, self-gates -> `scratchpad/s8k-gate.log`; it also retries the
  six Linux hangers. (22:10Z: first gate on `b795d9c` RED -- regressed=6 (r6_r3_svint_overflow, r1b_shortcircuit_oob, r6_r5_pairloop_counter, phase16_m3_rfind, r14_case2_degrade, r6_n21_pairloop_member) + new-failing=1; agent fixing (00:37Z: all six fixed in `c058475`; second gate `s8k-gate2.log` done: regressed=1 (r6_n36_raise_degrade rc=137 -- REAL: uncapped fallback query; fixed uncommitted, p9 32/32 green; agent died on a network error ~03:20Z, resumed 12:00Z; fix committed `4d66d76`, third gate `s8k-gate3.log` ~80% at 13:04Z, 0 FAIL), new-failing=0; 4 former Linux hangers (nulwitness, b1, b3, n10) now pass on Linux), then re-gates.)
- **Remaining:** S8k -> S8n -> S11 -> completion gate -> ff main + tag.
- **Open forks:** i2 (`blocked_by` edge, blocks nothing). i1 and i3 resolved.
- **Resume:** `/loop /tdd rfc-0005 til done. do not defer anything. use opus
  5.5 as the agent for the most dificult chunks try to plan that out.` -- on
  resume, check S8k (`rfc-0005-s8k`, `s8k-gate.log`); gates run from a
  worktree at the sha they certify, never the live checkout. Order: S8k -> S8n ->
  S11 -> completion gate (DoD §6 end-to-end via symexFind) -> ff main + tag ->
  `quipu warm --push`.

## Implementation plan — model allocation

Corey asked for Opus 5.5 on the hardest chunks. Allocation, by where the
soundness risk and the blast radius concentrate:

| slice | model | why |
|---|---|---|
| S0 exhibit pins | sonnet | test-only; needs care picking an over-only SUT |
| S0b payoff spike | sonnet | throwaway instrumentation + a long measurement run |
| S1 lattice/carrier/funnel | **opus** | 79 `uncertain` refs across the 17.6k-line runtime unit; the `degrade()` funnel shape is load-bearing for every later slice |
| S1b mint missing kinds | **opus** | ~40 `mkUnsupported` sites across `dsl_parser`/`canonicalize`; correspondence pin |
| S1c verdict rule | **opus** | the soundness-critical core: candidate pool, `shouldStop`, `isTargetLabel` solve |
| S2 replay substrate | **opus** | macro codegen, target-shaped replay, stackable capture |
| S3 monotonicity harness | sonnet | test macro over a battery |
| S4 classify allocDegrade | **opus** (upgraded 08:45) | first verdict flip; sets the pattern; `heUnresolvedRef` split |
| S5 classify funnels | **opus** (upgraded 09:55) | S4 found the shared-placeholder false-UNSAT hazard; same risk in `degradeStrArm`/R1 |
| S6 heap + kind splits | **opus** | `beBudgetExhausted` 3-way split is the most dangerous row in the RFC |
| S7 sinks + closure taint | **opus** | seven cross-path sinks; HOF decline migration gates S9 |
| S8 DeclineScope | **opus** | 39 `parseErrors.add` sites; structural totality pin (needs i3) |
| S9 delete vetoes | sonnet | small once S7/S8 hold |
| S10 SAT relaxation | **opus** | replay into the verdict across both `runSymex` consumers; Windows-only gate |
| S11 public surface | sonnet | `Soundness`, `gaps()`, render layer, cache schema |

## Slice ledger

| slice | state | commit | notes |
|---|---|---|---|
| S0 | done | `8a7384b` | 3 green pins through `symexFind`. Pin 1 routes `allocDegrade(heUnresolvedRef)` via `liftHeapValue`'s unsupported-pointee arm (string field through a ref) → flips at S4. Pin 2 `feUnsupportedExprKind` (inline `cast[int32]`) in a dead branch → cap veto. Pin 3 `ceUnsupportedHof` (`filter` over symbolic seq) → closure veto. Both flip to `sxSat` at S9. |
| S0b | done | (spike, nothing committed) | See **S0b result** below. |
| S1 | done | `d2c2226` | sweep 491/0/7, regressed=0, no bump. `degrade(w, kind, msg, sink = dsWalk)`, `DegradeSink` {dsWalk, dsHeapDepth, dsNewFieldZero, dsClosure}; `heapArmDegrade`; `lowerDegrade` + `takeLoweringPendingDegrade`; `forkPathTaintPrimitive` (grep-pinned private). `w.runTaint` has ONE writer (drain in `runSymexImpl`: `runTaintOf` over exnWarnings/parseErrors/closureErrs + ⊤ if `kindlessRunTaint`). 14 transitional sites marked `RFC-0005 S1b: mint kind`. Leak pin `stampLoweringPendingLeak` may fire in practice (unmeasured). `SymexErrorKind` has **61** members, not 41. |
| S1b | done | `a898905` | sweep regressed=0 after the N12 reason-suffix fix (full sweep regressed=1 before it; 24-test filtered re-sweep after). Minted `feUnsupportedStmtKind`, `weRecursionCycleCut`, `eeHandlerReraiseUnmodelled`, `ceClosureBodyDiverged` (walk sink, not closure sink), `weBreakOutsideLoop`, `beSolverUndef`; over-cap/missing callee kind via `unregisteredCalleeKey/Kind`. 54 `mkUnsupported` sites in `dsl_parser` take a kind; walker arm `w.degrade(stmt.unKind, stmt.reason)`. `kindlessPathDegrade` deleted; `kindlessRunDegrade` survives at exactly 2 sites (tainted target hit, tainted routeRaise) marked for S1c. Leak pin `stampLoweringPendingLeak` FIRES in `tsymex_r6_n40_alloc_totality` ({scSpurious, scIncomplete}) -- unfixed. Cycle cut now marks the run. Latent: parser flattens `block:` so `break` in a block inside a loop binds to the loop (out of scope, unfiled). Walker forks infeasible branches without a check -- walk-site records can come from dead paths (S8/S9). |
| S2 | done | `48c30d6`, merged `1519608` | 13 tests c+cpp green; `ReplayOutcome`, `replayWitness`, eligibility `pathTaint <= pathTaint(dcFreshSymbol)`, stackable capture (`enclosing`). S10 API: `emitReplayWitness(fn, parsed.params, witnessNode, targetNode, pathTaintNode)`; sxRaised replays against `tRaisedExn(raw.raisedTypeId)`. Refuted and inconclusive both go to sxUnknown; lossy witnesses: hit=confirmed, miss=inconclusive. Refuted pin uses a hand witness until S1c lets symexFind return one. Gate sweep at `1519608` pending. |
| S1c | done | `489a1e7` | sweep regressed=0 (second sweep; first regressed `tsymex_r6_n36_raise_degrade` 0->137 because solving a tainted path hung Z3 on the `iekStrInOptionRegion` decline residue). Fix: tainted-path solves run under `taintedSolveRLimit` (caller's `queryRLimit`, else `defaultConcreteBranchRLimit` 20M) -- **S10 must record this hazard.** Pure exported `decideVerdict(found, candidates, runTaint, vetoed)`; `RawResult.candidates` (empty on sxUnsat) for S10 replay; candidate extraction errors ride the candidate. `kindlessRunDegrade`/`kindlessRunTaint` deleted. n40 leak fixed (heap deref-write drains pending taint; `runConcolicCollectImpl` runs the leak stamp). Walker 140 -> 141. To force non-⊤ classes before S4: drive `decideVerdict` with a `Taint`, or IR via `mkUnsupported(kind, ...)`. S2's refuted pin still uses a hand witness (symexFind gives sxUnknown by rule 4 until S10). Vetoes unchanged (S9). |
| S3 | done | `e37c3b7` | test-only, no bump. `tests/tsymex_rfc0005_s3_monotonicity.nim` 29/29 c+cpp. `withPoisonedArm`; family 1: 3 witnesses (sxSat label, sxRaised, sxSat behind loop+call) x poison funnels F1 `heRefVariantUnsupported`, F2 `seUnsupportedStringOp` (`toOct`), F3 field-alloc decline, F4 heap-arm variant (2nd shape) x before/after. "After" poisons never fire (`shouldStop` halts on the clean witness) -- pinned as correct. Family 2a: sole tainted witness stays sxUnknown (4). Family 2b: over-taint-only unreachable pins at sxUnknown, commented with the flip slice -- S4/S5/S6 update them in place (verdict + classOf assert at the same site). |
| S4 | done | `e7d3c7b` | sweep regressed=0 new-ok=7; c+cpp green; walker 141 -> 142. **Spec correction (not a design change):** RFC §3.1's "`allocDegrade` arms = `dcFreshSymbol`" is mostly wrong -- only ONE allocDegrade site mints a truly fresh symbol. Minted `heUnsupportedPointeeRead` (tail, `liftHeapValue` else-arm, per-read `freshDegradeName`) = dcFreshSymbol; `seUnsupportedCompoundSortLeaf` = dcSubstituted (BV64 0 filler flows as a value); `heUnresolvedRef`, `heRefVariantUnsupported`, `heUnsupportedOwnership`, `feUnsupportedParamType/WitnessType`, `seUnsupportedTable{Val,Key}Type`, `seUnsupportedSetCharInterop`, `feUnsupportedExprKind`, `feUnsupportedOp`, `weInternalWalkerFault` audited and stay dcNoAnswer (substituting sites / wrong-sort shared-name placeholders); reasons commented on each `classOf` row. The `heUnresolvedRef` boundary arm is dead (`SymexRefUnresolvedError` only raised by `defaultZero`, always caught). **Hazard found:** a fixed placeholder name shared across reads correlates two "fresh" reads -> false sxUnsat (RED 2); every placeholder must use `freshDegradeName` per read before it may classify dcFreshSymbol (heap-arm tags like `__heapMultiVariantUnsupported` still fixed). `degradeHeapArmForPath` read sites skip `nilDerefFork` -> substituted until restructured. Flips: S0 pin 1 and S3 F2b-F1 -> sxUnsat via `checkUnsatOverTaintOnly`. Guards: n20:126,144 stay sxUnknown (ran); b7r2:381 reasoned (dcNoAnswer table kind). Later reclassifications must add their kind to the `reclassified` set in `tsymex_rfc0005_s1_lattice.nim`. |
| S5 | done | `c2beefd` | sweep regressed=0 new-ok=8, **no existing pin flipped** (new sxUnsat pins only in `tests/tsymex_rfc0005_s5_str.nim`, 40/40 c+cpp). Walker 142 -> 143. dcFreshSymbol: `seBytesLengthTooLarge`, `seBytesSymbolicLength`, `seZ3VersionMissing`, `seZ3StringIncomplete`. Minted `seRuneDecodeSymbolic` (dcSubstituted: `runeLen` forced 0, runes loop dropped). Audited dcNoAnswer: `seUnsupportedStringOp`, `seUnsupportedRegex`, `seNestedSeqUnsupported` (R1 funnel -- **RFC §3.1 wrong again**: R1 substitutes/omits; correction written in `classOf` + test header). **Hazard found + fixed:** declines raised BEFORE lowering their operands, silently dropping operand raises (`replaceAll($(a div b), ..)` lost DivByZero) -> 6 false sxUnsat observed; `runtime_strings.nim` now lowers operands (and parses the regex) first. `.high` pin is now an ordinal-adjacency pin. F2 (`toOct`) stays sxUnknown -- flipping needs an unplanned split of total-op string declines. R1 promotion would need fresh-per-read `iekSeqLen`, an IndexDefect fork in the `isIndex` decline, operand lowering in slice/add/del. Dead boundary arms for six string carriers (runtime.nim ~13139-13177) left in place. Regex tests use a local `re` shim (no libpcre in podman). |
| S6a | done | `a82ed95` | sweep regressed=0 new-ok=9; 31/31 c+cpp; walker 143 -> 144; **no flip possible or observed** (all three classes put scIncomplete on the run; payoff is S10 replay-ineligibility + S11 attribution). Site audit: k-unroll survivors (`:9642`, `:9921`) = dcFabricated keep `beBudgetExhausted`; AssumedBound (`:9913`) dcFabricated; `maxFrontierSize` prune (`:9689`) dcOmitted -> minted **`beBudgetExhaustedPrune`**; `maxCallDepth` bail (`:11165`) + two variant-constructor budget sites (`:10621`, `:10660`, unnamed in the RFC) dcSubstituted -> minted **`beBudgetExhaustedUnmodelled`**; `ceInlineBudgetExceeded` (2 sites) dcSubstituted, no split. Class channels: dcFabricated path ⊤ / run {scIncomplete}; dcSubstituted ⊤/⊤; dcOmitted path {} / run {scIncomplete} -- safe only because the prune is a halt; **structural pin: every dcOmitted degrade must be `discard w.degrade(`** (S6b must extend its scan if its halts emit via `heapArmDegrade`/`allocDegrade`/`runtime_heap.nim`). Site-count pin per budget kind now exists -- a new emission site must update it. **`ceInlineBudgetExceeded` still sets no PATH taint** (only the closure veto guards SAT) -- S7 must fix. Variant-constructor runs always also carry `feGlobalReadUnmodelled` (parser temp read unbound). 7 existing tests renamed to the split kinds. Sweep waiter: `.drift` is written at START; wait on line count. |
| S6b | done | `11e0f83` | gate: full sweep had 6 red (kind-name pins + `ln`), fixed; merged targeted resweep regressed=0 new-ok=10 -- full confirmation sweep of the sha: regressed=0. No existing pin flipped; new sxUnsat pins in `tests/tsymex_rfc0005_s6b_ops.nim` (41/41 c+cpp). Walker 144 -> 145. `feUnsupportedOp` split: majority stays `feUnsupportedOp` = dcSubstituted; minted **`feUnsupportedOpHavoc`** (dcFreshSymbol, 10 pinned sites) and **`feUnsupportedOpAborted`** (dcNoAnswer, boundary). `heNewFieldZeroUnsupported` dcFreshSymbol. Halts dcOmitted: `heDepthExhausted`, `heUnsafeCast`, `weBreakOutsideLoop`, `seVariantFieldOnDeclinedCtor`, `eeRaiseOutsideHandler`, `eeHandlerReraiseUnmodelled`. dcSubstituted: `seByteIterUnsupported`, `geInstantiationCapped`, `geDistinctBarrier`, `hePtrArith`, `feOpaqueCallUnmodelled`, `feEnumOrdinalUnresolved`, `feGlobalReadUnmodelled`, `feUnsupportedStmtKind`, `weRecursionCycleCut`. **`eeUnknownExnType` = dcSubstituted and taints** (closed a false sxUnsat AND a false sxSat): new `dsUnknownExn` sink, `taintsRun` predicate carves the sevWarning exception into `runTaintOf`/`checkUnsatOverTaintOnly`; path-joined only where the guess is acted on. Walk-level `iteSV` folds now drain pending merge taint. Residual ⊤: genuine (ekZ3*, walker fault, beSolverUndef, geConceptViolation, eeNotInHandler, ee*Unimplemented, feUnsupportedParam/WitnessType); S7 (ce*); S7/S10 (`ceNotImplemented`, `feExtractionFailed`); inert hints; S4/S5-audited ⊤; i3's `feTransparent*`. Dead boundary catches for RaiseOutsideHandler/RaiseUnimplemented/TryUnimplemented/ClosureUnimplemented. |
| S7 | done | `69a86a8` | sweep regressed=0 new-ok=11; c+cpp green; walker 145 -> 146; no kinds minted. **Sinks: 5 live, not 7** (RFC's two rows are one pool; parseInt digits-gate pool had no path scoping and was DELETED, `iekStrToInt` raise predicate widened instead). Closure call axioms admit only `taint == {}` arms and use a fresh result const per call occurrence; closure cache admits only clean; descent roots start `{}` and join exit taint into the caller; escaped body raises captured before `popFrame` and routed via `drainClosureRaises`. All 11 closure/HOF decline sites go through `closureDegrade` (sink + path taint). Classes: `ceClosureUnknownCallee` substituted, `ceClosureBodyUncertain` fresh, `ceUnsupportedHof` substituted, `ceClosureBodyDiverged` omitted; `ceNotImplemented` stays ⊤; `feExtractionFailed` ⊤, S10's. REDs included 5 **false sxUnsat** (closure raises dropped) and a false clean sxSat, now fixed. **S9 precondition pinned:** threadvar `rfc0005UnvetoedStatus*` = verdict with `vetoed=false`, never clean sxSat on S7 SUTs. **S9 must fix: capMutNeg -- a closure capturing a var mutated later still gives false sxSat without the veto.** S8: `runtime_heap` `lowerInExpr` sites never drain scalar raise forks (pre-existing, all raise sinks). S10: Nim `parseInt` accepts `+`/`_`, Z3 str.to_int doesn't -> widened raise predicate can over-report; replay should classify. |
| S9 | done | (this commit) | walker 151 -> 152. Vetoes deleted. The reach join (`reachJoinParseErrors`) recovers sxUnsat only behind a decline no path walks. The sxSat recovery comes from deleting the vetoes: a clean path wins under rule 1. Dedup is msg+scope. `reachUnknown` means an unplaced decline gives sxUnknown in both directions. By-reference captures are exact in frame and otherwise declined (`ceCaptureByRefUnmodelled`). Class B stays walk-record-only (a deviation from §2.5 point 1, recorded in the RFC). Pins: `tests/tsymex_rfc0005_s9_vetoes.nim` 19/19 c+cpp. |
| S10 | done | `fbbc373` | walker 146 -> 147. Replay in both consumers via one emitter `emitRunSymexReplayed` (`symex.nim` ~1570; symexFind ~1740, FindAllWitnesses/ForAll ~2530, replay before cache save). `SatCandidate` keeps its witness private; only symex.nim private procs convert it, only on confirmed replay (compile-time + file-scan pins). Refuted -> new `feReplayRefuted` hint. parseInt raise split: exact half clean, lax `+`/`_` half -> replay (`seParseIntLaxSyntax`); `"+5"` was a false sxRaised, now refuted. `--panics:on` -> no replay; lossy/converted witnesses confirm but never refute; unconvertible never run; non-void discarded. Cache stores confirmed candidate as its finding. **Contract (Corey 2026-09-26): fn must link+load; `SymexSettings.replay = false` opt-out emits no call** (cache key `;rp=off` only when off). g5 opts out. libpcre: dev image builds PCRE 8.45 from source (sha256 pinned; orchestrator verified tarball against PH10's GPG sig 45F6 8D54 ... 43D8); symex-mingw corpus job fetches `pcre64.dll` from nim-lang dlls.zip (hash-pinned). 10 replay-confirmed flips sxUnknown -> sxSat, each pinned with unvetoed-still-sxUnknown. Gate: sweep2 had 2 test-only fails fixed after (configdefaults field count, S3 F1 flip), substituted -> regressed=0 new-ok=12 (unmodified: `s10-sweep2.diff`). cpp S10/S2/S1c/S7 green. RFC §4.2 "As landed (S10)" records link contract + tainted-solve cost (N36 ~230s at 20M, not a hang). |

### S0b result — the payoff is real, and gated on S1c

Instrumented verdict site, 105 `== sxUnknown` files (the 5 Linux hangers
excluded), c backend: **727 runs** (sat 344, unknown 250, unsat 107, raised 26).

| population of the 250 `sxUnknown` runs | runs |
|---|---|
| over-taint-only, **no blocker at all** (flips on classification alone) | **4** (3 files, all `ceUnsupportedHof`) |
| over-taint-only, blocked only by kindless `isUnsupported` (S1b unlocks) | 1 |
| over-taint-only, blocked by kindless taint **and** tainted-label-reach (S1b+S1c unlock) | 49 |
| **over-taint-only ceiling** | **54 (24 files)** — pending Z3 confirming UNSAT on the newly-solved paths |
| blocked only by an ambiguous/split-pending kind | 81 (`beBudgetExhausted` 45, `feUnsupportedOp` 31, …) |
| carries an under/substituted/fabricated/no-answer kind | 115 |

- **`isTargetLabel`'s tainted-path skip fires in 195/250 (78%)** — the dominant
  blocker; confirms S1c (the solve) is load-bearing, not incidental.
- **Every `weInternalWalkerFault` (21) co-occurs with one of the two named
  kindless sites** — no unnamed kindless site exists in this corpus.
- **Split candidates the RFC's §3.2 does not name** (audit in S4–S6):
  `heUnresolvedRef`, `heRefVariantUnsupported`, `heUnsupportedOwnership`,
  `seUnsupportedTableValType`, `seUnsupportedSetCharInterop` are each reached
  both in-walk (fresh-symbol, `allocDegrade`-family) **and** at a param-boundary
  raise before any path exists (`dcNoAnswer`). **`heUnresolvedRef` is S0 pin 1's
  kind — S4 must split it** or pin 1 cannot flip. `ceInlineBudgetExceeded` is a
  budget kind analogous to `beBudgetExhausted`. `beBudgetExhaustedAssumedBound`
  (unnamed in the RFC) is unambiguously `dcFabricated`.
- The 19 legacy `except Symex*Error` boundary arms (`runtime.nim:12745-12932`)
  are mostly dead: only the old `raise (ref Symex...Error)(...)` spelling at
  param-boundary sites still reaches them.
- Spike artifacts: `scratchpad/classify.json` (best-effort, NOT the
  deliverable), `aggregate.py`, `spike-run-summary.tsv`.

**Found, out of scope, to file:** routing `cast[int32](x) + 1` through a helper
proc with declared return `int` trips a `lowerConvIntWidth` `AssertionDefect` on
the callee's return widening — caught at top level as a bare
`weInternalWalkerFault`. A real walker defect, unrelated to RFC-0005.

## What round 2 changed

Round 1 built the spec. Round 2 found that **four of its mechanisms were
unsound or unbuildable as specified**, that the slice plan would have shipped
green-but-inert for eight slices, and that two of its own flagship examples
contradicted the machinery meant to express them. The taxonomy, the naming, the
path-level decision and the veto redesign all survived.

### Corrections verified against the source (not taken on report)

| Round-1 claim | Reality | Where |
|---|---|---|
| Verdict rule: solve tainted paths in S8, flip UNSAT in S7 | **Mints a false `sxUnsat`.** `isTargetLabel` skips `trySolve` entirely on a tainted path, so a path that reaches the target unsolved is an *omission*. Shipping the UNSAT rule without the solve is exactly the failure the "S7 last" ordering existed to prevent. They are now one slice. | `runtime.nim:11159-11168`; §0.1, §2.3, S1c |
| Deleting `closureForcedUnknown` is safe once descent taint joins the caller | **Most closure emitters are not descents.** The HOF filter/map/fold declines mint `allocateSym("__hofFilterUnsupported")` into expression position and write only `closureCallErrors` + `sawUnknown` — **no path taint, and no `loweringDidDegrade`**, so the drain never taints the consumer. Same for `ceInlineBudgetExceeded` (`return funcApp`). Delete the veto first and a witness through the havoc value reports clean `sxSat`. | `runtime.nim:12505-12586`, `:11683-11691`, `:11815-11823`; §2.5, S7→S9 gate |
| "Every taint site has a `SymexErrorKind` in hand; the migration is mechanical" | **False at ≥9 sites.** The `isUnsupported` arm — §0.2's *flagship* example — forks tainted with **no error record at all**; `mkUnsupported` carries free text, not a kind. Also: cycle-break (no kind exists), over-cap missing-callee, `trySolve`'s `zsUnknown` result (both consumers, no kind — so a routine solver resource-out gets stamped `weInternalWalkerFault` today), handler re-raise, diverged closure body, break/continue, `isTargetLabel`'s own two writes. | `runtime.nim:11322-11338`, `:10855-10864`, `:7524-7525`/`:11167`/`:11491`, `:11226`, `:11866`, `:9564`, `:9574`; §2.2, S1b |
| `channels(k): tuple[path, run: Taint]` | **Cannot express its own motivating case.** The k-unroll survivor needs `(⊤, {scIncomplete})` and *no arm of round 1's sketch produced it* — §3.1 patched it with a footnote. Replaced by a named `DegradeClass` (5 members) with the coordinates derived once; 16 states → 5 named points. | §2.2 |
| `feUnsupportedOp` is "the known" split candidate | **`beBudgetExhausted` is the dangerous one** — one kind, three classes, merged deliberately, six emission sites. Round 1's §3.1 put "break-budget bails" under pure-drop, which gives `pathTaint = {}` and **removes** the taint the `maxCallDepth` site sets today → unreplayed `sxSat`. `feUnsupportedOp` itself has 12 sites in `runtime.nim` alone spanning ≥3 classes. | `runtime.nim:10759-10786`, `:9317`, `:9550`; §3.2 |
| §2.6 recovers raises on `scIncomplete`-only paths | **That set is empty by construction** — `pathTaint` only yields `{}`, `{scSpurious}` or `⊤`, closed under union. Round 1's DoD pin for it was unsatisfiable. The real recovery is the `scSpurious`-tainted raise, replay-gated. | §2.6, §6.2 |
| §2.1's negation proof ("inclusion preserved under arbitrary image") | **Not a proof.** Branching conjoins *different* predicates on the two sides; intersection preserves ⊇ only against the same constraint. Restated as per-trace simulation, with its hidden premise ("a `dcFreshSymbol` site's symbol is unconstrained at introduction") promoted to a pinned invariant — which makes §0.2 a corollary. | §2.1, DoD 5 |
| §8.2: carry 0011's bound provenance in the `errors` seq | **Structurally impossible for the case 0011 needs.** An `sxUnsat` has `scIncomplete notin runTaint`, so *no under-channel errors exist on exactly those runs*. Bound provenance is a settings echo, not an error. | §8.2 |
| §8.2's coverage paragraph | **Factually wrong at HEAD.** #163 already made `recordEdge`/`logCmp` `{.symexTransparent.}`; the parser drops them, `{.cover.}` taints nothing, and the advice tells users to add a pragma the procs already carry. The live interaction is user `{.symexOpaque.}` + the #137 opaque-call arm — which also had to move from `dcFreshSymbol` to `dcSubstituted` (it drops the callee's mutations). | `coverage.nim:100-140`, `canonicalize.nim:568,586`; §8.2, §3.1 |
| §2.4 row 3 cites `runtime_heap.nim:843-858` | No `Path(` construction there — it's the deref-drain comment. The real `uncertain: false` is `descentBase`, `runtime.nim:11730`. Four more cross-path sinks were missing entirely (`parseIntGateConstraintsLive`, `currentClosureCallAxioms`, `stripDecompConds`, `defectSurvivorPc` — all drained into *every* `trySolve`). | `runtime.nim:7481-7496`, `:11729`; §2.4 |
| §8.1: `forcedBy` on sxUnknown, `satPathTaint`/`replayVerified` on sxSat | `sxRaised` got **no taint fields**, yet §2.3 makes it obey the SAT rules verbatim and §6 pins a replay-gated raise — unauditable as drafted. Replaced by one common `Soundness` object (the `heapSnapshot` precedent) + `trusted()`. And `forcedBy` **is not the actionable surface**: it's a join, so it saturates to `⊤` on any multi-cause run; `gaps()` over `DegradeClass` is. | `types.nim:1888-1933`; §8.1 |
| §7 handles the cache | Key yes, **value no**. The verdict sentinel is an empty `seq[ChoiceNode]`, so every cache hit breaks the `forcedBy != {}` invariant and cannot say whether a served SAT was replay-confirmed. Sentinel widened; replay-precedes-persist added. | `symex.nim:259-297`, `:389-410`; §7 |
| Replay: `replayWitness(fn, witness, label): bool` | Wrong shape three ways — label-only (can't serve the raise-flavoured targets §2.3 puts in scope), `bool` conflates *refuted* with *couldn't run*, and it **cannot be a proc**: splatting a typed witness is macro codegen, so replay runs *after* `runSymex` returns and candidacy must cross `RawResult` unspellable-as-sat. **Both** `runSymex` consumers must discharge it; round 1's DoD wording forced only one. | `symex.nim:1481-1490`, `:1272`, `:2061`; §4.2 |
| Slice plan: S0 makes it "run end-to-end from slice 1" | It does not — S0 *records* today's behaviour. The first observable flip was **slice 9**; eight slices of lattice, replay and reclassification changed nothing a test could see, and the plan's own top risk (one under-as-over misclassification) stayed undetectable until S7's big bang. Also: S6 scheduled the 272-pin flip audit *before* any slice that can flip a pin. | §5 |
| S1/S6/S6a/S7/S8 are slices | **All rounds.** S6a alone: 39 `parseErrors.add` sites in a 9.7k-line `dsl_parser.nim` + the verdict block + closure descent + an unspecified type change — *and* it changes verdicts one slice before the "deliberately last" S7, with no walker bump scheduled. | §5 |

### The two structural changes

**1. `classOf` is total from S1 with a conservative `⊤` default.** All-`⊤`
reproduces today's behaviour bit-for-bit, so the verdict rule lands early
(S1c) as a behaviour-preserving refactor, and each classification slice then
flips **only its own funnel's pins** with its own audit. S0's exhibit is chosen
to route through `allocDegrade`, so the first observable payoff is **slice 6 of
13** instead of slice 10 — and a misclassification surfaces in the slice that
made it. Cost, accepted: six walker bumps instead of two, six Windows gates at
~1–1.5h each.

**2. `w.runTaint` is derived at drain time from the error seqs**, not written
at ~52 sites. This makes §10's "derived from errors, never set independently"
principle real instead of aspirational, and kills the largest mechanical
migration. It has a precondition — error-pairing totality — which is exactly
what S1b's kind-minting delivers. The **path** coordinate stays written, because
`errors` carries no path association; §10 row 5 was half false and is corrected.

### New sequencing (13 slices)

`S0` green exhibit + veto companion → **`S0b` measure the payoff before
building it** → `S1` lattice/carrier/funnel → `S1b` mint the missing kinds +
correspondence pin → `S1c` verdict rule **including the `isTargetLabel` solve**
→ `S2` replay substrate → `S3` monotonicity harness → **`S4` allocDegrade — S0's
exhibit flips here** → `S5` strings/placeholder → `S6` heap + the two mandatory
kind splits → `S7` cross-path sinks + closure/HOF taint migration → `S8`
`DeclineScope` + Class-A/B unification (vetoes retained) → `S9` delete the
vetoes → `S10` SAT relaxation → `S11` public surface.

### Measurements taken at HEAD (`6cbfe8f`)

| quantity | value |
|---|---|
| `sawUnknown = true` write sites in `src/` | 52 (**not the audit checklist** — see §3.4) |
| `forkPathTainted` call sites | **24 live** (round 1 said 25; regenerate in-slice) |
| `SymexErrorKind` members | 41 (~6 tombstoned) + the kinds S1b mints |
| `== sxUnknown` assertions in `tests/` | 272 across 110 files |
| `== sxUnsat` assertions in `tests/` | 283 across 130 files — **cannot regress** |
| `symexWalkerVersion` at HEAD | `"140"` (`canonicalize.nim:187`) |
| `runtime.nim` + its five `include`s | one ~17.6k-line compile unit |
| `dsl_parser.nim` | 9.7k lines, 39 `parseErrors.add`, 76 `mkUnsupported` refs |
| Windows CI cost | ~1–1.5h wall per gated push, ×6 semantics-bearing slices |

**Non-finding, checked and cleared:** concurrency. The fuzzer isolates workers
as processes (`fuzz.nim:160-178`) and every degrade sink is `{.threadvar.}`
(`runtime.nim:1233`), so `w.runTaint` inherits `sawUnknown`'s single-threaded
story unchanged.

### Constraints recorded in the RFC that lived nowhere findable

- **No non-top-level `try`/`except`** (round 1, §1.5) — now also the reason
  §4.2 rejects a replay watchdog in favour of the eligibility gate.
- **The most relevant pin suite cannot run on Linux.**
  `tests/tsymex_r6_b7r2_pathscope.nim` is one of the six hangers skipped in
  `scripts/sweep.sh:91-96`, so **S10 has no local gate at all**.
- **`examples/` is built by neither CI nor `nimble test`** — the file
  `examples/symex_loops.nim` records that it stopped compiling for a full
  release cycle unnoticed (its own lines 60-63). S11 puts the user-facing
  walkthrough in a registered test file instead.

## Review ledger — round 2

| lens | headline finding |
|---|---|
| depth | The closure veto is load-bearing for ≥4 value-substituting sites that carry no path taint — deleting it as specified reintroduces the S1 failure class; `beBudgetExhausted` is a mandatory 3-way split whose round-1 row would *remove* existing taint; §2.1's proof isn't one |
| breadth | Two `trySolve`-unknown sites taint with no kind (solver resource-out is stamped a walker fault today); `SymexFinding` + the render layer can't carry the new surface; §8.2's coverage paragraph is pre-#163; four undocumented cross-path sinks; RFC-0007 owes a soft edge |
| design | `channels()` can't express its own motivating case → `DegradeClass`; one `degrade()` funnel to make all three acts one kind mention; `Soundness` as a common field (sxRaised had none); `forcedBy` saturates to ⊤ and isn't the actionable surface |
| feasibility | **The S7/S8 boundary mints a false `sxUnsat`**; replay can't be a proc and its weight is on the wrong slice; S1/S6/S6a/S7/S8 are all rounds; the 272-pin audit was scheduled where zero pins can flip |
| liveness | The payoff sits behind eight inert slices; the measured payoff is counted at slice 8 and could be ~0; the SAT half's *live* payoff (veto + raise-routing) had no exhibit and no DoD pin |

Three lenses independently reached the candidate-vs-`shouldStop` regression
(a tainted candidate entering `w.found` halts the walk before a clean witness
is solved — so the "relaxation" can *lose* verdicts the engine earns today).
It was then verified directly at `runtime.nim:8212-8221` / `:11159-11168`
before being written into §2.3 as the candidate-pool rule.

## Open forks — awaiting Corey (§13)

1. **§13.1 — does §12.1's full-scope resolution still stand?** Not because it
   was wrong, but because round 2 changed the facts: the SAT half's live payoff
   is *only* veto-deletion + raise-routing; replay executes the SUT at verdict
   time (a contract change to `symexFind`); the plan is 13 slices / 6 bumps /
   6 Windows gates. My read: keep it as one RFC — the replay slices stay
   separable in-flight. **Conditional on S0b's number.**
2. **§13.2 — should `blocked_by = ["0001"]` become a soft edge?** Everything §1
   takes from 0001 is landed. The tracker derives readiness from it and 0011
   inherits the delay. Frontmatter deliberately **not** changed.
3. **§13.3 — `feTransparentResultUsed`/`feTransparentArgNotInert`:**
   `sevWarning`, or a fourth `dskCompanionAnchored` scope? The trade is how
   loudly an over-claimed `{.symexTransparent.}` should be surfaced — a product
   judgment, no design basis to prefer either.

**Lesson for future rounds:** round 1 verified its *citations* and did it well
— every line number it quoted was accurate. What it did not verify was whether
its own new machinery could express its own examples. Both of round 2's
design-level catches (`channels()` vs the k-unroll survivor, §2.6 vs the
`pathTaint` codomain) were found by *type-checking the RFC against itself*, not
against the source. Do that pass explicitly next time.
