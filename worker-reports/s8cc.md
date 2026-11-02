# S8cc: DONE

- **sha:** ab4e5b5 on `rfc-0005-s8cc` (pushed, no force-push)
- **base:** 136ad60 (batch 7, walker 237), reached by merge commit 8f58d0c. The job's base was a25229d.
- **walker:** 238, provisional. The job's provisional 235 was already below the base. CR2's `==` pin is 238, and both new suites carry the `>= 238` floor.
- **instrument:** f3d60c0 is reverted by 35b0f46. `git diff 136ad60 ab4e5b5 -- src/nelli/smt/runtime.nim` is empty.

## RED and GREEN observed

All RED and mutation runs were on Z3 5.1, c backend. The 4.13.4 runs below are GREEN only.

### Item 1: no code; batch 7 had already fixed it (as the coordinator suspected)
`tsymex_rfc0005_s8cc_cellquery` was run under an explicit `queryRLimit`:

| Tree | Budget | Result |
|---|---|---|
| a25229d (job base) | 20M | `cv_dead`, `cc_dead`, `cm_dead`, `cl_dead` all `sxUnknown` (`beSolverUndef`, "canceled"); live labels `sxSat` |
| 136ad60 (batch 7), original 8 labels | 20M | all decide, 3/0 |
| 136ad60 with `probeProto`'s `bvOfInt` removed | 20M | same four labels back to `sxUnknown` |
| a25229d with only that `probeProto` change added | 20M | `cv_dead`, `cc_dead`, `cl_dead` decide; `cm_dead` still `sxUnknown` |
| 136ad60 with `bvIntInverseFacts` returning nothing | 2M | `cm_dead` `sxUnknown` |
| merged head, 18 labels | 2M | all decide, 4/0 |

- **What fixed it:** S8bu. `probeProto` offering the bit-vector (1c56690) fixes the `+ c` shape. `bvIntInverseFacts` (0c4c19e, narrowed by 8815a81) is also needed for `cm`, the `v[] * 3 - k` shape.
- **Not re-run:** the unbounded 420 s case at a25229d. What I observed at the base is the bounded `sxUnknown`, plus the earlier agent's p1 log at 50M, killed by the 150 s bound under load. At head, `b7_integration`'s `ac_dead` default-budget test passes; that pin allows `sxUnsat` or a bounded decline, under 300 s.
- **Correction:** the inherited test comment said `queryRLimit` did not end the query. That did not reproduce at 20M, and I corrected the comment.

### Item 2
At 136ad60:
- `ri`, `rs`, `rd`, `ra` and their twins declined (`feEvalOrderUnmodelled`).
- `or` and `or_dead` were `sxUnknown` (`feGlobalHavoc`, replay refuted).

GREEN at head: 10/0.

### Item 3
At 136ad60, `fs`, `fa`, `fp`, `fc`, `fr`, `ft` and their twins declined (`feUnsupportedOp`). GREEN at head.

### Already right at the base (kept as pins)
- The writer declines (`wa` ... `wb`).
- The generics `gi`, `go`, `gn`. S8br's note that a generic's index call declines did not reproduce.

### Mutation on the new code
With the `nnkAddr` arm removed, `ob` is a false `sxUnsat`, and restoring the arm gives GREEN. See "Soundness bugs".

## Pinned decision time (item 1)
- **Step pin:** every query decides within 2M Z3 units on both versions, across 18 labels.
- **Clock, measured per `symexFind` including the walk, not pinned:** worst label is `cp_dead`, 417 ms on 5.1 and 393 ms on 4.13.4. Every other label is under 310 ms. Load was about 21-24 on 12 cores, with the pause flag absent.

## Soundness bugs
- **Pre-existing:** none found.
- **Would have been introduced by item 2, fixed before landing:** a by-value formal may be the caller's storage, since Nim passes a large one by address. Once such an argument reads as no write, `unsafeAddr x` in the callee gave a false `sxUnsat` through an opaque call. `addr` of a by-value formal now summarises as every global and heap. Pinned by `ob`.

## Design
- **Item 1:** no walker change. The query was `int2bv(sbv2int(k) + 5 + 0) != k + 5`, which has no array term, so the job's array-theory and frame-fact suspects were not the cause. Offline on the 4.13.4 CLI the dumped query had no result in 120 s. A hand-reduced form with the term spelled `bvadd(k, 5)` was `unsat` in 48 units. The added variants are a symbolic-index store, the input as the index, an `int32` element, a seq element and a local array.
- **Item 2:** `scanOpaqueEffects` lists the positions that only read (`scanRead`, `scanReadPath`, `scanCall`, `scanWrite`): assignment right side, declaration value, condition, `case` selector, by-value argument, and an index on an assignment's left side. A symbol anywhere else still counts as written.
  - A `var` formal counts by its declared type, because a magic such as `inc gi` has no `nnkHiddenAddr`.
  - A read whose value holds refs still reaches its heaps.
  - `result = gi` in a routine returning `var` counts.
  - Both consumers gain: `laterLeavesLvalue` and `opaqueWriteSummary`.
- **Item 3:** `hoistIndexCalls` binds every non-builtin index call once, under a mark of the call type's symbol (`int` for an anonymous `range`). This replaces S8br's `result`-symbol lookup. `indexCallDecline` remains for a spent mark counter. The call node cannot be marked as itself: compiling that aborted the compiler with an `IndexDefect`. The failing operation inside the compiler was not isolated.
- **S8br pin moved:** `fs_dead` goes from a decline to `sxUnsat`.

## Suites (`tests ok/failed`)
The c columns ran at 8a365c7. The cpp column ran on 5.1 at 97c6618. `-` means not run.

| Suite | c, Z3 5.1 | c, Z3 4.13.4 | cpp, 5.1 |
|---|---|---|---|
| s8cc_cellquery | 4/0 | 4/0 | 4/0 |
| s8cc_remainder | 10/0 | 10/0 | 10/0 |
| s8br_remainder | 5/0 | 5/0 | 5/0 |
| s8br_framecond | 3/0 | 3/0 | 3/0 |
| s8bk_argtiming | 5/0 | 5/0 | 5/0 |
| s8bk_argtiming_addr | 3/0 | 3/0 | 3/0 |
| s8bk_argtiming_checks | 4/0 | 4/0 | 4/0 |
| s8bs_addrglobal | 14/0 | 14/0 | 14/0 |
| s8bs_byref | 7/0 | 7/0 | 7/0 |
| s8bs_byvalue | 3/0 | 3/0 | 3/0 |
| s8bs_iterparams | 4/0 | 4/0 | 4/0 |
| s8be_remainder | 34/0 | 34/0 | 34/0 |
| s8ax_remainder | 53/0 | 53/0 | 53/0 |
| s8bh_remainder | 35/0 | 35/0 | 35/0 |
| s7_closure | 37/0 | 37/0 | 37/0 |
| phase15_CR2_cachekey (238) | 6/0 | 6/0 | 6/0 |
| s8as_remainder | 33/0 | 33/0 | - |
| b7_integration | 6/0 | 6/0 | - |
| phase15_N2_kindgate_audit | 5/0 | 5/0 | - |
| **All 84 suites** | **1131/0** | **1131/0** | 16 suites, 0 failed |

- **The 84-suite list** is in `s8cc-work/gate.list`: the named suites, every `addr`/`unsafeAddr` grep hit, every array/index-named suite, and every `feGlobalHavoc`/`feEvalOrderUnmodelled`/`symexOpaque` grep hit. Every run was rc=0 with none killed. Per-run logs and `summary.txt` are in `s8cc-work/logs/`.
- **Slowest run:** 164.9 s wall, on a shared box at load 20-30.
- **Later commits:**
  - 97c6618 removed an unused template from `s8br_remainder` and added the RFC note. `s8br_remainder` was re-run there: 5/0 on both versions, c.
  - ab4e5b5 changes one source comment and the RFC note only. Both s8cc suites were re-run there: c on both versions, 4/0 and 10/0.
- **Not run at ab4e5b5:** the other 82 suites and all cpp runs. No code differs from the runs above.

## Windows (ab4e5b5, all success)
- symex-mingw 41423730065
- fuzzer-mingw 41423729940
- fuzzer-msvc 41423729973

8a365c7, the sha the suite gate ran at, also passed all three: 41411621846, 41411621813, 41411621708. I did not read per-file Windows timings for the two new suites against the 60 s convention. Locally each took 54-89 s including compile, under load.

## Different mechanisms, reported and not fixed here
Also committed in the RFC under "As landed (S8cc)".
- **PRECISION:** `addr` of a global in a walked callee halts the path (`let p = addr gi; p[] = 1` as a later argument is `sxUnknown`, `heUnsafeCast`, `wp_dead`).
- **PRECISION:** `unsafeAddr` of a by-value array formal in a walked callee declines (`feUnsupportedOp`, S8ax's "`addr x` ... is not modelled", `wb_dead`). Seen in the mutation run, where the arm that otherwise pre-empts it was removed.

## Coordinator decisions
1. **Item 1 has no code.** Confirm the pin plus the root-cause attribution to S8bu closes it.
2. **Walker number.** 238 is provisional. Renumber if another slice takes it.
3. **History.** The branch merges 136ad60 rather than rebasing, and keeps f3d60c0 with its revert, since no force-push was allowed. Squash at landing if you want the instrument out of history.
4. **Commit trailers.** Omitted, per the job's rule.
