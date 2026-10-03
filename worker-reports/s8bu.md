# S8bu report: DONE

- **Branch:** rfc-0005-s8bu, pushed.
- **Head:** 5729b1a (docs). The last code commit is 8815a81.
- **Base:** e7965d0 (S8bs, walker 222).
- **Walker:** 225 (provisional). The CR2 `==` pin is updated and passes on both Z3 versions. Every S8bu suite has a `>= 225` floor pin.
- **Lock:** no bump was needed. All fixes are nelli-side, and `_deps` is clean at the lock.

## Commits (e7965d0..5729b1a)

| commit | item | change |
|---|---|---|
| a97922e | docs | adds the slice row |
| 0c4c19e | item 1a | bvIntInverseFacts; a finite default queryRLimit; the S8bs int forms restored |
| 1c56690 | item 1b | probeProto keeps Int-heap arithmetic in its bit-vector; queryTimeoutMs clock backstop; a timed-out unknown is not cached |
| b308300 | item 3 | addr b.x is a sub-cell of b's cell |
| 4ec5ed0 | item 2 | closure and proc-value calls bind to address cells (ccVarLocs) |
| d74c44b | item 4a/4b | openArray views; var openArray write-back (iekSeqSplice); string view declines |
| 45cdf06 | item 4c | mitems / mpairs |
| 0e0daa0 | item 5 | array steps on a path into an address-taken local |
| 3c6a564 | item 6 | a by-value seq shares an address-taken seq's memory (view cell entry) |
| d875c95 | Windows fix | brings the new code under the corpus audits (emit roundtrip, N27, S8m) |
| 8815a81 | Windows fix | bv2int facts relate only terms the query holds; queryRLimit default 250M |
| 5729b1a | docs | RFC "As landed (S8bu)"; the S8bu row is flipped to done |

## Item 1: cause and fix

**Cause.** An `int` read from an Int-sorted heap (an `int` field reached through a cell, or a `seq[int]` element cell) is linked to a bit-vector through `sbv2int`. Both Z3 versions expand `sbv2int` to an `ite` over `ubv2int`. Two kinds of query result:
- `sbv2int(r) == select(store(h, c, sbv2int(k)), c)` with `r != k`. Z3 can refute this only through the injectivity of that `ite`, which neither version found within 3M units. With the default `queryRLimit = 0` (unbounded), the walk never ended.
- `v * 2` on a value read back out of the heap lowered as `2 * sbv2int(k)`. On that query Z3's step counter stopped advancing (12.4M units at 10 s, 12.47M at 60 s), so no step bound could end it.

**Fix.**
1. `bvIntInverseFacts` asserts theorems beside every query, relating only terms the query already holds:
   - `int2bv(t) == x` where `t` is `sbv2int(x)`;
   - `a == b` implies `x == y` where the two sides are views of `x` and `y`.

   A side counts as a view after reading each `select(store(h,i,v),i)` as `v`.
2. `probeProto` lowers `v * 2` as `bvmul(2, k)`.
3. `queryRLimit` now defaults to 250M. `queryTimeoutMs` (default 600000) is a new clock backstop. Either cut-off gives `sxUnknown` with `beSolverUndef` naming the budget, and a clock cut-off is not cached. The concrete-branch and tainted solves keep their 20M budget.

## RED and GREEN (observed)

**Item 1.**
- **RED:** `sutIntField` and `sutSeqInt` (`tf`, `ts`) ran without end under the default budget (killed by the bound). `sutHeapArith` stalled at 12.4M units.
- **GREEN:** clean `sxSat`/`sxUnsat` on both Z3 versions. `sutCubes` with a 2 s clock gives `sxUnknown`, named, and is not cached.

**Item 2.**
- **RED:** `pp`, `lp`, `lb`, `pw` and `lw` declined (closure sink).
- **RED, soundness:** `pg` was `sxUnsat` and `pg_dead` was `sxSat` (swapped).
- **GREEN:** all clean and matching native runs.

**Item 3.**
- **RED:** `da`, `dw`, `pa`, `dn` and `dx` declined.
- **GREEN:** all clean. `de` (an element with element cells) declines by name.

**Item 4.**
- **RED:** the openArray, var openArray and mitems SUTs declined.
- **RED, soundness:** `vc` was a FALSE `sxUnsat`. A string passed to `openArray[char]` was opaque, while `cnt(st) == 2` is reachable natively.
- **GREEN:** clean verdicts, except that `vn` (negative length), `wf`, `mg` (resize in the body) and `vc` decline by name.
- The S8bs pins `oa`, `or` and `mi` (iterparams) and `sw` (byvalue) are repinned to the decided verdicts.

**Item 5.**
- **RED:** `ac`, `as`, `al`, `af` and `ae` declined (path `?`).
- **GREEN:** clean, by both a constant and a symbolic index.

**Item 6.**
- **RED:** `sv`, `su`, `sp` and `sf` declined. `p[][i] = v` was an "unsupported nnkAsgn shape".
- **GREEN:** clean. `sa` and `sg` decline "assigned whole or resized". `ss` and `sr` (strings) decline by name.

## Soundness bugs found and fixed

1. **By-value `Big` through a proc value.** It was passed as a copy, so the callee's write through the alias was lost and the verdicts were swapped (`pg` / `pg_dead`).
2. **String passed as `openArray[char]`.** It gave a false `sxUnsat` (`vc`). It now declines.

## Design per item

1. See "Item 1: cause and fix" above.
2. `closureCallIR` records each argument's origin (`ccVarLocs`). `applyClosureGround` binds formals to the caller's cells through `bindVarLocs`. A formal bound to the whole variable is not written back.
3. A path local with two cell entries (the variable's cell at `.x`, and the pointer's) is kept equal by a second pass of `syncAddrCells`.
4. openArray:
   - `openArray[T]` has the seq sort. An array becomes a seq literal of its elements.
   - `toOpenArray` becomes an `ssView` slice with bit-vector bounds bridged to Int. The `IndexDefect` rule is modelled as probed natively. A negative length declines on its paths.
   - var openArray: a whole seq is passed by address. An array or slice uses a temporary plus a write-back in `finally` (`iekSeqSplice`). This covers direct calls, closure calls and inlined iterators.
   - mitems / mpairs substitute the typed element `c[k]` for the loop variable. A seq resized in the body declines.
5. `varLocOf` accepts array steps, less the array's low bound. `locGet` / `locSet` handle `svArray`, using an `ite` chain for a symbolic index.
6. A `view` AddrCellEntry handles the by-value seq. `viewFollows` requires the same length term, with each data array a store chain over the old one (`peelSelect` / `storeChainOver`). Anything else taints the view: "assigned whole or resized". The `p[][i] = v` assignment arm is added.

## Suites (ok/failed)

The per-suite table covers c on Z3 5.1 and 4.13.4, and cpp on 5.1. Logs are in /home/corey/tmp-usage/work/s8bu-work/verify/.

What ran is every file in `verify/list.txt` (62 suites):
- the 6 S8bu suites;
- the 4 S8bs suites;
- s8be, s8ax, s8bh, s8bc, s8ac, s8an, s8as, s8ba, s8bd, s8bf_alias, s8i, s7_closure, s8ab_letaudit, s8x_vm_alias, h_stepC, H1, g4, g5 and CR2;
- every `command grep -l 'iterator\|openArray\|mitems\|addr '` match, and the fuzzy-name matches;
- the corpus suites Windows caught: configdefaults, augmented_assign, s8ad_remainder, r6_r6_emit_roundtrip, r6_n27_placeholder_read_audit, s8m_exits and s1c_verdict.

| suite | c 5.1 | c 4.13.4 | cpp 5.1 |
|---|---|---|---|
| rfc0005_s8bu_views | 5/0 | 5/0 | 5/0 |
| rfc0005_s8bu_calls | 8/0 | 8/0 | 8/0 |
| rfc0005_s8bu_term | 10/0 | 10/0 | 10/0 |
| rfc0005_s8bu_varviews | 5/0 | 5/0 | 5/0 |
| rfc0005_s8bu_mitems | 5/0 | 5/0 | 5/0 |
| rfc0005_s8bu_paths | 8/0 | 8/0 | 8/0 |
| rfc0005_s8bs_addrglobal | 14/0 | 14/0 | 14/0 |
| rfc0005_s8bs_byref | 7/0 | 7/0 | 7/0 |
| rfc0005_s8bs_iterparams | 4/0 | 4/0 | 4/0 |
| rfc0005_s8bs_byvalue | 3/0 | 3/0 | 3/0 |
| rfc0005_s8be_remainder | 34/0 | 34/0 | 34/0 |
| rfc0005_s8ax_remainder | 53/0 | 53/0 | 53/0 |
| rfc0005_s8bh_remainder | 35/0 | 35/0 | 35/0 |
| rfc0005_s8bc_remainder | 74/0 | 74/0 | 74/0 |
| rfc0005_s8ac_remainder | 19/0 | 19/0 | 19/0 |
| rfc0005_s8an_remainder | 25/0 | 25/0 | 25/0 |
| rfc0005_s8as_remainder | 33/0 | 33/0 | 33/0 |
| rfc0005_s8ba_remainder | 32/0 | 32/0 | 32/0 |
| rfc0005_s8bd_remainder | 23/0 | 23/0 | 23/0 |
| rfc0005_s8bf_alias | 13/0 | 13/0 | 13/0 |
| rfc0005_s8i_models | 39/0 | 39/0 | 39/0 |
| rfc0005_s7_closure | 37/0 | 37/0 | 37/0 |
| rfc0005_s8x_vm_alias | 7/0 | 7/0 | 7/0 |
| rfc0005_s8ab_letaudit | 28/0 | 28/0 | 28/0 |
| h_stepC_heapidentity | 10/0 | 10/0 | 10/0 |
| phase15_H1_path_heap_fields | 2/0 | 2/0 | 2/0 |
| g4_cmpwalk | 1/0 | 1/0 | 1/0 |
| phase15_g4_distinct_sort | 4/0 | 4/0 | 4/0 |
| phase15_CR2_cachekey | 6/0 | 6/0 | 6/0 |
| phase15_g5_distinct_borrow | 3/0 | 3/0 | 3/0 |
| a3_closure_iterators | 11/0 | 11/0 | 11/0 |
| a7_runes_iter | 6/0 | 6/0 | 6/0 |
| augmented_assign | 8/0 | 8/0 | 8/0 |
| phase14_multivariant_witness | 2/0 | 2/0 | 2/0 |
| phase15_N1_resolution_gates | 32/0 | 32/0 | 32/0 |
| phase15_N2_kindgate_audit | 5/0 | 5/0 | 5/0 |
| phase15_N3_scan_boundary | 5/0 | 5/0 | 5/0 |
| phase15_r11_unsafecast | 4/0 | 4/0 | 4/0 |
| phase15_r11b_smoke | 11/0 | 11/0 | 11/0 |
| rfc0005_s1_lattice | 23/0 | 23/0 | 23/0 |
| rfc0005_s1b_kinds | 18/0 | 18/0 | 18/0 |
| r6_n14_seqops | 25/0 | 25/0 | 25/0 |
| rfc0005_s2_replay | 15/0 | 15/0 | 15/0 |
| rfc0005_s6b_ops | 44/0 | 44/0 | 44/0 |
| rfc0005_s8ag_indexsplit | 15/0 | 15/0 | 15/0 |
| rfc0005_s8bb_constructs | 7/0 | 7/0 | 7/0 |
| rfc0005_s8au_remainder | 35/0 | 35/0 | 35/0 |
| rfc0005_s8c_resolution | 25/0 | 25/0 | 25/0 |
| rfc0005_s8e_scoping | 36/0 | 36/0 | 36/0 |
| rfc0005_s8n_precision | 19/0 | 19/0 | 19/0 |
| rfc0005_s8_scope | 28/0 | 28/0 | 28/0 |
| rfc0005_s8y_budget_decline | 8/0 | 8/0 | 8/0 |
| 163rev_int_literal_width | 27/0 | 27/0 | 27/0 |
| phase15_F2_float_literals | 5/0 | 5/0 | 5/0 |
| phase15_r7_alias_chain | 9/0 | 9/0 | 9/0 |
| r6_r6_emit_roundtrip | 104/0 | 104/0 | 104/0 |
| r6_n27_placeholder_read_audit | 4/0 | 4/0 | 4/0 |
| phase15_rereview_drains | 15/0 | 15/0 | 15/0 |
| rfc0005_s8m_exits | 32/0 | 32/0 | 32/0 |
| configdefaults | 24/0 | 24/0 | 23/0 rc=139 |
| rfc0005_s1c_verdict | 24/0 | 24/0 | 24/0 |
| rfc0005_s8ad_remainder | 13/0 | 13/0 | 13/0 |
| **total (62 suites)** | 1186/0 | 1186/0 | 1185/0 |

`tsymex_configdefaults` on cpp 5.1 segfaults (rc=139) in its round-2 `maxCallDepth` crash pin. This is **pre-existing**: the base worktree at e7965d0 crashes at the same test in the same way (`s8bu-work/base_cfg_cpp.log`).

**Compile time.** The host was loaded (load about 16 on 8 cores). In the same sweep:
- the S8bu suites took 67-108 s compile user time;
- `s8i_models` took 111-124 s (54 s unloaded);
- the S8bs suites took 66-109 s.

By that ratio every S8bu suite is under the 60 s budget unloaded. `views` was split into views, varviews and mitems for this reason.

## Windows

| head | symex-mingw | fuzzer-mingw | fuzzer-msvc |
|---|---|---|---|
| 3c6a564 | 37143898095 FAILED (6 suites) | 37143898065 success | 37143898099 success |
| 8815a81 | 37147844306 success | 37147844319 success | 37147844268 success |

The six suites that failed at 3c6a564, all fixed in d875c95 and 8815a81:
- `s8ad_remainder` was killed at 240 s on 4.13.4, because `int2bv` was added for every view.
- `augmented_assign` was `beSolverUndef` on 4.13.4 at the 20M budget; it needs 100M-150M units.
- `configdefaults`: the field count changed with the new budget field.
- `r6_r6_emit_roundtrip`: `iekSeqSplice` was not covered.
- `r6_n27`: unguarded `seqLen` reads in `viewFollows`.
- `s8m_exits`: a raw `Z3_mk_select` in a probe.

The same failures appeared earlier on 4ec5ed0 (37133852439) and 0c4c19e (37129196802).

5729b1a is docs-only, so the workflows' `paths-ignore` for `docs/**` skips it, and no Windows run exists for it.

## Different mechanisms, reported and not fixed here

These are also committed in the RFC under "As landed (S8bu)".
- **PRECISION:** `addr s[i]` of a seq with element cells, passed to a call, declines ("in the element's own heap").
- **PRECISION:** a closure capturing an address-taken variable declines (S8ax capture cells against the address cell).
- **PRECISION:** a heap lvalue `pb[].x` reached by a closure body declines (S8bh `touchMeetsOuter`).
- **PRECISION:** a seq argument to a proc value declines (`seUnsupportedCompoundSortLeaf`). This includes var openArray through a proc value.
- **PRECISION:** a string viewed as `openArray[char]`, and a by-value string of an address-taken string, decline (character writes are not modelled).
- **PRECISION:** `toOpenArray` of negative length declines on its paths. A mitems body that resizes the seq declines.
- **PRECISION:** `gps[].add` through a pointer to a seq gives `heUnsafeCast` (pre-existing).
- **SOUNDNESS (latent, no pinned SUT reaches it):** a whole assignment over a constant-array base, whose new data happens to be a store chain over the old data, would read as in place in `viewFollows`. Under ORC that copy is a use-after-free, so no defined program observes it, but the check is structural rather than semantic.

## Notes

- The diagnostic `_deps/z3/src/z3/solver.nim` query-dump hook was reverted and kept only as /home/corey/tmp-usage/work/s8bu-work/s8bu-dump-hook.patch. `_deps` was not edited for anything committed or verified.
- Scratch probes and query dumps were moved out of the worktree to s8bu-work/scratch/. The worktree is clean.

## Scratch-clobber incident (verdict: not affected)

Three S8bu files lived in the shared session scratchpad for about 50 minutes, from 13:50 to 14:38 UTC on 2026-10-03. All three were then moved to `s8bu-work/`.

| File | Created | What it was | Status |
|---|---|---|---|
| `z3f.sh` | 14:01 | offline re-checker for dumped `.smt2` queries | run from the scratchpad once, a 14:04 diagnostic that no reported result depends on |
| `solver.nim.orig` | 13:54 | backup taken before the temporary dump hook | the worktree's `_deps/z3/src/z3/solver.nim` is now byte-identical to the main clone's and clean at ae509f0 |
| `bv.log` | 14:17 | early `s8bs_byvalue` GREEN check output | superseded by the final sweep |

- **Search:** a grep for `scratchpad` and `/tmp/claude` over every runner (`trun.sh`, `verify/run.sh`, the other `s8bu-work` scripts, `dt413.sh`, `scripts/dt-bounded.sh`) finds nothing.
- **Certified results:** all come from the 62-suite sweep run from `s8bu-work/verify`, on Z3 5.1, Z3 4.13.4 and cpp, after 8815a81. That sweep includes `s8bs_byvalue` on all three, so the `bv.log` run was in effect redone.
