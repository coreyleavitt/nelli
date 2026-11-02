# S8cd: DONE

- **Sha:** 1ca792de2016de7a98053abb2ff93ad527aa44b4 (branch `rfc-0005-s8cd`, pushed)
- **Base:** 136ad60 (batch 7, walker 237), with batch 9 e497dcf (walker 245) merged at a043e38. `_deps/z3` is at cc5ffc9, identity 9a033beb (checked against the lock after the merge).
- **Walker:** 249. Provisional 244 is dropped. 245 is on the channel and 247 and 248 are on other branches (s8bz, s8cl), so 249 was the next free number. CR2 `==` pin is 249; the S8cd suites floor at `>= 249`.
- **Slice row:** `done`. "As landed (S8cd, walker 249)" is committed in `docs/rfc/0005-branch-scoped-degrade.md`.

## Windows at 1ca792d (all three green)

| leg | run id | result |
|---|---|---|
| symex-mingw | 41540723507 | success |
| fuzzer-mingw | 41540723454 | success |
| fuzzer-msvc | 41540723594 | success |

**Failed earlier run:** symex-mingw 41532974338 at d783a8c. Shards 3 and 11 failed on N40-6 (`tsymex_r6_n40_alloc_totality`) and N30-2 (`tsymex_r6_lows_declines`). Both pins expected a decline, and my `closureRetStructured` widening made them sxSat. I then added native captures: both labels are reached natively, and each pin now checks that itself, so neither is a false sxSat. These two suites were not in my local verification list before that failure.

### Per-file Windows times, symex-mingw run 41540723507 (from the `==>` timestamps in the logs; 60 s convention)

| file | s | |
|---|---|---|
| tsymex_rfc0005_s8cd_setorder_small | 88 | over |
| tsymex_rfc0005_s8cd_setorder_large | 68 | over |
| tsymex_rfc0005_s8cd_globals | 64 | over |
| tsymex_rfc0005_s8cd_ops | 59 | |
| tsymex_rfc0005_s8bw_remainder | 85 | over; was also over before this slice's repin (85.6 s at d783a8c) |
| tsymex_rfc0005_b6_globalrecv | 45 | |
| tsymex_r6_lows_declines | 44 | |
| tsymex_r6_n40_alloc_totality | 41 | |
| tsymex_r6_n27_placeholder_read_audit | 3 | |
| tsymex_phase15_CR2_cachekey | 2 | |

Three of my new files are over the convention. The item 4 suite was one file at 164 s at d783a8c and is now two. I did not split further, because the SUT set is what costs the time. Coordinator decision below.

## RED and GREEN observed

**RED** at 136ad60: `s8cd-work/red_g.log`, `red_o.log`.
- Item 1: `iekSeqLen: unsupported receiver kind`, plus a `weInternalWalkerFault` on `for x in f(k)`.
- Item 2: false sxUnsat, plus a decline on the `ini` fallback.
- Item 3: `feGlobalReadUnmodelled`.
- Item 4: wrong verdicts (below).
- Item 5: the reassignment declined. The RED for narrowing itself only shows once item 3 is in, because at the base the arm declines first.
- Item 6: `c_long`, `c_and`, `c_len` declined on the cap.

**GREEN** at 1ca792d: the table below.

## Soundness bugs found

Both are fixed on this branch. The coordinator already has both as RELEASE BLOCKER messages, with the three-way table.

1. **Store through a pointer to a global only read: false sxUnsat.** Covers a scalar, tuple field, array element, seq element and two pointers. Observed at 136ad60 and e497dcf; native reaches all five; 6cbfe8f declines. Cause: `ptrTargets` scanned only bound globals.
2. **Set expression order: false sxSat and false sxUnsat, no errors.** Observed at 136ad60 and e497dcf. At 6cbfe8f the `le` and `card` shapes decline and the other three shapes do not compile (`mx` inferred from `by`). Cause: `isEagerIR` had no `iekBitSet` arm, and the set operators' operands were not ordered.

## Design for each item, and where the job's assumptions did not hold

1. **`len` over receiver kinds.** Assumption drifted: ptr/ref deref and heap fields were already decided at the base, and "p5/p6" names no shape I could find. The error reproduced only for a proc value with no target. `IRExpr.ccRetTy` carries the return type (in the key as `;ret=`), so the unknown-callee arm binds a stand-in of that type and declines as `ceClosureUnknownCallee` / `ceUnsupportedHof`. A `for` over a call binds the result once. `closureRetStructured` adds Table, HashSet and set.
2. **`ptrTargets` on the global entry fallback.** `ptrInputOf` covers the fallback (text identical to S8bz's). Every `var` global that may hold the pointee is bound to its entry value, except names in `callGuardedNames`.
3. **Case-object globals.** `irTypeRefFree` gains variant and multi-variant arms (identical to S8bz's hunk), which reuses S8bw's machinery. `recvValue` reads a global at its type. A case object reaching a heap cell declines.
4. **`isEagerIR` and `iekBitSet`.** The job's "add it" is wrong as a blanket rule, decided by native measurement on c and cpp:
   - `{..}` naming a variable is eager at every size.
   - `+ - * <= <` are lazy at 64 values or fewer and eager above that (65 is the first array).
   - `==`, `in` and `card` are lazy over an operand that may be eager.
   - `x in {k, y}` compares inline.
   - Set operators go through `parseOperandPair`.
5. **`recvValue`.** It reads as a receiver, and each arm observes what it reads (`observeRecvPart`): seq index the length, pop the length and last element. `reassignReadsDisc` skips the discriminator when one branch holds every tag. The assumption is partly moot: arrays already observed nothing, and a seq's length is a genuine read.
6. **`rfind` under a tight cap.** The moved S8o pin (`lastIdx`) declines on `t.len > 10` under cap 8: the query has no model within the cap, so it keeps S8k's decline and the pin is unchanged. The shape that did decline wrongly was a leaf pinned to a literal longer than the cap. `seqLenCaps` now leaves a leaf equated to a string literal uncapped.

## Verification at 1ca792d (local; rc=0 and no [FAILED] in every row)

| suite | tests OK | Z3 5.1 s | Z3 4.13.4 s |
|---|---|---|---|
| tsymex_rfc0005_s8cd_globals | 21 | 78 | 60 |
| tsymex_rfc0005_s8cd_ops | 13 | 64 | 56 |
| tsymex_rfc0005_s8cd_setorder_small | 5 | 93 | 73 |
| tsymex_rfc0005_s8cd_setorder_large | 5 | 94 | 79 |
| s8bn_remainder | 37 | 110 | 95 |
| s8bw_remainder | 22 | 81 | 74 |
| b6_globalrecv | 8 | 46 | 48 |
| s8as_remainder | 33 | 69 | 72 |
| s8o_termination | 16 | 48 | 50 |
| s8au_remainder | 35 | 69 | 81 |
| s8bl_borrow | 4 | 42 | 48 |
| s8bl_gaps | 11 | 58 | 61 |
| s8bl_magicscan | 3 | 44 | 45 |
| s8bl_magics | 8 | 47 | 44 |
| s8bl_pairloop | 2 | 48 | 46 |
| s8bl_seqops | 4 | 42 | 40 |
| s8bl_setlen | 7 | 53 | 46 |
| s8bq_remainder | 62 | 75 | 67 |
| CR2_cachekey | 6 | 6 | 5 |
| n27_hof_placeholder | 6 | 45 | 45 |
| n27_placeholder_read_audit | 4 | 7 | 5 |
| r6_lows_declines | 15 | 48 | 49 |
| r6_n40_alloc_totality | 10 | 49 | 49 |

Times include compile, on a shared host with up to two of my runs at once plus other workers' runs. They are not clean performance measurements.

**cpp (Z3 5.1), passed at 1ca792d:** s8cd_globals 21, s8cd_ops 13, setorder_small 5, setorder_large 5.

**Run at d783a8c, not rerun locally at 1ca792d:** the source differs only by a comment in `dsl_parser.nim`. Windows ran the whole corpus at 1ca792d.
- s8bh, s8bi, s8ax and s8be on both Z3 versions (the Z3 5.1 run was at a043e38, whose source is the same as d783a8c).
- On 5.1 only: A2a_atomicir, A2a_chokepoint, N2_kindgate, r11_range_invariant, r6_degrade_pairing, r6_n36_raise_class, s8ba_remainder, s8_scope, s8x_vm_alias.

**Pins moved:**
- b6_globalrecv and s8bw reassignment: decline to candidate.
- N30-2 and N40-6: decline to sxSat, with native captures.
- N27 marker count 116 to 117: the new `seqLen` read in the index arm, after its placeholder guard.

## Different mechanisms, reported and not fixed here

All are also in the RFC under As landed. The first four were observed in probes at 136ad60 and not rerun after merging e497dcf, whose S8ca may have changed them.

- **PRECISION:** `len` of a nested seq (`seq[seq[int]]` heap field or proc-value result) declines.
- **PRECISION:** `HashSet[string]` behind a pointer or in a heap field declines.
- **PRECISION:** `f != nil` on a proc value with no lambda the walker built: `ceUnsupportedHof`.
- **PRECISION:** `addr o.xs` bound by a `let`: `heUnsafeCast`.
- **PRECISION:** a query SAT only past the cap declines (S8k), rfind or not (`lastIdx`); a leaf equal to a leaf equal to a literal still takes the cap.
- **PRECISION:** a case object reaching a heap cell, as a global, declines. Pinned at 1ca792d (`gr_after`, `gr_raise`).

No SOUNDNESS item is left open from this slice.

## Notes for the coordinator

- **Decision, files over 60 s on Windows:** s8cd_setorder_small 88, s8cd_setorder_large 68 and s8cd_globals 64 are over the convention. Either accept them or ask for a further split or a smaller SUT set. Other corpus files are also over (at d783a8c: configdefaults_depth 174, s8bc_remainder_c 163).
- **Decision, `lastIdx`:** it stays a decline, because the query is SAT only past cap 8 (S8k). The job expected item 6 to clear it; say if you want that pursued as a cap change, which this slice did not make.
- **Overlap with origin/rfc-0005-s8bz (walker 247, same base):** `ptrInputOf` and the `irTypeRefFree` variant arms are textually identical, copied to merge cleanly. S8bz also changes `registerUnwritten` and lists the late-store case. Expect its merge with this slice's `ptrTargets` binding to need checking.
- **Local tooling mistake:** my first two 5.1 runs never ran a test, because `runset.sh` used a relative log path after its `cd`. Nothing in the tree was affected; the path is fixed.
