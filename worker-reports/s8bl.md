# S8bl -- DONE

- **sha:** 1f38a13 on `rfc-0005-s8bl` (pushed). History on top of base: 4e81b5d `docs(rfc): 0005 S8bl -- add the slice row`, 7397f72 `feat(symex): RFC-0005 S8bl -- S8bc's remainder, walker 213`, 1f38a13 `feat(symex): RFC-0005 S8bl -- As landed, slice row done`.
- **base:** 22b67c7.
- **walker:** 203 -> 213 (provisional). The CR2 `==` pin is updated to 213 and run. The `>= 213` floor is in `tsymex_rfc0005_s8bl_magicscan`.
- **Tests registered:** the seven new suites `tsymex_rfc0005_s8bl_{magics,setlen,seqops,magicscan,gaps,borrow,pairloop}` and the three-way S8bc split `tsymex_rfc0005_s8bc_remainder_{a,b,c}` are all in `nelli.nimble`.

## RED and GREEN observed
All RED runs are at the base (22b67c7, Z3 5.1, c) unless noted.
- **setlen:** 6/7 tests FAILED at the base: false sxSat on a string `setLen`, `sxRaised`, and the seq decline.
- **gaps:** 12/12 FAILED at the base:
  - item 3 walker fault, Hash/alias declines, `for` over a literal walker fault;
  - mpairs/mvalues declines, the length-change decline;
  - the two-iteration false sxUnsat;
  - ref-part witness unsupported, long nested witness.

  The file was later regrouped to 11 tests.
- **borrow:** compile crash at the base ("node has no type").
- **magics:** at the base, swap of array elements or variables, `t[0].add 'x'` and a string `setLen` were false sxSat. `wasMoved`/`move` crashed the compile.
- **seqops:** `delete` declined at the base.
- **B6 file:** 741 s at the base under load.
- **pairloop** (added late, item 2 follow-up): with the literal-guard change disabled in this tree the file was killed at 300 s; an earlier probe ran past 900 s. The base answers the same in-loop target `sxUnknown` in 87 s.
- **GREEN:** every suite in the table below.

## Soundness bugs found
1. **SOUNDNESS: var-parameter system magics were silent no-ops.** `ensureProcRegistered` registered them with empty bodies. Each is now modelled or a scoped decline naming the magic (`varParamMagics`). `tsymex_rfc0005_s8bl_magicscan` scans system.nim and fails on any var-parameter magic the table does not classify.
2. **SOUNDNESS: two iterations of one input Table gave a false sxUnsat (C).** On cpp it was `weInternalWalkerFault`. The cause: an unconstrained key term of another path's enumeration, plus a witness-extraction raise inside the walk that the C backend lost. Every string key term is now a byte string.
3. **SOUNDNESS-adjacent (a regression inside this slice, caught and fixed):** the item 2 grounding made most `if` guards fold to literals, and both sides were still walked. That gave 2^k duplicate paths, and an in-body target hung. It is now `guardLiteral`, pinned by `pairloop`.

## Design per item
1. **Magics.**
   - Modelled: `swap`, `wasMoved`/`reset`/the `=wasMoved` hook, `move`, `setLen` on seq and string (`isSetLen`; the string grow pads NULs on a separate path), element `add`, `inc`/`dec` with n, `=copy`/`=sink`, and seq `delete` (`iekSeqDel` `delShift`: `lambda j. ite(j < i, a[j], a[j+1])`).
   - Declined, naming the magic: `incl`/`excl` on a builtin set, `=destroy`, `=trace`, `shallowCopy` (undeclared under ORC), and unreached shapes.
2. **Pair loop.** Every infeasible loop-exit target hit spent the 20M `seqQueryRLimit`, because the pinned scan was never ground. The fix has five parts:
   - an assumed `s == "lit"` binds the literal;
   - a ground one-character `indexof` folds;
   - a clean callee result that folds to literals is bound as them;
   - a refuted path still active at the unroll bound is dropped;
   - an `if` guard that folds to a literal takes one side only.

   `r6_b6_optionregion` now takes 61 s on Z3 5.1 and 37 s on Z3 4.13.4. That is the whole file including compile, measured during the 3-way sweep at load average 12-15 on 8 cores; the base took 741 s.
3. **Unbacked-element `add`:** the placeholder decline `seNestedSeqUnsupported`.
4. **The smaller gaps.**
   - Aliases classify as their target.
   - A fewer-formals borrow appends the base's defaults. Calls to such a borrow crash Nim 2.2.10's codegen, so the parse is pinned at IR level.
   - Borrow views are applied through `viewTypeKind`/`viewTypeInst`/`viewTypeImpl`.
   - `for x in [a, b]` binds a let.
   - mpairs/mvalues write back through `mutViewWriteBack`.
   - A Table length change raises `AssertionDefect`.
   - Ref-part seq elements are witness positions.
   - Nested seqs render up to 2^20 elements.
5. **Split:** the S8bc suite is split into a/b/c. Each file takes 46-48 s here on 5.1 including compile; the old file took 82 s on symex-mingw.

## Pins moved
These pinned gaps that S8bl closes:
- B6-1-red and B6-6 are now sxSat with the real accumulator.
- s8d typeheads: Natural alias and Rune are now sxSat.
- CR2c, tot1 and N43-P2: the unrenderable element is now a ref inside a Table.
- N27: the marker count is 97.
- s11 walkthrough 3: the sensor is read before the loop.
- phase13 cold UNSAT: no longer `x != x`.
- s8bc_c length change: `AssertionDefect`.
- setlen: the keep/pad pins use ground strings. Over a symbolic string both Z3s leave the `str.at` undecided, so they would be an honest sxUnknown.

## Suites (head tree, c; `ok/failed`)
| suite | Z3 5.1 | Z3 4.13.4 | cpp (5.1) |
|---|---|---|---|
| rfc0005_s8bl_magics | 8/0 | 8/0 | 8/0 |
| rfc0005_s8bl_setlen | 7/0 | 7/0 | 7/0 |
| rfc0005_s8bl_seqops | 4/0 | 4/0 | 4/0 |
| rfc0005_s8bl_magicscan | 3/0 | 3/0 | 3/0 |
| rfc0005_s8bl_gaps | 11/0 | 11/0 | 11/0 |
| rfc0005_s8bl_borrow | 4/0 | 4/0 | 4/0 |
| rfc0005_s8bl_pairloop | 2/0 | 2/0 | 2/0 |
| rfc0005_s8bc_remainder_a / b / c | 27/0, 18/0, 29/0 | same | same |
| r6_b6_optionregion | 8/0 (61 s) | 8/0 (37 s) | -- |
| rfc0005_s8at_remainder | 67/0 | 67/0 | -- |
| rfc0005_s8ar_remainder | 50/0 | 50/0 | -- |
| phase15_M1_seq_fixedwidth | 13/0 | 13/0 | -- |
| r6_r6_emit_roundtrip | 104/0 | 104/0 | -- |
| rfc0005_s8ab_letaudit | 28/0 | 28/0 | -- |
| phase15_CR2_cachekey | 6/0 | 6/0 | -- |
| CR2c_witnessreader_catchall | 17/0 | 17/0 | -- |
| phase5_seq / phase5_table | 3/0, 2/0 | same | -- |
| r6_n21_pairloop_member / r6_r5_pairloop_counter | 14/0, 5/0 | same | -- |

**Totals.**
- **Z3 5.1:** 127 files in the sweep (every r6_*, every rfc0005_*, CR2, M1, 163rev, F9b, phase5, r4). All rc=0 except `rfc0005_s11_surface`, whose pin was then moved and rerun green. `phase13_layer1_wire` (CI red) was also moved and rerun green.
- **Z3 4.13.4:** 75 files, all rc=0, plus s11 and phase13 rerun green.

## Windows CI
- **Final head 1f38a13:** symex-mingw 37127985755 success, fuzzer-mingw 37127985763 success, fuzzer-msvc 37127985778 success.
- **Previous code-identical WIP (2cef967):** all three legs green (37112690177 / 37112690272 / 37112690175).
- **1b0bcaa (guardLiteral):** symex-mingw red on s11 walkthrough 3 and phase13 cold UNSAT. Both pins are moved in the final head.

## Different mechanisms, reported and not fixed here (also in the RFC)
- **SOUNDNESS:** a raise from witness extraction inside the walk is lost on the C backend; the walk continues, and the verdict can be a false sxUnsat. S8bl removed the one trigger it found.
- **Crash:** a variant arm's untouched seq of an element holding a ref inside a Table fails the compile. `isRenderableWitnessTy` and the reader drift apart there.
- **PRECISION:** mpairs aliasing, where one call receives both the loop variable and the table.
- **PRECISION:** a length-preserving key change while iterating a Table follows the initial enumeration. Such paths are `feTableIterOrder`-tainted.
- **PRECISION:** string `setLen` over a symbolic string, where `str.at` is undecided on both Z3s (honest sxUnknown).
- **Integration:** `iekSeqNewZero` (S8bc) and `iekSeqNew` (S8bi) model the same `newSeq` family. Not reconciled here.

## Notes
- **Retracted finding.** Mid-slice I suspected a false sxSat in the pair loop (a 4-pair count over what I misread as an 8-pair literal). The literal holds 4 pairs, so the verdict was right and the finding is retracted. `pairloop` pins the exact counts.
- **Scratchpad collision.** The scratchpad is shared with other workers. My `sweep.sh` overwrote a same-named script of another worker at 03:20. That worker then ran it at 04:03, which ran my lists in my worktree. I stopped that process tree and moved my files to `scratchpad/s8bl-own`. The other worker's `sweep.sh` is lost and may need recreating.
