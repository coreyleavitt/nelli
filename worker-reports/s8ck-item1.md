# S8ck item 1: nim-z3 leak gate and examples, cc5ffc9 vs ae509f0

## Result

**Not clean as the job defines it, but nothing here is new at cc5ffc9, and no defect was found in the wrapper's hooks.** No fix was made and nothing was pushed.

1. **Invalid read at cc5ffc9, literal match for "soundness-grade".** There is one `Invalid read of size 1` in each of `tfixedpoint`, `tfixedpoint_newlemma` and `tfixedpoint_typed_callbacks`, on both Z3 versions.
   - It is inside libz3. On 4.13.4 the read is in `spacer::pob_queue::reset()`, of a block freed earlier in the same `spacer::context::solve_core`.
   - The alloc and free stacks contain no nim-z3 hook. The only Nim frames are the `Z3_fixedpoint_query` call chain.
   - It is identical at ae509f0.
   - nim-z3 cannot fix it, so it needs a decision: accept it as an upstream Z3 defect, or not. `src/nelli` has no fixedpoint reference (case-insensitive grep, no hits), so nelli's walker does not reach this path.
   - On 5.1 libz3 has no symbols. The same site is inferred from the matching read size, the matching offset (78 bytes into a 152-byte block) and the same stack shape.
2. **`run-tests.sh examples` is red at both shas.** `examples/properties.nim` does not compile at either: line 30 uses `.toInt` on a `Z3Int`, which has no such proc. This is not a memory defect and not an S8ce regression, so I left it unfixed. The other 12 examples pass on c and cpp.
3. **The gate passes for all 16 curated files at both shas.** Definite leaks are 0 throughout, with no invalid writes, invalid frees or double frees. Valgrind's loss records match exactly between the shas.

## The gate did not run exactly as the job assumed

- `tests/run.sh` does not exist. The script is `run-tests.sh` at the repo root (its header still says `tests/run.sh`).
- I ran it **one file at a time**, not as a single unfiltered `valgrind` or `examples` run. Its `set -e` stops at the first failure, which would hide every later file. Per file is the script's own documented explicit-file form. An unfiltered `examples` run would stop at `properties`, the 5th file, on both shas.
- I added options through `VALGRIND_OPTS`, leaving the script unchanged: `--num-callers=40 --freelist-vol=400000000 --keep-debuginfo=yes`. They give fuller stacks and hold freed blocks longer, so stale reads are more likely to be caught.
- The gate is C backend only, by its own design. cpp was not run under valgrind. Examples ran on both backends.

## What a pass does and does not show

- **The gate's pass criterion ignores invalid accesses.** It uses `--error-exitcode=0` and greps only `definitely lost: 0 bytes`. The invalid read/write/free counts below were taken from the logs, not from the gate's verdict.
- **It does not see contexts that stay unfreed.** `trcf` ends with 26 `Z3ContextOwn` blocks allocated by `newContext` still unfreed, and about 430 MB possibly lost, and it passes. `tfuncdecl` has 12 such blocks and `tfixedpoint` has 12. All are classed as possibly lost, and the counts are the same at both shas. This is consistent with item 2's missing `ctx` releases, but I did not establish which blocks are leaks and which are live-by-design globals. Item 2 needs `-d:z3CtxDestroyCount`, as the job says; the gate cannot prove that fix.
- **Limit on the double-free conclusion.** Valgrind only sees malloc and free. As I understand Z3's source (not tested here), ASTs live in Z3's own small-object allocator, so an extra `dec_ref` on an AST might not appear as a valgrind error. Supporting evidence, not proof:
  - possibly-lost totals, block counts and error counts are identical in all 54 sha pairs;
  - I read the hook diff for `lifecycle`, `ast`, `context`, `funcdecl_types` and `rcf`, and found the refcount conditions preserved. I did not read the other 12 changed `src` files line by line.

## Curated gate (16 files, the gate's own list)

Every run exited 0, and every log contains `definitely lost: 0 bytes`.

| test | Z3 | cc5 invalid R/W/free | ae5 invalid R/W/free | cc5 definite (bytes) | ae5 definite (bytes) | indirect, both | possibly lost, both (bytes / blocks) | same at both shas |
|---|---|---|---|---|---|---|---|---|
| tcontext | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,214,010 / 581 | yes |
| tcontext | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,208,618 / 545 | yes |
| tcontext_registry | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,214,010 / 581 | yes |
| tcontext_registry | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,208,618 / 545 | yes |
| td3_ctx_release | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,214,010 / 581 | yes |
| td3_ctx_release | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,208,618 / 545 | yes |
| tast | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,214,330 / 587 | yes |
| tast | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,208,906 / 553 | yes |
| tbitvec | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,233,926 / 635 | yes |
| tbitvec | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,222,790 / 585 | yes |
| tsolver | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,273,402 / 631 | yes |
| tsolver | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,267,690 / 597 | yes |
| tmodel | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,763,980 / 1,572 | yes |
| tmodel | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,693,564 / 1,362 | yes |
| tdatatypes | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,218,774 / 637 | yes |
| tdatatypes | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,212,438 / 599 | yes |
| tfp | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,287,022 / 664 | yes |
| tfp | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,275,814 / 614 | yes |
| tfixedpoint | 5.1 | 1/0/0 | 1/0/0 | 0 | 0 | 0 | 213,798,781 / 47,680 | yes |
| tfixedpoint | 4.13.4 | 1/0/0 | 1/0/0 | 0 | 0 | 0 | 210,919,310 / 39,954 | yes |
| tfixedpoint_ctxbox | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,282,250 / 840 | yes |
| tfixedpoint_ctxbox | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,258,994 / 756 | yes |
| tfixedpoint_handlers | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 51,825,894 / 2,100 | yes |
| tfixedpoint_handlers | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 51,789,534 / 1,906 | yes |
| tfixedpoint_newlemma | 5.1 | 1/0/0 | 1/0/0 | 0 | 0 | 0 | 225,108,774 / 8,639 | yes |
| tfixedpoint_newlemma | 4.13.4 | 1/0/0 | 1/0/0 | 0 | 0 | 0 | 225,013,802 / 7,684 | yes |
| tfixedpoint_typed_callbacks | 5.1 | 1/0/0 | 1/0/0 | 0 | 0 | 0 | 328,782,621 / 12,354 | yes |
| tfixedpoint_typed_callbacks | 4.13.4 | 1/0/0 | 1/0/0 | 0 | 0 | 0 | 328,650,849 / 11,106 | yes |
| tprobe | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,276,120 / 636 | yes |
| tprobe | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,270,248 / 597 | yes |
| tparity | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 51,707,688 / 1,882 | yes |
| tparity | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 51,685,624 / 1,762 | yes |

## Extension: hook families outside the curated list

These are not part of the gate. S8ce changed every hook and the curated list omits these families, so I ran the same mechanism on them.

Every cc5ffc9 run exited 0. `thook_raise_path` does not exist at ae509f0, so I copied it in temporarily and removed it afterwards. It exits 1 there, with 15 output lines matching `FAILED`, which is expected because it audits for the old hook shape. Its valgrind figures still match. At cc5ffc9 it shows 25 `[OK]`.

| test | Z3 | cc5 invalid R/W/free | ae5 invalid R/W/free | cc5 definite (bytes) | ae5 definite (bytes) | indirect, both | possibly lost, both (bytes / blocks) | same at both shas |
|---|---|---|---|---|---|---|---|---|
| thook_raise_path | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 137,881,684 / 4,660 | yes |
| thook_raise_path | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 137,826,788 / 4,348 | yes |
| trcf | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 430,806,866 / 14,136 | yes |
| trcf | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 430,688,770 / 13,238 | yes |
| tquantifier | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 87,640,968 / 5,739 | yes |
| tquantifier | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 87,419,592 / 5,064 | yes |
| tregex | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,729,576 / 1,683 | yes |
| tregex | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,659,032 / 1,481 | yes |
| tsequence | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,728,664 / 1,687 | yes |
| tsequence | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,658,760 / 1,485 | yes |
| tsets | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,248,087 / 595 | yes |
| tsets | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,242,599 / 559 | yes |
| tarray | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,749,467 / 1,521 | yes |
| tarray | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,684,683 / 1,330 | yes |
| tarray_sort_lifetime | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 86,072,338 / 2,881 | yes |
| tarray_sort_lifetime | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 86,044,450 / 2,708 | yes |
| tfuncdecl | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 190,871,289 / 9,388 | yes |
| tfuncdecl | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 190,612,125 / 8,351 | yes |
| tfuncinterp | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 86,374,038 / 3,219 | yes |
| tfuncinterp | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 86,317,454 / 2,969 | yes |
| tuninterpretedval | 5.1 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,216,466 / 589 | yes |
| tuninterpretedval | 4.13.4 | 0/0/0 | 0/0/0 | 0 | 0 | 0 | 17,211,074 / 553 | yes |

Across both tables, the multiset of leak records (bytes, blocks, kind) is equal in 54 of 54 sha pairs (27 files on 2 Z3 versions). Compiled binaries do differ between the shas (`cmp` on `tests/tast`), so these are two distinct builds. `ERROR SUMMARY` counts also match.

## Examples (`run-tests.sh examples <file>`, c then cpp)

Same result at cc5ffc9 and ae509f0, on Z3 5.1 and 4.13.4. Program output, with compiler lines filtered out, is identical between the shas.

| example | result |
|---|---|
| basic_solve, nqueens, bitvec_solve, pretty_and_smt2, tactic_pipeline, uninterpreted_axioms, float_verification, string_constraints, optimize_scheduling, array_memory, datatypes_list, smt2_roundtrip | pass, c and cpp |
| properties | **FAIL at compile, c; cpp never ran**: `examples/properties.nim(30, 26) Error: undeclared field: 'toInt' for type ast.Z3Int` |

- **Why it went unnoticed:** CI runs only `run-tests.sh test` (`.github/workflows/ci.yaml:87`). The example last changed at 3f3dc4d.
- **Candidate fix, tested but not committed:** `ensure s.model()[x].toInt64 == int64(k))`. With that line bind-mounted over the file, read-only, the example passes on c and cpp, on both shas and both Z3 versions. The source trees were not edited.

## Exact commands

Image, on top of `localhost/nelli-dev:latest`, whose image ID stayed `dbf4162a866f`. New image: `localhost/nelli-dev-valgrind:s8ck` (`352c7ee7b089`, valgrind 3.27.1, Z3 5.1.0):
```
podman --cgroup-manager=cgroupfs build -t localhost/nelli-dev-valgrind:s8ck -f image/Containerfile image/
```

Trees: `$W/s8ck-work/nim-z3-cc5` (local branch `rfc-0005-s8ck` at cc5ffc9, not pushed) and `$W/s8ck-work/nim-z3-ae5` (detached at ae509f0). Deps were fetched fresh from softlink v0.11.2 (8720427) and nelli ec7a405, as pinned in `milpa.lock`. They are byte-identical to S8ce's `_deps`.

Each run, with at most 2 at once and the pause flag checked before each launch (it was never set when checked):
```
timeout --signal=KILL <1800|900> podman run --rm --name s8ck_... -v $W/s8ck-work/nim-z3-<cc5|ae5>:/work -w /work \
  -e 'VALGRIND_OPTS=--num-callers=40 --freelist-vol=400000000 --keep-debuginfo=yes' \
  [-v $W/z3-4.13.4-x64-glibc-2.35/bin:/z3413:ro -e LD_LIBRARY_PATH=/z3413] \
  localhost/nelli-dev-valgrind:s8ck bash run-tests.sh <valgrind|examples> <file>
```
Which the script expands to:
```
nim c --threads:on --hints:off -d:debug -d:useMalloc --debugger:native --opt:none <f>
valgrind --leak-check=full --error-exitcode=0 --log-file=<f>.valgrind.log <bin>
grep -F 'definitely lost: 0 bytes' <log>
```

`z3FullVersion()`, run under valgrind in this image, printed `5.1.0.0` and `4.13.4.0` for the two configurations.

Scripts: `$W/s8ck-work/bin/`. Logs: `$W/s8ck-work/logs/{valgrind,examples}/<cc5|ae5>-<51|413>/`. Run index: `logs/results.txt`.

## Pushed

Nothing. There is nothing to commit: `rfc-0005-s8ck` exists locally at cc5ffc9 only.

