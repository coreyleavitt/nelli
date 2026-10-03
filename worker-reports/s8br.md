# S8br -- DONE

- **sha:** a25229d on `rfc-0005-s8br` (pushed). History on fa8edd8:
  - 429e413 `docs(rfc): 0005 -- add the S8br row`
  - d64b7ee `feat(symex): RFC-0005 S8br -- evaluate an index call once; frame-condition unsnapshotted checks`
  - a25229d `docs(rfc): 0005 S8br as landed -- ...; row done`

  There are no WIP commits.
- **base:** fa8edd8 (origin/rfc-0005-soundness-channels, batch 5, walker 223).
- **walker:** 223 -> 229.
  - The CR2 `==` pin is 229, and it was run: 6/0 on both Z3 versions.
  - The `>= 229` floor is in both S8br suites.

## RED and GREEN observed
New suites, both registered in nelli.nimble:
- `tests/tsymex_rfc0005_s8br_remainder.nim` (item 1): 5 tests, 14 labels.
- `tests/tsymex_rfc0005_s8br_framecond.nim` (item 2): 3 tests, 10 labels.

The `nim` tests assert every native outcome, and they passed at the base too: Nim calls `nextI` once, before the later argument, and the callee sees the element the later argument wrote.

| label | base (fa8edd8) | head | what it is |
|---|---|---|---|
| ic / ic_dead | sxUnknown (`unsupported nnkAsgn shape`) | sxSat (roConfirmed) / sxUnsat | `touch(gArr[nextI()], dblArr())` |
| iq / iq_dead | **sxUnsat / sxSat (false)** | sxSat (roConfirmed) / sxUnsat | the seq element: the copy-out called `nextI` a second time |
| iv / iv_dead | sxUnknown (nnkAsgn) | sxSat (roConfirmed) / sxUnsat | the later call moves what the index call read; the temporary keeps its value |
| ia / ia_dead | sxUnknown (nnkAsgn) | sxSat / sxUnsat | an `addr` actual (S8an's cell) |
| is | sxUnknown "never checked" | same | the later call shortens the seq; already right |
| fs_dead | **sxSat (false)** | sxUnknown, scoped feUnsupportedOp | `touch(gs[fv()], ...)`: an index call through a proc value cannot be named, so the write-back declines |
| ps / ps_dead | **sxUnsat / sxSat (false)** | sxSat (roConfirmed) / sxUnsat | the seq form through a proc value (`closureCallIR`) |
| pa / pa_dead | sxUnknown (nnkAsgn) | sxSat (roConfirmed) / sxUnsat | the array form through a proc value |
| hk / hk_dead | sxUnknown ("may change what the check read") | sxSat (roConfirmed) / sxUnsat | `touch(gH.s[gi], stampSeen())`: the later call leaves gH, its heap and gi alone |
| hb / hb_dead | sxUnknown (same) | sxSat (roConfirmed) / sxUnsat | the later call writes another heap (Box) |
| pk / pk_dead | sxUnknown (same) | sxSat (roConfirmed) / sxUnsat | `hk` through a proc value |
| hw, hi, he, pw | sxUnknown (decline) | same | the later call rebinds gH, moves gi, writes the seq, or rebinds gH through a proc value; already right |

**Vertical TDD caveat.**
- `ic` was RED at the unchanged head, then GREEN.
- Every other label's RED was observed on a base worktree (`wt/s8br-base`, detached fa8edd8, which has the same code on those paths).
- The proc-value pins and item 2's pins were added after their code was written. They were run RED on the base tree and GREEN at the head.

## Soundness bugs found
**SOUNDNESS: a seq element's copy-out evaluates an index call twice** (found pinning item 1, present at the base).
- `touch(gs[nextI()], f())`: the copy-out took `parseAsgn`'s `itSeq` arm, which re-parses the index, so `nextI` ran again.
- This is a false sxSat for the dead label and a false sxUnsat where Nim reaches the label.
- It affects the direct call (`iq`), a call through a proc value (`ps`), and an index call through a proc value (`fs_dead`).
- The array form declined instead.
- It is fixed by item 1's design.

## Design
1. **An index call in a by-address actual's lvalue.**
   - `hoistIndexCalls` lowers each user routine's call in an index on the lvalue path, root first and where the argument stands, into a `let`.
   - The `let` is named by a `markByRef` of the callee's own `result` symbol (`indexCallResult`), the way S8bd's `byRefSub` marks a call base: the mark keeps the type, and `strVal` reads it as the `let`'s name.
   - The actual is rebuilt around the mark; the call node is copied, never edited.
   - Copy-in, copy-out and S8an's cell all go through one value. S8bk's late address keeps the `let` in place, because it is not a lazy read, and moves the element read to the call.
   - It covers `userCallStmt` and S8bh's `closureCallIR`. On the proc-value path, an lvalue with an index call is never grouped as "the same location" as an earlier actual spelled alike (`hasIndexCall`).
   - A call the walk cannot name, such as one through a proc value or a generic call whose `result` type differs, gets a scoped `feUnsupportedOp` decline in the write-back instead of running twice (`indexCallLeft`, `indexCallDecline`).
   - `pureIndexExpr` already accepts the mark, because it is a symbol.
2. **A check no snapshot carries.**
   - `placeLateAddr`'s non-exact branch now declines only when a later argument may write a location the lvalue reads (`laterLeavesLvalue`): a variable it names (the root, or an index's variables) or a heap its path dereferences.
   - The later arguments' writes come from S8as/S8ax's summary (`laterArgWrites`):
     - per call, `scanOpaqueEffects` of the callee and `opaqueArgEffects` of its by-address actuals;
     - a routine passed as a value is summarised as a callee.
   - It treats as "may write anything":
     - a call through a proc value (`procValueSymKinds`), an assignment, or an inline routine;
     - a `ptr` step on the lvalue path;
     - a later argument that may write any heap or any global, or that reaches `*` or `t:?`.
   - If nothing is written, the lvalue is evaluated where it stands, which is exact.
   - `LateAddr` gained `lv` and `later`, set at all six of its constructions on both call paths.
3. **Compile time.**
   - The S8bk suite is now three files over one included fixture, `tests/s8bk_argtiming_fixture.nim`. The fixture is not named `t*`, so the sweep does not run it.
     - `tsymex_rfc0005_s8bk_argtiming`: copy-in/out, the chain, an element.
     - `..._addr`: the `addr` and by-reference actuals.
     - `..._checks`: the forwarded formal, the "never checked" declines, and the proc-value calls.
   - Each file has the native assertions for its own forms, and every function under test is the original.
   - The S8br suite was split for the same reason: as one file it took 56.3 s on Windows.
   - **Evidence (Windows symex-mingw, compile plus run per file, from the `==>`/`<==` timestamps):**

     | file | Windows time (s) |
     |---|---|
     | single S8bk file at fa8edd8 | 57.8 (run 37139806221) |
     | `_argtiming` at d64b7ee | 48.0 |
     | `_addr` at d64b7ee | 43.7 |
     | `_checks` at d64b7ee | 47.4 |
     | `s8br_remainder` at d64b7ee | 51.8 |
     | `s8br_framecond` at d64b7ee | 26.7 |
     | light `s8bm_stability`, same run | 49.3 |

     The d64b7ee times are from run 37159927354. Each file sits at the per-suite floor.
   - **Locally the box carried a load of about 15-21 on 8 cores** from other sessions (no pause flag was set). So local times measure load, not compile.
     - Run side by side, `s8bm_stability` took 94.5 s (c) and 116.2 s (cpp).
     - `s8bk_argtiming_checks` took 111.4 s (c) and 128.4 s (cpp).
     - The single S8bk file took 118.7 s (c) at the base under the same kind of load.
     - There was no Windows cpp leg.

## Suites (final code, c; tests ok/failed)
| suite | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| `rfc0005_s8br_remainder` | 5/0 | 5/0 |
| `rfc0005_s8br_framecond` | 3/0 | 3/0 |
| `rfc0005_s8bk_argtiming` | 5/0 | 5/0 |
| `rfc0005_s8bk_argtiming_addr` | 3/0 | 3/0 |
| `rfc0005_s8bk_argtiming_checks` | 4/0 | 4/0 |
| `rfc0005_s8ax_remainder` | 53/0 | 53/0 |
| `rfc0005_s8ba_remainder` | 32/0 | 32/0 |
| `rfc0005_s8bd_remainder` | 23/0 | 23/0 |
| `rfc0005_s8bf_alias` | 13/0 | 13/0 |
| `rfc0005_s8as_remainder` | 33/0 | 33/0 |
| `rfc0005_s8be_remainder` | 34/0 | 34/0 |
| `rfc0005_s8ab_letaudit` | 28/0 | 28/0 |
| `phase15_CR2_cachekey` (229) | 6/0 | 6/0 |
| `phase15_N2_kindgate_audit` | 5/0 | 5/0 |

**Totals:** 14 suites, 247/0 on Z3 5.1 and 247/0 on Z3 4.13.4.

**cpp (Z3 5.1):** `s8br_remainder` 5/0, `s8br_framecond` 3/0, `s8bk_argtiming` 5/0, `_addr` 3/0, `_checks` 4/0 (20/0).

**What was run:**
- The grep `command grep -l 'feEvalOrderUnmodelled' tests/tsymex_*.nim` returns `s8ax_remainder`, `s8be_remainder`, `s8bk_argtiming_checks`, `s8br_remainder` and `s8br_framecond`. All five are in the table.
- The other suites the job names: s8bk (3 files), s8ax, s8ba, s8bd, s8bf_alias, s8as, CR2 and letaudit.
- Added: N2, because Windows caught it, plus N0 (5/0) and N1 (32/0), run once each on 5.1 c.
- Every row is on the final code.
  - The verification queue (v3) started after the last source change, the N2 fix. It covered every suite above except the two S8br files, which were then split out of one file covering the same pins and run as v4.
  - The S8br split changed only test files and `nelli.nimble`.

## Windows
- **d64b7ee (the code of the final head):** symex-mingw 37159927354, fuzzer-mingw 37159927358, fuzzer-msvc 37159927403, all success.
- **a25229d** changes only `docs/`. The legs' `paths-ignore: docs/**` skips docs-only pushes, so no run was triggered.
- **Earlier runs:**
  - 58d0a08 symex-mingw 37154099381 failed only `tsymex_phase15_N2_kindgate_audit`: a bare `nskProc` kind gate in `laterArgWrites`. `procValueSymKinds` fixes it.
  - dc83791's runs (37156887549, 37156887544, 37156887562) failed only in the Z3 4.13.4 download step, a GitHub 503; every corpus shard passed. d64b7ee superseded them.

## Different mechanisms, reported and not fixed here
These are also committed in the RFC under "As landed (S8br)".
- **PRECISION: S8an's `addr` cell at a non-literal array index with an input-dependent value is a slow query.**
  - The probe: `var j = 1; touchP(addr gArr[j], 0); if gArr[1] != k + 5: ...`.
  - It did not finish in 420 s at the base, nor in 300 s at the head.
  - With `let j = nextI()` instead, the base returned `beSolverUndef` after about 200 s.
  - S8bk's `ai` and S8br's `ia` keep the written value constant for that reason.
- **PRECISION: S8as's summary treats every global a later callee names as written.** `scanOpaqueEffects` havocs each module-level `var` the body names, whether it is read or written. So `touch(gH.s[gi], f())` still declines when `f` only reads `gi` or `gH`.
- **PRECISION: an index call the walk cannot name declines.** These are `gs[fv()]` through a proc value, or a generic call whose `result` type differs from the call's. Nothing typed is available to mark, so the write-back declines rather than evaluate the call again.

## Tree state
- Untracked probes are in `wt/s8br/tests/probe_s8br/`; they are not committed.
- The base worktree is `wt/s8br-base` (detached fa8edd8) and holds untracked copies of the S8br test files plus probes.
- Scratch, logs, `run.sh`/`queue.sh` and `citimes.py` are in `/home/corey/tmp-usage/work/s8br-work/`.

## Scratch-clobber incident (verdict: not affected)

The parent session checked this directly.
- S8br started after the per-job-directory rule. All its scripts, job lists, logs and CI captures are in `/home/corey/tmp-usage/work/s8br-work/`.
- `grep -rln 'scratchpad\|/tmp/claude'` over its scripts and lists finds nothing, and no file in the shared scratchpad mentions S8br.
- No S8br result came from, or ran from, the shared scratchpad.
