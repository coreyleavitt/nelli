# S8cl report: DONE

- **SHA:** 9510e3eddc48de8fb9ce2a208a58b4ce61563cc4, branch `rfc-0005-s8cl`, pushed.
- **Base:** batch 9 e497dcf, merged at 2271cb1. Started on afce42a + S8ca 8cef160 (f7779d5).
- **Walker:** 248, provisional. Batch 9 is 245; 246 and 247 are taken. If 248 is also taken at integration, the integrator assigns the number. The CR2 pin and both new floors say 248.
- **nim-z3:** cc5ffc9 (lock identity 9a033beb...).
- **RFC:** the row is `done`; the note is "As landed (S8cl)" in docs/rfc/0005-branch-scoped-degrade.md.

## Windows, all at 9510e3e

| Leg | Run | Result |
|---|---|---|
| symex-mingw | 41537427038 | success |
| fuzzer-mingw | 41537427003 | success |
| fuzzer-msvc | 41537426940 | success |

Shards took 18.9 to 36.7 min against the 40 min budget.

**Earlier runs that are not green:**
- 28e2bc4: symex-mingw 41491401016 (attempt 2) failed on three suites.
  - `tsymex_rfc0005_s8ca_stack`: the call depth limit failure, fixed by batch 9's work.
  - `tsymex_rfc0005_b8_integration`: `pv_dead` false sxSat, which is S8ca's old base without batch 9's `closureTakesView`.
  - `tsymex_r6_n36_raise_class_audit`: my unmarked raise, now marked.
  - fuzzer-mingw 41491400836 and fuzzer-msvc 41491400805 (rerun) succeeded at that sha.
- 2271cb1: symex-mingw 41527451919 failed on one suite: `tsymex_rfc0005_b9_integration` still pinned the `unsafeNew` decline. `s8ca_stack` passed there. fuzzer-msvc 41527451880 and fuzzer-mingw 41527451895 succeeded.

## RED and GREEN observed

**RED at S8ca head 8cef160:** logs/RED.items123.s8cahead.a.log and .b.log.
- `unsafeNew(p, 8)`: `p != nil` false sxUnsat, `p == nil` false sxSat, `p[] = k` sxRaised. Nim hits the first and never raises. This is the October finding, reconstructed.
- `setLen`: sxUnknown on `nnkWhenStmt`, and the same for a `mitems` body that resizes with it.
- `wasMoved`: compile error, "Expected a node of kind nnkIdentDefs, got nnkSym".

**RED at the merged tree f7779d5:**
- logs/RED.magics.merged.log: 10 ok, 5 failed.
- logs/RED.strings.merged.log: 3 ok, 4 failed, all `newString`/`newStringOfCap` `feOpaqueCallUnmodelled`.
- n43 on cpp: deleted `std::atomic` `operator=`, reproduced.
- `create(int)` and `GC_ref` stopped the compile (observed in probes; logs are not kept as RED files).

**GREEN:** the suites below at the final source.

## How job items 1-3 stood against the tree

S8bl, in the base, already modelled `wasMoved`, `reset`, `setLen`, `move` and `swap`, and declined `unsafeNew`. So those items were pins rather than gaps, as you instructed.

The `unsafeNew` model **improves a decline on this stack; it does not fix a live false verdict**. At afce42a and e497dcf all its labels are sxUnknown; the false verdicts exist only at 8cef160.

## Soundness bugs found and fixed

Run results; the native column is observed. The 6cbfe8f and e497dcf columns are from the probes in s8cl-work/probe/.

| Finding | Native | 6cbfe8f | e497dcf | At 9510e3e |
|---|---|---|---|---|
| `gs.setLen(growG())`: `sw` | hit | sxUnknown | false sxUnsat | sxSat |
| same call: `sw_dead` | not hit | sxUnknown | false sxSat | sxUnsat |
| `setLen(a[gi], bumpLen())`: `sv_nim` (element values) | hit | sxUnknown | false sxUnsat | declines |
| same call: `sv_dead` | not hit | sxUnknown | false sxSat | declines |
| `procCall(idf(k))`: `pc_dead` | not hit | false sxSat | false sxSat | declines |
| `ensureMove(a)`: `em` | hit | sxUnknown | false sxUnsat | declines |
| same call: `em_dead` | not hit | sxUnknown | false sxSat | declines |

- The e497dcf `setLen` verdicts carry one "never reached" `feUnsupportedOp` diagnostic, so they are not literally clean. The `procCall` verdicts carry no errors on either sha, and neither do the `ensureMove` verdicts at e497dcf.
- The `setLen` rows are the release blocker reported earlier: new on the channel, cleared when S8cl lands.
- `sa_second` and `sa_first` (lengths only) are right at e497dcf by coincidence: the walk writes the old `a[0]`, cut to length 1, into `a[1]`.
- The 9510e3e column is pinned by the suites, using `sutSetLenWrites`, `sutSetLenLater`, `sutProcCall` and `sutEnsureMove`. The `sa` pin checks the decline, not the `sv` labels' text.

## Design per item

**1. Magics (src/nelli/smt/dsl_parser.nim).**
- `parseUnsafeNew`: a fresh zeroed cell through a pure lvalue, `RangeDefect` on a negative size, a decline when the size is under the pointee's or above `maxModelledInitialSize`, `feEvalOrderUnmodelled` when the size's call writes what the place reads.
- Any magic with no statement to walk declines, naming the magic (`magicBodyEmpty`).
- Decided and native-pinned: `reset` (variable, field), `move` (variable, array element), `new` (expression, field, object), `wasMoved` (seq, int, through a pointer), `=copy`.
- Declined and pinned: `new(p, finalizer)`, `=sink`, `=dup`, `=destroy`, `newStringUninit`.
- `shallowCopy` is not declared under ORC and stays `vmDeclined`; this is read from code, with no probe.

**2. What cannot be read declines.**
- `formalsReadable` covers a generated hook's `nnkArgList` and a generic instance's formal typed only by its default (`create`).
- The type bridge leaves an object with a `when` member unsupported (`GC_ref` reached one through `RefHeader`).

**3. `setLen`.**
- It reads the old value after its length for a bare variable.
- `laterArgDecline` covers an lvalue whose index the length's call writes.
- A `mitems` body that resizes with `setLen` decides. An element used after the resize stays a decline (S8ca's pin).

**4. `newString`.**
- `newString` and `newStringOfCap` go through `isSetLen` with `slFresh`: `Natural`'s check, the modelled bound, NUL bytes, `sbOwned`. A by-value copy of the address-taken result now decides.
- **An opaque call's result stays a decline:** it may be a literal's memory or its own, a by-value copy shares only the first, and no one answer is sound for both. Pinned in `_strings` and in S8ca's `_strings_byvalue`, whose source moved from `newString` to a `symexOpaque` call.

**5. cpp.**
- `storeOrdinal[F]` range-checks and writes through the bytes; `readCellField`'s ordinal arm and `validDefault` both use it. The raise is marked category-c and the inventory counts updated: `runtimeCount` 81, `cCount` 84.
- **No CI leg runs cpp.** The suites run on cpp in this verification and in `scripts/psweep.sh` (read from the script, not run). I did not add a CI cpp list.

**Pins changed in other suites:**
- `tsymex_rfc0005_b9_integration`: `unsafeNew` labels now take the verdicts Nim's run confirms.
- `tsymex_rfc0005_s8bl_magicscan`: its declined magic is now `new(p, finRef)`.
- `tsymex_rfc0005_s8ca_strings_byvalue`: see item 4.

`s8cl_magics` was split into `_magics` and `_lifetime` after 67 s on Windows.

## B21

`tsymex_r6_n42_deref_taint` and `tsymex_r6_n43_parity` on cpp at 9510e3e, on both Z3 versions, passed 15/0 and 25/0, rc 0. Run at the tip. This is not a release blocker.

## Overlap for the integrator: `ensureMove` and S8cb

S8cb 28ab1a7 models `ensureMove` as x's value (dsl_parser.nim:10438) and has its own empty-magic helper (~:18580). My `magicBodyEmpty` decline covers the same empty bodies. As instructed, I did not merge S8cb or change my pin.

- S8cb's model should win, with the decline kept for `procCall` (S8cb does not list it).
- `declines(sutEnsureMove, ...)` in `_magics` must become a decided pin.
- The two helpers should become one.

Observed at 28ab1a7 (z3 ae509f0): `em` sxSat, `em_dead` sxUnsat, `dn` sxSat, `dl_dead` sxUnsat, `d3` sxSat. All match native.

## Merge

The tree at 2271cb1 is e497dcf plus `git diff f7779d5 120509e`. **Batch 9's resolution of S8ca stands in place of the one in my trial-merge diff** (reports-out/s8ca-trial-merge.diff), which is superseded.

I built it with `merge -s ours`, then `read-tree --reset` to e497dcf, then `apply --3way`, because a plain merge conflicted heavily on the shared S8ca history. Parents are 120509e and e497dcf. My own `pv_dead` fix was dropped uncommitted.

## Per-suite results (ok/failed)

Source is the same as 9510e3e: `git diff --stat 2271cb1 9510e3e` touches only tests, docs and nimble. Suites changed after 2271cb1 were rerun: `_magics`, `_lifetime`, `b9_integration` on all four columns. A dash means not run on that column.

| Suite | 5.1 c | 4.13.4 c | 5.1 cpp | 4.13.4 cpp |
|---|---|---|---|---|
| tsymex_configdefaults | 23/0 | 23/0 | - | - |
| tsymex_configdefaults_depth | 1/0 | 1/0 | - | - |
| tsymex_phase15_CR2_cachekey | 6/0 | 6/0 | 6/0 | 6/0 |
| tsymex_phase15_N2_kindgate_audit | 5/0 | 5/0 | - | - |
| tsymex_r6_n27_hof_placeholder | 6/0 | 6/0 | - | - |
| tsymex_r6_n27_placeholder_read_audit | 4/0 | 4/0 | - | - |
| tsymex_r6_n36_raise_class_audit | 14/0 | 14/0 | - | - |
| tsymex_r6_n42_deref_taint | 15/0 | 15/0 | 15/0 | 15/0 |
| tsymex_r6_n43_parity | 25/0 | 25/0 | 25/0 | 25/0 |
| tsymex_r6_r6_emit_roundtrip | 112/0 | 112/0 | - | - |
| tsymex_rfc0005_b8_integration | 16/0 | 16/0 | - | - |
| tsymex_rfc0005_b9_calldepth | 3/0 | 3/0 | - | - |
| tsymex_rfc0005_b9_integration | 15/0 | 15/0 | 15/0 | 15/0 |
| tsymex_rfc0005_s7_closure | 37/0 | 37/0 | - | - |
| tsymex_rfc0005_s8ab_letaudit | 28/0 | 28/0 | - | - |
| tsymex_rfc0005_s8bl_magicscan | 3/0 | 3/0 | 3/0 | 3/0 |
| tsymex_rfc0005_s8bl_setlen | 7/0 | 7/0 | - | - |
| tsymex_rfc0005_s8bu_byvalseq | 5/0 | 5/0 | - | - |
| tsymex_rfc0005_s8bu_calls | 8/0 | 8/0 | - | - |
| tsymex_rfc0005_s8bu_mitems | 5/0 | 5/0 | - | - |
| tsymex_rfc0005_s8bu_paths | 4/0 | 4/0 | - | - |
| tsymex_rfc0005_s8bu_term | 10/0 | 10/0 | - | - |
| tsymex_rfc0005_s8bu_varviews | 5/0 | 5/0 | - | - |
| tsymex_rfc0005_s8bu_views | 5/0 | 5/0 | - | - |
| tsymex_rfc0005_s8bx_setlenstr | 3/0 | 3/0 | - | - |
| tsymex_rfc0005_s8ca_calls | 4/0 | 4/0 | - | - |
| tsymex_rfc0005_s8ca_closures | 3/0 | 3/0 | - | - |
| tsymex_rfc0005_s8ca_closures_heap | 4/0 | 4/0 | - | - |
| tsymex_rfc0005_s8ca_derefmut | 5/0 | 5/0 | - | - |
| tsymex_rfc0005_s8ca_procvals | 4/0 | 4/0 | - | - |
| tsymex_rfc0005_s8ca_resize | 6/0 | 6/0 | - | - |
| tsymex_rfc0005_s8ca_stack | 9/0 | 9/0 | - | - |
| tsymex_rfc0005_s8ca_strings | 4/0 | 4/0 | - | - |
| tsymex_rfc0005_s8ca_strings_byvalue | 3/0 | 3/0 | - | - |
| tsymex_rfc0005_s8ca_views | 7/0 | 7/0 | - | - |
| tsymex_rfc0005_s8cl_lifetime | 11/0 | 11/0 | 11/0 | 11/0 |
| tsymex_rfc0005_s8cl_magics | 7/0 | 7/0 | 7/0 | 7/0 |
| tsymex_rfc0005_s8cl_strings | 7/0 | 7/0 | 7/0 | 7/0 |

No cell fails. `b9_integration` at 2271cb1 was 14/1 on 5.1 c, before the repin.

## Per-file Windows times, symex-mingw 41537427038

Total is `==>` to `<==`, compile included. Suites in this slice's verification:

| File | Total s | Run s |
|---|---|---|
| tsymex_configdefaults_depth | 175.4 | 136.3 |
| tsymex_rfc0005_s8ab_letaudit | 107.8 | 0 |
| tsymex_rfc0005_b9_integration | 81.2 | 17 |
| tsymex_rfc0005_b8_integration | 77.8 | 10.5 |
| tsymex_rfc0005_s8bu_calls | 56.7 | 1.8 |
| tsymex_rfc0005_s8ca_stack | 55.6 | 14.3 |
| tsymex_rfc0005_s8cl_magics | 51.9 | 0.7 |
| tsymex_rfc0005_s8bu_mitems | 49.7 | 2.6 |
| tsymex_rfc0005_s7_closure | 49.4 | 2.3 |
| tsymex_rfc0005_s8ca_resize | 48.9 | 1.8 |
| tsymex_rfc0005_s8ca_views | 48.3 | 1 |
| tsymex_rfc0005_s8bu_views | 48.1 | 2.3 |
| tsymex_rfc0005_s8cl_lifetime | 47.4 | 1.1 |
| tsymex_rfc0005_s8ca_derefmut | 47.0 | 0.9 |
| tsymex_rfc0005_s8bu_byvalseq | 46.5 | 1.9 |
| tsymex_r6_n43_parity | 43.1 | 0.2 |
| tsymex_rfc0005_s8ca_strings_byvalue | 42.8 | 0.7 |
| tsymex_rfc0005_s8bl_magicscan | 39.5 | 0.1 |
| tsymex_rfc0005_b9_calldepth | 39.5 | 0.1 |
| tsymex_rfc0005_s8cl_strings | 38.8 | 2.2 |
| tsymex_configdefaults | 37.3 | 12.4 |
| tsymex_rfc0005_s8ca_strings | 37.0 | 7.8 |
| tsymex_rfc0005_s8bu_varviews | 36.9 | 1.2 |
| tsymex_rfc0005_s8ca_procvals | 36.6 | 3.2 |
| tsymex_rfc0005_s8bu_paths | 36.0 | 1.6 |
| tsymex_rfc0005_s8ca_calls | 35.4 | 1.3 |
| tsymex_rfc0005_s8ca_closures_heap | 35.0 | 0.8 |
| tsymex_r6_n27_hof_placeholder | 34.9 | 0.2 |
| tsymex_r6_n42_deref_taint | 34.2 | 0.5 |
| tsymex_rfc0005_s8bu_term | 29.2 | 4.7 |
| tsymex_rfc0005_s8ca_closures | 23.9 | 0.2 |
| tsymex_r6_r6_emit_roundtrip | 8.1 | 0 |
| tsymex_r6_n36_raise_class_audit | 4.1 | 0.5 |
| tsymex_r6_n27_placeholder_read_audit | 3.5 | 0.2 |
| tsymex_phase15_CR2_cachekey | 3.5 | 0 |

- Both S8cl files are under 60 s: `_magics` 51.9, `_lifetime` 47.4, `_strings` 38.8.
- 38 of 545 corpus files are over 60 s; none is S8cl's. In my list: `tsymex_configdefaults_depth` 175.4, `s8ab_letaudit` 107.8, `b9_integration` 81.2, `b8_integration` 77.8. The slowest overall are `s8bc_remainder_c` 154.2, `s8ax_remainder` 135.2, `s8s_precision` 132.9. I did not compare these against e497dcf.

## Different mechanisms, reported and not fixed here (also in the RFC note)

- **SOUNDNESS, fixed elsewhere: `$k` on a negative int and `ensureMove`.** False at e497dcf, right at S8cb 28ab1a7, observed. `$k` gives the same verdicts at 6cbfe8f, so it is old. Not reported as open.
- **SOUNDNESS, old and declined here: `procCall`.** False sxSat at 6cbfe8f and e497dcf.
- **PRECISION: `zeroMem` and `copyMem` on `addr x`** decline through a walker fault: `FieldDefect` reading `ptrPointeeTy` of an `itUninterp`.
- **PRECISION: declines left as declines.** `alloc0` behind a cast (`heUnsafeCast`), `ensureMove`, `procCall`, `create`, `new(p, finalizer)`, `GC_ref`, an object with a `when` member, a `type` section inside a SUT, a nested `s[gi]` of a seq of seqs.

## Process notes

- My first verification list included binaries, so some suites ran twice at once in one tree, against the no-concurrent-same-file rule (CR2, n27 audit, n43, magicscan, among others). I stopped it, discarded its results (logs/summary.discarded-duplicate-list.txt) and reran from a deduplicated list.
- `tsymex_rfc0005_b8_integration` and the n36 audit were not in my first list, which is why Windows found those two failures first.
- The wider magic-decline regression check was the full symex-mingw corpus at 9510e3e, not a local `scripts/sweep.sh`, plus the three other local users of the changed magics (`tsymex_rfc0005_s8bl_setlen`, `tsymex_rfc0005_s8bx_setlenstr`, `tsymex_phase15_N2_kindgate_audit`).
- The branch keeps its WIP commit 5d47936 and S8ca's WIP commits; no force-push was used.
- Scratch worktrees `s8cl-red` and `s8cl-p-*` are removed.
