# Lens E — reconciliation and harvest of the RFC-0016 work list

Snapshot `83c1d304` (= origin/main). Every claim is marked `read` (source,
test or doc read) or `ran` (a command was run and its output is quoted).
Nothing was built; no test was executed. Where a row's closure rests on a
test, the evidence is that the test is in the corpus at this sha and the
RFC-0005 handoff records the whole-suite gates green at `476976d3`
(c 975/975, cpp 975/975, Windows three legs; `0005-...handoff.md:573-583`,
`read`), which is the current head minus docs commits.

Status vocabulary used below:

- **open** — the item stands as written.
- **closed** — fixed, with a test in the corpus that pins the native
  behaviour (commit and test named).
- **closed-by-decline** — the false verdict is gone because the shape now
  declines; the decline is pinned with a native run. The soundness half is
  closed; what remains is a precision item and is named.
- **needs-native-repin** — the fix is in, but no test at head runs the
  shape natively (or the shape is not in the corpus at all). The test that
  would close it is named.
- **duplicate-of** — the same item under another id.
- **stale-evidence** — the row's evidence column no longer describes head.
- **mis-scoped / mis-filed** — belongs elsewhere (another RFC or section).

---

## 1. Row status table

### §5.1 Soundness (SND)

| Row | Status | Evidence | Action to close |
|---|---|---|---|
| SND-01 | **closed-by-decline** (native) | `tests/tsymex_rfc0005_s8cq_varret.nim:84,158-159` pins `rab(t["a"], t, "a")` (p01) `sxUnknown` with `nativeHit = true`; `tests/tsymex_rfc0005_s8cq_byvalue.nim:126,162-163` pins `vc_rx1` native HIT, walker `sxUnknown`. S8cq landed in batch 11 (`b23d9413`, `7ae4ab52`, merge `47e3363e`). `read` | Close the soundness row. The exact model of a `var`-returning actual has **no PRC row** — see HRV-01 |
| SND-02 | **closed** | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` checks `$n == "-5"` natively; `:62-63` pins `negs`/`negsu`. S8cb merged at `72b2c2b8`. `read` | none; drop the "confirm at the tag head" wording (the suite runs at head) |
| SND-03 | **closed** | same file, `:74-80` (`$` of a char), native values at `:37-52`. `read` | none |
| SND-04 | **closed** | same file, `:81-99` (`enumname`, `enumstrname*`), `:116-118` (`repr(enum)`). `read` | none |
| SND-05 | **closed** | `tests/tsymex_rfc0005_s8cl_magics.nim:208-218`: native run (`nativeHits(sutEnsureMove…)`) then `clean(sutEnsureMove, "em_dead", sxUnsat)`. `read` | none |
| SND-06 | **closed-by-decline** (native) | `tsymex_rfc0005_s8cl_magics.nim:220-222` `declines(sutProcCall, "pc_dead", "ProcCall")` after the native run at `:210`; the three `procCall` forms are also pinned in `tsymex_rfc0005_b10_integration_b.nim:9-12`. `read` | close; exact model stays as PRC-21 |
| SND-07 | **closed-by-decline, needs-native-repin** | `tests/tsymex_rfc0005_s8cp_unchecked.nim:229-230` pins `readsOtherArm`/`diff` as `sxUnknown` ("was a false sxRaised, main a false sxSat"). The file's `verdict` template (`:32-38`) has **no native run**; no `nat`/`symexCapture` in the s8cp suite. `read` | add a native run of `readsOtherArm` (HIT on `diff`, as the sort's `p_cp ua3_diff` had) in the same file; the exact model (bytes of the other arm after `uncheckedAssign`) has no PRC row — HRV-02 |
| SND-08 | **closed-by-decline** (native) | `tests/tsymex_rfc0005_s8cs_routes.nim:525-526,542-549` (`HeapH` `=destroy` writes `d.r[]`), native run `:603`, hit list `:616,622`; walker pins `tests/tsymex_rfc0005_s8cs_routes_c.nim:292-293` `declined(heap1, …)`. `read` | close; exact hook model is INT-10 / PRC-04's hook family. The row's "No owner. S8cs covers global write routes only" is **stale**: S8cs's "no global at all" suite covers it |
| SND-09 | **closed-by-decline** (native) | `tsymex_rfc0005_s8cs_routes.nim:110-113` (`w2`), native `:590`, hits `:608,622`, `declined(w2, "w2_live"/"w2_dead")` at `:642-643`. `read` | close |
| SND-10 | **closed** | `tests/tsymex_rfc0005_s8cf_limits.nim:71-85`: native `std/re` first, then `check … .status != sxUnsat` for `cf_match_hit`. S8cf merged at `d08fe846`. `read` | none (the pin is one-sided: not-wrong, not exact; exactness is PRC-33 item 10) |
| SND-11 | **closed** | same file `:92` `!= sxSat` for `cf_miss_long`. `read` | none |
| SND-12 | **needs-native-repin** | No test contains the `gc_shared` shape (`ran`: `grep gc_shared tests/` empty). The nearest pin is the local-seq cursor `sCur`/`cu_shared` (`tests/tsymex_rfc0005_s8cn_seqview_e.nim:124-128,158-172`, declined, native). The probe lives at `origin/worker-sls2:worker-reports/s8cn-blocker/s8cn_release_blocker_probe.nim` with logs for both shas (`ran`: `git ls-tree`). The decline mechanism is `letCursorDecline` (`dsl_parser.nim:16698-16706`). | port probe 1 (a `let` cursor over a shared **global**) into `tsymex_rfc0005_s8cn_seqview_*` at head: native HIT + `status != sxUnsat`, expected `sxUnknown` |

### §5.2 Precision (PRC)

| Row | Status | Evidence | Action to close |
|---|---|---|---|
| PRC-01 | open; **duplicate-of** INT-01, INT-14 | `replayproc.nim:161-178` `hostRuntimeHook`; Windows re-exec marshalling declines | one row, three ids: collapse |
| PRC-02 | open; **duplicate-of** INT-13 | same mechanism | collapse |
| PRC-03 | open | `tests/tsymex_rfc0005_s8cr_pins.nim:98` (`feGlobalHavoc`) | as written |
| PRC-04 | open (inventory) | 354 decline construction sites in `src/nelli/smt` (`declineAtSite|declineMarker|degrade(|…`, `ran` by the code-harvest lens); 91 `SymexErrorKind` members, 12 with no producer (§2 below) | the inventory should start from those 354 sites; INT-10 is a member of this row, not a separate one |
| PRC-05 | open | list matches `origin/worker-sls2:worker-reports/s8cn.md:186-203` item for item (`read`); the "ds, dt, dv forms" are not in that list (come from elsewhere). The "pointer plus 11 inserts" bullet in the report is CRH-05. `lentLoopDecline` `dsl_parser.nim:16658-16678`, `letCursorDecline` `:16698-16706` both say "(RFC-0016)" | as written; note CRH-05 is inside it |
| PRC-06 | open | `tests/tsymex_rfc0005_s8bc_remainder_c3.nim:119-124` pins `sxUnknown` + `reproduces(tiGrow(0), "ti_grow")`. `read` | as written (row accurate) |
| PRC-07 | open | `check_options.nim` source scan; S8cu `cl_*` suites | as written |
| PRC-08 | open | depends on PRC-07 | as written |
| PRC-09 | open | as written | |
| PRC-10 | open | `tests/tsymex_rfc0005_s8o_termination.nim:185-205`; `seqLenCaps` `runtime.nim:12706` (cap value not re-verified) | as written |
| PRC-11 | open, **stale-evidence** ("last probed at 136ad60") | no probe at head; `symex.nim:1735-1747` seq-of-unrenderable witness reader still "not yet implemented" | re-probe at head (cheap), then model or record |
| PRC-12 | open, stale-evidence (136ad60); AUD-08 widens it | `runtime.nim:6689-6792` `defaultZero` raises for non-int64 HashSet elements | merge AUD-08 into this row; re-probe |
| PRC-13 | open, stale-evidence (136ad60) | `ceUnsupportedHof` | re-probe |
| PRC-14 | open, stale-evidence (136ad60) | `heUnsafeCast` | re-probe |
| PRC-15 | open | | as written |
| PRC-16 | open; **mis-filed** (a walker *fault* is §5.3's class) | the only `zeroMem`/`copyMem` pins are the opaque-global form (`tests/tsymex_rfc0005_s8cs_routes2.nim:130-135,363-366`, `feOpaqueEffectHavoc`); the `zeroMem(addr x, …)` fault shape has no test. `read` | move to §5.3 (CRH) until "first make it a named decline" lands, then back here |
| PRC-17 | open | | |
| PRC-18 | open (precision only) | the compile stop is closed: `tests/tsymex_rfc0005_s8cl_lifetime_b.nim:99,193-199` `declines(sutCreate, "cr", "create")` with a native `nim` test at `:167`. `read` | row text should say "declines since S8cl (pinned)"; CRH-02 is the closed half |
| PRC-19 | open | `tsymex_rfc0005_s8cl_lifetime.nim` has `finalizer` | |
| PRC-20 | open (precision only) | `s8cl_lifetime_b.nim:105-109,200-201` `declines(sutGcRef, "gr", "nnkCast")`, `declines(sutWhenMember, "wn", "WhenMember")`. `read` | as PRC-18 |
| PRC-21 | open | SND-06's remainder | |
| PRC-22 | open; **overlaps** PRC-34 ("a type section in a routine body (with PRC-22)") | | merge into one row |
| PRC-23 | open | | |
| PRC-24 | open (precision); integrator's sub-task **done** | `tests/tsymex_rfc0005_b10_integration_b.nim:4-8`: `alt_miss` pinned `sxUnknown` with Nim's run beside it and "a larger budget does not change the answer". `read` | strike "Batch 10's integrator was to add a native pin and check with a longer budget"; what remains is identical to PRC-33 item 10 — merge |
| PRC-25 | open (guidance) | `runtime.nim:15430` `limitSitesIn` exists on the walker path; the concolic flip solve is INT-33's third bullet | fold into INT-33 or keep as "no verdict observed wrong" |
| PRC-26 | open, **stale-evidence** | `nsc_dead` is in no test (`ran`: grep empty); the probe is not in the corpus | re-collect the SUT or drop |
| PRC-27 | **closed** | `tests/tsymex_rfc0005_s8bt_limit_langs_b.nim:76-79`: `verdict(replaceTarget, "bt_limit_replace")` with the template default `want = sxSat` (`:59`) on the interpreter, comment "Z3 5.1 finds "c", Z3 4.13.4 … through step 1e (RFC-0005 S8cn)". The pin is no longer sat-or-decline. `read` | drop the row (closed by S8cn's step 1e) |
| PRC-28 | open; last two bullets **duplicate-of** PRC-30 (S8ch) | `pureLvalueTarget` `dsl_parser.nim:17611-17616` "exact model … is for RFC-0016" | strike the two S8ch bullets here |
| PRC-29 (S8cg) | open | item 4: `tsymex_rfc0005_s8bc_remainder_c2.nim:72-74` still `{sxSat, sxUnknown}` under defaults; item 5: `tsymex_rfc0005_s8bb_replace_d.nim:77-81` same. Item 8 timing: `s8bb_constructs` 40.7 s on Windows (`scripts/ci-suite-seconds.tsv`, `ran`), under 60; `tsymex_r6_b6_optionregion` is **not in the tsv at all** (`ran`: 0 hits) — it is in no Windows shard, so its time is unmeasured. `read`/`ran` | item 8 half-done; add r6_b6_optionregion to a shard or record why not |
| PRC-30 (S8ch) | open | no `s8ch` test exists | |
| PRC-31 (S8ci) | open; the `configdefaults_depth` bullet is **met by S8cm's split**, not by lowering the depth | `tests/tsymex_configdefaults_b.nim:21-22` "S8cm: part 2 of 2 … split so that each part compiles and runs in under 60 s"; part 2 is 53.6 s on Windows (`ran`); `maxCallDepth` pins unchanged (`:52-65`). `read` | strike that bullet; the other five stand |
| PRC-32 (S8cj item 1) | open | INT-04's cpp spend drift (`0005 handoff:580`: passed once at `476976d3`, "why is not yet known") is the same phenomenon in-process | cross-reference INT-04 |
| PRC-33 (S8co) | open | item 10 = PRC-24 | merge PRC-24 in |
| PRC-34 (S8cp item 7) | open | `runtime.nim:8341` confirms whole-`seq ==` shares `eqBV`'s catch-all with whole-tuple `==` | add "whole-seq `==`" to the bullet |
| PRC-35 (S8cp item 8) | open | `dsl_typebridge.nim:1500-1507` (holey enum), `dsl_parser.nim:11205,11831` (`$float`; `$bool` is also deferred and not named) | add `$bool` |

### §5.3 Crashes (CRH)

| Row | Status | Evidence | Action to close |
|---|---|---|---|
| CRH-01 | open; evidence **stale** | S8cu's three-way table confirmed SAME: `docs/rfc/0005-branch-scoped-degrade.md:15478` "`s.sort()` … aborts the compile, the same as main (`dsl_typebridge.nim(1261,20) Error: node has no type`)". `read` | replace "S8cu is collecting both columns again" with "confirmed SAME by S8cu"; INT-09 (`splitLines`) is the same `classifyType` family — one row |
| CRH-02 | **closed** | `tests/tsymex_rfc0005_s8cl_lifetime_b.nim:193-201` (create, GC_ref, when-member decline), native `nim` test `:167`. `read` | close; models stay as PRC-18/PRC-20 |
| CRH-03 | open; duplicate-of INT-02 | no `iteDeep`/OOM pin in `tests/` (`ran`: grep empty) | one row |
| CRH-04 | **closed** | `tests/tsymex_rfc0005_r1_pcrelimits.nim:6-18` cites CRH-04; commits `c9682ebc`, `9663105d`. Note the closure text sits in the **Owner** column of the table (format slip) | move the closure note into Evidence / strike the row |
| CRH-05 | open; **duplicate-of** PRC-05's "pointer plus 11 inserts" bullet | no liveness pin | one row |

### §5.4 CI (CI)

| Row | Status | Evidence | Action to close |
|---|---|---|---|
| CI-01 | **stale-evidence**; remainder = INT-17 | S8cm is done (`9ebe2a46`; shard target 23 min at `d7948de5`). `scripts/ci-suite-seconds.tsv` has **30** suites over 60 s (`ran`: awk). The row still says "S8cm is running" | rewrite as "S8cm done; 30 files over 60 s remain (INT-17)"; merge with INT-17 and INT-08 |
| CI-02 | open | `.github/workflows/` = `fuzzer-mingw`, `fuzzer-msvc`, `symex-mingw`, `tianguis-publish` (`ran`: ls). **No Linux leg of any kind**, no cpp, no `schedule:`. Z3 4.13.4 *is* run on every push by all three Windows legs (`symex-mingw.yaml:212`, `fuzzer-*.yaml`) | the "run 4.13.4 on a schedule" half is already met on Windows/c; what is missing is Linux + cpp |
| CI-03 | open; **stale-evidence**; duplicate-of INT-04 | at `476976d3` the cpp gate **passed** (`0005 handoff:574,580`: "fixed=1 … why is not yet known, so INT-04 stays open"); the row still says it fails deterministically on cpp. `tests/tsymex_rfc0005_s8by_remainder.nim:189` is still `check r.units == base.units` | update the evidence; one row with INT-04 and PRC-32 |

### §5.5 Infrastructure (INF)

| Row | Status | Evidence | Action to close |
|---|---|---|---|
| INF-01 | open (slice D1) | | |
| INF-02 | **closed** by decision D-0016-2 | front-matter `fork-c-clean-replay` resolved | strike from the work list (keep as record) |
| INF-03 | open | `docs/rfc/0016-native-parity-hardening.handoff.md` does not exist (`ran`: ls); no `F-NNNN` ledger, no weekly rate report | create it |
| INF-04 (S8ck-r) | open; external | nim-z3 items live in `~/projects/nim/libs/nim-z3`, not this repo; unverifiable from the snapshot | as written |
| INF-05 | **done** (2026-11-03) | | strike |

### §5.6 Upstream (UPS)

| Row | Status | Evidence | Action |
|---|---|---|---|
| UPS-01 | open (decided: file) | no issue URL anywhere in `docs/` (`ran`: grep for `nim-lang/Nim/issues`, `Z3Prover/z3/issues` empty); reduction at `origin/worker-sls2:worker-reports/s8ce-purenim.nim` is in git, not only on the offline host | file it; record the URL |
| UPS-02 | held (D-0016-3) | `mk_unique` appears in no src/test (`ran`) | wait for S8cj |
| UPS-03 | open (decided: file) | | file it |

### §5.7 Pending (PND) — most of this section is already dispositioned

The handoff's final entry (`0005 handoff:280-284`, `read`) says: "U1, U2, U6 and
U7 are verified; U5's original SUT is on the offline worker (INT-20). The two
latent crashes do not reproduce on either tree." The §5.7 table was not
updated after that.

| Row | Status | Evidence | Action |
|---|---|---|---|
| PND-01 (U1) | **closed at disposition** | verified on 8.37/8.39/8.44 JIT (INT-19); the candidate declines where `main` gave a false pair | strike; the only remainder is INT-19 (8.37 **without** JIT not run) |
| PND-02 (U2) | **closed at disposition**, remainder in S8co item 2 / INT-19 | as above | strike; keep the differential-only older-PCRE leg under PRC-33 |
| PND-03 (U3) | open | no macOS/BSD host; same as S8cp-r item 6 | one row with S8cp-r |
| PND-04 (U4) | open (latent, avoided) | `runtime.nim:12687` `byteLeafIds` unchanged; "does not reproduce on either tree" | keep; it is a §5.3 crash row now that disposition is done |
| PND-05 (N3) | **superseded by INT-18** | 450 runs × 3 trees rc 0; precision loss recorded | strike |
| PND-06 (U5) | **duplicate-of** INT-20 | | strike |
| PND-07 (U6) | **closed at disposition** | "U6 verified" | strike |
| PND-08 (U7) | **closed at disposition** | "U7 verified" | strike |
| PND-09 (U8) | **closed** | release gate: c + Z3 4.13.4 969/969, identical to 5.1 (`0005 handoff:272-274`) | strike |
| PND-10 | open; overlaps UPS-02 / S8cj item 2 | | one row |
| PND-11 | open | `check_options.nim:36-40`: a push the text does not show "is caught by its `{.pop.}`" only | keep; its class is soundness-risk (a miss is a false `sxRaised`) and it belongs in §5.1, not pending |
| PND-12 | **mostly closed** | S8cu's resumed rows have their three-way tables in the RFC-0005 as-landed note (`0005:15527-15560`), `main` column filled. The `cmpIgnoreStyle` hang and the nil-deref/`NilAccessDefect` rows: `tests/tsymex_rfc0005_s8cu_nil*.nim` exist; `cmpIgnoreStyle` is in no s8cu test (`ran`) | strike all but `cmpIgnoreStyle` (re-row it as a hang) |
| PND-13 | open | `tests/tsymex_rfc0005_s8ct_b19.nim` pins the walker's recursion, not Z3's internal depth | keep |

### §5.8 Intake (INT / AUD)

| Row | Status | Evidence | Action |
|---|---|---|---|
| INT-01 | duplicate-of PRC-01 | | collapse |
| INT-02 | duplicate-of CRH-03 | | collapse |
| INT-03 | duplicate-of CRH-04 (closed) | | strike |
| INT-04 | open; stale-evidence (passed on cpp at `476976d3`, cause unknown) | `0005 handoff:580` | one row with CI-03/PRC-32 |
| INT-05 | **mis-classified** | `tests/tsymex_rfc0005_s8ct_deepterm.nim:105-111` "two aliases to an object **build**, and decline as main does" (`feUnsupportedParamType`). It no longer stops the compile. `read` | reclass from "crash (compile stop)" to precision |
| INT-06 | open | `runtime.nim:5942` `termWalkMaxDepth` | |
| INT-07 | open (perf, nim-z3) | | |
| INT-08 | **closed** by S8cm's split | `s8ct_deepterm` 43.6 s, `_b` 50.4 s in `ci-suite-seconds.tsv` (`ran`); B19 split to `s8ct_b19` | strike |
| INT-09 | open; same family as CRH-01 | `s8cq_stops` covers a different stop (alias/pragma formal) | one row with CRH-01 |
| INT-10 | open; member of PRC-04 | `tests/tsymex_rfc0005_s8bg_remainder.nim:146-150` (`cvm` declines) | fold into PRC-04 |
| INT-11 | open | `tsymex_rfc0005_s8cs_routes.nim:195-199`: `trace1` is run natively only ("only Nim runs this one"); the walker is pinned on `trace2` (`:659`) | add a walker pin that expects a named decline, then fix the `coerceIntLit` fault |
| INT-12 | open | `tests/tsymex_rfc0005_s8cu_nil_setjmp.nim(.nims)` | |
| INT-13 | duplicate-of PRC-02 | | collapse |
| INT-14 | duplicate-of PRC-01 | | collapse |
| INT-15 | open | `replayproc.nim:171-176` lists six hooks; `setControlCHook` absent (`ran`: 0 hits in src) | three-way row then fix |
| INT-16 | closed (`8f00b736`) | | strike |
| INT-17 | open | 30 suites > 60 s (`ran`) | merge CI-01 into it |
| INT-18 | open (precision) | no `p7` test in the corpus (`ran`) | pin p7 at head, then model |
| INT-19 | open | | |
| INT-20 | **stale-evidence** | the sls2 host is offline, but `origin/worker-sls2` is fetched in this clone with 88 report files (`ran`: `git ls-tree`); the U5 SUT is **not** among them. S8cl's reconstruction is pinned at `tsymex_rfc0005_s8cl_magics.nim:61-72` | recover from the host or declare the reconstruction the pin and close |
| INT-21 | open | `ai_caught` is in no test (`ran`) | pin natively |
| INT-22 | open | `symex.nim:4030` comment: "after the target (`witnessUnsafe`) is never splatted here" — the **replayed** case; a clean winner never replayed still runs in the host | as written |
| INT-23 | open | `useMalloc` has no handling in `replayproc.nim` (`ran`: 0 hits) | as written |
| INT-24 | **closed** by review R1 | `d8969822` "Carry replay results and run-dependence as values, not threadvars"; `threadvar` has 0 hits in `replayproc.nim`/`replayresult.nim` (`ran`). The 0.9.1 wiring audit's "threadvar reset by each entry macro's settle" no longer describes head | strike |
| INT-25 | open (hypothesis, no host) | `replayproc.nim:392-393,470-471` `when defined(linux)` guards `setpgid`/`PDEATHSIG`; `:100-108` the macOS/musl `quit(n)` hint is a second macOS-only limitation (WA-13) not on any row — HRV-03 | |
| INT-26 | open | `tsymex_rfc0005_r1_pcrelimits.nim` raises `RegexError` through `symexFind` only; no test routes it through `symexFindAllWitnesses` (`ran`) | as written |
| INT-27 | open | `canonicalize.nim:6542` | |
| INT-28 | open; one sub-item stale | `waitpid(-1` has 0 hits (`ran`); `replayproc.nim:480` uses `waitpid(pid, …)` | strike the `waitpid(-1)` bullet |
| INT-29 | open | `replayproc.nim:1014` `c_exit_now`; `_exit(127)` literal not found but the path exists | |
| INT-30 | open | `replaywire.nim`: no depth/zero-size guard found (`ran`) | |
| INT-31 | open | `canonicalize.nim:6596-6620` `buildFlagsSegment` keys checks, danger, release, mm, backend, exceptions, threads, stackTrace, lineTrace — **not** `--opt`, `--cc`, `--cpu`, `--os`. `read` | as written |
| INT-32 | open; three sub-items **stale** | "three-valued" and "trusted by construction" strings have 0 hits (`ran`); the one-digit codec is enforced by `3476f039` ("refuse a field past one digit") | strike those three bullets |
| INT-33 | open | `engine/targeting.nim:390` `saveSecondary` still unguarded (`read`) | |
| INT-34 | open | `runtime_*.nim` are six files (`ls`); `FindingHint` strings | |
| INT-35 | open | `exits.nim` `mitemsSince`; `runtime.nim` `forEachExitGroup` | |
| INT-36 | open | `engine/frame.nim` `droppedSymexFindings` — 3 hits, all in that file (`ran`) | |
| INT-37 | open | `symBodyHash` in `check_options.nim`, `dsl_parser.nim`, `symex.nim` | |
| INT-38 | open | `symex.nim` `raised2` (2 hits) | |
| INT-39 | open (decided) | `types.nim:3141` `fromCache*: bool` still present | remove in 0.10.0 |
| AUD-01 | open ("stays by design" record) | | write the record; no slice |
| AUD-02 | open (policy) | | |
| AUD-03 | open (test-harness) | | |
| AUD-04 | closed | | strike |
| AUD-05 | open | | |
| AUD-06 | open | | |
| AUD-07 | open | | |
| AUD-08 | open; merge into PRC-12 | `runtime.nim:6689-6792`: Table with **non-string keys** also raises in `defaultZero` and is on no row — HRV-04 | |
| AUD-09 | open (record) | | |
| AUD-10 | closed | | strike |
| AUD-11 | open (record) | | |

### Front-matter `[[slice]]` rows

| Slice | Status | Overlaps |
|---|---|---|
| D1 | pending | = INF-01 |
| S8cg | pending | = PRC-29 |
| S8ch | pending | = PRC-30 = PRC-28's last two bullets |
| S8ci | pending | = PRC-31 |
| S8cj | pending | = PRC-32 + UPS-02 + PND-10 |
| S8ck-r | pending | = INF-04 |
| S8co | pending | = PRC-33 (+ PRC-24, PND-02 remainder) |
| S8cp-r | pending | items: 4 = INT-18 (p7 no longer crashes), 5 = "n42 on cpp" — the handoff's pre-tag probes say "cpp n42, n43 … pass" (`0005 handoff:283`), so this item is **closed**; 6 = PND-03; 7 = PRC-34; 8 = PRC-35 |
| rv0005-lows | pending | = INT-28..INT-38 |

**Tracker finding.** `quipu show 0016` (`ran`) reports "progress: 8/17 rows
done" — that is 4 items + 4 decisions + 9 slices. The ~105 table rows in §5
are not tracked at all. Under D-0016-1 ("closes when the work list is empty")
the exit criterion has no machine-readable measure; every §5 row that is to be
worked needs a `[[slice]]` (or the tracker needs to read the tables).

### Counts (126 table ids: SND 12, PRC 35, CRH 5, CI 3, INF 5, UPS 3, PND 13, INT 39, AUD 11 — `ran`; plus 9 `[[slice]]` rows that all map onto them)

| Class | Count | Ids |
|---|---|---|
| closed (strike) | 22 | SND-02, 03, 04, 05, 10, 11; PRC-27; CRH-02, 04; INF-02, 05; PND-01, 02, 05 (superseded by INT-18), 07, 08, 09; INT-08, 16, 24; AUD-04, 10. (The document already marks 6 of these closed: CRH-04, INF-05, INT-16, AUD-04, AUD-10, INF-02 — the other 16 are new closures) |
| closed-by-decline: soundness done, precision remainder | 4 | SND-01 (→ **no row**, HRV-01), SND-06 (→ PRC-21), SND-08 (→ PRC-04/INT-10), SND-09 (→ PRC-04) |
| needs-native-repin | 2 | SND-07, SND-12 |
| duplicate-of (collapse into the named row) | 14 | INT-01, INT-14 → PRC-01; INT-13 → PRC-02; INT-02 → CRH-03; INT-03 → CRH-04; INT-04 → CI-03; PND-06 → INT-20; CRH-05 → PRC-05; PRC-30 ↔ PRC-28; PRC-24 → PRC-33; PRC-22 ↔ PRC-34; INT-10 → PRC-04; CI-01 → INT-17; AUD-08 → PRC-12 |
| stale-evidence (still open; rewrite the evidence cell) | 11 | CRH-01, CI-03, INT-20, INT-28 (one bullet), INT-32 (three bullets), PND-12, PRC-26, PRC-11, PRC-12, PRC-13, PRC-14 |
| mis-classified / mis-filed (still open) | 3 | INT-05 (builds and declines; not a compile stop), PRC-16 (a walker fault; §5.3), PND-11 (a soundness risk; §5.1) |
| open as written | 70 | the rest |

Net: 126 ids − 22 closed − 14 duplicates − 4 decline-closed = **86 distinct
open rows** (70 as written, 11 with stale evidence, 3 to re-file, 2 to
re-pin), before the harvest below adds to them.

---

## 2. Harvest — in-code markers (`src/nelli/smt/`, `src/nelli/symex.nim`)

Collected by a read-only sub-lens over 562 marker hits (`ran`: grep), 44 kept;
`symexWalkerVersion` = 272 (`canonicalize.nim:251`). Full table in §2.2; the
headline items first.

### 2.1 Proposed new rows from code

| Id | Source | Item | Class | Already a row? |
|---|---|---|---|---|
| HRV-01 | SND-01's remainder; `dsl_parser.nim:8022-8029` | exact model of a `var`-returning actual (`rab(t["a"], t, "a")`, `mgetOrPut` actual, user `var`-return): the callee writes the location through both actuals | precision | no (SND-01 closes as a decline; no PRC row names it) |
| HRV-02 | SND-07's remainder | exact model of `uncheckedAssign` where the other arm's bytes differ | precision | no |
| HRV-03 | `replayproc.nim:100-108` (WA-13) | forked child without `on_exit` (macOS, musl) reports `quit(n)` as exit code 0 in the hint text | precision (hint) | no; same no-host blocker as INT-25 |
| HRV-04 | `runtime.nim:6689-6792` `defaultZero` | a `Table` with non-string keys (and `HashSet` with non-int64 elements) raises `ValueError` at zero-init, wrapped into a decline | precision | HashSet half = AUD-08/PRC-12; Table half **no** |
| HRV-05 | `types.nim:1968-2389` (12 members), `runtime.nim:111-153, 28175-28232` | 12 `SymexErrorKind` members with no producer (`geVtableDispatch`, `geUnresolvedGeneric`, `ceUnsupportedCapture`, `seByteIndexUnsupported`, `feConvDomainExcluded`, `heUnsupportedVarRef` (undocumented), `hePtrArith`, `seParseIntPreE`, `seBytesSymbolicLength`, `seBytesLengthTooLarge`, `feTransparentArgNotInert`, `feTransparentResultUsed`); two more (`eeRaiseUnimplemented`, `eeTryUnimplemented`) produced only in `except` arms for exception types never raised; five dead exception types | hygiene | no; INT-16 shows ordinals are a documented surface, so this is a 0.10.0 decision alongside INT-39 |
| HRV-06 | `dsl_parser.nim:16196-16244` | `unsupportedFieldPlaceholder` falls back to `mkIntLit(0)` for `itTable/itSet/itArray/itVariant/itMultiVariant/itDistinct/itUninterp` — "same residual risk as before R8" (R8 fixed a `weInternalWalkerFault` for the other kinds) | crash (latent) | no |
| HRV-07 | `runtime.nim:6659, 20169-20193, 23496`; `canonicalize.nim:3971` | composite-typed proc return through a raise-fork or implicit-result path "not yet wired" → `feUnsupportedOp` | precision | no |
| HRV-08 | `runtime.nim:7447-7460` | array/seq of proc values indexed symbolically declines (`iteSV` of `svClosure` unmergeable) | precision | no |
| HRV-09 | `runtime.nim:10757, 27899-27982` | symbolic-length `filter`/`map`(with captures)/`fold` → `ceUnsupportedHof` ("DEFERRED to Phase 16") | precision | no (PRC-13 is a different `ceUnsupportedHof` shape) |
| HRV-10 | `runtime.nim:3232` | `distinct` of `distinct`: no ground eject axiom | precision | no |
| HRV-11 | `runtime.nim:11346` | `seq[ref T]` witness renders elements as default cells (R11b/R12 format deferred): sound, not reproducible | precision (witness) | no |
| HRV-12 | `runtime.nim:18292` | `sxRaised` loses a non-literal `newException` message | precision | no |
| HRV-13 | `runtime.nim:29314, 29669`; `concolictaxonomy.nim:155` | concolic G1b does not symbolicate `ckFloat`/`ckBytes`/`ckString` draws | precision (fuzzer path) | no (INT-33 is liveness) |
| HRV-14 | `dsl_parser.nim:19614-19626` | inlined iterator: `return` in the body (CRIT-1) and `break`/`continue` in the for-body decline; the comment promises "lifted in S2" and nothing did | precision | no |
| HRV-15 | `dsl_parser.nim:10404-10422, 19848-19858` | closure-iterator values in expression position / `let it = someIter` (ADR-0014 D6) decline | precision | no |
| HRV-16 | `dsl_parser.nim:13146-13155, 18879, 18914` | multi-case object constructor with a symbolic discriminator (ADR-0029 consumer-gated); multi-variant static-tag reassign "future cycle" | precision | no |
| HRV-17 | `dsl_parser.nim:13302-13310, 13340-13347` | ref-typed field initialised from a non-address expression (P2b) declines | precision | no |
| HRV-18 | `dsl_parser.nim:16136-16185`, `dsl_typebridge.nim:1275,1738` | `owned T` / `Atomic[T]` → `heUnsupportedOwnership` | precision; "stays, reason recorded" candidate (`owned` is dead in Nim; `Atomic` is concurrency, out of both RFCs) | no |
| HRV-19 | `dsl_parser.nim:11740-11747` | `low`/`high` on a non-int-family receiver → `feUnsupportedExprKind` | precision | no |
| HRV-20 | `dsl_parser.nim:20500-20506` | `&`/`&=` with a `char` RHS → `mkUnsupported` (a `needleAsStr` bridge exists for `find`) | precision | no |
| HRV-21 | `dsl_parser.nim:20440-20444` | `raise <existing exception value>` declines (no value tracking) | precision | no |
| HRV-22 | `dsl_parser.nim:20736-20741` | a `symexTarget` nested in an unsupported statement is silently unreachable (hint only; "Phase 12 deferral #3") | precision (label reach) | no |
| HRV-23 | `dsl_parser.nim:15950-15955, 15989-15995` | tuple-yield inlining: non-constructor `yield myTupleVar` declines (ADR-0014 S2 remainder) | precision | no |
| HRV-24 | `abstraction.nim:410-422` | under `-d:danger`/`overflowChecks:off` one unprovable node disables interval promotion everywhere ("recovering precision … is a follow-up") | precision (performance) | no; adjacent to PRC-07/08 |
| HRV-25 | `abstraction.nim:205-213` | `iekStrLen`/`iekStrToInt` intervals unknown → stay BV | precision | no |
| HRV-26 | `transparency.nim:50-63, 144-157, 288-315` | `span-composite ∘ {span-composite, branching}` cells are `dOpaque()` stubs; the classifier never produces `dkSpanComposite` | design-debt | no |
| HRV-27 | `stdlib_models.nim:77-82`, `runtime_floats.nim:74-77` | `nextafter` recognised, not modelled (no SMT-LIB FP primitive) | precision; "stays, reason recorded" candidate | no |
| HRV-28 | `symex.nim:1088-1095` | `symexForAll` named-field tuple strategies: compile `error`, not a decline | precision (API) | no |
| HRV-29 | `types.nim:2887` | `acRange` int-width narrowing "R16-5, deferred … no fork emitted yet" — possibly stale (S8g/S8j model range narrowing at `runtime.nim:1938,6247`) | precision or stale-doc; verify | no |
| HRV-30 | `types.nim:3059` | heap field of container/variant/nested-by-value type renders `<unsupported>` in a witness; unreplayable | precision (witness) | no |
| HRV-31 | stale-doc family: `types.nim:54,77,733,738,1231-1247`; `runtime.nim:248-257,3951,4255,7447,16134,1001-1006`; `abstraction.nim:324-331`; `dsl_typebridge.nim:1750-1752`; `canonicalize.nim:5326-5330`; `dsl_parser.nim:759`; `runtime_heap.nim:724-734` ("temporary" N42 comment); `symex.nim:25-30, 4428-4478` (self-contradicting label-suppression doc); `scan.nim:78` | "STUB in C1/E1/R1a", "defer to #142", "fail before H1 GREEN" comments describing pre-landing state | hygiene (one zero-tech-debt slice, no walker bump) | no |
| HRV-32 | `dsl_parser.nim:5770-5774` | `caseNarrow` tag mining duplicated, not shared ("a later slice can lift it") | design-debt | no |
| →0017 | `canonicalize.nim:2568-2588` (N20 per-iteration solve), `runtime.nim:23022,23060` (`geInstantiationCapped`), `runtime.nim:23590` (call-cache conservatism), `dsl_parser.nim:13775,14394-14398,14900-14906` (idiom recogniser scope) | structural reach | →0017 | 0017 §2 already names the cap and the cache |

### 2.2 Code markers already matching a 0016 row (no action)

`dsl_parser.nim:8022-8029` (by-value sharing, PRC-04); `:16658-16678`
(`lentLoopDecline`, PRC-05); `:16698-16706` (`letCursorDecline`,
PRC-05/SND-12); `:17611-17616` (`pureLvalueTarget`, PRC-28); `runtime.nim:8341`
(whole-seq `==`, PRC-34); `dsl_typebridge.nim:1500-1507` (holey enum, PRC-35);
`dsl_parser.nim:11205` (`$float`, PRC-35); `runtime.nim:6689-6792` (HashSet
non-int, AUD-08/PRC-12). No in-code marker contradicts an existing row.

Soundness-class markers found in code: **none** (every "unsound" hit describes a
fixed defect or `isLoose`, AUD-01). Hang-class: none. Crash-class: one latent
(HRV-06).


---

## 3. Harvest — docs, other RFCs, ADRs, issue handoffs, GitHub

Collected by a read-only sub-lens over `docs/rfc/0001*`, `0011`, `0014`,
`0015`, `0005` (+ handoff, review), `docs/SYMEX_PLAN.md`, `docs/symex/*`,
`docs/issue-016*.handoff.md`, `CHANGELOG.md`, `docs/migration/0.9.{0,1}.md`
and `gh issue list` (36 open). I re-read the four soundness-class citations
myself (`ran`/`read`): N24 is at `0001h:1166` (inside the consolidated
round-1 bullet), the `;impl=` hole at `docs/migration/0.9.1.md:264-273`, the
S8cu UB note at `0005:15483-15485`, S8cs's "Not covered" at
`0005:15212-15222`. Where the sub-lens could not verify a closure it says so.

Abbreviations: `0001h` = `docs/rfc/0001-chapulin-hardening.handoff.md`,
`0005` = `docs/rfc/0005-branch-scoped-degrade.md`, `SP` = `docs/SYMEX_PLAN.md`,
`P16` = `docs/symex/RFC-phase16-language-fragments.md`,
`m0.9.0` = `docs/migration/0.9.0.md`.

### 3.1 Soundness-class items with no 0016 row (these come first)

| Id | Source | Item | Already a row? | Note |
|---|---|---|---|---|
| HRV-33 | `0001h:1166` (N24, "DEFERRED with rationale") | direct arithmetic on an **unstamped top-level int-offset parameter** has no overflow fork → a false `sxUnsat` is reachable on defect-only queries; the naive stamp was a 15-min non-termination; "needs its own design round" | no — AUD-01 is the opt-in `isLoose` case; this is the default route | RFC-0014 (#166) is the design round and is `seed`; 0016 should own the row or point at 0014 explicitly |
| HRV-34 | `docs/rfc/0014:56-74,192`; issue #166 | `isIntOffset` promotions carry no `ziWidth`, so derived arithmetic drops the `OverflowDefect` fork on the default `isOptimised` route; `canonicalize.nim:2221` marks W8 open | partial AUD-01 (which calls the opt-in case "by design"; 0014 calls the default case a soundness payment) | same family as HRV-33; decide the owner |
| HRV-35 | `docs/rfc/0014:113-138,220-230`; #169 | `range[0'u64 .. > int64.high]` bounds round-trip negative through `int64` fields (`smt/types.nim:154,332,1731`) | no | latent; 0014 item i1 awaits Corey |
| HRV-36 | `docs/migration/0.9.1.md:264-273`; `0005-review.md:45` (R1-09) | the `;impl=` cache-key digest does **not** key: `importc`/`dynlib` bodies, a method `fn`'s overrides' own callees, the target of a call through a proc value, the compiler `lib/` tree — "changing a body no key covers still serves the old run's result" | no — INT-31 lists `--opt/--cc/--cpu/--os` and an in-`fn` push only | documented hole; add to INT-31 |
| HRV-37 | `0005:15483-15485` (S8cu "SOUNDNESS (C)") | inline `(v + 1) < 0` at `high(int)` under overflow off is signed-overflow UB gcc folds to false at `-O0`; S8w's wrap presumes C wraps; only the suites were changed (`let` binds the sum first) | no | standing vs `main` unmeasured; needs a three-way row |
| HRV-38 | `0005:15212-15218` (S8cs "Not covered") | stores S8cs's route analysis never sees: a thread/signal handler started before the routine; a hook of a dynamic exception subtype, a `ref Base` or a stored closure that stores through a `ref` or to a local; the ORC cycle collector running a hook of outside garbage | no | stated limit; needs a three-way row or a "stays" record |
| HRV-39 | `m0.9.0:921-923` | Windows re-exec: macro-generated hooks are not seen by the footprint; stdlib C private state is not carried | no (INT-14 adjacent) | unclear class; three-way row |
| HRV-40 | `0005-handoff:336` (S1b) | the parser flattens `block:` so a `break` inside a block in a loop binds to the loop | no | likely fixed by `mkLabelledBlock` (`0005:2466-2517`); closure unverified |
| HRV-41 | `0005-handoff:344` (S7) | `runtime_heap` `lowerInExpr` sites never drain scalar raise forks | no | S8g/S8bb drains likely close it; closure unverified |
| HRV-42 | `docs/rfc/0014:191` | S3 condition: `reconcileInt` must refuse to bridge a banned BV to Int | no | a design constraint for 0014's work, not a defect today |

### 3.2 Crash / hang class with no 0016 row

| Id | Source | Item | Already a row? | Note |
|---|---|---|---|---|
| HRV-43 | `0001h:1097,1155` (N35) | runtime OOM when a proc with its own `while`+`continue` guard is an operand of a `while` guard (`while check(x) and …`); "PRIORITY candidate for the next engine round" | no (CRH-03 is a different OOM) | |
| HRV-44 | `0001h:1139` (N19) | generic procs indexing / `.len` / `.add` on their generic param hit an unguarded `classifyType` ("node has no type" compile stop) | no; same family as CRH-01/INT-09 | zero corpus coverage |
| HRV-45 | `0005-handoff:380-383` (S0b) | `cast[int32](x) + 1` via a helper returning `int` trips a `lowerConvIntWidth` `AssertionDefect` → bare `weInternalWalkerFault`; "to file", never filed | no | `0005:8059` fixed a different `lowerConvIntWidth` fault |
| HRV-46 | `0005:14831-14833,14873-14875`; `m0.9.0:697-698` | PCRE 8.45 **interpreter** SIGSEGV near 8000 subject bytes (`(a|b)*c`) on an 8 MB stack; "no verdict models the crash" | partial PND-01 (JIT `-27` only) | `limitReach` covers match/recursion/JIT limits, not the C stack |
| HRV-47 | `0001h:836-837` | `{'0'..'9'}` set-membership `contains` fails at parse (`getImpl for callee contains`) | no | closure unverified |
| HRV-48 | `0001h:1130` | witness-rendering `KeyError` on ref-to-multi-axis-variant params | no | may be `0005:2451` "N46-followup-2"; closure unverified |
| HRV-49 | `PHASE11_PLAN.md:300` (#8); `P16:299-312` | composite arm-field types under `obj.kind = X` reassignment → walker `ValueError`; `array[SomeEnum, T]` indexing stops the compile | no | closure unverified |
| HRV-50 | `0005:15918-15920` | `$simplify(..)` literal tests in `runtime.nim` print their term; a large term hangs (`guardLiteral` hung 400 s). 8 sites remain: `runtime.nim:6125,7730,7757,18640,18825,18932,21687,22047` | no | hang |
| HRV-51 | `0001:1433` | cumulative `Z3_MEMOUT_FAIL` at about 20 sequential `symexFind` calls in one binary | adjacent INT-07 (same "cumulative Z3 state" family) | hang |

### 3.3 Precision class with no 0016 row (or only a partial one)

| Id | Source | Item | Already a row? |
|---|---|---|---|
| HRV-52 | `0001h:47-53,153-156` (N18) | sentinel-width overflow forks deferred; the gate was lifted when N45 was refuted and never re-decided | no — needs a decision, not a slice |
| HRV-53 | `0001h:265,1103` | `seq == seq` declined with doctrine (quantifier-free) | no; sibling of PRC-34's whole-tuple `==` (see HRV-… in §2: `runtime.nim:8341`) |
| HRV-54 | `0001:1426,1448-1450`; ADR-0011:97,132 (R16-5) | narrowing `uint8(x)` / same-width reinterpret conversions decline; `nnkHiddenStdConv` pass-through; "no truncate primitive". `tests/tsymex_r6_b2_intwidth.nim` exists — closure unverified. Same item as code HRV-29 (`types.nim:2887`) | no |
| HRV-55 | `0001:1444` (ADR-0027) | byte-wise `xor`/bitwise pushing a BV into a Sequence-theory bound declines | no |
| HRV-56 | `0001:1413-1418,1431` | `seq[(string, string)]` formal: witness-reader gap | no |
| HRV-57 | `0001:1405,1409`; `0001h:910` | constructor omitting a `seq[byte]` field degrades the whole proof | no; closure unverified |
| HRV-58 | `0001h:921`; `0001:1027`; `docs/symex/SYMEX_PLAN.md:78` | `s.add('c')` outside recognised loops → `seUnsupportedStringOp`; `&` with a char RHS (code HRV-20 is the same) | no; closure unverified |
| HRV-59 | `0001:1069-1082` | `nnkCurly` set literal (`chars = Whitespace`) unmodelled in strutils routing | no; closure unverified |
| HRV-60 | `0001h:291,393` | universal/UNSAT relational proofs across a call-inlining boundary can diverge | no; "pre-existing general engine limitation" documented only in test comments |
| HRV-61 | `0014:189,93-111`; #167, #168 | literal-initialised BV local carries no interval; whole-program promotion ban | no — owned by 0014 (seed) |
| HRV-62 | `0005-handoff:147-148`; `m0.9.0:473` | `OrderedTable` / `CountTable` → `feUnsupportedParamType` | no |
| HRV-63 | `0005:15334-15336` | S8ct `deepUnsat`: `sxUnsat` on Z3 5.1, `beSolverUndef` on 4.13.4, pinned per version | no; a Z3-version-dependent verdict |
| HRV-64 | `0005:14432-14435,15097-15100`; `m0.9.0:726-727` | a string of unknown provenance (opaque result) with a by-value copy declines | no; "stays" candidate under PRC-04 |
| HRV-65 | `0005:15079,14926-14934`; `m0.9.0:732-735` | declined magics with no row: `newStringUninit`, `deepCopy`, `shallowCopy`, `<`/`<=` of `pointer`, `finished`, `cstring` `isNil`/`$`, `=destroy` | partial PRC-35 |
| HRV-66 | `0005:15308-15309` | a `symexFind` nested inside a replayed SUT declines on every platform | no |
| HRV-67 | `0005:15913-15916` (S8bv remainder, no later slice) | multi-axis variant result holding a `newSeqUninit` seq not paired by `noteUninitReturn`; `for x in s` over a set domain > 256 declines | no |
| HRV-68 | `0005:14807-14815,15090-15092` | by-value declines with a known Nim answer (small sets/arrays, `{.bycopy.}`, `lent`, global with an unrelated writer); targets under `dec`/`+=`/`setLen`/`move`/`new`; `getOS().s.add(1)` family | partial PRC-04/PRC-28 (shapes not itemised) |
| HRV-69 | `0005:15989-15993` | S8cp item 2's declines: `uncheckedAssign` via ref/ptr receiver, `addr`, `var` arg, seq element; runtime-disc constructor; alias after rearm | partial SND-07 / HRV-02 |
| HRV-70 | `0005:15476-15477` | `acRange` not credited under `rangeChecks: off`; the wrapped conversion value is unmodelled | partial PRC-07 |
| HRV-71 | `0005:15580-15582,15622-15624`; `m0.9.0:834-848` | S8cu scan misses after the slice: `mitems[T]` first instantiated elsewhere under a push; a hidden push never popped; an importer outside the graph; nelli under a user push ("may be worse than main") | partial PND-11 (predates these) — soundness-adjacent |
| HRV-72 | `0005:14736-14737` | direct `f(x, x)` still declines (the closure form decides) | partial PRC-05 |
| HRV-73 | `0005-handoff:341` (S5) | `toOct` stays `sxUnknown` | no; closure unverified |
| HRV-74 | `0005-handoff:77-78` (S8b) | `collectUserExnAncestors` skips `nnkType` except types | no; unverified whether a hierarchy is lost |
| HRV-75 | `SP:1041-1049`; `canonicalize.nim:4896` | `seq[Node]` witness is length-only (`extractSeqElements` itRef stub) | partial PRC-05 (witness half unrowed) |
| HRV-76 | `SP:1072-1076` | generic ref objects (`Box[int]`) stay `sxUnknown` | no; closure unverified |
| HRV-77 | `SP:2202-2206` (ADR-0029) | `ref` variant construction; discriminants past the cardinality budget | no |
| HRV-78 | `docs/symex/SYMEX_PLAN.md:71`; `P16:99` | `findRe` deferred (no Z3 indexOf-on-regex) | no; closure unverified after the PCRE move |
| HRV-79 | ADR-0009:385; `closures.md:275-278`; `m0.9.0:453-455` | `var T` capture → `ceUnsupportedCapture` / `ceCaptureByRefUnmodelled`. Note code HRV-05: `ceUnsupportedCapture` has **no producer** at head, so the doc is stale on which kind fires | no |
| HRV-80 | ADR-0014:195-202,244 | first-class resumable iterators; non-call / `var`-iterable `for` stay `sxUnknown` (code HRV-15 is the same) | no |
| HRV-81 | `P16:299-312,297-298`; `RFC-phase15:2940` | `s[a..b] = v`; `countup/countdown(step)`; `set[T]` union/intersect; `case s: string`; `for c in s` over a free string; `varargs` (no IR); `s[i] in set[char]` → `seUnsupportedSetCharInterop` (9 sites) | partial PRC-29/PRC-33; closure unverified (P16 header says "DRAFT STUB", its handoff says shipped at walker v37) |
| HRV-82 | `extending-stdlib.md:101-112` | an opaque proc with `var T` params leaves the env unmutated; `{.symexOpaque(returnRange:)}` follow-up | no; the `var T` case is soundness-adjacent (PRC-04 covers opaque *global* writes only) |
| HRV-83 | `witness-format-v3.md:260-264,311-320` | in-solver-only witness shapes: `seq[ref T]` pointees, recursion past heap depth → nil, `ptr T` in-tuple nil (code HRV-11/HRV-30 are the same) | no |
| HRV-84 | `0163:730-734` | concolic binding covers only scalar `itInt`/`itBool` top-level params (code HRV-13 is the draw-kind half) | no |
| HRV-85 | `m0.9.0:460-461,489-495,548-553,563-567,606-613,716-718,807-808,862-864,906-909,976-980` | the 0.9.0 known-gap list items with no row: generic callees decline; `heNewFieldZeroUnsupported`; reassigning a declined construction; `maxSeqLen`/`seqQueryRLimit` `beSolverUndef`; `maxRecursiveValueDepth = 2` is a const; `feTableIterOrder`; seq ctor > 2^20; the `unsafeNew` cases; `push` in a body; setjmp `heNilDerefMayBeCaught`; fork-held locks; `termWalkMaxDepth` conjunct dropped past 256 (INT-06 is the array half) | no — each needs a row or a "stays, with the number" record under PRC-04 |
| HRV-86 | `m0.9.0:957,985-986,744-745,441-443`; `m0.9.1:56-59`; `CHANGELOG:165-169,103-110` | module vars of wire-uncarriable types decline Windows replay; proc value with no target (`ceClosureUnknownCallee`); `replace` without `str.replace_all` on old Z3 (`seZ3VersionMissing`); `succ/pred/inc/dec/+=/-=` on a type whose bounds are not read; accepted PCRE patterns past 65536 decline; a check-off callee forks a Defect it cannot raise and the hit is replayed each time | partial PRC-01/02, PRC-13, CI-02, CRH-04, PRC-07 |
| HRV-87 | #157, #155 (`dsl_parser.nim:10376-10385`, `tests/tsymex_phase15_A1_loopguard.nim:178`) | CR-1b `nnkStmtListExpr` preamble loop has no `inGuardCond` gate; a `!=`/compound while guard with `continue` over-degrades to `sxUnknown` | no; verified open |
| HRV-88 | ADR-0003:140-144,229-237; `RFC-completeness.md:958-969` | float/string/object discriminators; parallel symex; generic procs under `symexForAll` | partial PRC-05/AUD-08 |

### 3.4 CI, hygiene, design, docs

| Id | Source | Item | Class | Already a row? |
|---|---|---|---|---|
| HRV-89 | `0001h:264,1105,147-151` (N46) | mingw walker divergence on B5-4; k=2 cap + CI skip stay on mingw; needs mingw-side profiling | ci / hang | no (CI-01/02 are budgets and a cpp leg) |
| HRV-90 | `0001h:69-71` | `fuzzer-msvc.yaml` has no `pull_request` trigger (memory confirms) | ci | no |
| HRV-91 | `0005:16010-16011` | `--mm:refc` never tested; refc takes `dwmHavoc`; native bytes under refc unmeasured — §2.2 "same build" asks for this pin | ci | no |
| HRV-92 | `0015:186-202`; #172 | `tn45probe` / `tprobe_n45stats` run in no Windows leg (files still unrenamed) | ci | no — owned by 0015 (seed, Category core) |
| HRV-93 | `CHANGELOG:170-186` | R1-12, R1-13 shipped unpinned ("no program found that reaches the write") | ci | no |
| HRV-94 | `0163:1737-1740`; `0161:198-204` | `dt-bounded.sh` orphan-containment claim false (orphans survived 19–35 h) | ci | no; closure unverified |
| HRV-95 | `SP:2282-2285` (OQ5) | witness folding may change across nim-z3 minor versions; "worth a regression test" | ci | no |
| HRV-96 | GitHub #152, #153, #160, #161, #162, #163 | open issues for shipped work (A5 g8/g10 fix; Euclidean `mod` S8i; Z3-free `import nelli` RFC-0004; the three 016x handoffs shipped in 0.9.0) | hygiene | n/a — close them |
| HRV-97 | `README.md:16`; `.gitignore:41-45`; `0003:37`; ADR-0030:10; #146/#148/#149/#150 | RFC-0002 (parser normalisation) is listed in the README and gitignored by name; no `docs/rfc/0002*` exists; 0003 says "shipped at 0.3.5"; its four issues are open; ADR-0030 N2/N3 (migrate ~13 resolution sites onto `resolveRoutineImpl`; reconcile two `RoutineNodes` sets) = #148/#150 | hygiene | no — commit-or-drop |
| HRV-98 | `0015:135-152`; #171 | four `macros.owner` guards in `dsl_parser.nim` (5181, 6997, 7732, 11789) are correctness-load-bearing; extract `originModule` | hygiene | no — owned by 0015 |
| HRV-99 | `0005-handoff:341,343,374-376`; `0001h:389-401,1130`; `SP:625-641` | dead boundary arms: six string carriers (`runtime.nim` ~13139-13177), four S6b `except` catches, 19 legacy `except Symex*Error` arms, ~18 fixed-name degrade symbols, 18 `CatchableError` carriers; slice-agent residue never ledgered (`ctorIsRefAliasedVariant` re-derivation, `tryEvalInterval`, `ScanError` raisedTypeId, `iteSV` svSeq merge). INF-05's audit started at S8c; the S1–S7 notes were outside it. Same slice as code HRV-05/HRV-31 | hygiene | no |
| HRV-100 | `0001:593-614,1047-1048` (CR-1c) | Defect net inert under `--panics:on`; the walker unit must keep `--checks:on`; stack overflow / libz3 aborts are uncatchable; the build-docs requirement was never shown landed | design / docs | adjacent INT-27 |
| HRV-101 | `0005:15219-15222,15486-15487`; `0005:14434-14435,15093` | a hook that quits on `sxSat`; a `=copy/=sink/=dup` probe that fails to compile is taken for `{.error.}`; `arithChecks` without `acOverflow` is the caller's unchecked claim; `mitems` element used after a resize (UB natively) | design ("stays by design" records) | partial AUD-01/02, PRC-04 |
| HRV-102 | `0015:90-111`; #165 (`symex.nim:1015`) | `forAllWithSymexSeeds` hardcodes `inMemoryDatabase()`, `dbEnabled = false` | design | no — owned by 0015 |
| HRV-103 | `0163:899-901,1599-1604,1660-1662`; `PHASE12_PLAN.md:640-649`; `RFC-unsat-caching.md:192-195,670-675`; `determinism.md:760-771` | no raised-verdict channel from `ConcolicCollectResult` (recorded decision); `drawVars: seq[SymVal]` crosses the public boundary; `dbReusePhase` skips symex seeds on warm runs; generic/typedesc `fn` under `symexForAll` errors; verdict keys reaching shared corpora unenforced; Z3 internal-error catch-to-`sfUnknown`; IR hash compression, DB eviction | design | partial INT-34/INT-38/INT-39 |
| HRV-104 | #159 (`coverage.nim`) | `recordEdge`'s inferred `.sideEffect` makes `{.cover.}` unusable on a `func` | design | no (fuzzer-side, not symex) |
| HRV-105 | `SP:2253-2254`; `RFC-phase15:512-516`; ADR-0005:237-245; `docs/symex/SYMEX_PLAN.md:75,128`; ADR-0006:286-288, 291-292 | "genuine-cannot" families with no "stays" record in 0016: concurrency (no owner anywhere), sNaN/NaN payloads/float80, symbolic-length `sort`, full-Unicode case fold, symbolic-length `filter` by measurement, `cstring` interop, `nextafter` (code HRV-27) | design ("stays, reason recorded") | no |
| HRV-106 | `0011:11-24,90-101` | RFC-0011 items i1–i3; its §5 "0005 is the only unblocked item" is stale (0005 shipped) | design (i3 → 0017) | no |
| HRV-107 | `0014:202-203`; `0015:216-218` | gates cite `base-bbde48c.log`, a pre-0.9.0 baseline | docs | no |
| HRV-108 | `0001:15`; CLAUDE.md; `0001h:3-5` | RFC-0001 Status "Complete" is not in the README vocabulary; CLAUDE.md still names 0001 as the active RFC; the handoff's header says newest-at-end but the 2026-09-01 entries are at `:13-19` and the bottom is 2026-08-22 | docs | no |
| HRV-109 | `SP:12-18,33,58,767,1803,2069,2241-2243`; `README.md:381-422`; ADR-0001:253-271 vs `0017:188` | stale text: SP status block (walker "3", Phases 0–13); ADR-0022/0028/0029 "PROPOSED" (landed); "out of scope v1" lists (shipped); ADR table lists 3 of 18; SP:33 says #133–#135 shipped at `4381404` while ADR-0001 and 0017 §2.1 say loop invariants / assert refinement do not exist — contradiction to settle | docs | no |
| HRV-110 | `m0.9.0:515-517` vs `:853-864`, `:767-769`; `templates-macros.md:86-125`; `abstraction-internals.md:157-159`; `determinism.md:772-782`; PHASE11/12 deferral tables; `RFC-phase16 handoff:67-86`; `0163:2627-2631`; `0162:272-273` | stale "known limitation"/"deferred"/"not tagged" text whose items landed | docs | no |

### 3.5 Items that belong to RFC-0017 (`→0017`), not 0016

| Source | Item |
|---|---|
| `0001h:264,1104,1177`; `0001:783-792,1424,1031-1082,1445` | N7 scan-recogniser dispatch; Q1 char-class/predicate/backward scans; B0 alias-bound scan; Q2 general `s.len`-bounded loops; checksum loops (0017 L2) |
| `0001h:265-266,1103`; `canonicalize.nim:2568-2588` | N20 per-iteration solver check at k-unroll (0017 L1) |
| `SP:380-383,2255-2256`; #133 | loop-invariant inference (0017 L3); #134/#135 assert-based refinement stay precision |
| `SP:2244-2252,2267-2279,1376-1380,2059-2065` | unbounded loops; OQ1 path merging (P1); OQ3 `maxLoopUnwind = 5` never validated (M1); ADR-0028 uncovered loop shapes |
| `SP`; #138; `dsl_parser.nim:20953` | cross-module private callees (0017 E1; 0017 does not cite #138) |
| `m0.9.0:568-577`; `runtime.nim:23022,23060,23590` | `maxRecursionDepth`/`maxHeapDepth` declines; `geInstantiationCapped`; call-cache conservatism (0017 §2.2/§2.4) |
| `RFC-unsat-caching.md:670-675`; `0017:216-219` | `maxFrontierSize` default 0 and the stale `canonicalize.nim:2033` comment (0017 P2) |
| `0014:161-167` | interval survival across loop iterations (fixpoint/widening) borders 0017 L3 |
| `0011:101` | i3: a proof under `maxLoopUnwind = 8` is not a proof |
| CRH-03 | the ref-merge OOM borders 0017 P1; 0017 §4.3 should cite it |

---

## 4. Counts

**Row reconciliation (126 ids + 9 slices):** closed 22 (16 newly found
closed) · closed-by-decline 4 · needs-native-repin 2 · duplicate 14 ·
stale-evidence 11 · mis-filed 3 · open as written 70 → **86 distinct open
rows** after collapsing.

**Harvest (HRV-01 … HRV-110, deduplicated across code and docs; several HRV
ids name the same item from two sources — HRV-20/58, HRV-29/54, HRV-11/30/83,
HRV-15/80, HRV-13/84, HRV-27/105, HRV-05/31/99):**

| Class | New items (no row) | Partial (row exists, shape unnamed) |
|---|---|---|
| soundness | 8 (HRV-33..41, two closure-unverified) | 3 (HRV-34 vs AUD-01, HRV-39 vs INT-14, HRV-71 vs PND-11) |
| crash | 8 (HRV-06, 43, 44, 45, 47, 48, 49; HRV-46 partial PND-01) | 1 |
| hang | 2 (HRV-50, 51) | 0 |
| precision | ~45 (HRV-01..04, 07..12, 14..25, 28..30, 52..88 less partials) | ~15 (PRC-04/05/07/13/28/29/33/35, SND-07, PRC-01/02, CI-02, CRH-04) |
| ci | 7 (HRV-89..95) | 0 |
| hygiene | 6 families (HRV-05, 26, 31/99, 32, 96, 97, 98) | 0 |
| design / "stays by design" records | ~10 (HRV-42, 100..106) | 3 |
| docs (stale text) | 4 families (HRV-107..110) | 0 |
| →0017 | 10 families (§3.5) | — |

Roughly **100 distinct new or partial items**, of which 8 soundness-class and
10 crash/hang-class have no row today.

**Not harvested as new (already covered):** all 37 RFC-0005 review Lows are
cited by id in INT-28..INT-38; the wiring audit's leftovers are INT-22..27;
the pre-tag probe follow-ups are INT-18..21; the 0.9.0/0.9.1 known-gap lists
cite PRC-01..03, 06..09, 13, 15, 21, SND-06, INT-05/06/09/12/13/14/25/27,
PND-02/03, CRH-01, CI-02 (`read`).

## 5. The five corrections that matter most

1. **Sixteen rows are closed and still listed as open**: SND-02..05, 10, 11
   (S8cb/S8cl/S8cf native pins), PRC-27 (step 1e made `bt_limit_replace`
   exact; `s8bt_limit_langs_b.nim:76-79`), CRH-02 (`s8cl_lifetime_b.nim:193-201`),
   PND-01/02/07/08/09 (dispositioned before the tag, `0005 handoff:280-284`),
   INT-08 (S8cm split), INT-24 (`d8969822`), PND-05 (superseded by INT-18).
   The four remaining SND rows (01, 06, 08, 09) are closed as declines with
   native runs; only SND-07 and SND-12 lack a native pin at head.
2. **Fourteen ids are duplicates** (INT-01/13/14 of PRC-01/02, INT-02/03/04
   of CRH-03/04/CI-03, CRH-05 of PRC-05, PRC-24 of PRC-33, PRC-22 of PRC-34,
   PRC-30 of PRC-28, INT-10 of PRC-04, PND-06 of INT-20, CI-01 of INT-17,
   AUD-08 of PRC-12). The tracker counts none of the 126 table rows at all
   (`quipu show 0016`: 8/17 = items + decisions + slices), so "work list
   empty" is currently unmeasurable.
3. **Three rows are mis-classified**: INT-05 builds and declines
   (`s8ct_deepterm.nim:105-111`), not a compile stop; PRC-16 is a walker fault
   (§5.3); PND-11 is a soundness risk (§5.1), not "pending".
4. **Eight soundness-class items have no row**: N24 unstamped int-offset
   arithmetic (`0001h:1166`) and its 0014 siblings (#166, #169), the `;impl=`
   digest's documented holes (`m0.9.1:264-273`, belongs in INT-31), S8cu's
   signed-overflow UB (`0005:15483`), S8cs's "not covered" store routes
   (`0005:15212`), Windows re-exec's unseen macro-generated hooks
   (`m0.9.0:921`); plus two closure-unverified parser items (S1b block/break,
   S7 drains).
5. **Stale evidence to rewrite**: CI-01 ("S8cm is running" — it is done;
   30 files remain over 60 s), CI-03/INT-04 (passed on cpp at `476976d3`,
   cause unknown), CRH-01 (S8cu confirmed SAME), INT-20 (the sls2 host is
   offline but `origin/worker-sls2` holds the reports; the U5 SUT is not
   among them), INT-28/INT-32 sub-bullets fixed by the review (`waitpid(-1)`,
   "three-valued", "trusted by construction", one-digit codec), PRC-11..14
   ("last probed at 136ad60"), PRC-26 (`nsc_dead` is in no test). Also: the
   closure text of CRH-04 sits in the Owner column; `ceUnsupportedCapture`
   (ADR-0009) and `geVtableDispatch` have no producer, so docs naming them
   as the decline that fires are wrong.
